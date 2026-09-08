/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr

/-!
# Mates in bicategories

This file establishes the bijection between the 2-cells

```
         l₁                  r₁
      c --→ d             c ←-- d
    g ↓  ↗  ↓ h         g ↓  ↘  ↓ h
      e --→ f             e ←-- f
         l₂                  r₂
```

where `l₁ ⊣ r₁` and `l₂ ⊣ r₂`. The corresponding 2-morphisms are called mates.

For the bicategory `Cat`, the definitions in this file are provided in
`Mathlib/CategoryTheory/Adjunction/Mates.lean`, where you can find more detailed documentation
about mates.


## Implementation

The correspondence between mates is obtained by combining
bijections of the form `(g ⟶ l ≫ h) ≃ (r ≫ g ⟶ h)`
and `(g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r)` when `l ⊣ r` is an adjunction.
Indeed, `g ≫ l₂ ⟶ l₁ ≫ h` identifies to `g ⟶ (l₁ ≫ h) ≫ r₂` by using the
second bijection applied to `l₂ ⊣ r₂`, and this identifies to `r₁ ≫ g ⟶ h ≫ r₂`
by using the first bijection applied to `l₁ ⊣ r₁`.

## Remarks

To be precise, the definitions in `Mathlib/CategoryTheory/Adjunction/Mates.lean` are universe
polymorphic, so they are not simple specializations of the definitions in this file.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Bicategory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adjunction

variable {a b c d : B} {l : b ⟶ c} {r : c ⟶ b} (adj : l ⊣ r)

/-- The bijection `(g ⟶ l ≫ h) ≃ (r ≫ g ⟶ h)` induced by an adjunction
`l ⊣ r` in a bicategory. -/
@[simps -isSimp]
/-
**CategoryTheory.Bicategory.Adjunction.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory.Adjunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(g ⟶ l ≫ h) ≃ (r ≫ g ⟶ h)` induced by an adjunction
`l ⊣ r` in a bicategory.
-/
def homEquiv₁ {g : b ⟶ d} {h : c ⟶ d} : (g ⟶ l ≫ h) ≃ (r ≫ g ⟶ h) where
  toFun γ := r ◁ γ ≫ (α_ _ _ _).inv ≫ adj.counit ▷ h ≫ (λ_ _).hom
  invFun β := (λ_ _).inv ≫ adj.unit ▷ _ ≫ (α_ _ _ _).hom ≫ l ◁ β
  left_inv γ :=
    calc
      _ = 𝟙 _ ⊗≫ (adj.unit ▷ g ≫ (l ≫ r) ◁ γ) ⊗≫ l ◁ adj.counit ▷ h ⊗≫ 𝟙 _ := by
        bicategory
      _ = γ ⊗≫ leftZigzag adj.unit adj.counit ▷ h ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.left_triangle]
        bicategory
  right_inv β := by
    calc
      _ = 𝟙 _ ⊗≫ r ◁ adj.unit ▷ g ⊗≫ ((r ≫ l) ◁ β ≫ adj.counit ▷ h) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ rightZigzag adj.unit adj.counit ▷ g ⊗≫ β := by
        rw [whisker_exchange]
        bicategory
      _ = β := by
        rw [adj.right_triangle]
        bicategory

/-- The bijection `(g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r)` induced by an adjunction
`l ⊣ r` in a bicategory. -/
@[simps -isSimp]
/-
**CategoryTheory.Bicategory.Adjunction.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory.Adjunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r)` induced by an adjunction
`l ⊣ r` in a bicategory.
-/
def homEquiv₂ {g : a ⟶ b} {h : a ⟶ c} : (g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r) where
  toFun α := (ρ_ _).inv ≫ g ◁ adj.unit ≫ (α_ _ _ _).inv ≫ α ▷ r
  invFun γ := γ ▷ l ≫ (α_ _ _ _).hom ≫ h ◁ adj.counit ≫ (ρ_ _).hom
  left_inv α :=
    calc
      _ = 𝟙 _ ⊗≫ g ◁ adj.unit ▷ l ⊗≫ (α ▷ (r ≫ l) ≫ h ◁ adj.counit) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ g ◁ leftZigzag adj.unit adj.counit ⊗≫ α := by
        rw [← whisker_exchange]
        bicategory
      _ = α := by
        rw [adj.left_triangle]
        bicategory
  right_inv γ :=
    calc
      _ = 𝟙 _ ⊗≫ (g ◁ adj.unit ≫ γ ▷ (l ≫ r)) ⊗≫ h ◁ adj.counit ▷ r ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ γ ⊗≫ h ◁ rightZigzag adj.unit adj.counit ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.right_triangle]
        bicategory

end Adjunction

section mateEquiv

section

variable {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- Suppose we have a square of 1-morphisms (where the top and bottom are adjunctions `l₁ ⊣ r₁`
and `l₂ ⊣ r₂` respectively).
```
      c ↔ d
    g ↓   ↓ h
      e ↔ f
```

Then we have a bijection between 2-morphisms `g ≫ l₂ ⟶ l₁ ≫ h` and
`r₁ ≫ g ⟶ h ≫ r₂`. This can be seen as a bijection of the 2-cells:

```
         l₁                  r₁
      c --→ d             c ←-- d
    g ↓  ↗  ↓ h         g ↓  ↘  ↓ h
      e --→ f             e ←-- f
         l₂                  r₂
```

Note that if one of the 2-morphisms is an iso, it does not imply the other is an iso.
-/
@[simps! -isSimp]
/-
**CategoryTheory.Bicategory.mateEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Bicategory`。
形式化陈述：mateEquiv : (g ≫ l₂ ⟶ l₁ ≫ h) ≃ (r₁ ≫ g ⟶ h ≫ r₂)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Suppose we have a square of 1-morphisms (where the top and bottom are adjunction
s `l₁ ⊣ r₁`
and `l₂ ⊣ r₂` respectively).
```
      c ↔ d
    g ↓   ↓ h
      e ↔ f
```

Then we have a bijection between 2-morphisms `g ≫ l₂ ⟶ l₁ ≫ h` and
`r₁ ≫ g ⟶ h ≫ r₂`. This can be seen as a bijection of the 2-cells:

```
         l₁                  r₁
      c --→ d             c ←-- d
    g ↓  ↗  ↓ h         g ↓  ↘  ↓ h
      e --→ f             e ←-- f
         l₂                  r₂
```

Note that if one of the 2-morphisms is an iso, it does not imply the other is an
 iso.
-/
def mateEquiv : (g ≫ l₂ ⟶ l₁ ≫ h) ≃ (r₁ ≫ g ⟶ h ≫ r₂) :=
  adj₂.homEquiv₂.trans ((Iso.homCongr (Iso.refl _) (α_ _ _ _)).trans adj₁.homEquiv₁)
/-
**CategoryTheory.Bicategory.mateEquiv_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：mateEquiv_eq_iff (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂) : mateEquiv a
dj₁ adj₂ α = β ↔ adj₁.homEquiv₁.symm β = adj₂.homEquiv₂ α ≫ (α_ _ _ _).hom
参数：α : g ≫ l₂ ⟶ l₁ ≫ h；β : r₁ ≫ g ⟶ h ≫ r₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_apply`：∀ {B : Type u} [inst : Catego
ryTheory.Bicategory B] {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : 
d ⟶ c}   {l₂ : e ⟶ f} {r₂ : f ⟶…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mateEquiv_eq_iff (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂) :
    mateEquiv adj₁ adj₂ α = β ↔
    adj₁.homEquiv₁.symm β = adj₂.homEquiv₂ α ≫ (α_ _ _ _).hom := by
  conv_lhs => rw [eq_comm, ← adj₁.homEquiv₁.symm.injective.eq_iff']
  rw [mateEquiv_apply, Equiv.symm_apply_apply]
/-
**CategoryTheory.Bicategory.mateEquiv_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：mateEquiv_apply' (α : g ≫ l₂ ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otime
s≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁ α ▷ r₂ otimes≫ adj₁.counit ▷ h ▷ r₂ otimes≫ 𝟙
 _
参数：α : g ≫ l₂ ⟶ l₁ ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_apply`：∀ {B : Type u} [inst : Catego
ryTheory.Bicategory B] {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : 
d ⟶ c}   {l₂ : e ⟶ f} {r₂ : f ⟶…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.homEquiv₂_apply`：∀ {B : Type u} [in
st : CategoryTheory.Bicategory B] {a b c : B} {l : b ⟶ c} {r : c ⟶ b}   (adj : C
ategoryTheory.Bicategory.Adjunction l r) {…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.homEquiv₁_apply`：∀ {B : Type u} [in
st : CategoryTheory.Bicategory B] {b c d : B} {l : b ⟶ c} {r : c ⟶ b}   (adj : C
ategoryTheory.Bicategory.Adjunction l r) {…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
-/
lemma mateEquiv_apply' (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ α =
      𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫ adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by
  rw [mateEquiv_apply, Adjunction.homEquiv₂_apply, Adjunction.homEquiv₁_apply]
  bicategory
/-
**CategoryTheory.Bicategory.mateEquiv_symm_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：mateEquiv_symm_apply' (β : r₁ ≫ g ⟶ h ≫ r₂) : (mateEquiv adj₁ adj₂).symm β
 = 𝟙 _ otimes≫ adj₁.unit ▷ g ▷ l₂ otimes≫ l₁ ◁ β ▷ l₂ otimes≫ l₁ ◁ h ◁ adj₂.coun
it otimes≫ 𝟙 _
参数：β : r₁ ≫ g ⟶ h ≫ r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_symm_apply`：∀ {B : Type u} [inst : C
ategoryTheory.Bicategory B] {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {
r₁ : d ⟶ c}   {l₂ : e ⟶ f} {r₂ : f ⟶…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.homEquiv₂_symm_apply`：∀ {B : Type u
} [inst : CategoryTheory.Bicategory B] {a b c : B} {l : b ⟶ c} {r : c ⟶ b}   (ad
j : CategoryTheory.Bicategory.Adjunction l r) {…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.homEquiv₁_symm_apply`：∀ {B : Type u
} [inst : CategoryTheory.Bicategory B] {b c d : B} {l : b ⟶ c} {r : c ⟶ b}   (ad
j : CategoryTheory.Bicategory.Adjunction l r) {…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
（共 31 条，此处仅展示前 30 条）
-/
lemma mateEquiv_symm_apply' (β : r₁ ≫ g ⟶ h ≫ r₂) :
    (mateEquiv adj₁ adj₂).symm β =
      𝟙 _ ⊗≫ adj₁.unit ▷ g ▷ l₂ ⊗≫ l₁ ◁ β ▷ l₂ ⊗≫ l₁ ◁ h ◁ adj₂.counit ⊗≫ 𝟙 _ := by
  rw [mateEquiv_symm_apply, Adjunction.homEquiv₂_symm_apply, Adjunction.homEquiv₁_symm_apply]
  bicategory

end

section

variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : c ⟶ d} {r₂ : d ⟶ c} (adj₂ : l₂ ⊣ r₂)
  {f : a ⟶ c} {g : b ⟶ d}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Bicategory.mateEquiv_id_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Bicategory`。
形式化陈述：mateEquiv_id_comp_right (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g) : mateEquiv adj₁ ((Adj
unction.id _).comp adj₂) φ = mateEquiv adj₁ adj₂ (f ◁ (fun_ l₂).inv ≫ φ) ≫ (ρ_ _
).inv ≫ (α_ _ _ _).hom
参数：φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_apply`：∀ {B : Type u} [inst : Catego
ryTheory.Bicategory B] {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : 
d ⟶ c}   {l₂ : e ⟶ f} {r₂ : f ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
（共 31 条，此处仅展示前 30 条）
-/
lemma mateEquiv_id_comp_right (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g) :
    mateEquiv adj₁ ((Adjunction.id _).comp adj₂) φ =
      mateEquiv adj₁ adj₂ (f ◁ (λ_ l₂).inv ≫ φ) ≫ (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Bicategory.mateEquiv_comp_id_right** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Bicategory`。
形式化陈述：mateEquiv_comp_id_right (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g) : mateEquiv adj₁ (adj₂
.comp (Adjunction.id _)) φ = mateEquiv adj₁ adj₂ ((ρ_ _).inv ≫ (α_ _ _ _).hom ≫ 
φ) ≫ g ◁ (fun_ r₂).inv
参数：φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_apply`：∀ {B : Type u} [inst : Catego
ryTheory.Bicategory B] {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : 
d ⟶ c}   {l₂ : e ⟶ f} {r₂ : f ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
-/
lemma mateEquiv_comp_id_right (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g) :
    mateEquiv adj₁ (adj₂.comp (Adjunction.id _)) φ =
      mateEquiv adj₁ adj₂ ((ρ_ _).inv ≫ (α_ _ _ _).hom ≫ φ) ≫ g ◁ (λ_ r₂).inv := by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

end

end mateEquiv

section mateEquivVComp

variable {a b c d e f : B} {g₁ : a ⟶ c} {g₂ : c ⟶ e} {h₁ : b ⟶ d} {h₂ : d ⟶ f}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c} {l₃ : e ⟶ f} {r₃ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/-- Squares between left adjoints can be composed "vertically" by pasting. -/
/-
**CategoryTheory.Bicategory.leftAdjointSquare.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.leftAdjointSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d e f :
 B} →       {g₁ : a ⟶ c} →         {g₂ : c ⟶ e} →           {h₁ : b ⟶ d} →      
       {h₂ : d ⟶ f} →               {l₁ : a ⟶ b} →                 {l₂ : c ⟶ d} 
→                   {l₃ : e ⟶ f} →                     (CategoryTheory.CategoryS
truct.comp g₁ l₂ ⟶ CategoryTheory.CategoryStruct.comp l₁ h₁) →                  
     (CategoryTheory.CategoryStruct.comp g₂ l₃ ⟶ CategoryTheory.CategoryStruct.c
omp l₂ h₂) →                         (CategoryTheory.CategoryStruct.comp (Catego
ryTheory.CategoryStruct.comp g₁ g₂) l₃ ⟶                           CategoryTheor
y.CategoryStruct.comp l₁ (CategoryTheory.CategoryStruct.comp h₁ h₂))
参数：CategoryTheory.CategoryStruct.comp g₁ l₂ ⟶ CategoryTheory.CategoryStruct.comp
 l₁ h₁；CategoryTheory.CategoryStruct.comp g₂ l₃ ⟶ CategoryTheory.CategoryStruct.
comp l₂ h₂；CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.com
p g₁ g₂) l₃ ⟶                           CategoryTheory.CategoryStruct.comp l₁ (C
ategoryTheory.CategoryStruct.comp h₁ h₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Squares between left adjoints can be composed "vertically" by pasting.
-/
def leftAdjointSquare.vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) :
    (g₁ ≫ g₂) ≫ l₃ ⟶ l₁ ≫ (h₁ ≫ h₂) :=
  (α_ _ _ _).hom ≫ g₁ ◁ β ≫ (α_ _ _ _).inv ≫ α ▷ h₂ ≫ (α_ _ _ _).hom

/-- Squares between right adjoints can be composed "vertically" by pasting. -/
/-
**CategoryTheory.Bicategory.rightAdjointSquare.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.rightAdjointSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d e f :
 B} →       {g₁ : a ⟶ c} →         {g₂ : c ⟶ e} →           {h₁ : b ⟶ d} →      
       {h₂ : d ⟶ f} →               {r₁ : b ⟶ a} →                 {r₂ : d ⟶ c} 
→                   {r₃ : f ⟶ e} →                     (CategoryTheory.CategoryS
truct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.comp h₁ r₂) →                  
     (CategoryTheory.CategoryStruct.comp r₂ g₂ ⟶ CategoryTheory.CategoryStruct.c
omp h₂ r₃) →                         (CategoryTheory.CategoryStruct.comp r₁ (Cat
egoryTheory.CategoryStruct.comp g₁ g₂) ⟶                           CategoryTheor
y.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp h₁ h₂) r₃)
参数：CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.comp
 h₁ r₂；CategoryTheory.CategoryStruct.comp r₂ g₂ ⟶ CategoryTheory.CategoryStruct.
comp h₂ r₃；CategoryTheory.CategoryStruct.comp r₁ (CategoryTheory.CategoryStruct.
comp g₁ g₂) ⟶                           CategoryTheory.CategoryStruct.comp (Cate
goryTheory.CategoryStruct.comp h₁ h₂) r₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Squares between right adjoints can be composed "vertically" by pasting.
-/
def rightAdjointSquare.vcomp (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₂) (β : r₂ ≫ g₂ ⟶ h₂ ≫ r₃) :
    r₁ ≫ (g₁ ≫ g₂) ⟶ (h₁ ≫ h₂) ≫ r₃ :=
  (α_ _ _ _).inv ≫ α ▷ g₂ ≫ (α_ _ _ _).hom ≫ h₁ ◁ β ≫ (α_ _ _ _).inv

/-- The mates equivalence commutes with vertical composition. -/
/-
**CategoryTheory.Bicategory.mateEquiv_vcomp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：mateEquiv_vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) : mateEqui
v adj₁ adj₃ (leftAdjointSquare.vcomp α β) = rightAdjointSquare.vcomp (mateEquiv 
adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β)
参数：α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁；β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
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
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The mates equivalence commutes with vertical composition.
-/
theorem mateEquiv_vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) :
    mateEquiv adj₁ adj₃ (leftAdjointSquare.vcomp α β) =
      rightAdjointSquare.vcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  simp only [leftAdjointSquare.vcomp, mateEquiv_apply', rightAdjointSquare.vcomp]
  symm
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ ⊗≫ r₁ ◁ α ▷ r₂ ▷ g₂ ⊗≫
          ((adj₁.counit ▷ (h₁ ≫ r₂ ≫ g₂ ≫ 𝟙 e)) ≫ 𝟙 b ◁ (h₁ ◁ r₂ ◁ g₂ ◁ adj₃.unit)) ⊗≫
            h₁ ◁ r₂ ◁ β ▷ r₃ ⊗≫ h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ ⊗≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ 𝟙 e) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ g₂ ◁ adj₃.unit)) ⊗≫
            ((adj₁.counit ▷ (h₁ ≫ r₂) ▷ (g₂ ≫ l₃) ≫ (𝟙 b ≫ h₁ ≫ r₂) ◁ β) ▷ r₃) ⊗≫
              h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ 𝟙 e) ≫ (l₂ ≫ r₂) ◁ g₂ ◁ adj₃.unit) ⊗≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ l₃) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ β) ▷ r₃) ⊗≫
            (adj₁.counit ▷ h₁ ▷ (r₂ ≫ l₂) ≫ (𝟙 b ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, ← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit ⊗≫
          r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ l₃) ≫ (l₂ ≫ r₂) ◁ β) ▷ r₃ ⊗≫
            r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ ⊗≫
              adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, ← whisker_exchange, ← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit ⊗≫ r₁ ◁ g₁ ◁ β ▷ r₃ ⊗≫
          ((r₁ ≫ g₁) ◁ leftZigzag adj₂.unit adj₂.counit ▷ (h₂ ≫ r₃)) ⊗≫
            r₁ ◁ α ▷ h₂ ▷ r₃ ⊗≫ adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, ← whisker_exchange]
      bicategory
    _ = _ := by
      rw [adj₂.left_triangle]
      bicategory

end mateEquivVComp

section mateEquivHComp

variable {a : B} {b : B} {c : B} {d : B} {e : B} {f : B}
variable {g : a ⟶ d} {h : b ⟶ e} {k : c ⟶ f}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : d ⟶ e} {r₂ : e ⟶ d}
variable {l₃ : b ⟶ c} {r₃ : c ⟶ b} {l₄ : e ⟶ f} {r₄ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃) (adj₄ : l₄ ⊣ r₄)

/-- Squares between left adjoints can be composed "horizontally" by pasting. -/
/-
**CategoryTheory.Bicategory.leftAdjointSquare.hcomp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.leftAdjointSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d e f :
 B} →       {g : a ⟶ d} →         {h : b ⟶ e} →           {k : c ⟶ f} →         
    {l₁ : a ⟶ b} →               {l₂ : d ⟶ e} →                 {l₃ : b ⟶ c} →  
                 {l₄ : e ⟶ f} →                     (CategoryTheory.CategoryStru
ct.comp g l₂ ⟶ CategoryTheory.CategoryStruct.comp l₁ h) →                       
(CategoryTheory.CategoryStruct.comp h l₄ ⟶ CategoryTheory.CategoryStruct.comp l₃
 k) →                         (CategoryTheory.CategoryStruct.comp g (CategoryThe
ory.CategoryStruct.comp l₂ l₄) ⟶                           CategoryTheory.Catego
ryStruct.comp (CategoryTheory.CategoryStruct.comp l₁ l₃) k)
参数：CategoryTheory.CategoryStruct.comp g l₂ ⟶ CategoryTheory.CategoryStruct.comp 
l₁ h；CategoryTheory.CategoryStruct.comp h l₄ ⟶ CategoryTheory.CategoryStruct.com
p l₃ k；CategoryTheory.CategoryStruct.comp g (CategoryTheory.CategoryStruct.comp 
l₂ l₄) ⟶                           CategoryTheory.CategoryStruct.comp (CategoryT
heory.CategoryStruct.comp l₁ l₃) k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Squares between left adjoints can be composed "horizontally" by pasting.
-/
def leftAdjointSquare.hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) :
    g ≫ (l₂ ≫ l₄) ⟶ (l₁ ≫ l₃) ≫ k :=
  (α_ _ _ _).inv ≫ α ▷ l₄ ≫ (α_ _ _ _).hom ≫ l₁ ◁ β ≫ (α_ _ _ _).inv

/-- Squares between right adjoints can be composed "horizontally" by pasting. -/
/-
**CategoryTheory.Bicategory.rightAdjointSquare.hcomp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.rightAdjointSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d e f :
 B} →       {g : a ⟶ d} →         {h : b ⟶ e} →           {k : c ⟶ f} →         
    {r₁ : b ⟶ a} →               {r₂ : e ⟶ d} →                 {r₃ : c ⟶ b} →  
                 {r₄ : f ⟶ e} →                     (CategoryTheory.CategoryStru
ct.comp r₁ g ⟶ CategoryTheory.CategoryStruct.comp h r₂) →                       
(CategoryTheory.CategoryStruct.comp r₃ h ⟶ CategoryTheory.CategoryStruct.comp k 
r₄) →                         (CategoryTheory.CategoryStruct.comp (CategoryTheor
y.CategoryStruct.comp r₃ r₁) g ⟶                           CategoryTheory.Catego
ryStruct.comp k (CategoryTheory.CategoryStruct.comp r₄ r₂))
参数：CategoryTheory.CategoryStruct.comp r₁ g ⟶ CategoryTheory.CategoryStruct.comp 
h r₂；CategoryTheory.CategoryStruct.comp r₃ h ⟶ CategoryTheory.CategoryStruct.com
p k r₄；CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp r₃
 r₁) g ⟶                           CategoryTheory.CategoryStruct.comp k (Categor
yTheory.CategoryStruct.comp r₄ r₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Squares between right adjoints can be composed "horizontally" by pasting.
-/
def rightAdjointSquare.hcomp (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₃ ≫ h ⟶ k ≫ r₄) :
    (r₃ ≫ r₁) ≫ g ⟶ k ≫ (r₄ ≫ r₂) :=
  (α_ _ _ _).hom ≫ r₃ ◁ α ≫ (α_ _ _ _).inv ≫ β ▷ r₂ ≫ (α_ _ _ _).hom

set_option backward.defeqAttrib.useBackward true in
/-- The mates equivalence commutes with horizontal composition of squares. -/
/-
**CategoryTheory.Bicategory.mateEquiv_hcomp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：mateEquiv_hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) : (mateEquiv (
adj₁.comp adj₃) (adj₂.comp adj₄)) (leftAdjointSquare.hcomp α β) = rightAdjointSq
uare.hcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₃ adj₄ β)
参数：α : g ≫ l₂ ⟶ l₁ ≫ h；β : h ≫ l₄ ⟶ l₃ ≫ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
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
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The mates equivalence commutes with horizontal composition of squares.
-/
theorem mateEquiv_hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (leftAdjointSquare.hcomp α β) =
      rightAdjointSquare.hcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₃ adj₄ β) := by
  simp only [mateEquiv_apply']
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp]
  calc
    _ = 𝟙 _ ⊗≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit ⊗≫
          r₃ ◁ r₁ ◁ ((g ≫ l₂) ◁ adj₄.unit ≫ α ▷ (l₄ ≫ r₄)) ▷ r₂ ⊗≫
            r₃ ◁ ((r₁ ≫ l₁) ◁ β ≫ adj₁.counit ▷ (l₃ ≫ k)) ▷ r₄ ▷ r₂ ⊗≫
              adj₃.counit ▷ k ▷ r₄ ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₃ ◁ r₁ ◁ α ▷ r₂ ⊗≫
          r₃ ◁ ((r₁ ≫ l₁) ◁ h ◁ adj₄.unit ≫ adj₁.counit ▷ (h ≫ l₄ ≫ r₄)) ▷ r₂ ⊗≫
            r₃ ◁ β ▷ r₄ ▷ r₂ ⊗≫ adj₃.counit ▷ k ▷ r₄ ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange, whisker_exchange]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

end mateEquivHComp

section mateEquivSquareComp

variable {a b c d e f x y z : B}
variable {g₁ : a ⟶ d} {h₁ : b ⟶ e} {k₁ : c ⟶ f} {g₂ : d ⟶ x} {h₂ : e ⟶ y} {k₂ : f ⟶ z}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : b ⟶ c} {r₂ : c ⟶ b} {l₃ : d ⟶ e} {r₃ : e ⟶ d}
variable {l₄ : e ⟶ f} {r₄ : f ⟶ e} {l₅ : x ⟶ y} {r₅ : y ⟶ x} {l₆ : y ⟶ z} {r₆ : z ⟶ y}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)
variable (adj₄ : l₄ ⊣ r₄) (adj₅ : l₅ ⊣ r₅) (adj₆ : l₆ ⊣ r₆)

section leftAdjointSquare.comp

variable (α : g₁ ≫ l₃ ⟶ l₁ ≫ h₁) (β : h₁ ≫ l₄ ⟶ l₂ ≫ k₁)
variable (γ : g₂ ≫ l₅ ⟶ l₃ ≫ h₂) (δ : h₂ ≫ l₆ ⟶ l₄ ≫ k₂)

/-- A square of squares between left adjoints can be composed by iterating vertical and horizontal
composition.
-/
/-
**CategoryTheory.Bicategory.leftAdjointSquare.comp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Bicategory.leftAdjointSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d e f x
 y z : B} →       {g₁ : a ⟶ d} →         {h₁ : b ⟶ e} →           {k₁ : c ⟶ f} →
             {g₂ : d ⟶ x} →               {h₂ : e ⟶ y} →                 {k₂ : f
 ⟶ z} →                   {l₁ : a ⟶ b} →                     {l₂ : b ⟶ c} →     
                  {l₃ : d ⟶ e} →                         {l₄ : e ⟶ f} →         
                  {l₅ : x ⟶ y} →                             {l₆ : y ⟶ z} →     
                          (CategoryTheory.CategoryStruct.comp g₁ l₃ ⟶ CategoryTh
eory.CategoryStruct.comp l₁ h₁) →                                 (CategoryTheor
y.CategoryStruct.comp h₁ l₄ ⟶ CategoryTheory.CategoryStruct.comp l₂ k₁) →       
                            (CategoryTheory.CategoryStruct.comp g₂ l₅ ⟶         
                              CategoryTheory.CategoryStruct.comp l₃ h₂) →       
                              (CategoryTheory.CategoryStruct.comp h₂ l₆ ⟶       
                                  CategoryTheory.CategoryStruct.comp l₄ k₂) →   
                                    (CategoryTheory.CategoryStruct.comp (Categor
yTheory.CategoryStruct.comp g₁ g₂)                                           (Ca
tegoryTheory.CategoryStruct.comp l₅ l₆) ⟶                                       
  CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp l₁ l₂) 
                                          (CategoryTheory.CategoryStruct.comp k₁
 k₂))
参数：CategoryTheory.CategoryStruct.comp g₁ l₃ ⟶ CategoryTheory.CategoryStruct.comp
 l₁ h₁；CategoryTheory.CategoryStruct.comp h₁ l₄ ⟶ CategoryTheory.CategoryStruct.
comp l₂ k₁；CategoryTheory.CategoryStruct.comp g₂ l₅ ⟶                           
            CategoryTheory.CategoryStruct.comp l₃ h₂；CategoryTheory.CategoryStru
ct.comp h₂ l₆ ⟶                                         CategoryTheory.CategoryS
truct.comp l₄ k₂；CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStru
ct.comp g₁ g₂)                                           (CategoryTheory.Categor
yStruct.comp l₅ l₆) ⟶                                         CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.CategoryStruct.comp l₁ l₂)                     
                      (CategoryTheory.CategoryStruct.comp k₁ k₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square of squares between left adjoints can be composed by iterating vertical 
and horizontal
composition.
-/
def leftAdjointSquare.comp :
    ((g₁ ≫ g₂) ≫ (l₅ ≫ l₆)) ⟶ ((l₁ ≫ l₂) ≫ (k₁ ≫ k₂)) :=
  vcomp (hcomp α β) (hcomp γ δ)
/-
**CategoryTheory.Bicategory.leftAdjointSquare.comp_vhcomp** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Bicategory.leftAdjointSquare`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c d e f x y z : B
} {g₁ : a ⟶ d} {h₁ : b ⟶ e} {k₁ : c ⟶ f}   {g₂ : d ⟶ x} {h₂ : e ⟶ y} {k₂ : f ⟶ z
} {l₁ : a ⟶ b} {l₂ : b ⟶ c} {l₃ : d ⟶ e} {l₄ : e ⟶ f} {l₅ : x ⟶ y} {l₆ : y ⟶ z} 
  (α : CategoryTheory.CategoryStruct.comp g₁ l₃ ⟶ CategoryTheory.CategoryStruct.
comp l₁ h₁)   (β : CategoryTheory.CategoryStruct.comp h₁ l₄ ⟶ CategoryTheory.Cat
egoryStruct.comp l₂ k₁)   (γ : CategoryTheory.CategoryStruct.comp g₂ l₅ ⟶ Catego
ryTheory.CategoryStruct.comp l₃ h₂)   (δ : CategoryTheory.CategoryStruct.comp h₂
 l₆ ⟶ CategoryTheory.CategoryStruct.comp l₄ k₂),   CategoryTheory.Bicategory.lef
tAdjointSquare.comp α β γ δ =     CategoryTheory.Bicategory.leftAdjointSquare.vc
omp (CategoryTheory.Bicategory.leftAdjointSquare.hcomp α β)       (CategoryTheor
y.Bicategory.leftAdjointSquare.hcomp γ δ)
参数：α : CategoryTheory.CategoryStruct.comp g₁ l₃ ⟶ CategoryTheory.CategoryStruct.
comp l₁ h₁；β : CategoryTheory.CategoryStruct.comp h₁ l₄ ⟶ CategoryTheory.Categor
yStruct.comp l₂ k₁；γ : CategoryTheory.CategoryStruct.comp g₂ l₅ ⟶ CategoryTheory
.CategoryStruct.comp l₃ h₂；δ : CategoryTheory.CategoryStruct.comp h₂ l₆ ⟶ Catego
ryTheory.CategoryStruct.comp l₄ k₂；CategoryTheory.Bicategory.leftAdjointSquare.h
comp α β；CategoryTheory.Bicategory.leftAdjointSquare.hcomp γ δ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftAdjointSquare.comp_vhcomp : comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ) := rfl

/-- Horizontal and vertical composition of squares commutes. -/
/-
**CategoryTheory.Bicategory.leftAdjointSquare.comp_hvcomp** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Bicategory.leftAdjointSquare`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c d e f x y z : B
} {g₁ : a ⟶ d} {h₁ : b ⟶ e} {k₁ : c ⟶ f}   {g₂ : d ⟶ x} {h₂ : e ⟶ y} {k₂ : f ⟶ z
} {l₁ : a ⟶ b} {l₂ : b ⟶ c} {l₃ : d ⟶ e} {l₄ : e ⟶ f} {l₅ : x ⟶ y} {l₆ : y ⟶ z} 
  (α : CategoryTheory.CategoryStruct.comp g₁ l₃ ⟶ CategoryTheory.CategoryStruct.
comp l₁ h₁)   (β : CategoryTheory.CategoryStruct.comp h₁ l₄ ⟶ CategoryTheory.Cat
egoryStruct.comp l₂ k₁)   (γ : CategoryTheory.CategoryStruct.comp g₂ l₅ ⟶ Catego
ryTheory.CategoryStruct.comp l₃ h₂)   (δ : CategoryTheory.CategoryStruct.comp h₂
 l₆ ⟶ CategoryTheory.CategoryStruct.comp l₄ k₂),   CategoryTheory.Bicategory.lef
tAdjointSquare.comp α β γ δ =     CategoryTheory.Bicategory.leftAdjointSquare.hc
omp (CategoryTheory.Bicategory.leftAdjointSquare.vcomp α γ)       (CategoryTheor
y.Bicategory.leftAdjointSquare.vcomp β δ)
参数：α : CategoryTheory.CategoryStruct.comp g₁ l₃ ⟶ CategoryTheory.CategoryStruct.
comp l₁ h₁；β : CategoryTheory.CategoryStruct.comp h₁ l₄ ⟶ CategoryTheory.Categor
yStruct.comp l₂ k₁；γ : CategoryTheory.CategoryStruct.comp g₂ l₅ ⟶ CategoryTheory
.CategoryStruct.comp l₃ h₂；δ : CategoryTheory.CategoryStruct.comp h₂ l₆ ⟶ Catego
ryTheory.CategoryStruct.comp l₄ k₂；CategoryTheory.Bicategory.leftAdjointSquare.v
comp α γ；CategoryTheory.Bicategory.leftAdjointSquare.vcomp β δ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…

--- 原说明 ---
Horizontal and vertical composition of squares commutes.
-/
theorem leftAdjointSquare.comp_hvcomp :
    comp α β γ δ = hcomp (vcomp α γ) (vcomp β δ) := by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ ⊗≫ g₁ ◁ γ ▷ l₆ ⊗≫ ((g₁ ≫ l₃) ◁ δ ≫ α ▷ (l₄ ≫ k₂)) ⊗≫ l₁ ◁ β ▷ k₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

end leftAdjointSquare.comp

section rightAdjointSquare.comp

variable (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₃) (β : r₂ ≫ h₁ ⟶ k₁ ≫ r₄)
variable (γ : r₃ ≫ g₂ ⟶ h₂ ≫ r₅) (δ : r₄ ≫ h₂ ⟶ k₂ ≫ r₆)

/-- A square of squares between right adjoints can be composed by iterating vertical and horizontal
composition.
-/
/-
**CategoryTheory.Bicategory.rightAdjointSquare.comp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.rightAdjointSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d e f x
 y z : B} →       {g₁ : a ⟶ d} →         {h₁ : b ⟶ e} →           {k₁ : c ⟶ f} →
             {g₂ : d ⟶ x} →               {h₂ : e ⟶ y} →                 {k₂ : f
 ⟶ z} →                   {r₁ : b ⟶ a} →                     {r₂ : c ⟶ b} →     
                  {r₃ : e ⟶ d} →                         {r₄ : f ⟶ e} →         
                  {r₅ : y ⟶ x} →                             {r₆ : z ⟶ y} →     
                          (CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTh
eory.CategoryStruct.comp h₁ r₃) →                                 (CategoryTheor
y.CategoryStruct.comp r₂ h₁ ⟶ CategoryTheory.CategoryStruct.comp k₁ r₄) →       
                            (CategoryTheory.CategoryStruct.comp r₃ g₂ ⟶         
                              CategoryTheory.CategoryStruct.comp h₂ r₅) →       
                              (CategoryTheory.CategoryStruct.comp r₄ h₂ ⟶       
                                  CategoryTheory.CategoryStruct.comp k₂ r₆) →   
                                    (CategoryTheory.CategoryStruct.comp (Categor
yTheory.CategoryStruct.comp r₂ r₁)                                           (Ca
tegoryTheory.CategoryStruct.comp g₁ g₂) ⟶                                       
  CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp k₁ k₂) 
                                          (CategoryTheory.CategoryStruct.comp r₆
 r₅))
参数：CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.comp
 h₁ r₃；CategoryTheory.CategoryStruct.comp r₂ h₁ ⟶ CategoryTheory.CategoryStruct.
comp k₁ r₄；CategoryTheory.CategoryStruct.comp r₃ g₂ ⟶                           
            CategoryTheory.CategoryStruct.comp h₂ r₅；CategoryTheory.CategoryStru
ct.comp r₄ h₂ ⟶                                         CategoryTheory.CategoryS
truct.comp k₂ r₆；CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStru
ct.comp r₂ r₁)                                           (CategoryTheory.Categor
yStruct.comp g₁ g₂) ⟶                                         CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.CategoryStruct.comp k₁ k₂)                     
                      (CategoryTheory.CategoryStruct.comp r₆ r₅)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square of squares between right adjoints can be composed by iterating vertical
 and horizontal
composition.
-/
def rightAdjointSquare.comp :
    ((r₂ ≫ r₁) ≫ (g₁ ≫ g₂) ⟶ (k₁ ≫ k₂) ≫ (r₆ ≫ r₅)) :=
  vcomp (hcomp α β) (hcomp γ δ)
/-
**CategoryTheory.Bicategory.rightAdjointSquare.comp_vhcomp** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory.rightAdjointSquare`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c d e f x y z : B
} {g₁ : a ⟶ d} {h₁ : b ⟶ e} {k₁ : c ⟶ f}   {g₂ : d ⟶ x} {h₂ : e ⟶ y} {k₂ : f ⟶ z
} {r₁ : b ⟶ a} {r₂ : c ⟶ b} {r₃ : e ⟶ d} {r₄ : f ⟶ e} {r₅ : y ⟶ x} {r₆ : z ⟶ y} 
  (α : CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.
comp h₁ r₃)   (β : CategoryTheory.CategoryStruct.comp r₂ h₁ ⟶ CategoryTheory.Cat
egoryStruct.comp k₁ r₄)   (γ : CategoryTheory.CategoryStruct.comp r₃ g₂ ⟶ Catego
ryTheory.CategoryStruct.comp h₂ r₅)   (δ : CategoryTheory.CategoryStruct.comp r₄
 h₂ ⟶ CategoryTheory.CategoryStruct.comp k₂ r₆),   CategoryTheory.Bicategory.rig
htAdjointSquare.comp α β γ δ =     CategoryTheory.Bicategory.rightAdjointSquare.
vcomp (CategoryTheory.Bicategory.rightAdjointSquare.hcomp α β)       (CategoryTh
eory.Bicategory.rightAdjointSquare.hcomp γ δ)
参数：α : CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.
comp h₁ r₃；β : CategoryTheory.CategoryStruct.comp r₂ h₁ ⟶ CategoryTheory.Categor
yStruct.comp k₁ r₄；γ : CategoryTheory.CategoryStruct.comp r₃ g₂ ⟶ CategoryTheory
.CategoryStruct.comp h₂ r₅；δ : CategoryTheory.CategoryStruct.comp r₄ h₂ ⟶ Catego
ryTheory.CategoryStruct.comp k₂ r₆；CategoryTheory.Bicategory.rightAdjointSquare.
hcomp α β；CategoryTheory.Bicategory.rightAdjointSquare.hcomp γ δ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightAdjointSquare.comp_vhcomp : comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ) := rfl

/-- Horizontal and vertical composition of squares commutes. -/
/-
**CategoryTheory.Bicategory.rightAdjointSquare.comp_hvcomp** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory.rightAdjointSquare`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c d e f x y z : B
} {g₁ : a ⟶ d} {h₁ : b ⟶ e} {k₁ : c ⟶ f}   {g₂ : d ⟶ x} {h₂ : e ⟶ y} {k₂ : f ⟶ z
} {r₁ : b ⟶ a} {r₂ : c ⟶ b} {r₃ : e ⟶ d} {r₄ : f ⟶ e} {r₅ : y ⟶ x} {r₆ : z ⟶ y} 
  (α : CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.
comp h₁ r₃)   (β : CategoryTheory.CategoryStruct.comp r₂ h₁ ⟶ CategoryTheory.Cat
egoryStruct.comp k₁ r₄)   (γ : CategoryTheory.CategoryStruct.comp r₃ g₂ ⟶ Catego
ryTheory.CategoryStruct.comp h₂ r₅)   (δ : CategoryTheory.CategoryStruct.comp r₄
 h₂ ⟶ CategoryTheory.CategoryStruct.comp k₂ r₆),   CategoryTheory.Bicategory.rig
htAdjointSquare.comp α β γ δ =     CategoryTheory.Bicategory.rightAdjointSquare.
hcomp (CategoryTheory.Bicategory.rightAdjointSquare.vcomp α γ)       (CategoryTh
eory.Bicategory.rightAdjointSquare.vcomp β δ)
参数：α : CategoryTheory.CategoryStruct.comp r₁ g₁ ⟶ CategoryTheory.CategoryStruct.
comp h₁ r₃；β : CategoryTheory.CategoryStruct.comp r₂ h₁ ⟶ CategoryTheory.Categor
yStruct.comp k₁ r₄；γ : CategoryTheory.CategoryStruct.comp r₃ g₂ ⟶ CategoryTheory
.CategoryStruct.comp h₂ r₅；δ : CategoryTheory.CategoryStruct.comp r₄ h₂ ⟶ Catego
ryTheory.CategoryStruct.comp k₂ r₆；CategoryTheory.Bicategory.rightAdjointSquare.
vcomp α γ；CategoryTheory.Bicategory.rightAdjointSquare.vcomp β δ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…

--- 原说明 ---
Horizontal and vertical composition of squares commutes.
-/
theorem rightAdjointSquare.comp_hvcomp :
    comp α β γ δ = hcomp (vcomp α γ) (vcomp β δ) := by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ ⊗≫ r₂ ◁ α ▷ g₂ ⊗≫ (β ▷ (r₃ ≫ g₂) ≫ (k₁ ≫ r₄) ◁ γ) ⊗≫ k₁ ◁ δ ▷ r₅ ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

end rightAdjointSquare.comp

/-- The mates equivalence commutes with composition of a square of squares. These results form the
basis for an isomorphism of double categories to be proven later.
-/
/-
**CategoryTheory.Bicategory.mateEquiv_square** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：mateEquiv_square (α : g₁ ≫ l₃ ⟶ l₁ ≫ h₁) (β : h₁ ≫ l₄ ⟶ l₂ ≫ k₁) (γ : g₂ ≫
 l₅ ⟶ l₃ ≫ h₂) (δ : h₂ ≫ l₆ ⟶ l₄ ≫ k₂) : (mateEquiv (adj₁.comp adj₂) (adj₅.comp 
adj₆)) (leftAdjointSquare.comp α β γ δ) = rightAdjointSquare.comp (mateEquiv adj
₁ adj₃ α) (mateEquiv adj₂ adj₄ β) (mateEquiv adj₃ adj₅ γ) (mateEquiv adj₄ adj₆ δ
)
参数：α : g₁ ≫ l₃ ⟶ l₁ ≫ h₁；β : h₁ ≫ l₄ ⟶ l₂ ≫ k₁；γ : g₂ ≫ l₅ ⟶ l₃ ≫ h₂；δ : h₂ ≫ l₆
 ⟶ l₄ ≫ k₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_vcomp`：mateEquiv_vcomp (α : g₁ ≫ l₂ 
⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) : mateEquiv adj₁ adj₃ (leftAdjointSquare.vcom
p α β) = rightAdjointSquare.vco…
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_hcomp`：mateEquiv_hcomp (α : g ≫ l₂ ⟶
 l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) : (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (
leftAdjointSquare.hcomp α β) = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The mates equivalence commutes with composition of a square of squares. These re
sults form the
basis for an isomorphism of double categories to be proven later.
-/
theorem mateEquiv_square
    (α : g₁ ≫ l₃ ⟶ l₁ ≫ h₁) (β : h₁ ≫ l₄ ⟶ l₂ ≫ k₁)
    (γ : g₂ ≫ l₅ ⟶ l₃ ≫ h₂) (δ : h₂ ≫ l₆ ⟶ l₄ ≫ k₂) :
    (mateEquiv (adj₁.comp adj₂) (adj₅.comp adj₆))
        (leftAdjointSquare.comp α β γ δ) =
      rightAdjointSquare.comp
        (mateEquiv adj₁ adj₃ α) (mateEquiv adj₂ adj₄ β)
        (mateEquiv adj₃ adj₅ γ) (mateEquiv adj₄ adj₆ δ) := by
  have vcomp :=
    mateEquiv_vcomp (adj₁.comp adj₂) (adj₃.comp adj₄) (adj₅.comp adj₆)
      (leftAdjointSquare.hcomp α β) (leftAdjointSquare.hcomp γ δ)
  have hcomp1 := mateEquiv_hcomp adj₁ adj₃ adj₂ adj₄ α β
  have hcomp2 := mateEquiv_hcomp adj₃ adj₅ adj₄ adj₆ γ δ
  rw [hcomp1, hcomp2] at vcomp
  exact vcomp

end mateEquivSquareComp

section conjugateEquiv

section

variable {c d : B}
variable {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- Given two adjunctions `l₁ ⊣ r₁` and `l₂ ⊣ r₂` both between objects `c`, `d`, there is a
bijection between 2-morphisms `l₂ ⟶ l₁` and 2-morphisms `r₁ ⟶ r₂`. This is
defined as a special case of `mateEquiv`, where the two "vertical" 1-morphisms are identities.
This bijection is `conjugateEquiv`; the image of a 2-morphism under it is called its conjugate.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a 2-morphism is an iso
iff its image under the bijection is an iso.
-/
/-
**CategoryTheory.Bicategory.conjugateEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Bicategory`。
形式化陈述：conjugateEquiv : (l₂ ⟶ l₁) ≃ (r₁ ⟶ r₂)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given two adjunctions `l₁ ⊣ r₁` and `l₂ ⊣ r₂` both between objects `c`, `d`, the
re is a
bijection between 2-morphisms `l₂ ⟶ l₁` and 2-morphisms `r₁ ⟶ r₂`. This is
defined as a special case of `mateEquiv`, where the two "vertical" 1-morphisms a
re identities.
This bijection is `conjugateEquiv`; the image of a 2-morphism under it is called
 its conjugate.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a 2-morp
hism is an iso
iff its image under the bijection is an iso.
-/
def conjugateEquiv : (l₂ ⟶ l₁) ≃ (r₁ ⟶ r₂) :=
  calc
    (l₂ ⟶ l₁) ≃ _ := (Iso.homCongr (λ_ l₂) (ρ_ l₁)).symm
    _ ≃ _ := mateEquiv adj₁ adj₂
    _ ≃ (r₁ ⟶ r₂) := Iso.homCongr (ρ_ r₁) (λ_ r₂)
/-
**CategoryTheory.Bicategory.conjugateEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：conjugateEquiv_apply (α : l₂ ⟶ l₁) : conjugateEquiv adj₁ adj₂ α = (ρ_ r₁).
inv ≫ mateEquiv adj₁ adj₂ ((fun_ l₂).hom ≫ α ≫ (ρ_ l₁).inv) ≫ (fun_ r₂).hom
参数：α : l₂ ⟶ l₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjugateEquiv_apply (α : l₂ ⟶ l₁) :
    conjugateEquiv adj₁ adj₂ α =
      (ρ_ r₁).inv ≫ mateEquiv adj₁ adj₂ ((λ_ l₂).hom ≫ α ≫ (ρ_ l₁).inv) ≫ (λ_ r₂).hom :=
  rfl
/-
**CategoryTheory.Bicategory.conjugateEquiv_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_apply' (α : l₂ ⟶ l₁) : conjugateEquiv adj₁ adj₂ α = (ρ_ _).
inv ≫ r₁ ◁ adj₂.unit ≫ r₁ ◁ α ▷ r₂ ≫ (α_ _ _ _).inv ≫ adj₁.counit ▷ r₂ ≫ (fun_ _
).hom
参数：α : l₂ ⟶ l₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_apply`：conjugateEquiv_apply (α 
: l₂ ⟶ l₁) : conjugateEquiv adj₁ adj₂ α = (ρ_ r₁).inv ≫ mateEquiv adj₁ adj₂ ((fu
n_ l₂).hom ≫ α ≫ (ρ_ l₁).inv) ≫ (fun…
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
-/
theorem conjugateEquiv_apply' (α : l₂ ⟶ l₁) :
    conjugateEquiv adj₁ adj₂ α =
      (ρ_ _).inv ≫ r₁ ◁ adj₂.unit ≫ r₁ ◁ α ▷ r₂ ≫ (α_ _ _ _).inv ≫
        adj₁.counit ▷ r₂ ≫ (λ_ _).hom := by
  rw [conjugateEquiv_apply, mateEquiv_apply']
  bicategory
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_apply (α : r₁ ⟶ r₂) : (conjugateEquiv adj₁ adj₂).symm 
α = (fun_ l₂).inv ≫ (mateEquiv adj₁ adj₂).symm ((ρ_ r₁).hom ≫ α ≫ (fun_ r₂).inv)
 ≫ (ρ_ l₁).hom
参数：α : r₁ ⟶ r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem conjugateEquiv_symm_apply (α : r₁ ⟶ r₂) :
    (conjugateEquiv adj₁ adj₂).symm α =
      (λ_ l₂).inv ≫ (mateEquiv adj₁ adj₂).symm ((ρ_ r₁).hom ≫ α ≫ (λ_ r₂).inv) ≫ (ρ_ l₁).hom :=
  rfl
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_apply' (α : r₁ ⟶ r₂) : (conjugateEquiv adj₁ adj₂).symm
 α = (fun_ _).inv ≫ adj₁.unit ▷ l₂ ≫ (α_ _ _ _).hom ≫ l₁ ◁ α ▷ l₂ ≫ l₁ ◁ adj₂.co
unit ≫ (ρ_ _).hom
参数：α : r₁ ⟶ r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_symm_apply`：conjugateEquiv_symm
_apply (α : r₁ ⟶ r₂) : (conjugateEquiv adj₁ adj₂).symm α = (fun_ l₂).inv ≫ (mate
Equiv adj₁ adj₂).symm ((ρ_ r₁).hom ≫ α ≫ …
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_symm_apply'`：mateEquiv_symm_apply' (
β : r₁ ≫ g ⟶ h ≫ r₂) : (mateEquiv adj₁ adj₂).symm β = 𝟙 _ otimes≫ adj₁.unit ▷ g 
▷ l₂ otimes≫ l₁ ◁ β ▷ l₂ otimes≫ l₁ ◁…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
-/
theorem conjugateEquiv_symm_apply' (α : r₁ ⟶ r₂) :
    (conjugateEquiv adj₁ adj₂).symm α =
      (λ_ _).inv ≫ adj₁.unit ▷ l₂ ≫ (α_ _ _ _).hom ≫ l₁ ◁ α ▷ l₂ ≫
        l₁ ◁ adj₂.counit ≫ (ρ_ _).hom := by
  rw [conjugateEquiv_symm_apply, mateEquiv_symm_apply']
  bicategory

@[simp]
/-
**CategoryTheory.Bicategory.conjugateEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：conjugateEquiv_id : conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_apply`：conjugateEquiv_apply (α 
: l₂ ⟶ l₁) : conjugateEquiv adj₁ adj₂ α = (ρ_ r₁).inv ≫ mateEquiv adj₁ adj₂ ((fu
n_ l₂).hom ≫ α ≫ (ρ_ l₁).inv) ≫ (fun…
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
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
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.right_triangle`：∀ {B : Type u₁} [in
st : CategoryTheory.Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}   (self : Ca
tegoryTheory.Bicategory.Adjunction f g), …
-/
theorem conjugateEquiv_id : conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  rw [conjugateEquiv_apply, mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ rightZigzag adj₁.unit adj₁.counit ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 r₁ := by
      rw [adj₁.right_triangle]
      bicategory

@[simp]
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_id** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_id : (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_id`：conjugateEquiv_id : conjuga
teEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _
-/
theorem conjugateEquiv_symm_id : (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_id]
/-
**CategoryTheory.Bicategory.conjugateEquiv_adjunction_id** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_adjunction_id {l r : c ⟶ c} (adj : l ⊣ r) (α : 𝟙 c ⟶ l) : (
conjugateEquiv adj (Adjunction.id c) α) = (ρ_ _).inv ≫ r ◁ α ≫ adj.counit
参数：adj : l ⊣ r；α : 𝟙 c ⟶ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_apply`：conjugateEquiv_apply (α 
: l₂ ⟶ l₁) : conjugateEquiv adj₁ adj₂ α = (ρ_ r₁).inv ≫ mateEquiv adj₁ adj₂ ((fu
n_ l₂).hom ≫ α ≫ (ρ_ l₁).inv) ≫ (fun…
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
-/
theorem conjugateEquiv_adjunction_id {l r : c ⟶ c} (adj : l ⊣ r) (α : 𝟙 c ⟶ l) :
    (conjugateEquiv adj (Adjunction.id c) α) = (ρ_ _).inv ≫ r ◁ α ≫ adj.counit := by
  rw [conjugateEquiv_apply, mateEquiv_apply']
  dsimp [Adjunction.id]
  bicategory
/-
**CategoryTheory.Bicategory.conjugateEquiv_adjunction_id_symm** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_adjunction_id_symm {l r : c ⟶ c} (adj : l ⊣ r) (α : r ⟶ 𝟙 c
) : (conjugateEquiv adj (Adjunction.id c)).symm α = adj.unit ≫ l ◁ α ≫ (ρ_ _).ho
m
参数：adj : l ⊣ r；α : r ⟶ 𝟙 c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_symm_apply`：conjugateEquiv_symm
_apply (α : r₁ ⟶ r₂) : (conjugateEquiv adj₁ adj₂).symm α = (fun_ l₂).inv ≫ (mate
Equiv adj₁ adj₂).symm ((ρ_ r₁).hom ≫ α ≫ …
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_symm_apply'`：mateEquiv_symm_apply' (
β : r₁ ≫ g ⟶ h ≫ r₂) : (mateEquiv adj₁ adj₂).symm β = 𝟙 _ otimes≫ adj₁.unit ▷ g 
▷ l₂ otimes≫ l₁ ◁ β ▷ l₂ otimes≫ l₁ ◁…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
-/
theorem conjugateEquiv_adjunction_id_symm {l r : c ⟶ c} (adj : l ⊣ r) (α : r ⟶ 𝟙 c) :
    (conjugateEquiv adj (Adjunction.id c)).symm α = adj.unit ≫ l ◁ α ≫ (ρ_ _).hom := by
  rw [conjugateEquiv_symm_apply, mateEquiv_symm_apply']
  dsimp [Adjunction.id]
  bicategory

end

@[simp]
/-
**CategoryTheory.Bicategory.mateEquiv_leftUnitor_hom_rightUnitor_inv** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：mateEquiv_leftUnitor_hom_rightUnitor_inv {a b : B} {l : a ⟶ b} {r : b ⟶ a}
 (adj : l ⊣ r) : mateEquiv adj adj ((fun_ _).hom ≫ (ρ_ _).inv) = (ρ_ _).hom ≫ (f
un_ _).inv
参数：adj : l ⊣ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_id`：conjugateEquiv_id : conjuga
teEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mateEquiv_leftUnitor_hom_rightUnitor_inv
    {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r) :
    mateEquiv adj adj ((λ_ _).hom ≫ (ρ_ _).inv) = (ρ_ _).hom ≫ (λ_ _).inv := by
  simp [← cancel_mono (λ_ r).hom,
    ← conjugateEquiv_id adj, conjugateEquiv_apply]

section

variable {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    {l' : a ⟶ b} {r' : b ⟶ a} (adj' : l' ⊣ r') (φ : l' ⟶ l)

/-
**CategoryTheory.Bicategory.conjugateEquiv_id_comp_right_apply** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_id_comp_right_apply : conjugateEquiv adj ((Adjunction.id _)
.comp adj') ((fun_ _).hom ≫ φ) = conjugateEquiv adj adj' φ ≫ (ρ_ _).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_id_comp_right`：mateEquiv_id_comp_rig
ht (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g) : mateEquiv adj₁ ((Adjunction.id _).comp adj₂) φ 
= mateEquiv adj₁ adj₂ (f ◁ (fun_ l₂).in…
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
-/
lemma conjugateEquiv_id_comp_right_apply :
    conjugateEquiv adj ((Adjunction.id _).comp adj') ((λ_ _).hom ≫ φ) =
      conjugateEquiv adj adj' φ ≫ (ρ_ _).inv := by
  simp only [conjugateEquiv_apply, mateEquiv_id_comp_right,
    id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  bicategory
/-
**CategoryTheory.Bicategory.conjugateEquiv_comp_id_right_apply** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_comp_id_right_apply : conjugateEquiv adj (adj'.comp (Adjunc
tion.id _)) ((ρ_ _).hom ≫ φ) = conjugateEquiv adj adj' φ ≫ (fun_ _).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_comp_id_right`：mateEquiv_comp_id_rig
ht (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g) : mateEquiv adj₁ (adj₂.comp (Adjunction.id _)) φ 
= mateEquiv adj₁ adj₂ ((ρ_ _).inv ≫ (α_…
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
-/
lemma conjugateEquiv_comp_id_right_apply :
    conjugateEquiv adj (adj'.comp (Adjunction.id _)) ((ρ_ _).hom ≫ φ) =
      conjugateEquiv adj adj' φ ≫ (λ_ _).inv := by
  simp only [conjugateEquiv_apply, Category.assoc, mateEquiv_comp_id_right, id_whiskerLeft,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id, Iso.cancel_iso_inv_left,
    EmbeddingLike.apply_eq_iff_eq]
  bicategory

end

/-
**CategoryTheory.Bicategory.conjugateEquiv_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_whiskerLeft {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l
₁ ⊣ r₁) {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂) {l₂' : b ⟶ c} {r₂' : c ⟶ b} (
adj₂' : l₂' ⊣ r₂') (φ : l₂' ⟶ l₂) : conjugateEquiv (adj₁.comp adj₂) (adj₁.comp a
dj₂') (l₁ ◁ φ) = conjugateEquiv adj₂ adj₂' φ ▷ r₁
参数：adj₁ : l₁ ⊣ r₁；adj₂ : l₂ ⊣ r₂；adj₂' : l₂' ⊣ r₂'；φ : l₂' ⟶ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_hcomp`：mateEquiv_hcomp (α : g ≫ l₂ ⟶
 l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) : (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (
leftAdjointSquare.hcomp α β) = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_whiskerRight`：leftUnitor_whiskerRig
ht (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (fun_ (f ≫ 
g)).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor_inv`：whiskerLeft_right
Unitor_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g
 (𝟙 c)).hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) {Z : a ⟶ c}   (h : Cat
egoryTheory.CategoryStruct.com…
· 使用定理 `CategoryTheory.Bicategory.inv_hom_whiskerRight_assoc`：∀ {B : Type u} [in
st : CategoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶
 c) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_leftUnitor_hom_rightUnitor_inv`：mate
Equiv_leftUnitor_hom_rightUnitor_inv {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l 
⊣ r) : mateEquiv adj adj ((fun_ _).hom ≫ (ρ_ _).inv) = (…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc_comp_left_inv_assoc`：∀ {B : Typ
e u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) {Z
 : a ⟶ c}   (h :     CategoryTheory.CategoryStruct…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjugateEquiv_whiskerLeft
    {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
    {l₂' : b ⟶ c} {r₂' : c ⟶ b} (adj₂' : l₂' ⊣ r₂') (φ : l₂' ⟶ l₂) :
    conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂') (l₁ ◁ φ) =
      conjugateEquiv adj₂ adj₂' φ ▷ r₁ := by
  have := mateEquiv_hcomp adj₁ adj₁ adj₂ adj₂' ((λ_ _).hom ≫ (ρ_ _).inv)
    ((λ_ _).hom ≫ φ ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    whiskerLeft_rightUnitor, triangle_assoc_comp_left_inv_assoc, Iso.hom_inv_id_assoc] at this
  simp [conjugateEquiv_apply, this]
/-
**CategoryTheory.Bicategory.conjugateEquiv_whiskerRight** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_whiskerRight {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : 
l₁ ⊣ r₁) {l₁' : a ⟶ b} {r₁' : b ⟶ a} (adj₁' : l₁' ⊣ r₁') {l₂ : b ⟶ c} {r₂ : c ⟶ 
b} (adj₂ : l₂ ⊣ r₂) (φ : l₁' ⟶ l₁) : conjugateEquiv (adj₁.comp adj₂) (adj₁'.comp
 adj₂) (φ ▷ l₂) = r₂ ◁ conjugateEquiv adj₁ adj₁' φ
参数：adj₁ : l₁ ⊣ r₁；adj₁' : l₁' ⊣ r₁'；adj₂ : l₂ ⊣ r₂；φ : l₁' ⟶ l₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_hcomp`：mateEquiv_hcomp (α : g ≫ l₂ ⟶
 l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) : (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (
leftAdjointSquare.hcomp α β) = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_whiskerRight`：leftUnitor_whiskerRig
ht (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (fun_ (f ≫ 
g)).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor_inv`：whiskerLeft_right
Unitor_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g
 (𝟙 c)).hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) {Z : a ⟶ c}   (h : Cat
egoryTheory.CategoryStruct.com…
· 使用定理 `CategoryTheory.Bicategory.inv_hom_whiskerRight_assoc`：∀ {B : Type u} [in
st : CategoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶
 c) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_leftUnitor_hom_rightUnitor_inv`：mate
Equiv_leftUnitor_hom_rightUnitor_inv {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l 
⊣ r) : mateEquiv adj adj ((fun_ _).hom ≫ (ρ_ _).inv) = (…
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_inv_whiskerRight`：leftUnitor_inv_wh
iskerRight (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).inv ▷ g = (fun_ (f ≫ g)).inv ≫ (α_
 (𝟙 a) f g).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc_comp_right_assoc`：∀ {B : Type u
} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) {Z : 
a ⟶ c}   (h : CategoryTheory.CategoryStruct.com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjugateEquiv_whiskerRight
    {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    {l₁' : a ⟶ b} {r₁' : b ⟶ a} (adj₁' : l₁' ⊣ r₁')
    {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂) (φ : l₁' ⟶ l₁) :
    conjugateEquiv (adj₁.comp adj₂) (adj₁'.comp adj₂) (φ ▷ l₂) =
      r₂ ◁ conjugateEquiv adj₁ adj₁' φ := by
  have := mateEquiv_hcomp adj₁ adj₁' adj₂ adj₂
    ((λ_ _).hom ≫ φ ≫ (ρ_ _).inv) ((λ_ _).hom ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id, triangle_assoc_comp_right_assoc] at this
  simp [conjugateEquiv_apply, this]

set_option linter.flexible false in -- simp followed by bicategory
/-
**CategoryTheory.Bicategory.conjugateEquiv_associator_hom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_associator_hom {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj
₁ : l₁ ⊣ r₁) {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂) {l₃ : c ⟶ d} {r₃ : d ⟶ c
} (adj₃ : l₃ ⊣ r₃) : conjugateEquiv (adj₁.comp (adj₂.comp adj₃)) ((adj₁.comp adj
₂).comp adj₃) (α_ _ _ _).hom = (α_ _ _ _).hom
参数：adj₁ : l₁ ⊣ r₁；adj₂ : l₂ ⊣ r₂；adj₃ : l₃ ⊣ r₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.homEquiv₁_symm_apply`：∀ {B : Type u
} [inst : CategoryTheory.Bicategory B] {b c d : B} {l : b ⟶ c} {r : c ⟶ b}   (ad
j : CategoryTheory.Bicategory.Adjunction l r) {…
· 使用定理 `CategoryTheory.Bicategory.unitors_inv_equal`：unitors_inv_equal : (fun_ (
𝟙 a)).inv = (ρ_ (𝟙 a)).inv
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.Adjunction.comp_unit`：∀ {B : Type u₁} [inst : 
CategoryTheory.Bicategory B] {a b c : B} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} 
{g₂ : c ⟶ b}   (adj₁ : CategoryTheor…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_inv_hom_assoc`：∀ {B : Type u} [ins
t : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ 
h) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Bicategory.Adjunction.homEquiv₂_apply`：∀ {B : Type u} [in
st : CategoryTheory.Bicategory B] {a b c : B} {l : b ⟶ c} {r : c ⟶ b}   (adj : C
ategoryTheory.Bicategory.Adjunction l r) {…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
（共 59 条，此处仅展示前 30 条）
-/
lemma conjugateEquiv_associator_hom
    {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
    {l₃ : c ⟶ d} {r₃ : d ⟶ c} (adj₃ : l₃ ⊣ r₃) :
    conjugateEquiv (adj₁.comp (adj₂.comp adj₃))
      ((adj₁.comp adj₂).comp adj₃) (α_ _ _ _).hom = (α_ _ _ _).hom := by
  simp [← cancel_epi (ρ_ ((r₃ ≫ r₂) ≫ r₁)).hom, ← cancel_mono (λ_ (r₃ ≫ r₂ ≫ r₁)).inv,
    conjugateEquiv_apply, mateEquiv_eq_iff, Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply]
  bicategory

end conjugateEquiv

section ConjugateComposition
variable {c d : B}
variable {l₁ l₂ l₃ : c ⟶ d} {r₁ r₂ r₃ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

@[simp]
/-
**CategoryTheory.Bicategory.conjugateEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：conjugateEquiv_comp (α : l₂ ⟶ l₁) (β : l₃ ⟶ l₂) : conjugateEquiv adj₁ adj₂
 α ≫ conjugateEquiv adj₂ adj₃ β = conjugateEquiv adj₁ adj₃ (β ≫ α)
参数：α : l₂ ⟶ l₁；β : l₃ ⟶ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_vcomp`：mateEquiv_vcomp (α : g₁ ≫ l₂ 
⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) : mateEquiv adj₁ adj₃ (leftAdjointSquare.vcom
p α β) = rightAdjointSquare.vco…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
（共 34 条，此处仅展示前 30 条）
-/
theorem conjugateEquiv_comp (α : l₂ ⟶ l₁) (β : l₃ ⟶ l₂) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β =
      conjugateEquiv adj₁ adj₃ (β ≫ α) := by
  simp only [conjugateEquiv_apply]
  calc
    _ = 𝟙 r₁ ⊗≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((λ_ _).hom ≫ α ≫ (ρ_ _).inv))
            (mateEquiv adj₂ adj₃ ((λ_ _).hom ≫ β ≫ (ρ_ _).inv)) ⊗≫ 𝟙 r₃ := by
      dsimp only [rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply']
      bicategory

@[simp]
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_comp (α : r₁ ⟶ r₂) (β : r₂ ⟶ r₃) : (conjugateEquiv adj
₂ adj₃).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = (conjugateEquiv adj₁ adj₃).
symm (α ≫ β)
参数：α : r₁ ⟶ r₂；β : r₂ ⟶ r₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_comp`：conjugateEquiv_comp (α : 
l₂ ⟶ l₁) (β : l₃ ⟶ l₂) : conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β
 = conjugateEquiv adj₁ adj₃ (β ≫ α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjugateEquiv_symm_comp (α : r₁ ⟶ r₂) (β : r₂ ⟶ r₃) :
    (conjugateEquiv adj₂ adj₃).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α =
      (conjugateEquiv adj₁ adj₃).symm (α ≫ β) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]
/-
**CategoryTheory.Bicategory.conjugateEquiv_comm** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：conjugateEquiv_comm {α : l₂ ⟶ l₁} {β : l₁ ⟶ l₂} (βα : β ≫ α = 𝟙 _) : conju
gateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₁ β = 𝟙 _
参数：βα : β ≫ α = 𝟙 _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_comp`：conjugateEquiv_comp (α : 
l₂ ⟶ l₁) (β : l₃ ⟶ l₂) : conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β
 = conjugateEquiv adj₁ adj₃ (β ≫ α)
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_id`：conjugateEquiv_id : conjuga
teEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _
-/
theorem conjugateEquiv_comm {α : l₂ ⟶ l₁} {β : l₁ ⟶ l₂} (βα : β ≫ α = 𝟙 _) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₁ β = 𝟙 _ := by
  rw [conjugateEquiv_comp, βα, conjugateEquiv_id]
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_comm** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_comm {α : r₁ ⟶ r₂} {β : r₂ ⟶ r₁} (αβ : α ≫ β = 𝟙 _) : 
(conjugateEquiv adj₂ adj₁).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = 𝟙 _
参数：αβ : α ≫ β = 𝟙 _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_symm_comp`：conjugateEquiv_symm_
comp (α : r₁ ⟶ r₂) (β : r₂ ⟶ r₃) : (conjugateEquiv adj₂ adj₃).symm β ≫ (conjugat
eEquiv adj₁ adj₂).symm α = (conjugateEqu…
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_symm_id`：conjugateEquiv_symm_id
 : (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _
-/
theorem conjugateEquiv_symm_comm {α : r₁ ⟶ r₂} {β : r₂ ⟶ r₁} (αβ : α ≫ β = 𝟙 _) :
    (conjugateEquiv adj₂ adj₁).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = 𝟙 _ := by
  rw [conjugateEquiv_symm_comp, αβ, conjugateEquiv_symm_id]

end ConjugateComposition

section ConjugateIsomorphism

variable {c d : B}
variable {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- If `α` is an isomorphism between left adjoints, then its conjugate 2-morphism is an
isomorphism. The converse is given in `conjugateEquiv_of_iso`.
-/
/-
**CategoryTheory.Bicategory.conjugateEquiv_iso** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：conjugateEquiv_iso (α : l₂ ⟶ l₁) [IsIso α] : IsIso (conjugateEquiv adj₁ ad
j₂ α)
参数：α : l₂ ⟶ l₁。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_comm`：conjugateEquiv_comm {α : 
l₂ ⟶ l₁} {β : l₁ ⟶ l₂} (βα : β ≫ α = 𝟙 _) : conjugateEquiv adj₁ adj₂ α ≫ conjuga
teEquiv adj₂ adj₁ β = 𝟙 _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X

--- 原说明 ---
If `α` is an isomorphism between left adjoints, then its conjugate 2-morphism is
 an
isomorphism. The converse is given in `conjugateEquiv_of_iso`.
-/
instance conjugateEquiv_iso (α : l₂ ⟶ l₁) [IsIso α] :
    IsIso (conjugateEquiv adj₁ adj₂ α) :=
  ⟨⟨conjugateEquiv adj₂ adj₁ (inv α),
      ⟨conjugateEquiv_comm _ _ (by simp), conjugateEquiv_comm _ _ (by simp)⟩⟩⟩

/-- If `α` is an isomorphism between right adjoints, then its conjugate 2-morphism is an
isomorphism. The converse is given in `conjugateEquiv_symm_of_iso`.
-/
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_iso** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_iso (α : r₁ ⟶ r₂) [IsIso α] : IsIso ((conjugateEquiv a
dj₁ adj₂).symm α)
参数：α : r₁ ⟶ r₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Bicategory.conjugateEquiv_symm_comm`：conjugateEquiv_symm_
comm {α : r₁ ⟶ r₂} {β : r₂ ⟶ r₁} (αβ : α ≫ β = 𝟙 _) : (conjugateEquiv adj₂ adj₁)
.symm β ≫ (conjugateEquiv adj₁ adj₂).sym…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X

--- 原说明 ---
If `α` is an isomorphism between right adjoints, then its conjugate 2-morphism i
s an
isomorphism. The converse is given in `conjugateEquiv_symm_of_iso`.
-/
instance conjugateEquiv_symm_iso (α : r₁ ⟶ r₂) [IsIso α] :
    IsIso ((conjugateEquiv adj₁ adj₂).symm α) :=
  ⟨⟨(conjugateEquiv adj₂ adj₁).symm (inv α),
      ⟨conjugateEquiv_symm_comm _ _ (by simp), conjugateEquiv_symm_comm _ _ (by simp)⟩⟩⟩

/-- If `α` is a 2-morphism between left adjoints whose conjugate 2-morphism
is an isomorphism, then `α` is an isomorphism. The converse is given in `conjugateEquiv_iso`.
-/
/-
**CategoryTheory.Bicategory.conjugateEquiv_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_of_iso (α : l₂ ⟶ l₁) [IsIso (conjugateEquiv adj₁ adj₂ α)] :
 IsIso α
参数：α : l₂ ⟶ l₁；conjugateEquiv adj₁ adj₂ α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
If `α` is a 2-morphism between left adjoints whose conjugate 2-morphism
is an isomorphism, then `α` is an isomorphism. The converse is given in `conjuga
teEquiv_iso`.
-/
theorem conjugateEquiv_of_iso (α : l₂ ⟶ l₁) [IsIso (conjugateEquiv adj₁ adj₂ α)] :
    IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂).symm (conjugateEquiv adj₁ adj₂ α))
    by simpa only [Equiv.symm_apply_apply] using this
  infer_instance

/--
If `α` is a 2-morphism between right adjoints whose conjugate 2-morphism is
an isomorphism, then `α` is an isomorphism. The converse is given in `conjugateEquiv_symm_iso`.
-/
/-
**CategoryTheory.Bicategory.conjugateEquiv_symm_of_iso** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_symm_of_iso (α : r₁ ⟶ r₂) [IsIso ((conjugateEquiv adj₁ adj₂
).symm α)] : IsIso α
参数：α : r₁ ⟶ r₂；(conjugateEquiv adj₁ adj₂).symm α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
If `α` is a 2-morphism between right adjoints whose conjugate 2-morphism is
an isomorphism, then `α` is an isomorphism. The converse is given in `conjugateE
quiv_symm_iso`.
-/
theorem conjugateEquiv_symm_of_iso (α : r₁ ⟶ r₂)
    [IsIso ((conjugateEquiv adj₁ adj₂).symm α)] : IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂) ((conjugateEquiv adj₁ adj₂).symm α))
    by simpa only [Equiv.apply_symm_apply] using this
  infer_instance

/-- Thus conjugation defines an equivalence between isomorphisms. -/
@[simps]
/-
**CategoryTheory.Bicategory.conjugateIsoEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：conjugateIsoEquiv : (l₂ ≅ l₁) ≃ (r₁ ≅ r₂) where toFun α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Thus conjugation defines an equivalence between isomorphisms.
-/
def conjugateIsoEquiv : (l₂ ≅ l₁) ≃ (r₁ ≅ r₂) where
  toFun α :=
    { hom := conjugateEquiv adj₁ adj₂ α.hom
      inv := conjugateEquiv adj₂ adj₁ α.inv
      hom_inv_id := by
        rw [conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id]
      inv_hom_id := by
        rw [conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id] }
  invFun β :=
    { hom := (conjugateEquiv adj₁ adj₂).symm β.hom
      inv := (conjugateEquiv adj₂ adj₁).symm β.inv
      hom_inv_id := by
        rw [conjugateEquiv_symm_comp, Iso.inv_hom_id, conjugateEquiv_symm_id]
      inv_hom_id := by
        rw [conjugateEquiv_symm_comp, Iso.hom_inv_id, conjugateEquiv_symm_id] }
  left_inv := by
    intro α
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro α
    simp only [Equiv.apply_symm_apply]

end ConjugateIsomorphism

section IteratedMateEquiv
variable {a b c d : B}
variable {f₁ : a ⟶ c} {u₁ : c ⟶ a} {f₂ : b ⟶ d} {u₂ : d ⟶ b}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : f₁ ⊣ u₁) (adj₄ : f₂ ⊣ u₂)

/-- When all four morphisms in a square are left adjoints, the mates operation can be iterated:
```
         l₁                  r₁                  r₁
      a --→ b             a ←-- b             a ←-- b
   f₁ ↓  ↗  ↓  f₂      f₁ ↓  ↘  ↓ f₂       u₁ ↑  ↙  ↑ u₂
      c --→ d             c ←-- d             c ←-- d
         l₂                  r₂                  r₂
```
In this case the iterated mate equals the conjugate of the original 2-morphism and is thus an
isomorphism if and only if the original 2-morphism is. This explains why some Beck-Chevalley
2-morphisms are isomorphisms.
-/
/-
**CategoryTheory.Bicategory.iterated_mateEquiv_conjugateEquiv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：iterated_mateEquiv_conjugateEquiv (α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂) : mateEquiv adj₄
 adj₃ (mateEquiv adj₁ adj₂ α) = conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)
 α
参数：α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
When all four morphisms in a square are left adjoints, the mates operation can b
e iterated:
```
         l₁                  r₁                  r₁
      a --→ b             a ←-- b             a ←-- b
   f₁ ↓  ↗  ↓  f₂      f₁ ↓  ↘  ↓ f₂       u₁ ↑  ↙  ↑ u₂
      c --→ d             c ←-- d             c ←-- d
         l₂                  r₂                  r₂
```
In this case the iterated mate equals the conjugate of the original 2-morphism a
nd is thus an
isomorphism if and only if the original 2-morphism is. This explains why some Be
ck-Chevalley
2-morphisms are isomorphisms.
-/
theorem iterated_mateEquiv_conjugateEquiv (α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂) :
    mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α) =
      conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α := by
  simp only [conjugateEquiv_apply, mateEquiv_apply']
  dsimp [Adjunction.comp]
  bicategory
/-
**CategoryTheory.Bicategory.iterated_mateEquiv_conjugateEquiv_symm** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：iterated_mateEquiv_conjugateEquiv_symm (α : u₂ ≫ r₁ ⟶ r₂ ≫ u₁) : (mateEqui
v adj₁ adj₂).symm ((mateEquiv adj₄ adj₃).symm α) = (conjugateEquiv (adj₁.comp ad
j₄) (adj₃.comp adj₂)).symm α
参数：α : u₂ ≫ r₁ ⟶ r₂ ≫ u₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.iterated_mateEquiv_conjugateEquiv`：iterated_ma
teEquiv_conjugateEquiv (α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂) : mateEquiv adj₄ adj₃ (mateEquiv 
adj₁ adj₂ α) = conjugateEquiv (adj₁.comp adj₄) (a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iterated_mateEquiv_conjugateEquiv_symm (α : u₂ ≫ r₁ ⟶ r₂ ≫ u₁) :
    (mateEquiv adj₁ adj₂).symm ((mateEquiv adj₄ adj₃).symm α) =
      (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm α := by
  rw [Equiv.eq_symm_apply, ← iterated_mateEquiv_conjugateEquiv]
  simp only [Equiv.apply_symm_apply]

end IteratedMateEquiv

section mateEquiv_conjugateEquiv_vcomp

variable {a b c d : B}
variable {g : a ⟶ c} {h : b ⟶ d}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c} {l₃ : c ⟶ d} {r₃ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/-- Composition of a square between left adjoints with a conjugate square. -/
/-
**CategoryTheory.Bicategory.leftAdjointSquareConjugate.vcomp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Bicategory.leftAdjointSquareConjugate`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d : B} 
→       {g : a ⟶ c} →         {h : b ⟶ d} →           {l₁ : a ⟶ b} →            
 {l₂ l₃ : c ⟶ d} →               (CategoryTheory.CategoryStruct.comp g l₂ ⟶ Cate
goryTheory.CategoryStruct.comp l₁ h) →                 (l₃ ⟶ l₂) → (CategoryTheo
ry.CategoryStruct.comp g l₃ ⟶ CategoryTheory.CategoryStruct.comp l₁ h)
参数：CategoryTheory.CategoryStruct.comp g l₂ ⟶ CategoryTheory.CategoryStruct.comp 
l₁ h；l₃ ⟶ l₂；CategoryTheory.CategoryStruct.comp g l₃ ⟶ CategoryTheory.CategorySt
ruct.comp l₁ h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a square between left adjoints with a conjugate square.
-/
def leftAdjointSquareConjugate.vcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂) :
    g ≫ l₃ ⟶ l₁ ≫ h :=
  g ◁ β ≫ α

/-- Composition of a square between right adjoints with a conjugate square. -/
/-
**CategoryTheory.Bicategory.rightAdjointSquareConjugate.vcomp** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Bicategory.rightAdjointSquareConjugate`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d : B} 
→       {g : a ⟶ c} →         {h : b ⟶ d} →           {r₁ : b ⟶ a} →            
 {r₂ r₃ : d ⟶ c} →               (CategoryTheory.CategoryStruct.comp r₁ g ⟶ Cate
goryTheory.CategoryStruct.comp h r₂) →                 (r₂ ⟶ r₃) → (CategoryTheo
ry.CategoryStruct.comp r₁ g ⟶ CategoryTheory.CategoryStruct.comp h r₃)
参数：CategoryTheory.CategoryStruct.comp r₁ g ⟶ CategoryTheory.CategoryStruct.comp 
h r₂；r₂ ⟶ r₃；CategoryTheory.CategoryStruct.comp r₁ g ⟶ CategoryTheory.CategorySt
ruct.comp h r₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a square between right adjoints with a conjugate square.
-/
def rightAdjointSquareConjugate.vcomp (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₂ ⟶ r₃) :
    r₁ ≫ g ⟶ h ≫ r₃ :=
  α ≫ h ◁ β

/-- The mates equivalence commutes with this composition, essentially by `mateEquiv_vcomp`. -/
/-
**CategoryTheory.Bicategory.mateEquiv_conjugateEquiv_vcomp** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory`。
形式化陈述：mateEquiv_conjugateEquiv_vcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂) : (mate
Equiv adj₁ adj₃) (leftAdjointSquareConjugate.vcomp α β) = rightAdjointSquareConj
ugate.vcomp (mateEquiv adj₁ adj₂ α) (conjugateEquiv adj₂ adj₃ β)
参数：α : g ≫ l₂ ⟶ l₁ ≫ h；β : l₃ ⟶ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
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
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_vcomp`：mateEquiv_vcomp (α : g₁ ≫ l₂ 
⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) : mateEquiv adj₁ adj₃ (leftAdjointSquare.vcom
p α β) = rightAdjointSquare.vco…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The mates equivalence commutes with this composition, essentially by `mateEquiv_
vcomp`.
-/
theorem mateEquiv_conjugateEquiv_vcomp
    (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂) :
    (mateEquiv adj₁ adj₃) (leftAdjointSquareConjugate.vcomp α β) =
      rightAdjointSquareConjugate.vcomp (mateEquiv adj₁ adj₂ α) (conjugateEquiv adj₂ adj₃ β) := by
  symm
  calc
    _ = 𝟙 _ ⊗≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ α)
            (mateEquiv adj₂ adj₃ ((λ_ l₃).hom ≫ β ≫ (ρ_ l₂).inv)) ⊗≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointSquareConjugate.vcomp,
        rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointSquareConjugate.vcomp]
      bicategory

end mateEquiv_conjugateEquiv_vcomp

section conjugateEquiv_mateEquiv_vcomp

variable {a b c d : B}
variable {g : a ⟶ c} {h : b ⟶ d}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : a ⟶ b} {r₂ : b ⟶ a} {l₃ : c ⟶ d} {r₃ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/-- Composition of a conjugate square with a square between left adjoints. -/
/-
**CategoryTheory.Bicategory.leftAdjointConjugateSquare.vcomp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Bicategory.leftAdjointConjugateSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d : B} 
→       {g : a ⟶ c} →         {h : b ⟶ d} →           {l₁ l₂ : a ⟶ b} →         
    {l₃ : c ⟶ d} →               (l₂ ⟶ l₁) →                 (CategoryTheory.Cat
egoryStruct.comp g l₃ ⟶ CategoryTheory.CategoryStruct.comp l₂ h) →              
     (CategoryTheory.CategoryStruct.comp g l₃ ⟶ CategoryTheory.CategoryStruct.co
mp l₁ h)
参数：l₂ ⟶ l₁；CategoryTheory.CategoryStruct.comp g l₃ ⟶ CategoryTheory.CategoryStru
ct.comp l₂ h；CategoryTheory.CategoryStruct.comp g l₃ ⟶ CategoryTheory.CategorySt
ruct.comp l₁ h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a conjugate square with a square between left adjoints.
-/
def leftAdjointConjugateSquare.vcomp (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h) :
    g ≫ l₃ ⟶ l₁ ≫ h :=
  β ≫ α ▷ h

/-- Composition of a conjugate square with a square between right adjoints. -/
/-
**CategoryTheory.Bicategory.rightAdjointConjugateSquare.vcomp** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Bicategory.rightAdjointConjugateSquare`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c d : B} 
→       {g : a ⟶ c} →         {h : b ⟶ d} →           {r₁ r₂ : b ⟶ a} →         
    {r₃ : d ⟶ c} →               (r₁ ⟶ r₂) →                 (CategoryTheory.Cat
egoryStruct.comp r₂ g ⟶ CategoryTheory.CategoryStruct.comp h r₃) →              
     (CategoryTheory.CategoryStruct.comp r₁ g ⟶ CategoryTheory.CategoryStruct.co
mp h r₃)
参数：r₁ ⟶ r₂；CategoryTheory.CategoryStruct.comp r₂ g ⟶ CategoryTheory.CategoryStru
ct.comp h r₃；CategoryTheory.CategoryStruct.comp r₁ g ⟶ CategoryTheory.CategorySt
ruct.comp h r₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a conjugate square with a square between right adjoints.
-/
def rightAdjointConjugateSquare.vcomp (α : r₁ ⟶ r₂) (β : r₂ ≫ g ⟶ h ≫ r₃) :
    r₁ ≫ g ⟶ h ≫ r₃ :=
  α ▷ g ≫ β

/-- The mates equivalence commutes with this composition, essentially by `mateEquiv_vcomp`. -/
/-
**CategoryTheory.Bicategory.conjugateEquiv_mateEquiv_vcomp** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory`。
形式化陈述：conjugateEquiv_mateEquiv_vcomp (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h) : (mate
Equiv adj₁ adj₃) (leftAdjointConjugateSquare.vcomp α β) = rightAdjointConjugateS
quare.vcomp (conjugateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β)
参数：α : l₂ ⟶ l₁；β : g ≫ l₃ ⟶ l₂ ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.mateEquiv_vcomp`：mateEquiv_vcomp (α : g₁ ≫ l₂ 
⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) : mateEquiv adj₁ adj₃ (leftAdjointSquare.vcom
p α β) = rightAdjointSquare.vco…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Bicategory.mateEquiv_apply'`：mateEquiv_apply' (α : g ≫ l₂
 ⟶ l₁ ≫ h) : mateEquiv adj₁ adj₂ α = 𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁
 α ▷ r₂ otimes≫ adj₁.counit ▷ h …
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The mates equivalence commutes with this composition, essentially by `mateEquiv_
vcomp`.
-/
theorem conjugateEquiv_mateEquiv_vcomp
    (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h) :
    (mateEquiv adj₁ adj₃) (leftAdjointConjugateSquare.vcomp α β) =
      rightAdjointConjugateSquare.vcomp (conjugateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  symm
  calc
    _ = 𝟙 _ ⊗≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((λ_ l₂).hom ≫ α ≫ (ρ_ l₁).inv))
            (mateEquiv adj₂ adj₃ β) ⊗≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointConjugateSquare.vcomp, rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointConjugateSquare.vcomp]
      bicategory

end conjugateEquiv_mateEquiv_vcomp

end Bicategory

end CategoryTheory

