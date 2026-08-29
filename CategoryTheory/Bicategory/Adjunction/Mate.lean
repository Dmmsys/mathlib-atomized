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
         l₁ r₁
      c --→ d c ←-- d
    g ↓ ↗ ↓ h g ↓ ↘ ↓ h
      e --→ f e ←-- f
         l₂ r₂
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
/--
Definition of `homEquiv₁` / `homEquiv₁` 的定义

English:
definition homEquiv₁
  signature: {g : b ⟶ d} {h : c ⟶ d}
  body: r ◁ γ ≫ (α_ _ _ _).inv ≫ adj.counit ▷ h ≫ (fun_ _).hom
  invFun β := (fun_ _).inv ≫ adj.unit ▷ _ ≫ (α_ _ _ _).hom ≫ l ◁ β
  left_inv γ :=
    calc
      _ = 𝟙 _ otimes≫ (adj.unit ▷ g ≫ (l ≫ r) ◁ γ) otimes≫ l ◁ adj.counit ▷ h otimes≫ 𝟙 _ := by
        bicategory
      _ = γ otimes≫ leftZigzag adj.unit adj.counit ▷ h otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.left_triangle]
        bicategory
  right_inv β := by
    calc
      _ = 𝟙 _ otimes≫ r ◁ adj.unit ▷ g otimes≫ ((r ≫ l) ◁ β ≫ adj.counit ▷ h) otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ rightZigzag adj.unit adj.counit ▷ g otimes≫ β := by
        rw [whisker_exchange]
        bicategory
      _ = β := by
        rw [adj.right_triangle]
        bicategory

中文:
定义 homEquiv₁
  签名: {g : b ⟶ d} {h : c ⟶ d}
  定义体: r ◁ γ ≫ (α_ _ _ _).inv ≫ adj.counit ▷ h ≫ (fun_ _).hom
  invFun β := (fun_ _).inv ≫ adj.unit ▷ _ ≫ (α_ _ _ _).hom ≫ l ◁ β
  left_inv γ :=
    calc
      _ = 𝟙 _ otimes≫ (adj.unit ▷ g ≫ (l ≫ r) ◁ γ) otimes≫ l ◁ adj.counit ▷ h otimes≫ 𝟙 _ := by
        bicategory
      _ = γ otimes≫ leftZigzag adj.unit adj.counit ▷ h otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.left_triangle]
        bicategory
  right_inv β := by
    calc
      _ = 𝟙 _ otimes≫ r ◁ adj.unit ▷ g otimes≫ ((r ≫ l) ◁ β ≫ adj.counit ▷ h) otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ rightZigzag adj.unit adj.counit ▷ g otimes≫ β := by
        rw [whisker_exchange]
        bicategory
      _ = β := by
        rw [adj.right_triangle]
        bicategory

Depends on / 依赖: adj.counit, counit, fun_
-/
def homEquiv₁ {g : b ⟶ d} {h : c ⟶ d} : (g ⟶ l ≫ h) ≃ (r ≫ g ⟶ h) where
  toFun γ := r ◁ γ ≫ (α_ _ _ _).inv ≫ adj.counit ▷ h ≫ (fun_ _).hom
  invFun β := (fun_ _).inv ≫ adj.unit ▷ _ ≫ (α_ _ _ _).hom ≫ l ◁ β
  left_inv γ :=
    calc
      _ = 𝟙 _ otimes≫ (adj.unit ▷ g ≫ (l ≫ r) ◁ γ) otimes≫ l ◁ adj.counit ▷ h otimes≫ 𝟙 _ := by
        bicategory
      _ = γ otimes≫ leftZigzag adj.unit adj.counit ▷ h otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.left_triangle]
        bicategory
  right_inv β := by
    calc
      _ = 𝟙 _ otimes≫ r ◁ adj.unit ▷ g otimes≫ ((r ≫ l) ◁ β ≫ adj.counit ▷ h) otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ rightZigzag adj.unit adj.counit ▷ g otimes≫ β := by
        rw [whisker_exchange]
        bicategory
      _ = β := by
        rw [adj.right_triangle]
        bicategory

/-- The bijection `(g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r)` induced by an adjunction
`l ⊣ r` in a bicategory. -/
@[simps -isSimp]
/--
Definition of `homEquiv₂` / `homEquiv₂` 的定义

English:
definition homEquiv₂
  signature: {g : a ⟶ b} {h : a ⟶ c}
  body: (ρ_ _).inv ≫ g ◁ adj.unit ≫ (α_ _ _ _).inv ≫ α ▷ r
  invFun γ := γ ▷ l ≫ (α_ _ _ _).hom ≫ h ◁ adj.counit ≫ (ρ_ _).hom
  left_inv α :=
    calc
      _ = 𝟙 _ otimes≫ g ◁ adj.unit ▷ l otimes≫ (α ▷ (r ≫ l) ≫ h ◁ adj.counit) otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ g ◁ leftZigzag adj.unit adj.counit otimes≫ α := by
        rw [← whisker_exchange]
        bicategory
      _ = α := by
        rw [adj.left_triangle]
        bicategory
  right_inv γ :=
    calc
      _ = 𝟙 _ otimes≫ (g ◁ adj.unit ≫ γ ▷ (l ≫ r)) otimes≫ h ◁ adj.counit ▷ r otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ γ otimes≫ h ◁ rightZigzag adj.unit adj.counit otimes≫ 𝟙 _ := by
        rw [whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.right_triangle]
        bicategory

中文:
定义 homEquiv₂
  签名: {g : a ⟶ b} {h : a ⟶ c}
  定义体: (ρ_ _).inv ≫ g ◁ adj.unit ≫ (α_ _ _ _).inv ≫ α ▷ r
  invFun γ := γ ▷ l ≫ (α_ _ _ _).hom ≫ h ◁ adj.counit ≫ (ρ_ _).hom
  left_inv α :=
    calc
      _ = 𝟙 _ otimes≫ g ◁ adj.unit ▷ l otimes≫ (α ▷ (r ≫ l) ≫ h ◁ adj.counit) otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ g ◁ leftZigzag adj.unit adj.counit otimes≫ α := by
        rw [← whisker_exchange]
        bicategory
      _ = α := by
        rw [adj.left_triangle]
        bicategory
  right_inv γ :=
    calc
      _ = 𝟙 _ otimes≫ (g ◁ adj.unit ≫ γ ▷ (l ≫ r)) otimes≫ h ◁ adj.counit ▷ r otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ γ otimes≫ h ◁ rightZigzag adj.unit adj.counit otimes≫ 𝟙 _ := by
        rw [whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.right_triangle]
        bicategory

Depends on / 依赖: adj.unit
-/
def homEquiv₂ {g : a ⟶ b} {h : a ⟶ c} : (g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r) where
  toFun α := (ρ_ _).inv ≫ g ◁ adj.unit ≫ (α_ _ _ _).inv ≫ α ▷ r
  invFun γ := γ ▷ l ≫ (α_ _ _ _).hom ≫ h ◁ adj.counit ≫ (ρ_ _).hom
  left_inv α :=
    calc
      _ = 𝟙 _ otimes≫ g ◁ adj.unit ▷ l otimes≫ (α ▷ (r ≫ l) ≫ h ◁ adj.counit) otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ g ◁ leftZigzag adj.unit adj.counit otimes≫ α := by
        rw [← whisker_exchange]
        bicategory
      _ = α := by
        rw [adj.left_triangle]
        bicategory
  right_inv γ :=
    calc
      _ = 𝟙 _ otimes≫ (g ◁ adj.unit ≫ γ ▷ (l ≫ r)) otimes≫ h ◁ adj.counit ▷ r otimes≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ otimes≫ γ otimes≫ h ◁ rightZigzag adj.unit adj.counit otimes≫ 𝟙 _ := by
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
    g ↓ ↓ h
      e ↔ f
```

Then we have a bijection between 2-morphisms `g ≫ l₂ ⟶ l₁ ≫ h` and
`r₁ ≫ g ⟶ h ≫ r₂`. This can be seen as a bijection of the 2-cells:

```
         l₁ r₁
      c --→ d c ←-- d
    g ↓ ↗ ↓ h g ↓ ↘ ↓ h
      e --→ f e ←-- f
         l₂ r₂
```

Note that if one of the 2-morphisms is an iso, it does not imply the other is an iso.
-/
@[simps! -isSimp]
/--
Definition of `mateEquiv` / `mateEquiv` 的定义

English:
definition mateEquiv
  signature: : (g ≫ l₂ ⟶ l₁ ≫ h) ≃ (r₁ ≫ g ⟶ h ≫ r₂)
  body: adj₂.homEquiv₂.trans ((Iso.homCongr (Iso.refl _) (α_ _ _ _)).trans adj₁.homEquiv₁)

中文:
定义 mateEquiv
  签名: : (g ≫ l₂ ⟶ l₁ ≫ h) ≃ (r₁ ≫ g ⟶ h ≫ r₂)
  定义体: adj₂.homEquiv₂.trans ((Iso.homCongr (Iso.refl _) (α_ _ _ _)).trans adj₁.homEquiv₁)

Depends on / 依赖: Iso.homCongr, Iso.refl, homCongr
-/
def mateEquiv : (g ≫ l₂ ⟶ l₁ ≫ h) ≃ (r₁ ≫ g ⟶ h ≫ r₂) :=
  adj₂.homEquiv₂.trans ((Iso.homCongr (Iso.refl _) (α_ _ _ _)).trans adj₁.homEquiv₁)

/--
lemma `mateEquiv_eq_iff` / 引理 `mateEquiv_eq_iff`

English:
lemma mateEquiv_eq_iff
  given: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂)
  proof: by
  conv_lhs => rw [eq_comm, ← adj₁.homEquiv₁.symm.injective.eq_iff']
  rw [mateEquiv_apply]; rw [Equiv.symm_apply_apply]

中文:
引理 mateEquiv_eq_iff
  条件: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂)
  证明: by
  conv_lhs => rw [eq_comm, ← adj₁.homEquiv₁.symm.injective.eq_iff']
  rw [mateEquiv_apply]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, conv_lhs, eq_comm, eq_iff, injective, mateEquiv_apply, symm.injective.eq_iff, symm_apply_apply
-/
lemma mateEquiv_eq_iff (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂) :
    mateEquiv adj₁ adj₂ α = β ↔
    adj₁.homEquiv₁.symm β = adj₂.homEquiv₂ α ≫ (α_ _ _ _).hom := by
  conv_lhs => rw [eq_comm, ← adj₁.homEquiv₁.symm.injective.eq_iff']
  rw [mateEquiv_apply]; rw [Equiv.symm_apply_apply]

/--
lemma `mateEquiv_apply'` / 引理 `mateEquiv_apply'`

English:
lemma mateEquiv_apply'
  given: (α : g ≫ l₂ ⟶ l₁ ≫ h)
  proof: by
  rw [mateEquiv_apply]; rw [Adjunction.homEquiv₂_apply]; rw [Adjunction.homEquiv₁_apply]
  bicategory

中文:
引理 mateEquiv_apply'
  条件: (α : g ≫ l₂ ⟶ l₁ ≫ h)
  证明: by
  rw [mateEquiv_apply]; rw [Adjunction.homEquiv₂_apply]; rw [Adjunction.homEquiv₁_apply]
  bicategory

Depends on / 依赖: Adjunction, Adjunction.homEquiv, bicategory, mateEquiv_apply
-/
lemma mateEquiv_apply' (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ α =
      𝟙 _ otimes≫ r₁ ◁ g ◁ adj₂.unit otimes≫ r₁ ◁ α ▷ r₂ otimes≫ adj₁.counit ▷ h ▷ r₂ otimes≫ 𝟙 _ := by
  rw [mateEquiv_apply]; rw [Adjunction.homEquiv₂_apply]; rw [Adjunction.homEquiv₁_apply]
  bicategory

/--
lemma `mateEquiv_symm_apply'` / 引理 `mateEquiv_symm_apply'`

English:
lemma mateEquiv_symm_apply'
  given: (β : r₁ ≫ g ⟶ h ≫ r₂)
  proof: by
  rw [mateEquiv_symm_apply]; rw [Adjunction.homEquiv₂_symm_apply]; rw [Adjunction.homEquiv₁_symm_apply]
  bicategory

中文:
引理 mateEquiv_symm_apply'
  条件: (β : r₁ ≫ g ⟶ h ≫ r₂)
  证明: by
  rw [mateEquiv_symm_apply]; rw [Adjunction.homEquiv₂_symm_apply]; rw [Adjunction.homEquiv₁_symm_apply]
  bicategory

Depends on / 依赖: Adjunction, Adjunction.homEquiv, bicategory, mateEquiv_symm_apply
-/
lemma mateEquiv_symm_apply' (β : r₁ ≫ g ⟶ h ≫ r₂) :
    (mateEquiv adj₁ adj₂).symm β =
      𝟙 _ otimes≫ adj₁.unit ▷ g ▷ l₂ otimes≫ l₁ ◁ β ▷ l₂ otimes≫ l₁ ◁ h ◁ adj₂.counit otimes≫ 𝟙 _ := by
  rw [mateEquiv_symm_apply]; rw [Adjunction.homEquiv₂_symm_apply]; rw [Adjunction.homEquiv₁_symm_apply]
  bicategory

end

section

variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : c ⟶ d} {r₂ : d ⟶ c} (adj₂ : l₂ ⊣ r₂)
  {f : a ⟶ c} {g : b ⟶ d}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mateEquiv_id_comp_right` / 引理 `mateEquiv_id_comp_right`

English:
lemma mateEquiv_id_comp_right
  given: (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g)
  proof: by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

中文:
引理 mateEquiv_id_comp_right
  条件: (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g)
  证明: by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

Depends on / 依赖: Adjunction, Adjunction.homEquiv, Adjunction.id, bicategory, mateEquiv_apply
-/
lemma mateEquiv_id_comp_right (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g) :
    mateEquiv adj₁ ((Adjunction.id _).comp adj₂) φ =
      mateEquiv adj₁ adj₂ (f ◁ (fun_ l₂).inv ≫ φ) ≫ (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mateEquiv_comp_id_right` / 引理 `mateEquiv_comp_id_right`

English:
lemma mateEquiv_comp_id_right
  given: (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g)
  proof: by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

中文:
引理 mateEquiv_comp_id_right
  条件: (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g)
  证明: by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

Depends on / 依赖: Adjunction, Adjunction.homEquiv, Adjunction.id, bicategory, mateEquiv_apply
-/
lemma mateEquiv_comp_id_right (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g) :
    mateEquiv adj₁ (adj₂.comp (Adjunction.id _)) φ =
      mateEquiv adj₁ adj₂ ((ρ_ _).inv ≫ (α_ _ _ _).hom ≫ φ) ≫ g ◁ (fun_ r₂).inv := by
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

/--
Definition of `leftAdjointSquare.vcomp` / `leftAdjointSquare.vcomp` 的定义

English:
definition leftAdjointSquare.vcomp
  signature: (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂)
  body: (α_ _ _ _).hom ≫ g₁ ◁ β ≫ (α_ _ _ _).inv ≫ α ▷ h₂ ≫ (α_ _ _ _).hom

中文:
定义 leftAdjointSquare.vcomp
  签名: (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂)
  定义体: (α_ _ _ _).hom ≫ g₁ ◁ β ≫ (α_ _ _ _).inv ≫ α ▷ h₂ ≫ (α_ _ _ _).hom
-/
def leftAdjointSquare.vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) :
    (g₁ ≫ g₂) ≫ l₃ ⟶ l₁ ≫ (h₁ ≫ h₂) :=
  (α_ _ _ _).hom ≫ g₁ ◁ β ≫ (α_ _ _ _).inv ≫ α ▷ h₂ ≫ (α_ _ _ _).hom

/--
Definition of `rightAdjointSquare.vcomp` / `rightAdjointSquare.vcomp` 的定义

English:
definition rightAdjointSquare.vcomp
  signature: (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₂) (β : r₂ ≫ g₂ ⟶ h₂ ≫ r₃)
  body: (α_ _ _ _).inv ≫ α ▷ g₂ ≫ (α_ _ _ _).hom ≫ h₁ ◁ β ≫ (α_ _ _ _).inv

中文:
定义 rightAdjointSquare.vcomp
  签名: (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₂) (β : r₂ ≫ g₂ ⟶ h₂ ≫ r₃)
  定义体: (α_ _ _ _).inv ≫ α ▷ g₂ ≫ (α_ _ _ _).hom ≫ h₁ ◁ β ≫ (α_ _ _ _).inv
-/
def rightAdjointSquare.vcomp (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₂) (β : r₂ ≫ g₂ ⟶ h₂ ≫ r₃) :
    r₁ ≫ (g₁ ≫ g₂) ⟶ (h₁ ≫ h₂) ≫ r₃ :=
  (α_ _ _ _).inv ≫ α ▷ g₂ ≫ (α_ _ _ _).hom ≫ h₁ ◁ β ≫ (α_ _ _ _).inv

/--
theorem `mateEquiv_vcomp` / 定理 `mateEquiv_vcomp`

English:
theorem mateEquiv_vcomp
  given: (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂)
  proof: by
  simp only [leftAdjointSquare.vcomp, mateEquiv_apply', rightAdjointSquare.vcomp]
  symm
  calc
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ otimes≫ r₁ ◁ α ▷ r₂ ▷ g₂ otimes≫
          ((adj₁.counit ▷ (h₁ ≫ r₂ ≫ g₂ ≫ 𝟙 e)) ≫ 𝟙 b ◁ (h₁ ◁ r₂ ◁ g₂ ◁ adj₃.unit)) otimes≫
            h₁ ◁ r₂ ◁ β ▷ r₃ otimes≫ h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ otimes≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ 𝟙 e) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ g₂ ◁ adj₃.unit)) otimes≫
            ((adj₁.counit ▷ (h₁ ≫ r₂) ▷ (g₂ ≫ l₃) ≫ (𝟙 b ≫ h₁ ≫ r₂) ◁ β) ▷ r₃) otimes≫
              h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ 𝟙 e) ≫ (l₂ ≫ r₂) ◁ g₂ ◁ adj₃.unit) otimes≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ l₃) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ β) ▷ r₃) otimes≫
            (adj₁.counit ▷ h₁ ▷ (r₂ ≫ l₂) ≫ (𝟙 b ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit otimes≫
          r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ l₃) ≫ (l₂ ≫ r₂) ◁ β) ▷ r₃ otimes≫
            r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ otimes≫
              adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit otimes≫ r₁ ◁ g₁ ◁ β ▷ r₃ otimes≫
          ((r₁ ≫ g₁) ◁ leftZigzag adj₂.unit adj₂.counit ▷ (h₂ ≫ r₃)) otimes≫
            r₁ ◁ α ▷ h₂ ▷ r₃ otimes≫ adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = _ := by
      rw [adj₂.left_triangle]
      bicategory

中文:
定理 mateEquiv_vcomp
  条件: (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂)
  证明: by
  simp only [leftAdjointSquare.vcomp, mateEquiv_apply', rightAdjointSquare.vcomp]
  symm
  calc
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ otimes≫ r₁ ◁ α ▷ r₂ ▷ g₂ otimes≫
          ((adj₁.counit ▷ (h₁ ≫ r₂ ≫ g₂ ≫ 𝟙 e)) ≫ 𝟙 b ◁ (h₁ ◁ r₂ ◁ g₂ ◁ adj₃.unit)) otimes≫
            h₁ ◁ r₂ ◁ β ▷ r₃ otimes≫ h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ otimes≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ 𝟙 e) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ g₂ ◁ adj₃.unit)) otimes≫
            ((adj₁.counit ▷ (h₁ ≫ r₂) ▷ (g₂ ≫ l₃) ≫ (𝟙 b ≫ h₁ ≫ r₂) ◁ β) ▷ r₃) otimes≫
              h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ 𝟙 e) ≫ (l₂ ≫ r₂) ◁ g₂ ◁ adj₃.unit) otimes≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ l₃) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ β) ▷ r₃) otimes≫
            (adj₁.counit ▷ h₁ ▷ (r₂ ≫ l₂) ≫ (𝟙 b ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit otimes≫
          r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ l₃) ≫ (l₂ ≫ r₂) ◁ β) ▷ r₃ otimes≫
            r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ otimes≫
              adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit otimes≫ r₁ ◁ g₁ ◁ β ▷ r₃ otimes≫
          ((r₁ ≫ g₁) ◁ leftZigzag adj₂.unit adj₂.counit ▷ (h₂ ≫ r₃)) otimes≫
            r₁ ◁ α ▷ h₂ ▷ r₃ otimes≫ adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = _ := by
      rw [adj₂.left_triangle]
      bicategory

Depends on / 依赖: bicategory, counit, leftAdjointSquare, leftAdjointSquare.vcomp, mateEquiv_apply, otimes, rightAdjointSquare, rightAdjointSquare.vcomp
-/
theorem mateEquiv_vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) :
    mateEquiv adj₁ adj₃ (leftAdjointSquare.vcomp α β) =
      rightAdjointSquare.vcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  simp only [leftAdjointSquare.vcomp, mateEquiv_apply', rightAdjointSquare.vcomp]
  symm
  calc
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ otimes≫ r₁ ◁ α ▷ r₂ ▷ g₂ otimes≫
          ((adj₁.counit ▷ (h₁ ≫ r₂ ≫ g₂ ≫ 𝟙 e)) ≫ 𝟙 b ◁ (h₁ ◁ r₂ ◁ g₂ ◁ adj₃.unit)) otimes≫
            h₁ ◁ r₂ ◁ β ▷ r₃ otimes≫ h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ otimes≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ 𝟙 e) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ g₂ ◁ adj₃.unit)) otimes≫
            ((adj₁.counit ▷ (h₁ ≫ r₂) ▷ (g₂ ≫ l₃) ≫ (𝟙 b ≫ h₁ ≫ r₂) ◁ β) ▷ r₃) otimes≫
              h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ 𝟙 e) ≫ (l₂ ≫ r₂) ◁ g₂ ◁ adj₃.unit) otimes≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ l₃) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ β) ▷ r₃) otimes≫
            (adj₁.counit ▷ h₁ ▷ (r₂ ≫ l₂) ≫ (𝟙 b ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit otimes≫
          r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ l₃) ≫ (l₂ ≫ r₂) ◁ β) ▷ r₃ otimes≫
            r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ otimes≫
              adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]; rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ otimes≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit otimes≫ r₁ ◁ g₁ ◁ β ▷ r₃ otimes≫
          ((r₁ ≫ g₁) ◁ leftZigzag adj₂.unit adj₂.counit ▷ (h₂ ≫ r₃)) otimes≫
            r₁ ◁ α ▷ h₂ ▷ r₃ otimes≫ adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; rw [← whisker_exchange]
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

/--
Definition of `leftAdjointSquare.hcomp` / `leftAdjointSquare.hcomp` 的定义

English:
definition leftAdjointSquare.hcomp
  signature: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k)
  body: (α_ _ _ _).inv ≫ α ▷ l₄ ≫ (α_ _ _ _).hom ≫ l₁ ◁ β ≫ (α_ _ _ _).inv

中文:
定义 leftAdjointSquare.hcomp
  签名: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k)
  定义体: (α_ _ _ _).inv ≫ α ▷ l₄ ≫ (α_ _ _ _).hom ≫ l₁ ◁ β ≫ (α_ _ _ _).inv
-/
def leftAdjointSquare.hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) :
    g ≫ (l₂ ≫ l₄) ⟶ (l₁ ≫ l₃) ≫ k :=
  (α_ _ _ _).inv ≫ α ▷ l₄ ≫ (α_ _ _ _).hom ≫ l₁ ◁ β ≫ (α_ _ _ _).inv

/--
Definition of `rightAdjointSquare.hcomp` / `rightAdjointSquare.hcomp` 的定义

English:
definition rightAdjointSquare.hcomp
  signature: (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₃ ≫ h ⟶ k ≫ r₄)
  body: (α_ _ _ _).hom ≫ r₃ ◁ α ≫ (α_ _ _ _).inv ≫ β ▷ r₂ ≫ (α_ _ _ _).hom

中文:
定义 rightAdjointSquare.hcomp
  签名: (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₃ ≫ h ⟶ k ≫ r₄)
  定义体: (α_ _ _ _).hom ≫ r₃ ◁ α ≫ (α_ _ _ _).inv ≫ β ▷ r₂ ≫ (α_ _ _ _).hom
-/
def rightAdjointSquare.hcomp (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₃ ≫ h ⟶ k ≫ r₄) :
    (r₃ ≫ r₁) ≫ g ⟶ k ≫ (r₄ ≫ r₂) :=
  (α_ _ _ _).hom ≫ r₃ ◁ α ≫ (α_ _ _ _).inv ≫ β ▷ r₂ ≫ (α_ _ _ _).hom

set_option backward.defeqAttrib.useBackward true in
/--
theorem `mateEquiv_hcomp` / 定理 `mateEquiv_hcomp`

English:
theorem mateEquiv_hcomp
  given: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k)
  proof: by
  simp only [mateEquiv_apply']
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp]
  calc
    _ = 𝟙 _ otimes≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit otimes≫
          r₃ ◁ r₁ ◁ ((g ≫ l₂) ◁ adj₄.unit ≫ α ▷ (l₄ ≫ r₄)) ▷ r₂ otimes≫
            r₃ ◁ ((r₁ ≫ l₁) ◁ β ≫ adj₁.counit ▷ (l₃ ≫ k)) ▷ r₄ ▷ r₂ otimes≫
              adj₃.counit ▷ k ▷ r₄ ▷ r₂ otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit otimes≫ r₃ ◁ r₁ ◁ α ▷ r₂ otimes≫
          r₃ ◁ ((r₁ ≫ l₁) ◁ h ◁ adj₄.unit ≫ adj₁.counit ▷ (h ≫ l₄ ≫ r₄)) ▷ r₂ otimes≫
            r₃ ◁ β ▷ r₄ ▷ r₂ otimes≫ adj₃.counit ▷ k ▷ r₄ ▷ r₂ otimes≫ 𝟙 _ := by
      rw [whisker_exchange]; rw [whisker_exchange]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

中文:
定理 mateEquiv_hcomp
  条件: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k)
  证明: by
  simp only [mateEquiv_apply']
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp]
  calc
    _ = 𝟙 _ otimes≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit otimes≫
          r₃ ◁ r₁ ◁ ((g ≫ l₂) ◁ adj₄.unit ≫ α ▷ (l₄ ≫ r₄)) ▷ r₂ otimes≫
            r₃ ◁ ((r₁ ≫ l₁) ◁ β ≫ adj₁.counit ▷ (l₃ ≫ k)) ▷ r₄ ▷ r₂ otimes≫
              adj₃.counit ▷ k ▷ r₄ ▷ r₂ otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit otimes≫ r₃ ◁ r₁ ◁ α ▷ r₂ otimes≫
          r₃ ◁ ((r₁ ≫ l₁) ◁ h ◁ adj₄.unit ≫ adj₁.counit ▷ (h ≫ l₄ ≫ r₄)) ▷ r₂ otimes≫
            r₃ ◁ β ▷ r₄ ▷ r₂ otimes≫ adj₃.counit ▷ k ▷ r₄ ▷ r₂ otimes≫ 𝟙 _ := by
      rw [whisker_exchange]; rw [whisker_exchange]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

Depends on / 依赖: bicategory, counit, leftAdjointSquare, leftAdjointSquare.hcomp, mateEquiv_apply, otimes, rightAdjointSquare, rightAdjointSquare.hcomp
-/
theorem mateEquiv_hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (leftAdjointSquare.hcomp α β) =
      rightAdjointSquare.hcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₃ adj₄ β) := by
  simp only [mateEquiv_apply']
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp]
  calc
    _ = 𝟙 _ otimes≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit otimes≫
          r₃ ◁ r₁ ◁ ((g ≫ l₂) ◁ adj₄.unit ≫ α ▷ (l₄ ≫ r₄)) ▷ r₂ otimes≫
            r₃ ◁ ((r₁ ≫ l₁) ◁ β ≫ adj₁.counit ▷ (l₃ ≫ k)) ▷ r₄ ▷ r₂ otimes≫
              adj₃.counit ▷ k ▷ r₄ ▷ r₂ otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit otimes≫ r₃ ◁ r₁ ◁ α ▷ r₂ otimes≫
          r₃ ◁ ((r₁ ≫ l₁) ◁ h ◁ adj₄.unit ≫ adj₁.counit ▷ (h ≫ l₄ ≫ r₄)) ▷ r₂ otimes≫
            r₃ ◁ β ▷ r₄ ▷ r₂ otimes≫ adj₃.counit ▷ k ▷ r₄ ▷ r₂ otimes≫ 𝟙 _ := by
      rw [whisker_exchange]; rw [whisker_exchange]
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

/--
Definition of `leftAdjointSquare.comp` / `leftAdjointSquare.comp` 的定义

English:
definition leftAdjointSquare.comp
  signature: :
  body: vcomp (hcomp α β) (hcomp γ δ)

中文:
定义 leftAdjointSquare.comp
  签名: :
  定义体: vcomp (hcomp α β) (hcomp γ δ)
-/
def leftAdjointSquare.comp :
    ((g₁ ≫ g₂) ≫ (l₅ ≫ l₆)) ⟶ ((l₁ ≫ l₂) ≫ (k₁ ≫ k₂)) :=
  vcomp (hcomp α β) (hcomp γ δ)

/--
theorem `leftAdjointSquare.comp_vhcomp` / 定理 `leftAdjointSquare.comp_vhcomp`

English:
theorem leftAdjointSquare.comp_vhcomp
  statement: comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ)
  proof: rfl

中文:
定理 leftAdjointSquare.comp_vhcomp
  结论: comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ)
  证明: rfl
-/
theorem leftAdjointSquare.comp_vhcomp : comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ) := rfl

/--
theorem `leftAdjointSquare.comp_hvcomp` / 定理 `leftAdjointSquare.comp_hvcomp`

English:
theorem leftAdjointSquare.comp_hvcomp
  proof: by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ otimes≫ g₁ ◁ γ ▷ l₆ otimes≫ ((g₁ ≫ l₃) ◁ δ ≫ α ▷ (l₄ ≫ k₂)) otimes≫ l₁ ◁ β ▷ k₂ otimes≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

中文:
定理 leftAdjointSquare.comp_hvcomp
  证明: by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ otimes≫ g₁ ◁ γ ▷ l₆ otimes≫ ((g₁ ≫ l₃) ◁ δ ≫ α ▷ (l₄ ≫ k₂)) otimes≫ l₁ ◁ β ▷ k₂ otimes≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

Depends on / 依赖: bicategory, otimes, whisker_exchange
-/
theorem leftAdjointSquare.comp_hvcomp :
    comp α β γ δ = hcomp (vcomp α γ) (vcomp β δ) := by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ otimes≫ g₁ ◁ γ ▷ l₆ otimes≫ ((g₁ ≫ l₃) ◁ δ ≫ α ▷ (l₄ ≫ k₂)) otimes≫ l₁ ◁ β ▷ k₂ otimes≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

end leftAdjointSquare.comp

section rightAdjointSquare.comp

variable (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₃) (β : r₂ ≫ h₁ ⟶ k₁ ≫ r₄)
variable (γ : r₃ ≫ g₂ ⟶ h₂ ≫ r₅) (δ : r₄ ≫ h₂ ⟶ k₂ ≫ r₆)

/--
Definition of `rightAdjointSquare.comp` / `rightAdjointSquare.comp` 的定义

English:
definition rightAdjointSquare.comp
  signature: :
  body: vcomp (hcomp α β) (hcomp γ δ)

中文:
定义 rightAdjointSquare.comp
  签名: :
  定义体: vcomp (hcomp α β) (hcomp γ δ)
-/
def rightAdjointSquare.comp :
    ((r₂ ≫ r₁) ≫ (g₁ ≫ g₂) ⟶ (k₁ ≫ k₂) ≫ (r₆ ≫ r₅)) :=
  vcomp (hcomp α β) (hcomp γ δ)

/--
theorem `rightAdjointSquare.comp_vhcomp` / 定理 `rightAdjointSquare.comp_vhcomp`

English:
theorem rightAdjointSquare.comp_vhcomp
  statement: comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ)
  proof: rfl

中文:
定理 rightAdjointSquare.comp_vhcomp
  结论: comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ)
  证明: rfl
-/
theorem rightAdjointSquare.comp_vhcomp : comp α β γ δ = vcomp (hcomp α β) (hcomp γ δ) := rfl

/--
theorem `rightAdjointSquare.comp_hvcomp` / 定理 `rightAdjointSquare.comp_hvcomp`

English:
theorem rightAdjointSquare.comp_hvcomp
  proof: by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ otimes≫ r₂ ◁ α ▷ g₂ otimes≫ (β ▷ (r₃ ≫ g₂) ≫ (k₁ ≫ r₄) ◁ γ) otimes≫ k₁ ◁ δ ▷ r₅ otimes≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

中文:
定理 rightAdjointSquare.comp_hvcomp
  证明: by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ otimes≫ r₂ ◁ α ▷ g₂ otimes≫ (β ▷ (r₃ ≫ g₂) ≫ (k₁ ≫ r₄) ◁ γ) otimes≫ k₁ ◁ δ ▷ r₅ otimes≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

Depends on / 依赖: bicategory, otimes, whisker_exchange
-/
theorem rightAdjointSquare.comp_hvcomp :
    comp α β γ δ = hcomp (vcomp α γ) (vcomp β δ) := by
  dsimp only [comp, vcomp, hcomp]
  calc
    _ = 𝟙 _ otimes≫ r₂ ◁ α ▷ g₂ otimes≫ (β ▷ (r₃ ≫ g₂) ≫ (k₁ ≫ r₄) ◁ γ) otimes≫ k₁ ◁ δ ▷ r₅ otimes≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

end rightAdjointSquare.comp

/--
theorem `mateEquiv_square` / 定理 `mateEquiv_square`

English:
theorem mateEquiv_square
  proof: by
  have vcomp :=
    mateEquiv_vcomp (adj₁.comp adj₂) (adj₃.comp adj₄) (adj₅.comp adj₆)
      (leftAdjointSquare.hcomp α β) (leftAdjointSquare.hcomp γ δ)
  have hcomp1 := mateEquiv_hcomp adj₁ adj₃ adj₂ adj₄ α β
  have hcomp2 := mateEquiv_hcomp adj₃ adj₅ adj₄ adj₆ γ δ
  rw [hcomp1]; rw [hcomp2] at vcomp
  exact vcomp

中文:
定理 mateEquiv_square
  证明: by
  have vcomp :=
    mateEquiv_vcomp (adj₁.comp adj₂) (adj₃.comp adj₄) (adj₅.comp adj₆)
      (leftAdjointSquare.hcomp α β) (leftAdjointSquare.hcomp γ δ)
  have hcomp1 := mateEquiv_hcomp adj₁ adj₃ adj₂ adj₄ α β
  have hcomp2 := mateEquiv_hcomp adj₃ adj₅ adj₄ adj₆ γ δ
  rw [hcomp1]; rw [hcomp2] at vcomp
  exact vcomp

Depends on / 依赖: hcomp1, hcomp2, leftAdjointSquare, leftAdjointSquare.hcomp, mateEquiv_hcomp, mateEquiv_vcomp
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
  rw [hcomp1]; rw [hcomp2] at vcomp
  exact vcomp

end mateEquivSquareComp

section conjugateEquiv

section

variable {c d : B}
variable {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/--
Definition of `conjugateEquiv` / `conjugateEquiv` 的定义

English:
definition conjugateEquiv
  signature: : (l₂ ⟶ l₁) ≃ (r₁ ⟶ r₂)
  body: calc
    (l₂ ⟶ l₁) ≃ _ := (Iso.homCongr (fun_ l₂) (ρ_ l₁)).symm
    _ ≃ _ := mateEquiv adj₁ adj₂
    _ ≃ (r₁ ⟶ r₂) := Iso.homCongr (ρ_ r₁) (fun_ r₂)

中文:
定义 conjugateEquiv
  签名: : (l₂ ⟶ l₁) ≃ (r₁ ⟶ r₂)
  定义体: calc
    (l₂ ⟶ l₁) ≃ _ := (Iso.homCongr (fun_ l₂) (ρ_ l₁)).symm
    _ ≃ _ := mateEquiv adj₁ adj₂
    _ ≃ (r₁ ⟶ r₂) := Iso.homCongr (ρ_ r₁) (fun_ r₂)

Depends on / 依赖: Iso.homCongr, fun_, homCongr, mateEquiv
-/
def conjugateEquiv : (l₂ ⟶ l₁) ≃ (r₁ ⟶ r₂) :=
  calc
    (l₂ ⟶ l₁) ≃ _ := (Iso.homCongr (fun_ l₂) (ρ_ l₁)).symm
    _ ≃ _ := mateEquiv adj₁ adj₂
    _ ≃ (r₁ ⟶ r₂) := Iso.homCongr (ρ_ r₁) (fun_ r₂)

/--
theorem `conjugateEquiv_apply` / 定理 `conjugateEquiv_apply`

English:
theorem conjugateEquiv_apply
  given: (α : l₂ ⟶ l₁)
  proof: rfl

中文:
定理 conjugateEquiv_apply
  条件: (α : l₂ ⟶ l₁)
  证明: rfl
-/
theorem conjugateEquiv_apply (α : l₂ ⟶ l₁) :
    conjugateEquiv adj₁ adj₂ α =
      (ρ_ r₁).inv ≫ mateEquiv adj₁ adj₂ ((fun_ l₂).hom ≫ α ≫ (ρ_ l₁).inv) ≫ (fun_ r₂).hom :=
  rfl

/--
theorem `conjugateEquiv_apply'` / 定理 `conjugateEquiv_apply'`

English:
theorem conjugateEquiv_apply'
  given: (α : l₂ ⟶ l₁)
  proof: by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  bicategory

中文:
定理 conjugateEquiv_apply'
  条件: (α : l₂ ⟶ l₁)
  证明: by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  bicategory

Depends on / 依赖: bicategory, conjugateEquiv_apply, mateEquiv_apply
-/
theorem conjugateEquiv_apply' (α : l₂ ⟶ l₁) :
    conjugateEquiv adj₁ adj₂ α =
      (ρ_ _).inv ≫ r₁ ◁ adj₂.unit ≫ r₁ ◁ α ▷ r₂ ≫ (α_ _ _ _).inv ≫
        adj₁.counit ▷ r₂ ≫ (fun_ _).hom := by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  bicategory

/--
theorem `conjugateEquiv_symm_apply` / 定理 `conjugateEquiv_symm_apply`

English:
theorem conjugateEquiv_symm_apply
  given: (α : r₁ ⟶ r₂)
  proof: rfl

中文:
定理 conjugateEquiv_symm_apply
  条件: (α : r₁ ⟶ r₂)
  证明: rfl
-/
theorem conjugateEquiv_symm_apply (α : r₁ ⟶ r₂) :
    (conjugateEquiv adj₁ adj₂).symm α =
      (fun_ l₂).inv ≫ (mateEquiv adj₁ adj₂).symm ((ρ_ r₁).hom ≫ α ≫ (fun_ r₂).inv) ≫ (ρ_ l₁).hom :=
  rfl

/--
theorem `conjugateEquiv_symm_apply'` / 定理 `conjugateEquiv_symm_apply'`

English:
theorem conjugateEquiv_symm_apply'
  given: (α : r₁ ⟶ r₂)
  proof: by
  rw [conjugateEquiv_symm_apply]; rw [mateEquiv_symm_apply']
  bicategory

@[simp]

中文:
定理 conjugateEquiv_symm_apply'
  条件: (α : r₁ ⟶ r₂)
  证明: by
  rw [conjugateEquiv_symm_apply]; rw [mateEquiv_symm_apply']
  bicategory

@[simp]

Depends on / 依赖: bicategory, conjugateEquiv_symm_apply, mateEquiv_symm_apply
-/
theorem conjugateEquiv_symm_apply' (α : r₁ ⟶ r₂) :
    (conjugateEquiv adj₁ adj₂).symm α =
      (fun_ _).inv ≫ adj₁.unit ▷ l₂ ≫ (α_ _ _ _).hom ≫ l₁ ◁ α ▷ l₂ ≫
        l₁ ◁ adj₂.counit ≫ (ρ_ _).hom := by
  rw [conjugateEquiv_symm_apply]; rw [mateEquiv_symm_apply']
  bicategory

@[simp]
/--
theorem `conjugateEquiv_id` / 定理 `conjugateEquiv_id`

English:
theorem conjugateEquiv_id
  statement: conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _
  proof: by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  calc
    _ = 𝟙 _ otimes≫ rightZigzag adj₁.unit adj₁.counit otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 r₁ := by
      rw [adj₁.right_triangle]
      bicategory

@[simp]

中文:
定理 conjugateEquiv_id
  结论: conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _
  证明: by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  calc
    _ = 𝟙 _ otimes≫ rightZigzag adj₁.unit adj₁.counit otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 r₁ := by
      rw [adj₁.right_triangle]
      bicategory

@[simp]

Depends on / 依赖: bicategory, conjugateEquiv_apply, counit, mateEquiv_apply, of_vComp, otimes, rightZigzag, right_triangle
-/
theorem conjugateEquiv_id : conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  calc
    _ = 𝟙 _ otimes≫ rightZigzag adj₁.unit adj₁.counit otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 r₁ := by
      rw [adj₁.right_triangle]
      bicategory

@[simp]
/--
theorem `conjugateEquiv_symm_id` / 定理 `conjugateEquiv_symm_id`

English:
theorem conjugateEquiv_symm_id
  statement: (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _
  proof: by
  rw [Equiv.symm_apply_eq]; rw [conjugateEquiv_id]

中文:
定理 conjugateEquiv_symm_id
  结论: (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _
  证明: by
  rw [Equiv.symm_apply_eq]; rw [conjugateEquiv_id]

Depends on / 依赖: Equiv.symm_apply_eq, conjugateEquiv_id, symm_apply_eq
-/
theorem conjugateEquiv_symm_id : (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq]; rw [conjugateEquiv_id]

/--
theorem `conjugateEquiv_adjunction_id` / 定理 `conjugateEquiv_adjunction_id`

English:
theorem conjugateEquiv_adjunction_id
  given: {l r : c ⟶ c} (adj : l ⊣ r) (α : 𝟙 c ⟶ l)
  proof: by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  dsimp [Adjunction.id]
  bicategory

中文:
定理 conjugateEquiv_adjunction_id
  条件: {l r : c ⟶ c} (adj : l ⊣ r) (α : 𝟙 c ⟶ l)
  证明: by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  dsimp [Adjunction.id]
  bicategory

Depends on / 依赖: Adjunction, Adjunction.id, TwoSquare, TwoSquare.vComp, bicategory, conjugateEquiv_apply, mateEquiv_apply, vComp_iff_of_equivalences, whiskerVertical_iff
-/
theorem conjugateEquiv_adjunction_id {l r : c ⟶ c} (adj : l ⊣ r) (α : 𝟙 c ⟶ l) :
    (conjugateEquiv adj (Adjunction.id c) α) = (ρ_ _).inv ≫ r ◁ α ≫ adj.counit := by
  rw [conjugateEquiv_apply]; rw [mateEquiv_apply']
  dsimp [Adjunction.id]
  bicategory

/--
theorem `conjugateEquiv_adjunction_id_symm` / 定理 `conjugateEquiv_adjunction_id_symm`

English:
theorem conjugateEquiv_adjunction_id_symm
  given: {l r : c ⟶ c} (adj : l ⊣ r) (α : r ⟶ 𝟙 c)
  proof: by
  rw [conjugateEquiv_symm_apply]; rw [mateEquiv_symm_apply']
  dsimp [Adjunction.id]
  bicategory

中文:
定理 conjugateEquiv_adjunction_id_symm
  条件: {l r : c ⟶ c} (adj : l ⊣ r) (α : r ⟶ 𝟙 c)
  证明: by
  rw [conjugateEquiv_symm_apply]; rw [mateEquiv_symm_apply']
  dsimp [Adjunction.id]
  bicategory

Depends on / 依赖: Adjunction, Adjunction.id, bicategory, conjugateEquiv_symm_apply, mateEquiv_symm_apply
-/
theorem conjugateEquiv_adjunction_id_symm {l r : c ⟶ c} (adj : l ⊣ r) (α : r ⟶ 𝟙 c) :
    (conjugateEquiv adj (Adjunction.id c)).symm α = adj.unit ≫ l ◁ α ≫ (ρ_ _).hom := by
  rw [conjugateEquiv_symm_apply]; rw [mateEquiv_symm_apply']
  dsimp [Adjunction.id]
  bicategory

end

@[simp]
/--
lemma `mateEquiv_leftUnitor_hom_rightUnitor_inv` / 引理 `mateEquiv_leftUnitor_hom_rightUnitor_inv`

English:
lemma mateEquiv_leftUnitor_hom_rightUnitor_inv
  proof: by
  simp [← cancel_mono (fun_ r).hom,
    ← conjugateEquiv_id adj, conjugateEquiv_apply]

中文:
引理 mateEquiv_leftUnitor_hom_rightUnitor_inv
  证明: by
  simp [← cancel_mono (fun_ r).hom,
    ← conjugateEquiv_id adj, conjugateEquiv_apply]

Depends on / 依赖: cancel_mono, conjugateEquiv_apply, conjugateEquiv_id, fun_
-/
lemma mateEquiv_leftUnitor_hom_rightUnitor_inv
    {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r) :
    mateEquiv adj adj ((fun_ _).hom ≫ (ρ_ _).inv) = (ρ_ _).hom ≫ (fun_ _).inv := by
  simp [← cancel_mono (fun_ r).hom,
    ← conjugateEquiv_id adj, conjugateEquiv_apply]

section

variable {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    {l' : a ⟶ b} {r' : b ⟶ a} (adj' : l' ⊣ r') (φ : l' ⟶ l)

/--
lemma `conjugateEquiv_id_comp_right_apply` / 引理 `conjugateEquiv_id_comp_right_apply`

English:
lemma conjugateEquiv_id_comp_right_apply
  proof: by
  simp only [conjugateEquiv_apply, mateEquiv_id_comp_right,
    id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  bicategory

中文:
引理 conjugateEquiv_id_comp_right_apply
  证明: by
  simp only [conjugateEquiv_apply, mateEquiv_id_comp_right,
    id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  bicategory

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, bicategory, conjugateEquiv_apply, id_whiskerLeft, inv_hom_id_assoc, mateEquiv_id_comp_right
-/
lemma conjugateEquiv_id_comp_right_apply :
    conjugateEquiv adj ((Adjunction.id _).comp adj') ((fun_ _).hom ≫ φ) =
      conjugateEquiv adj adj' φ ≫ (ρ_ _).inv := by
  simp only [conjugateEquiv_apply, mateEquiv_id_comp_right,
    id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  bicategory

/--
lemma `conjugateEquiv_comp_id_right_apply` / 引理 `conjugateEquiv_comp_id_right_apply`

English:
lemma conjugateEquiv_comp_id_right_apply
  proof: by
  simp only [conjugateEquiv_apply, Category.assoc, mateEquiv_comp_id_right, id_whiskerLeft,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id, Iso.cancel_iso_inv_left,
    EmbeddingLike.apply_eq_iff_eq]
  bicategory

中文:
引理 conjugateEquiv_comp_id_right_apply
  证明: by
  simp only [conjugateEquiv_apply, Category.assoc, mateEquiv_comp_id_right, id_whiskerLeft,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id, Iso.cancel_iso_inv_left,
    EmbeddingLike.apply_eq_iff_eq]
  bicategory

Depends on / 依赖: Abelian, Category, Category.assoc, Category.comp_id, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Iso.cancel_iso_inv_left, Iso.hom_inv_id, Iso.inv_hom_id, apply_eq_iff_eq, bicategory, cancel_iso_inv_left, comp_id, conjugateEquiv_apply, hom_inv_id, id_whiskerLeft, inv_hom_id, isIdempotentComplete_of_abelian, mateEquiv_comp_id_right
-/
lemma conjugateEquiv_comp_id_right_apply :
    conjugateEquiv adj (adj'.comp (Adjunction.id _)) ((ρ_ _).hom ≫ φ) =
      conjugateEquiv adj adj' φ ≫ (fun_ _).inv := by
  simp only [conjugateEquiv_apply, Category.assoc, mateEquiv_comp_id_right, id_whiskerLeft,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id, Iso.cancel_iso_inv_left,
    EmbeddingLike.apply_eq_iff_eq]
  bicategory

end

/--
lemma `conjugateEquiv_whiskerLeft` / 引理 `conjugateEquiv_whiskerLeft`

English:
lemma conjugateEquiv_whiskerLeft
  proof: by
  have := mateEquiv_hcomp adj₁ adj₁ adj₂ adj₂' ((fun_ _).hom ≫ (ρ_ _).inv)
    ((fun_ _).hom ≫ φ ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    whiskerLeft_rightUnitor, triangle_assoc_comp_left_inv_assoc, Iso.hom_inv_id_assoc] at this
  simp [conjugateEquiv_apply, this]

中文:
引理 conjugateEquiv_whiskerLeft
  证明: by
  have := mateEquiv_hcomp adj₁ adj₁ adj₂ adj₂' ((fun_ _).hom ≫ (ρ_ _).inv)
    ((fun_ _).hom ≫ φ ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    whiskerLeft_rightUnitor, triangle_assoc_comp_left_inv_assoc, Iso.hom_inv_id_assoc] at this
  simp [conjugateEquiv_apply, this]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.h, Iso.hom_inv_id, Iso.inv_hom_id_assoc, comp_id, comp_whiskerRight, fun_, hom_inv_id, inv_hom_id_assoc, inv_hom_whiskerRight_assoc, leftAdjointSquare, leftAdjointSquare.hcomp, leftUnitor_whiskerRight, mateEquiv_hcomp, mateEquiv_leftUnitor_hom_rightUnitor_inv, rightAdjointSquare, rightAdjointSquare.hcomp, triangle_assoc
-/
lemma conjugateEquiv_whiskerLeft
    {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
    {l₂' : b ⟶ c} {r₂' : c ⟶ b} (adj₂' : l₂' ⊣ r₂') (φ : l₂' ⟶ l₂) :
    conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂') (l₁ ◁ φ) =
      conjugateEquiv adj₂ adj₂' φ ▷ r₁ := by
  have := mateEquiv_hcomp adj₁ adj₁ adj₂ adj₂' ((fun_ _).hom ≫ (ρ_ _).inv)
    ((fun_ _).hom ≫ φ ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    whiskerLeft_rightUnitor, triangle_assoc_comp_left_inv_assoc, Iso.hom_inv_id_assoc] at this
  simp [conjugateEquiv_apply, this]

/--
lemma `conjugateEquiv_whiskerRight` / 引理 `conjugateEquiv_whiskerRight`

English:
lemma conjugateEquiv_whiskerRight
  proof: by
  have := mateEquiv_hcomp adj₁ adj₁' adj₂ adj₂
    ((fun_ _).hom ≫ φ ≫ (ρ_ _).inv) ((fun_ _).hom ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id, triangle_assoc_comp_right_assoc] at this
  simp [conjugateEquiv_apply, this]

中文:
引理 conjugateEquiv_whiskerRight
  证明: by
  have := mateEquiv_hcomp adj₁ adj₁' adj₂ adj₂
    ((fun_ _).hom ≫ φ ≫ (ρ_ _).inv) ((fun_ _).hom ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id, triangle_assoc_comp_right_assoc] at this
  simp [conjugateEquiv_apply, this]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.hom_inv_id, Iso.inv_hom_id, Iso.inv_hom_id_assoc, comp_id, comp_whiskerRight, fun_, hom_inv_id, inv_hom_id, inv_hom_id_assoc, inv_hom_whiskerRight_assoc, leftAdjointSquare, leftAdjointSquare.hcomp, leftUnitor_inv_whiskerRight, leftUnitor_whiskerRight, mateEquiv_hcomp, mateEquiv_leftUnitor_hom_rightUnitor_inv, rightAdjointSquare
-/
lemma conjugateEquiv_whiskerRight
    {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    {l₁' : a ⟶ b} {r₁' : b ⟶ a} (adj₁' : l₁' ⊣ r₁')
    {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂) (φ : l₁' ⟶ l₁) :
    conjugateEquiv (adj₁.comp adj₂) (adj₁'.comp adj₂) (φ ▷ l₂) =
      r₂ ◁ conjugateEquiv adj₁ adj₁' φ := by
  have := mateEquiv_hcomp adj₁ adj₁' adj₂ adj₂
    ((fun_ _).hom ≫ φ ≫ (ρ_ _).inv) ((fun_ _).hom ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id, triangle_assoc_comp_right_assoc] at this
  simp [conjugateEquiv_apply, this]

set_option linter.flexible false in -- simp followed by bicategory
/--
lemma `conjugateEquiv_associator_hom` / 引理 `conjugateEquiv_associator_hom`

English:
lemma conjugateEquiv_associator_hom
  proof: by
  simp [← cancel_epi (ρ_ ((r₃ ≫ r₂) ≫ r₁)).hom, ← cancel_mono (fun_ (r₃ ≫ r₂ ≫ r₁)).inv,
    conjugateEquiv_apply, mateEquiv_eq_iff, Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply]
  bicategory

中文:
引理 conjugateEquiv_associator_hom
  证明: by
  simp [← cancel_epi (ρ_ ((r₃ ≫ r₂) ≫ r₁)).hom, ← cancel_mono (fun_ (r₃ ≫ r₂ ≫ r₁)).inv,
    conjugateEquiv_apply, mateEquiv_eq_iff, Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply]
  bicategory

Depends on / 依赖: Adjunction, Adjunction.homEquiv, bicategory, cancel_epi, cancel_mono, conjugateEquiv_apply, fun_, mateEquiv_eq_iff
-/
lemma conjugateEquiv_associator_hom
    {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
    {l₃ : c ⟶ d} {r₃ : d ⟶ c} (adj₃ : l₃ ⊣ r₃) :
    conjugateEquiv (adj₁.comp (adj₂.comp adj₃))
      ((adj₁.comp adj₂).comp adj₃) (α_ _ _ _).hom = (α_ _ _ _).hom := by
  simp [← cancel_epi (ρ_ ((r₃ ≫ r₂) ≫ r₁)).hom, ← cancel_mono (fun_ (r₃ ≫ r₂ ≫ r₁)).inv,
    conjugateEquiv_apply, mateEquiv_eq_iff, Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply]
  bicategory

end conjugateEquiv

section ConjugateComposition
variable {c d : B}
variable {l₁ l₂ l₃ : c ⟶ d} {r₁ r₂ r₃ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

@[simp]
/--
theorem `conjugateEquiv_comp` / 定理 `conjugateEquiv_comp`

English:
theorem conjugateEquiv_comp
  given: (α : l₂ ⟶ l₁) (β : l₃ ⟶ l₂)
  proof: by
  simp only [conjugateEquiv_apply]
  calc
    _ = 𝟙 r₁ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((fun_ _).hom ≫ α ≫ (ρ_ _).inv))
            (mateEquiv adj₂ adj₃ ((fun_ _).hom ≫ β ≫ (ρ_ _).inv)) otimes≫ 𝟙 r₃ := by
      dsimp only [rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply']
      bicategory

@[simp]

中文:
定理 conjugateEquiv_comp
  条件: (α : l₂ ⟶ l₁) (β : l₃ ⟶ l₂)
  证明: by
  simp only [conjugateEquiv_apply]
  calc
    _ = 𝟙 r₁ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((fun_ _).hom ≫ α ≫ (ρ_ _).inv))
            (mateEquiv adj₂ adj₃ ((fun_ _).hom ≫ β ≫ (ρ_ _).inv)) otimes≫ 𝟙 r₃ := by
      dsimp only [rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply']
      bicategory

@[simp]

Depends on / 依赖: bicategory, conjugateEquiv_apply, fun_, leftAdjointSquare, leftAdjointSquare.vcomp, mateEquiv, mateEquiv_apply, mateEquiv_vcomp, otimes, rightAdjointSquare, rightAdjointSquare.vcomp
-/
theorem conjugateEquiv_comp (α : l₂ ⟶ l₁) (β : l₃ ⟶ l₂) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β =
      conjugateEquiv adj₁ adj₃ (β ≫ α) := by
  simp only [conjugateEquiv_apply]
  calc
    _ = 𝟙 r₁ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((fun_ _).hom ≫ α ≫ (ρ_ _).inv))
            (mateEquiv adj₂ adj₃ ((fun_ _).hom ≫ β ≫ (ρ_ _).inv)) otimes≫ 𝟙 r₃ := by
      dsimp only [rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply']
      bicategory

@[simp]
/--
theorem `conjugateEquiv_symm_comp` / 定理 `conjugateEquiv_symm_comp`

English:
theorem conjugateEquiv_symm_comp
  given: (α : r₁ ⟶ r₂) (β : r₂ ⟶ r₃)
  proof: by
  rw [Equiv.eq_symm_apply]; rw [← conjugateEquiv_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]

中文:
定理 conjugateEquiv_symm_comp
  条件: (α : r₁ ⟶ r₂) (β : r₂ ⟶ r₃)
  证明: by
  rw [Equiv.eq_symm_apply]; rw [← conjugateEquiv_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.eq_symm_apply, apply_symm_apply, conjugateEquiv_comp, eq_symm_apply
-/
theorem conjugateEquiv_symm_comp (α : r₁ ⟶ r₂) (β : r₂ ⟶ r₃) :
    (conjugateEquiv adj₂ adj₃).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α =
      (conjugateEquiv adj₁ adj₃).symm (α ≫ β) := by
  rw [Equiv.eq_symm_apply]; rw [← conjugateEquiv_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]

/--
theorem `conjugateEquiv_comm` / 定理 `conjugateEquiv_comm`

English:
theorem conjugateEquiv_comm
  given: {α : l₂ ⟶ l₁} {β : l₁ ⟶ l₂} (βα : β ≫ α = 𝟙 _)
  proof: by
  rw [conjugateEquiv_comp]; rw [βα]; rw [conjugateEquiv_id]

中文:
定理 conjugateEquiv_comm
  条件: {α : l₂ ⟶ l₁} {β : l₁ ⟶ l₂} (βα : β ≫ α = 𝟙 _)
  证明: by
  rw [conjugateEquiv_comp]; rw [βα]; rw [conjugateEquiv_id]

Depends on / 依赖: conjugateEquiv_comp, conjugateEquiv_id
-/
theorem conjugateEquiv_comm {α : l₂ ⟶ l₁} {β : l₁ ⟶ l₂} (βα : β ≫ α = 𝟙 _) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₁ β = 𝟙 _ := by
  rw [conjugateEquiv_comp]; rw [βα]; rw [conjugateEquiv_id]

/--
theorem `conjugateEquiv_symm_comm` / 定理 `conjugateEquiv_symm_comm`

English:
theorem conjugateEquiv_symm_comm
  given: {α : r₁ ⟶ r₂} {β : r₂ ⟶ r₁} (αβ : α ≫ β = 𝟙 _)
  proof: by
  rw [conjugateEquiv_symm_comp]; rw [αβ]; rw [conjugateEquiv_symm_id]

中文:
定理 conjugateEquiv_symm_comm
  条件: {α : r₁ ⟶ r₂} {β : r₂ ⟶ r₁} (αβ : α ≫ β = 𝟙 _)
  证明: by
  rw [conjugateEquiv_symm_comp]; rw [αβ]; rw [conjugateEquiv_symm_id]

Depends on / 依赖: conjugateEquiv_symm_comp, conjugateEquiv_symm_id
-/
theorem conjugateEquiv_symm_comm {α : r₁ ⟶ r₂} {β : r₂ ⟶ r₁} (αβ : α ≫ β = 𝟙 _) :
    (conjugateEquiv adj₂ adj₁).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = 𝟙 _ := by
  rw [conjugateEquiv_symm_comp]; rw [αβ]; rw [conjugateEquiv_symm_id]

end ConjugateComposition

section ConjugateIsomorphism

variable {c d : B}
variable {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/--
Instance `conjugateEquiv_iso` / 实例 `conjugateEquiv_iso`

English:
instance conjugateEquiv_iso
  signature: (α : l₂ ⟶ l₁) [IsIso α]
  body: ⟨⟨conjugateEquiv adj₂ adj₁ (inv α),
      ⟨conjugateEquiv_comm _ _ (by simp), conjugateEquiv_comm _ _ (by simp)⟩⟩⟩

中文:
实例 conjugateEquiv_iso
  签名: (α : l₂ ⟶ l₁) [是同构 α]
  定义体: ⟨⟨conjugateEquiv adj₂ adj₁ (inv α),
      ⟨conjugateEquiv_comm _ _ (by simp), conjugateEquiv_comm _ _ (by simp)⟩⟩⟩

Depends on / 依赖: conjugateEquiv, conjugateEquiv_comm
-/
instance conjugateEquiv_iso (α : l₂ ⟶ l₁) [IsIso α] :
    IsIso (conjugateEquiv adj₁ adj₂ α) :=
  ⟨⟨conjugateEquiv adj₂ adj₁ (inv α),
      ⟨conjugateEquiv_comm _ _ (by simp), conjugateEquiv_comm _ _ (by simp)⟩⟩⟩

/--
Instance `conjugateEquiv_symm_iso` / 实例 `conjugateEquiv_symm_iso`

English:
instance conjugateEquiv_symm_iso
  signature: (α : r₁ ⟶ r₂) [IsIso α]
  body: ⟨⟨(conjugateEquiv adj₂ adj₁).symm (inv α),
      ⟨conjugateEquiv_symm_comm _ _ (by simp), conjugateEquiv_symm_comm _ _ (by simp)⟩⟩⟩

中文:
实例 conjugateEquiv_symm_iso
  签名: (α : r₁ ⟶ r₂) [是同构 α]
  定义体: ⟨⟨(conjugateEquiv adj₂ adj₁).symm (inv α),
      ⟨conjugateEquiv_symm_comm _ _ (by simp), conjugateEquiv_symm_comm _ _ (by simp)⟩⟩⟩

Depends on / 依赖: conjugateEquiv, conjugateEquiv_symm_comm
-/
instance conjugateEquiv_symm_iso (α : r₁ ⟶ r₂) [IsIso α] :
    IsIso ((conjugateEquiv adj₁ adj₂).symm α) :=
  ⟨⟨(conjugateEquiv adj₂ adj₁).symm (inv α),
      ⟨conjugateEquiv_symm_comm _ _ (by simp), conjugateEquiv_symm_comm _ _ (by simp)⟩⟩⟩

/--
theorem `conjugateEquiv_of_iso` / 定理 `conjugateEquiv_of_iso`

English:
theorem conjugateEquiv_of_iso
  given: (α : l₂ ⟶ l₁) [IsIso (conjugateEquiv adj₁ adj₂ α)]
  proof: by
  suffices IsIso ((conjugateEquiv adj₁ adj₂).symm (conjugateEquiv adj₁ adj₂ α))
    by simpa only [Equiv.symm_apply_apply] using this
  infer_instance

中文:
定理 conjugateEquiv_of_iso
  条件: (α : l₂ ⟶ l₁) [是同构 (conjugateEquiv adj₁ adj₂ α)]
  证明: by
  suffices IsIso ((conjugateEquiv adj₁ adj₂).symm (conjugateEquiv adj₁ adj₂ α))
    by simpa only [Equiv.symm_apply_apply] using this
  infer_instance

Depends on / 依赖: Equiv.symm_apply_apply, conjugateEquiv, infer_instance, symm_apply_apply
-/
theorem conjugateEquiv_of_iso (α : l₂ ⟶ l₁) [IsIso (conjugateEquiv adj₁ adj₂ α)] :
    IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂).symm (conjugateEquiv adj₁ adj₂ α))
    by simpa only [Equiv.symm_apply_apply] using this
  infer_instance

/--
theorem `conjugateEquiv_symm_of_iso` / 定理 `conjugateEquiv_symm_of_iso`

English:
theorem conjugateEquiv_symm_of_iso
  statement: (α : r₁ ⟶ r₂)
  proof: by
  suffices IsIso ((conjugateEquiv adj₁ adj₂) ((conjugateEquiv adj₁ adj₂).symm α))
    by simpa only [Equiv.apply_symm_apply] using this
  infer_instance

中文:
定理 conjugateEquiv_symm_of_iso
  结论: (α : r₁ ⟶ r₂)
  证明: by
  suffices IsIso ((conjugateEquiv adj₁ adj₂) ((conjugateEquiv adj₁ adj₂).symm α))
    by simpa only [Equiv.apply_symm_apply] using this
  infer_instance

Depends on / 依赖: Equiv.apply_symm_apply, P.complement.decompId.symm, P.complement.decompId_i, P.complement.decompId_p, P.decompId.symm, P.decompId_i, P.decompId_p, apply_symm_apply, comp_f, comp_id, comp_sub, complement, complement_X, complement_p, conjugateEquiv, decompId, decompId_i, decompId_i_f, decompId_p, decompId_p_f
-/
theorem conjugateEquiv_symm_of_iso (α : r₁ ⟶ r₂)
    [IsIso ((conjugateEquiv adj₁ adj₂).symm α)] : IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂) ((conjugateEquiv adj₁ adj₂).symm α))
    by simpa only [Equiv.apply_symm_apply] using this
  infer_instance

/-- Thus conjugation defines an equivalence between isomorphisms. -/
@[simps]
/--
Definition of `conjugateIsoEquiv` / `conjugateIsoEquiv` 的定义

English:
definition conjugateIsoEquiv
  signature: : (l₂ ≅ l₁) ≃ (r₁ ≅ r₂) where
  body: { hom := conjugateEquiv adj₁ adj₂ α.hom
      inv := conjugateEquiv adj₂ adj₁ α.inv
      hom_inv_id := by
        rw [conjugateEquiv_comp]; rw [Iso.inv_hom_id]; rw [conjugateEquiv_id]
      inv_hom_id := by
        rw [conjugateEquiv_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_id] }
  invFun β :=
    { hom := (conjugateEquiv adj₁ adj₂).symm β.hom
      inv := (conjugateEquiv adj₂ adj₁).symm β.inv
      hom_inv_id := by
        rw [conjugateEquiv_symm_comp]; rw [Iso.inv_hom_id]; rw [conjugateEquiv_symm_id]
      inv_hom_id := by
        rw [conjugateEquiv_symm_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_symm_id] }
  left_inv := by
    intro α
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro α
    simp only [Equiv.apply_symm_apply]

中文:
定义 conjugateIsoEquiv
  签名: : (l₂ ≅ l₁) ≃ (r₁ ≅ r₂) where
  定义体: { hom := conjugateEquiv adj₁ adj₂ α.hom
      inv := conjugateEquiv adj₂ adj₁ α.inv
      hom_inv_id := by
        rw [conjugateEquiv_comp]; rw [Iso.inv_hom_id]; rw [conjugateEquiv_id]
      inv_hom_id := by
        rw [conjugateEquiv_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_id] }
  invFun β :=
    { hom := (conjugateEquiv adj₁ adj₂).symm β.hom
      inv := (conjugateEquiv adj₂ adj₁).symm β.inv
      hom_inv_id := by
        rw [conjugateEquiv_symm_comp]; rw [Iso.inv_hom_id]; rw [conjugateEquiv_symm_id]
      inv_hom_id := by
        rw [conjugateEquiv_symm_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_symm_id] }
  left_inv := by
    intro α
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro α
    simp only [Equiv.apply_symm_apply]

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, conjugateEquiv, conjugateEquiv_comp, conjugateEquiv_id, conjugateEquiv_symm_comp, conjugateEquiv_symm_id, hom_inv_id, invFun, inv_hom_id
-/
def conjugateIsoEquiv : (l₂ ≅ l₁) ≃ (r₁ ≅ r₂) where
  toFun α :=
    { hom := conjugateEquiv adj₁ adj₂ α.hom
      inv := conjugateEquiv adj₂ adj₁ α.inv
      hom_inv_id := by
        rw [conjugateEquiv_comp]; rw [Iso.inv_hom_id]; rw [conjugateEquiv_id]
      inv_hom_id := by
        rw [conjugateEquiv_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_id] }
  invFun β :=
    { hom := (conjugateEquiv adj₁ adj₂).symm β.hom
      inv := (conjugateEquiv adj₂ adj₁).symm β.inv
      hom_inv_id := by
        rw [conjugateEquiv_symm_comp]; rw [Iso.inv_hom_id]; rw [conjugateEquiv_symm_id]
      inv_hom_id := by
        rw [conjugateEquiv_symm_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_symm_id] }
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

/--
theorem `iterated_mateEquiv_conjugateEquiv` / 定理 `iterated_mateEquiv_conjugateEquiv`

English:
theorem iterated_mateEquiv_conjugateEquiv
  given: (α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂)
  proof: by
  simp only [conjugateEquiv_apply, mateEquiv_apply']
  dsimp [Adjunction.comp]
  bicategory

中文:
定理 iterated_mateEquiv_conjugateEquiv
  条件: (α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂)
  证明: by
  simp only [conjugateEquiv_apply, mateEquiv_apply']
  dsimp [Adjunction.comp]
  bicategory

Depends on / 依赖: Adjunction, Adjunction.comp, bicategory, conjugateEquiv_apply, mateEquiv_apply
-/
theorem iterated_mateEquiv_conjugateEquiv (α : f₁ ≫ l₂ ⟶ l₁ ≫ f₂) :
    mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α) =
      conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α := by
  simp only [conjugateEquiv_apply, mateEquiv_apply']
  dsimp [Adjunction.comp]
  bicategory

/--
theorem `iterated_mateEquiv_conjugateEquiv_symm` / 定理 `iterated_mateEquiv_conjugateEquiv_symm`

English:
theorem iterated_mateEquiv_conjugateEquiv_symm
  given: (α : u₂ ≫ r₁ ⟶ r₂ ≫ u₁)
  proof: by
  rw [Equiv.eq_symm_apply]; rw [← iterated_mateEquiv_conjugateEquiv]
  simp only [Equiv.apply_symm_apply]

中文:
定理 iterated_mateEquiv_conjugateEquiv_symm
  条件: (α : u₂ ≫ r₁ ⟶ r₂ ≫ u₁)
  证明: by
  rw [Equiv.eq_symm_apply]; rw [← iterated_mateEquiv_conjugateEquiv]
  simp only [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.eq_symm_apply, apply_symm_apply, eq_symm_apply, iterated_mateEquiv_conjugateEquiv
-/
theorem iterated_mateEquiv_conjugateEquiv_symm (α : u₂ ≫ r₁ ⟶ r₂ ≫ u₁) :
    (mateEquiv adj₁ adj₂).symm ((mateEquiv adj₄ adj₃).symm α) =
      (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm α := by
  rw [Equiv.eq_symm_apply]; rw [← iterated_mateEquiv_conjugateEquiv]
  simp only [Equiv.apply_symm_apply]

end IteratedMateEquiv

section mateEquiv_conjugateEquiv_vcomp

variable {a b c d : B}
variable {g : a ⟶ c} {h : b ⟶ d}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c} {l₃ : c ⟶ d} {r₃ : d ⟶ c}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/--
Definition of `leftAdjointSquareConjugate.vcomp` / `leftAdjointSquareConjugate.vcomp` 的定义

English:
definition leftAdjointSquareConjugate.vcomp
  signature: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂)
  body: g ◁ β ≫ α

中文:
定义 leftAdjointSquareConjugate.vcomp
  签名: (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂)
  定义体: g ◁ β ≫ α
-/
def leftAdjointSquareConjugate.vcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂) :
    g ≫ l₃ ⟶ l₁ ≫ h :=
  g ◁ β ≫ α

/--
Definition of `rightAdjointSquareConjugate.vcomp` / `rightAdjointSquareConjugate.vcomp` 的定义

English:
definition rightAdjointSquareConjugate.vcomp
  signature: (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₂ ⟶ r₃)
  body: α ≫ h ◁ β

中文:
定义 rightAdjointSquareConjugate.vcomp
  签名: (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₂ ⟶ r₃)
  定义体: α ≫ h ◁ β
-/
def rightAdjointSquareConjugate.vcomp (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₂ ⟶ r₃) :
    r₁ ≫ g ⟶ h ≫ r₃ :=
  α ≫ h ◁ β

/--
theorem `mateEquiv_conjugateEquiv_vcomp` / 定理 `mateEquiv_conjugateEquiv_vcomp`

English:
theorem mateEquiv_conjugateEquiv_vcomp
  proof: by
  symm
  calc
    _ = 𝟙 _ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ α)
            (mateEquiv adj₂ adj₃ ((fun_ l₃).hom ≫ β ≫ (ρ_ l₂).inv)) otimes≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointSquareConjugate.vcomp,
        rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointSquareConjugate.vcomp]
      bicategory

中文:
定理 mateEquiv_conjugateEquiv_vcomp
  证明: by
  symm
  calc
    _ = 𝟙 _ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ α)
            (mateEquiv adj₂ adj₃ ((fun_ l₃).hom ≫ β ≫ (ρ_ l₂).inv)) otimes≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointSquareConjugate.vcomp,
        rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointSquareConjugate.vcomp]
      bicategory

Depends on / 依赖: bicategory, conjugateEquiv_apply, fun_, leftAdjointSquare, leftAdjointSquare.vcomp, leftAdjointSquareConjugate, leftAdjointSquareConjugate.vcomp, mateEquiv, mateEquiv_apply, mateEquiv_vcomp, otimes, rightAdjointSquare, rightAdjointSquare.vcomp, rightAdjointSquareConjugate, rightAdjointSquareConjugate.vcomp
-/
theorem mateEquiv_conjugateEquiv_vcomp
    (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : l₃ ⟶ l₂) :
    (mateEquiv adj₁ adj₃) (leftAdjointSquareConjugate.vcomp α β) =
      rightAdjointSquareConjugate.vcomp (mateEquiv adj₁ adj₂ α) (conjugateEquiv adj₂ adj₃ β) := by
  symm
  calc
    _ = 𝟙 _ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ α)
            (mateEquiv adj₂ adj₃ ((fun_ l₃).hom ≫ β ≫ (ρ_ l₂).inv)) otimes≫ 𝟙 _ := by
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

/--
Definition of `leftAdjointConjugateSquare.vcomp` / `leftAdjointConjugateSquare.vcomp` 的定义

English:
definition leftAdjointConjugateSquare.vcomp
  signature: (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h)
  body: β ≫ α ▷ h

中文:
定义 leftAdjointConjugateSquare.vcomp
  签名: (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h)
  定义体: β ≫ α ▷ h
-/
def leftAdjointConjugateSquare.vcomp (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h) :
    g ≫ l₃ ⟶ l₁ ≫ h :=
  β ≫ α ▷ h

/--
Definition of `rightAdjointConjugateSquare.vcomp` / `rightAdjointConjugateSquare.vcomp` 的定义

English:
definition rightAdjointConjugateSquare.vcomp
  signature: (α : r₁ ⟶ r₂) (β : r₂ ≫ g ⟶ h ≫ r₃)
  body: α ▷ g ≫ β

中文:
定义 rightAdjointConjugateSquare.vcomp
  签名: (α : r₁ ⟶ r₂) (β : r₂ ≫ g ⟶ h ≫ r₃)
  定义体: α ▷ g ≫ β
-/
def rightAdjointConjugateSquare.vcomp (α : r₁ ⟶ r₂) (β : r₂ ≫ g ⟶ h ≫ r₃) :
    r₁ ≫ g ⟶ h ≫ r₃ :=
  α ▷ g ≫ β

/--
theorem `conjugateEquiv_mateEquiv_vcomp` / 定理 `conjugateEquiv_mateEquiv_vcomp`

English:
theorem conjugateEquiv_mateEquiv_vcomp
  proof: by
  symm
  calc
    _ = 𝟙 _ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((fun_ l₂).hom ≫ α ≫ (ρ_ l₁).inv))
            (mateEquiv adj₂ adj₃ β) otimes≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointConjugateSquare.vcomp, rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointConjugateSquare.vcomp]
      bicategory

中文:
定理 conjugateEquiv_mateEquiv_vcomp
  证明: by
  symm
  calc
    _ = 𝟙 _ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((fun_ l₂).hom ≫ α ≫ (ρ_ l₁).inv))
            (mateEquiv adj₂ adj₃ β) otimes≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointConjugateSquare.vcomp, rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointConjugateSquare.vcomp]
      bicategory

Depends on / 依赖: bicategory, conjugateEquiv_apply, fun_, leftAdjointConjugateSquare, leftAdjointConjugateSquare.vcomp, leftAdjointSquare, leftAdjointSquare.vcomp, mateEquiv, mateEquiv_apply, mateEquiv_vcomp, otimes, rightAdjointConjugateSquare, rightAdjointConjugateSquare.vcomp, rightAdjointSquare, rightAdjointSquare.vcomp
-/
theorem conjugateEquiv_mateEquiv_vcomp
    (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h) :
    (mateEquiv adj₁ adj₃) (leftAdjointConjugateSquare.vcomp α β) =
      rightAdjointConjugateSquare.vcomp (conjugateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  symm
  calc
    _ = 𝟙 _ otimes≫
          rightAdjointSquare.vcomp
            (mateEquiv adj₁ adj₂ ((fun_ l₂).hom ≫ α ≫ (ρ_ l₁).inv))
            (mateEquiv adj₂ adj₃ β) otimes≫ 𝟙 _ := by
      dsimp only [conjugateEquiv_apply, rightAdjointConjugateSquare.vcomp, rightAdjointSquare.vcomp]
      bicategory
    _ = _ := by
      rw [← mateEquiv_vcomp]
      simp only [leftAdjointSquare.vcomp, mateEquiv_apply', leftAdjointConjugateSquare.vcomp]
      bicategory

end conjugateEquiv_mateEquiv_vcomp

end Bicategory

end CategoryTheory
