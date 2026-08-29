/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes

/-!
# Coherence tactic for monoidal categories

We provide a `monoidal_coherence` tactic,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike MonoidalCategory

namespace Mathlib.Tactic.Monoidal

section

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

local infixr:81 " ◁ " => MonoidalCategory.whiskerLeftIso
local infixl:81 " ▷ " => MonoidalCategory.whiskerRightIso

/--
Definition of `normalizeIsoComp` / `normalizeIsoComp` 的定义

English:
abbreviation normalizeIsoComp
  signature: {p f g pf pfg : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg)
  body: (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

中文:
缩写 normalizeIsoComp
  签名: {p f g pf pfg : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg)
  定义体: (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

Depends on / 依赖: whiskerRightIso
-/
abbrev normalizeIsoComp {p f g pf pfg : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

/--
theorem `naturality_associator` / 定理 `naturality_associator`

English:
theorem naturality_associator
  statement: {p f g h pf pfg pfgh : C}
  proof: Iso.ext (by simp)

中文:
定理 naturality_associator
  结论: {p f g h pf pfg pfgh : C}
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_associator {p f g h pf pfg pfgh : C}
    (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : pfg otimes h ≅ pfgh) :
    p ◁ (α_ f g h) ≪≫ normalizeIsoComp η_f (normalizeIsoComp η_g η_h) =
    normalizeIsoComp (normalizeIsoComp η_f η_g) η_h :=
  Iso.ext (by simp)

/--
theorem `naturality_leftUnitor` / 定理 `naturality_leftUnitor`

English:
theorem naturality_leftUnitor
  given: {p f pf : C} (η_f : p otimes f ≅ pf)
  proof: Iso.ext (by simp)

中文:
定理 naturality_leftUnitor
  条件: {p f pf : C} (η_f : p otimes f ≅ pf)
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_leftUnitor {p f pf : C} (η_f : p otimes f ≅ pf) :
    p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p) η_f :=
  Iso.ext (by simp)

/--
theorem `naturality_rightUnitor` / 定理 `naturality_rightUnitor`

English:
theorem naturality_rightUnitor
  given: {p f pf : C} (η_f : p otimes f ≅ pf)
  proof: Iso.ext (by simp)

中文:
定理 naturality_rightUnitor
  条件: {p f pf : C} (η_f : p otimes f ≅ pf)
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_rightUnitor {p f pf : C} (η_f : p otimes f ≅ pf) :
    p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (ρ_ pf) :=
  Iso.ext (by simp)

/--
theorem `naturality_id` / 定理 `naturality_id`

English:
theorem naturality_id
  given: {p f pf : C} (η_f : p otimes f ≅ pf)
  proof: by
  simp

中文:
定理 naturality_id
  条件: {p f pf : C} (η_f : p otimes f ≅ pf)
  证明: by
  simp
-/
theorem naturality_id {p f pf : C} (η_f : p otimes f ≅ pf) :
    p ◁ Iso.refl f ≪≫ η_f = η_f := by
  simp

/--
theorem `naturality_comp` / 定理 `naturality_comp`

English:
theorem naturality_comp
  statement: {p f g h pf : C} {η : f ≅ g} {θ : g ≅ h}
  proof: by
  simp_all

中文:
定理 naturality_comp
  结论: {p f g h pf : C} {η : f ≅ g} {θ : g ≅ h}
  证明: by
  simp_all
-/
theorem naturality_comp {p f g h pf : C} {η : f ≅ g} {θ : g ≅ h}
    (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h : p otimes h ≅ pf)
    (ih_η : p ◁ η ≪≫ η_g = η_f) (ih_θ : p ◁ θ ≪≫ η_h = η_g) :
    p ◁ (η ≪≫ θ) ≪≫ η_h = η_f := by
  simp_all

/--
theorem `naturality_whiskerLeft` / 定理 `naturality_whiskerLeft`

English:
theorem naturality_whiskerLeft
  statement: {p f g h pf pfg : C} {η : g ≅ h}
  proof: by
  rw [← ih_η]
  apply Iso.ext
  simp [← whisker_exchange_assoc]

中文:
定理 naturality_whiskerLeft
  结论: {p f g h pf pfg : C} {η : g ≅ h}
  证明: by
  rw [← ih_η]
  apply Iso.ext
  simp [← whisker_exchange_assoc]

Depends on / 依赖: Iso.ext, whisker_exchange_assoc
-/
theorem naturality_whiskerLeft {p f g h pf pfg : C} {η : g ≅ h}
    (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pfg) (η_fh : (pf otimes h) ≅ pfg)
    (ih_η : pf ◁ η ≪≫ η_fh = η_fg) :
    p ◁ (f ◁ η) ≪≫ normalizeIsoComp η_f η_fh = normalizeIsoComp η_f η_fg := by
  rw [← ih_η]
  apply Iso.ext
  simp [← whisker_exchange_assoc]

/--
theorem `naturality_whiskerRight` / 定理 `naturality_whiskerRight`

English:
theorem naturality_whiskerRight
  statement: {p f g h pf pfh : C} {η : f ≅ g}
  proof: by
  rw [← ih_η]
  apply Iso.ext
  simp

中文:
定理 naturality_whiskerRight
  结论: {p f g h pf pfh : C} {η : f ≅ g}
  证明: by
  rw [← ih_η]
  apply Iso.ext
  simp

Depends on / 依赖: Iso.ext
-/
theorem naturality_whiskerRight {p f g h pf pfh : C} {η : f ≅ g}
    (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_fh : (pf otimes h) ≅ pfh)
    (ih_η : p ◁ η ≪≫ η_g = η_f) :
    p ◁ (η ▷ h) ≪≫ normalizeIsoComp η_g η_fh = normalizeIsoComp η_f η_fh := by
  rw [← ih_η]
  apply Iso.ext
  simp

/--
theorem `naturality_tensorHom` / 定理 `naturality_tensorHom`

English:
theorem naturality_tensorHom
  statement: {p f₁ g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂}
  proof: by
  rw [tensorIso_def]
  apply naturality_comp
  · apply naturality_whiskerRight _ _ _ ih_η
  · apply naturality_whiskerLeft _ _ _ ih_θ

中文:
定理 naturality_tensorHom
  结论: {p f₁ g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂}
  证明: by
  rw [tensorIso_def]
  apply naturality_comp
  · apply naturality_whiskerRight _ _ _ ih_η
  · apply naturality_whiskerLeft _ _ _ ih_θ

Depends on / 依赖: naturality_comp, naturality_whiskerLeft, naturality_whiskerRight, tensorIso_def
-/
theorem naturality_tensorHom {p f₁ g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂}
    (η_f₁ : p otimes f₁ ≅ pf₁) (η_g₁ : p otimes g₁ ≅ pf₁) (η_f₂ : pf₁ otimes f₂ ≅ pf₁f₂) (η_g₂ : pf₁ otimes g₂ ≅ pf₁f₂)
    (ih_η : p ◁ η ≪≫ η_g₁ = η_f₁)
    (ih_θ : pf₁ ◁ θ ≪≫ η_g₂ = η_f₂) :
    p ◁ (η otimesᵢ θ) ≪≫ normalizeIsoComp η_g₁ η_g₂ = normalizeIsoComp η_f₁ η_f₂ := by
  rw [tensorIso_def]
  apply naturality_comp
  · apply naturality_whiskerRight _ _ _ ih_η
  · apply naturality_whiskerLeft _ _ _ ih_θ

/--
theorem `naturality_inv` / 定理 `naturality_inv`

English:
theorem naturality_inv
  statement: {p f g pf : C} {η : f ≅ g}
  proof: by
  rw [← ih]
  apply Iso.ext
  simp

中文:
定理 naturality_inv
  结论: {p f g pf : C} {η : f ≅ g}
  证明: by
  rw [← ih]
  apply Iso.ext
  simp

Depends on / 依赖: Iso.ext
-/
theorem naturality_inv {p f g pf : C} {η : f ≅ g}
    (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η_f) :
    p ◁ η.symm ≪≫ η_f = η_g := by
  rw [← ih]
  apply Iso.ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadNormalizeNaturality MonoidalM
  body: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have pfgh : Q($ctx.C) := pfgh.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($pf otimes $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg otimes $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have η_h : Q($p otimes $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_fg : Q($pf otimes $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf otimes $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfh : Q($ctx.C) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have η_fh : Q($pf otimes $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp p pf₁ pf₁f₂ f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f₁ : Q($ctx.C) := f₁.e
    have g₁ : Q($ctx.C) := g₁.e
    have f₂ : Q($ctx.C) := f₂.e
    have g₂ : Q($ctx.C) := g₂.e
    have pf₁ : Q($ctx.C) := pf₁.e.e
    have pf₁f₂ : Q($ctx.C) := pf₁f₂.e.e
    have η : Q($f₁ ≅ $g₁) := η.e
    have θ : Q($f₂ ≅ $g₂) := θ.e
    have η_f₁ : Q($p otimes $f₁ ≅ $pf₁) := η_f₁.e
    have η_g₁ : Q($p otimes $g₁ ≅ $pf₁) := η_g₁.e
    have η_f₂ : Q($pf₁ otimes $f₂ ≅ $pf₁f₂) := η_f₂.e
    have η_g₂ : Q($pf₁ otimes $g₂ ≅ $pf₁f₂) := η_g₂.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g₁ = $η_f₁) := ih_η
    have ih_θ : Q($pf₁ ◁ $θ ≪≫ $η_g₂ = $η_f₂) := ih_θ
    return q(naturality_tensorHom $η_f₁ $η_g₁ $η_f₂ $η_g₂ $ih_η $ih_θ)
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)

中文:
实例 :
  签名: MonadNormalize自然数urality MonoidalM
  定义体: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have pfgh : Q($ctx.C) := pfgh.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($pf otimes $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg otimes $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have η_h : Q($p otimes $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_fg : Q($pf otimes $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf otimes $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfh : Q($ctx.C) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have η_fh : Q($pf otimes $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp p pf₁ pf₁f₂ f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f₁ : Q($ctx.C) := f₁.e
    have g₁ : Q($ctx.C) := g₁.e
    have f₂ : Q($ctx.C) := f₂.e
    have g₂ : Q($ctx.C) := g₂.e
    have pf₁ : Q($ctx.C) := pf₁.e.e
    have pf₁f₂ : Q($ctx.C) := pf₁f₂.e.e
    have η : Q($f₁ ≅ $g₁) := η.e
    have θ : Q($f₂ ≅ $g₂) := θ.e
    have η_f₁ : Q($p otimes $f₁ ≅ $pf₁) := η_f₁.e
    have η_g₁ : Q($p otimes $g₁ ≅ $pf₁) := η_g₁.e
    have η_f₂ : Q($pf₁ otimes $f₂ ≅ $pf₁f₂) := η_f₂.e
    have η_g₂ : Q($pf₁ otimes $g₂ ≅ $pf₁f₂) := η_g₂.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g₁ = $η_f₁) := ih_η
    have ih_θ : Q($pf₁ ◁ $θ ≪≫ $η_g₂ = $η_f₂) := ih_θ
    return q(naturality_tensorHom $η_f₁ $η_g₁ $η_f₂ $η_g₂ $ih_η $ih_θ)
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)
-/
instance : MonadNormalizeNaturality MonoidalM where
  mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have pfgh : Q($ctx.C) := pfgh.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($pf otimes $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg otimes $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have η_h : Q($p otimes $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_fg : Q($pf otimes $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf otimes $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfh : Q($ctx.C) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have η_fh : Q($pf otimes $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp p pf₁ pf₁f₂ f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f₁ : Q($ctx.C) := f₁.e
    have g₁ : Q($ctx.C) := g₁.e
    have f₂ : Q($ctx.C) := f₂.e
    have g₂ : Q($ctx.C) := g₂.e
    have pf₁ : Q($ctx.C) := pf₁.e.e
    have pf₁f₂ : Q($ctx.C) := pf₁f₂.e.e
    have η : Q($f₁ ≅ $g₁) := η.e
    have θ : Q($f₂ ≅ $g₂) := θ.e
    have η_f₁ : Q($p otimes $f₁ ≅ $pf₁) := η_f₁.e
    have η_g₁ : Q($p otimes $g₁ ≅ $pf₁) := η_g₁.e
    have η_f₂ : Q($pf₁ otimes $f₂ ≅ $pf₁f₂) := η_f₂.e
    have η_g₂ : Q($pf₁ otimes $g₂ ≅ $pf₁f₂) := η_g₂.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g₁ = $η_f₁) := ih_η
    have ih_θ : Q($pf₁ ◁ $θ ≪≫ $η_g₂ = $η_f₂) := ih_θ
    return q(naturality_tensorHom $η_f₁ $η_g₁ $η_f₂ $η_g₂ $ih_η $ih_θ)
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p otimes $f ≅ $pf) := η_f.e
    have η_g : Q($p otimes $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)

/--
theorem `of_normalize_eq` / 定理 `of_normalize_eq`

English:
theorem of_normalize_eq
  statement: {f g f' : C} {η θ : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otimes g ≅ f')
  proof: by
  apply Iso.ext
  calc
    η.hom = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]

中文:
定理 of_normalize_eq
  结论: {f g f' : C} {η θ : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otimes g ≅ f')
  证明: by
  apply Iso.ext
  calc
    η.hom = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]

Depends on / 依赖: Iso.ext, Iso.hom, _f.hom, _g.inv, fun_, reassoc_of
-/
theorem of_normalize_eq {f g f' : C} {η θ : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otimes g ≅ f')
    (h_η : 𝟙_ C ◁ η ≪≫ η_g = η_f)
    (h_θ : 𝟙_ C ◁ θ ≪≫ η_g = η_f) : η = θ := by
  apply Iso.ext
  calc
    η.hom = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]

/--
theorem `mk_eq_of_naturality` / 定理 `mk_eq_of_naturality`

English:
theorem mk_eq_of_naturality
  statement: {f g f' : C} {η θ : f ⟶ g} {η' θ' : f ≅ g}
  proof: calc
    η = η'.hom := η_hom.symm
    _ = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη)]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ)]
    _ = θ := Θ_hom

中文:
定理 mk_eq_of_naturality
  结论: {f g f' : C} {η θ : f ⟶ g} {η' θ' : f ≅ g}
  证明: calc
    η = η'.hom := η_hom.symm
    _ = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη)]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ)]
    _ = θ := Θ_hom

Depends on / 依赖: Iso.hom, _f.hom, _g.inv, _hom.symm, fun_, reassoc_of
-/
theorem mk_eq_of_naturality {f g f' : C} {η θ : f ⟶ g} {η' θ' : f ≅ g}
    (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otimes g ≅ f')
    (η_hom : η'.hom = η) (Θ_hom : θ'.hom = θ)
    (Hη : whiskerLeftIso (𝟙_ C) η' ≪≫ η_g = η_f)
    (Hθ : whiskerLeftIso (𝟙_ C) θ' ≪≫ η_g = η_f) : η = θ :=
  calc
    η = η'.hom := η_hom.symm
    _ = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη)]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ)]
    _ = θ := Θ_hom

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEqOfNaturality MonoidalM
  body: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have f' : Q($ctx.C) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙_ _ otimes $f ≅ $f') := η_f.e
    have η_g : Q(𝟙_ _ otimes $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙_ _) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙_ _) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)

中文:
实例 :
  签名: MkEqOf自然数urality MonoidalM
  定义体: do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have f' : Q($ctx.C) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙_ _ otimes $f ≅ $f') := η_f.e
    have η_g : Q(𝟙_ _ otimes $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙_ _) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙_ _) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)
-/
instance : MkEqOfNaturality MonoidalM where
  mkEqOfNaturality η θ ηIso θIso η_f η_g Hη Hθ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have f' : Q($ctx.C) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙_ _ otimes $f ≅ $f') := η_f.e
    have η_g : Q(𝟙_ _ otimes $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙_ _) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙_ _) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)

open Elab.Tactic

/--
Definition of `pureCoherence` / `pureCoherence` 的定义

English:
definition pureCoherence
  signature: (mvarId : MVarId)
  body: BicategoryLike.pureCoherence Monoidal.Context `monoidal mvarId

@[inherit_doc pureCoherence]

中文:
定义 pureCoherence
  签名: (mvarId : MVarId)
  定义体: BicategoryLike.pureCoherence Monoidal.Context `monoidal mvarId

@[inherit_doc pureCoherence]

Depends on / 依赖: BicategoryLike, BicategoryLike.pureCoherence, Context, Monoidal, Monoidal.Context, monoidal, mvarId, pureCoherence
-/
def pureCoherence (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.pureCoherence Monoidal.Context `monoidal mvarId

@[inherit_doc pureCoherence]
elab "monoidal_coherence" : tactic => withMainContext do
replaceMainGoal ← Monoidal.pureCoherence ← getMainGoal

end Mathlib.Tactic.Monoidal
