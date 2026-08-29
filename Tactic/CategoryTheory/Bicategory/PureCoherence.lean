/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes
public import Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence

/-!
# Coherence tactic for bicategories

We provide a `bicategory_coherence` tactic,
which proves that any two morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike Bicategory

namespace Mathlib.Tactic.Bicategory

section

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

local infixr:81 " ◁ " => Bicategory.whiskerLeftIso
local infixl:81 " ▷ " => Bicategory.whiskerRightIso

/--
Definition of `normalizeIsoComp` / `normalizeIsoComp` 的定义

English:
abbreviation normalizeIsoComp
  signature: {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
  body: (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

中文:
缩写 normalizeIsoComp
  签名: {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
  定义体: (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

Depends on / 依赖: whiskerRightIso
-/
abbrev normalizeIsoComp {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
    (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

/--
theorem `naturality_associator` / 定理 `naturality_associator`

English:
theorem naturality_associator
  proof: Iso.ext (by simp)

中文:
定理 naturality_associator
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_associator
    {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh : a ⟶ e}
    (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg) (η_h : pfg ≫ h ≅ pfgh) :
    p ◁ (α_ f g h) ≪≫ (normalizeIsoComp η_f (normalizeIsoComp η_g η_h)) =
    (normalizeIsoComp (normalizeIsoComp η_f η_g) η_h) :=
  Iso.ext (by simp)

/--
theorem `naturality_leftUnitor` / 定理 `naturality_leftUnitor`

English:
theorem naturality_leftUnitor
  given: {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf)
  proof: Iso.ext (by simp)

中文:
定理 naturality_leftUnitor
  条件: {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf)
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_leftUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p) η_f :=
  Iso.ext (by simp)

/--
theorem `naturality_rightUnitor` / 定理 `naturality_rightUnitor`

English:
theorem naturality_rightUnitor
  given: {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf)
  proof: Iso.ext (by simp)

中文:
定理 naturality_rightUnitor
  条件: {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf)
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_rightUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (ρ_ pf) :=
  Iso.ext (by simp)

/--
theorem `naturality_id` / 定理 `naturality_id`

English:
theorem naturality_id
  given: {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf)
  proof: Iso.ext (by simp)

中文:
定理 naturality_id
  条件: {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf)
  证明: Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_id {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ Iso.refl f ≪≫ η_f = η_f :=
  Iso.ext (by simp)

/--
theorem `naturality_comp` / 定理 `naturality_comp`

English:
theorem naturality_comp
  statement: {p : a ⟶ b} {f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h}
  proof: by
  rw [← ih_η]; rw [← ih_θ]
  apply Iso.ext (by simp)

中文:
定理 naturality_comp
  结论: {p : a ⟶ b} {f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h}
  证明: by
  rw [← ih_η]; rw [← ih_θ]
  apply Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_comp {p : a ⟶ b} {f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h}
    (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (η_h : p ≫ h ≅ pf)
    (ih_η : p ◁ η ≪≫ η_g = η_f) (ih_θ : p ◁ θ ≪≫ η_h = η_g) :
    p ◁ (η ≪≫ θ) ≪≫ η_h = η_f := by
  rw [← ih_η]; rw [← ih_θ]
  apply Iso.ext (by simp)

/--
theorem `naturality_whiskerLeft` / 定理 `naturality_whiskerLeft`

English:
theorem naturality_whiskerLeft
  statement: {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
  proof: by
  rw [← ih_η]
  apply Iso.ext (by simp [← whisker_exchange_assoc])

中文:
定理 naturality_whiskerLeft
  结论: {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
  证明: by
  rw [← ih_η]
  apply Iso.ext (by simp [← whisker_exchange_assoc])

Depends on / 依赖: Iso.ext, whisker_exchange_assoc
-/
theorem naturality_whiskerLeft {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
    {η : g ≅ h} (η_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg) (η_fh : pf ≫ h ≅ pfg)
    (ih_η : pf ◁ η ≪≫ η_fh = η_fg) :
    p ◁ (f ◁ η) ≪≫ normalizeIsoComp η_f η_fh = normalizeIsoComp η_f η_fg := by
  rw [← ih_η]
  apply Iso.ext (by simp [← whisker_exchange_assoc])

/--
theorem `naturality_whiskerRight` / 定理 `naturality_whiskerRight`

English:
theorem naturality_whiskerRight
  statement: {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d}
  proof: by
  rw [← ih_η]
  apply Iso.ext (by simp)

中文:
定理 naturality_whiskerRight
  结论: {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d}
  证明: by
  rw [← ih_η]
  apply Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_whiskerRight {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d}
    {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (η_fh : pf ≫ h ≅ pfh)
    (ih_η : p ◁ η ≪≫ η_g = η_f) :
    p ◁ (η ▷ h) ≪≫ normalizeIsoComp η_g η_fh = normalizeIsoComp η_f η_fh := by
  rw [← ih_η]
  apply Iso.ext (by simp)

/--
theorem `naturality_inv` / 定理 `naturality_inv`

English:
theorem naturality_inv
  statement: {p : a ⟶ b} {f g : b ⟶ c} {pf : a ⟶ c}
  proof: by
  rw [← ih]
  apply Iso.ext (by simp)

中文:
定理 naturality_inv
  结论: {p : a ⟶ b} {f g : b ⟶ c} {pf : a ⟶ c}
  证明: by
  rw [← ih]
  apply Iso.ext (by simp)

Depends on / 依赖: Iso.ext
-/
theorem naturality_inv {p : a ⟶ b} {f g : b ⟶ c} {pf : a ⟶ c}
    {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : p ◁ η ≪≫ η_g = η_f) :
    p ◁ η.symm ≪≫ η_f = η_g := by
  rw [← ih]
  apply Iso.ext (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadNormalizeNaturality BicategoryM
  body: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have e : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($d ⟶ $e) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have pfgh : Q($a ⟶ $e) := pfgh.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($pf ≫ $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg ≫ $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_h : Q($p ≫ $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_fg : Q($pf ≫ $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf ≫ $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfh : Q($a ⟶ $d) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_fh : Q($pf ≫ $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "horizontal composition is not implemented"
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)

中文:
实例 :
  签名: MonadNormalize自然数urality BicategoryM
  定义体: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have e : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($d ⟶ $e) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have pfgh : Q($a ⟶ $e) := pfgh.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($pf ≫ $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg ≫ $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_h : Q($p ≫ $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_fg : Q($pf ≫ $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf ≫ $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfh : Q($a ⟶ $d) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_fh : Q($pf ≫ $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "horizontal composition is not implemented"
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)
-/
instance : MonadNormalizeNaturality BicategoryM where
  mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have e : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($d ⟶ $e) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have pfgh : Q($a ⟶ $e) := pfgh.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($pf ≫ $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg ≫ $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_h : Q($p ≫ $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_fg : Q($pf ≫ $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf ≫ $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfh : Q($a ⟶ $d) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_fh : Q($pf ≫ $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "horizontal composition is not implemented"
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)

/--
theorem `of_normalize_eq` / 定理 `of_normalize_eq`

English:
theorem of_normalize_eq
  statement: {f g f' : a ⟶ b} {η θ : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
  proof: by
  apply Iso.ext
  calc
    η.hom = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]

中文:
定理 of_normalize_eq
  结论: {f g f' : a ⟶ b} {η θ : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
  证明: by
  apply Iso.ext
  calc
    η.hom = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]

Depends on / 依赖: Iso.ext, Iso.hom, _f.hom, _g.inv, fun_, reassoc_of
-/
theorem of_normalize_eq {f g f' : a ⟶ b} {η θ : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
    (h_η : 𝟙 a ◁ η ≪≫ η_g = η_f)
    (h_θ : 𝟙 a ◁ θ ≪≫ η_g = η_f) : η = θ := by
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
  statement: {f g f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g}
  proof: calc
    η = η'.hom := Hη.symm
    _ = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη')]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ')]
    _ = θ := Hθ

中文:
定理 mk_eq_of_naturality
  结论: {f g f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g}
  证明: calc
    η = η'.hom := Hη.symm
    _ = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη')]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ')]
    _ = θ := Hθ

Depends on / 依赖: Iso.hom, _f.hom, _g.inv, fun_, reassoc_of
-/
theorem mk_eq_of_naturality {f g f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g}
    (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
    (Hη : η'.hom = η) (Hθ : θ'.hom = θ)
    (Hη' : whiskerLeftIso (𝟙 a) η' ≪≫ η_g = η_f)
    (Hθ' : whiskerLeftIso (𝟙 a) θ' ≪≫ η_g = η_f) : η = θ :=
  calc
    η = η'.hom := Hη.symm
    _ = (fun_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (fun_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη')]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ')]
    _ = θ := Hθ

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkEqOfNaturality BicategoryM
  body: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have f' : Q($a ⟶ $b) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙 $a ≫ $f ≅ $f') := η_f.e
    have η_g : Q(𝟙 $a ≫ $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙 $a) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙 $a) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)

中文:
实例 :
  签名: MkEqOf自然数urality BicategoryM
  定义体: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have f' : Q($a ⟶ $b) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙 $a ≫ $f ≅ $f') := η_f.e
    have η_g : Q(𝟙 $a ≫ $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙 $a) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙 $a) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)
-/
instance : MkEqOfNaturality BicategoryM where
  mkEqOfNaturality η θ ηIso θIso η_f η_g Hη Hθ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have f' : Q($a ⟶ $b) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙 $a ≫ $f ≅ $f') := η_f.e
    have η_g : Q(𝟙 $a ≫ $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙 $a) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙 $a) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)

open Elab.Tactic

/--
Definition of `pureCoherence` / `pureCoherence` 的定义

English:
definition pureCoherence
  signature: (mvarId : MVarId)
  body: BicategoryLike.pureCoherence Bicategory.Context `bicategory mvarId

@[inherit_doc pureCoherence]

中文:
定义 pureCoherence
  签名: (mvarId : MVarId)
  定义体: BicategoryLike.pureCoherence Bicategory.Context `bicategory mvarId

@[inherit_doc pureCoherence]

Depends on / 依赖: Bicategory, Bicategory.Context, BicategoryLike, BicategoryLike.pureCoherence, Context, bicategory, mvarId, pureCoherence
-/
def pureCoherence (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.pureCoherence Bicategory.Context `bicategory mvarId

@[inherit_doc pureCoherence]
elab "bicategory_coherence" : tactic => withMainContext do
replaceMainGoal ← Bicategory.pureCoherence ← getMainGoal

end Mathlib.Tactic.Bicategory
