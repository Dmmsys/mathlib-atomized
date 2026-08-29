/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Hom.Order
public import Mathlib.Order.BourbakiWitt

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `OrderHom.lfp`: The least fixed point of a bundled monotone function.
* `OrderHom.gfp`: The greatest fixed point of a bundled monotone function.
* `OrderHom.prevFixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `OrderHom.nextFixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixedPoints.completeLattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function (fixedPoints IsFixedPt)

namespace OrderHom

section Basic

variable [CompleteLattice α] (f : α ->o α)

/--
Definition of `lfp` / `lfp` 的定义

English:
definition lfp
  signature: : (α ->o α) ->o α where
  body: sInf { a | f a <= a }
  monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

中文:
定义 lfp
  签名: : (α ->o α) ->o α where
  定义体: sInf { a | f a <= a }
  monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha
-/
def lfp : (α ->o α) ->o α where
  toFun f := sInf { a | f a <= a }
  monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

/--
Definition of `gfp` / `gfp` 的定义

English:
definition gfp
  signature: : (α ->o α) ->o α where
  body: sSup { a | a <= f a }
  monotone' _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)

中文:
定义 gfp
  签名: : (α ->o α) ->o α where
  定义体: sSup { a | a <= f a }
  monotone' _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)
-/
def gfp : (α ->o α) ->o α where
  toFun f := sSup { a | a <= f a }
  monotone' _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)

/--
theorem `lfp_le` / 定理 `lfp_le`

English:
theorem lfp_le
  given: {a : α} (h : f a <= a)
  statement: f.lfp <= a
  proof: sInf_le h

中文:
定理 lfp_le
  条件: {a : α} (h : f a <= a)
  结论: f.lfp <= a
  证明: sInf_le h

Depends on / 依赖: sInf_le
-/
theorem lfp_le {a : α} (h : f a <= a) : f.lfp <= a :=
  sInf_le h

/--
theorem `lfp_le_fixed` / 定理 `lfp_le_fixed`

English:
theorem lfp_le_fixed
  given: {a : α} (h : f a = a)
  statement: f.lfp <= a
  proof: f.lfp_le h.le

中文:
定理 lfp_le_fixed
  条件: {a : α} (h : f a = a)
  结论: f.lfp <= a
  证明: f.lfp_le h.le

Depends on / 依赖: f.lfp_le, h.le, lfp_le
-/
theorem lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a :=
  f.lfp_le h.le

/--
theorem `le_lfp` / 定理 `le_lfp`

English:
theorem le_lfp
  given: {a : α} (h : forall b, f b <= b -> a <= b)
  statement: a <= f.lfp
  proof: le_sInf h

中文:
定理 le_lfp
  条件: {a : α} (h : 对任意 b, f b <= b -> a <= b)
  结论: a <= f.lfp
  证明: le_sInf h

Depends on / 依赖: le_sInf
-/
theorem le_lfp {a : α} (h : forall b, f b <= b -> a <= b) : a <= f.lfp :=
  le_sInf h

/--
theorem `map_le_lfp` / 定理 `map_le_lfp`

English:
theorem map_le_lfp
  given: {a : α} (ha : a <= f.lfp)
  statement: f a <= f.lfp
  proof: f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb

@[simp]

中文:
定理 map_le_lfp
  条件: {a : α} (ha : a <= f.lfp)
  结论: f a <= f.lfp
  证明: f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb

@[simp]

Depends on / 依赖: f.le_lfp, f.mono, le_lfp, le_sInf_iff
-/
theorem map_le_lfp {a : α} (ha : a <= f.lfp) : f a <= f.lfp :=
  f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb

@[simp]
/--
theorem `map_lfp` / 定理 `map_lfp`

English:
theorem map_lfp
  statement: f f.lfp = f.lfp
  proof: have h : f f.lfp <= f.lfp := f.map_le_lfp le_rfl
h.antisymm f.lfp_le f.mono h

中文:
定理 map_lfp
  结论: f f.lfp = f.lfp
  证明: have h : f f.lfp <= f.lfp := f.map_le_lfp le_rfl
h.antisymm f.lfp_le f.mono h

Depends on / 依赖: antisymm, f.lfp, f.lfp_le, f.map_le_lfp, f.mono, h.antisymm, le_rfl, lfp_le, map_le_lfp
-/
theorem map_lfp : f f.lfp = f.lfp :=
  have h : f f.lfp <= f.lfp := f.map_le_lfp le_rfl
h.antisymm f.lfp_le f.mono h

/--
theorem `isFixedPt_lfp` / 定理 `isFixedPt_lfp`

English:
theorem isFixedPt_lfp
  statement: IsFixedPt f f.lfp
  proof: f.map_lfp

中文:
定理 isFixedPt_lfp
  结论: IsFixedPt f f.lfp
  证明: f.map_lfp

Depends on / 依赖: f.map_lfp, map_lfp
-/
theorem isFixedPt_lfp : IsFixedPt f f.lfp :=
  f.map_lfp

/--
theorem `lfp_le_map` / 定理 `lfp_le_map`

English:
theorem lfp_le_map
  given: {a : α} (ha : f.lfp <= a)
  statement: f.lfp <= f a
  proof: calc
    f.lfp = f f.lfp := f.map_lfp.symm
    _ <= f a := f.mono ha

中文:
定理 lfp_le_map
  条件: {a : α} (ha : f.lfp <= a)
  结论: f.lfp <= f a
  证明: calc
    f.lfp = f f.lfp := f.map_lfp.symm
    _ <= f a := f.mono ha

Depends on / 依赖: f.lfp, f.map_lfp.symm, f.mono, map_lfp
-/
theorem lfp_le_map {a : α} (ha : f.lfp <= a) : f.lfp <= f a :=
  calc
    f.lfp = f f.lfp := f.map_lfp.symm
    _ <= f a := f.mono ha

/--
theorem `isLeast_lfp_le` / 定理 `isLeast_lfp_le`

English:
theorem isLeast_lfp_le
  statement: IsLeast { a | f a <= a } f.lfp
  proof: ⟨f.map_lfp.le, fun _ => f.lfp_le⟩

中文:
定理 isLeast_lfp_le
  结论: IsLeast { a | f a <= a } f.lfp
  证明: ⟨f.map_lfp.le, fun _ => f.lfp_le⟩

Depends on / 依赖: f.lfp_le, f.map_lfp.le, lfp_le, map_lfp
-/
theorem isLeast_lfp_le : IsLeast { a | f a <= a } f.lfp :=
  ⟨f.map_lfp.le, fun _ => f.lfp_le⟩

/--
theorem `isLeast_lfp` / 定理 `isLeast_lfp`

English:
theorem isLeast_lfp
  statement: IsLeast (fixedPoints f) f.lfp
  proof: ⟨f.isFixedPt_lfp, fun _ => f.lfp_le_fixed⟩

中文:
定理 isLeast_lfp
  结论: IsLeast (fixedPoints f) f.lfp
  证明: ⟨f.isFixedPt_lfp, fun _ => f.lfp_le_fixed⟩

Depends on / 依赖: f.isFixedPt_lfp, f.lfp_le_fixed, isFixedPt_lfp, lfp_le_fixed
-/
theorem isLeast_lfp : IsLeast (fixedPoints f) f.lfp :=
  ⟨f.isFixedPt_lfp, fun _ => f.lfp_le_fixed⟩

/--
theorem `lfp_induction` / 定理 `lfp_induction`

English:
theorem lfp_induction
  statement: {p : α -> Prop} (step : forall a, p a -> a <= f.lfp -> p (f a))
  proof: by
  set s := { a | a <= f.lfp ∧ p a }
  specialize hSup s fun a => And.right
  suffices sSup s = f.lfp from this ▸ hSup
  have h : sSup s <= f.lfp := sSup_le fun b => And.left
  have hmem : f (sSup s) in s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_sSup hmem)

中文:
定理 lfp_induction
  结论: {p : α -> 命题} (step : 对任意 a, p a -> a <= f.lfp -> p (f a))
  证明: by
  set s := { a | a <= f.lfp ∧ p a }
  specialize hSup s fun a => And.right
  suffices sSup s = f.lfp from this ▸ hSup
  have h : sSup s <= f.lfp := sSup_le fun b => And.left
  have hmem : f (sSup s) in s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_sSup hmem)

Depends on / 依赖: And.left, And.right, antisymm, f.lfp, f.lfp_le, f.map_le_lfp, h.antisymm, le_sSup, lfp_le, map_le_lfp, sSup_le, specialize
-/
theorem lfp_induction {p : α -> Prop} (step : forall a, p a -> a <= f.lfp -> p (f a))
    (hSup : forall s, (forall a in s, p a) -> p (sSup s)) : p f.lfp := by
  set s := { a | a <= f.lfp ∧ p a }
  specialize hSup s fun a => And.right
  suffices sSup s = f.lfp from this ▸ hSup
  have h : sSup s <= f.lfp := sSup_le fun b => And.left
  have hmem : f (sSup s) in s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_sSup hmem)

/--
theorem `le_gfp` / 定理 `le_gfp`

English:
theorem le_gfp
  given: {a : α} (h : a <= f a)
  statement: a <= f.gfp
  proof: le_sSup h

中文:
定理 le_gfp
  条件: {a : α} (h : a <= f a)
  结论: a <= f.gfp
  证明: le_sSup h

Depends on / 依赖: le_sSup
-/
theorem le_gfp {a : α} (h : a <= f a) : a <= f.gfp :=
  le_sSup h

/--
theorem `gfp_le` / 定理 `gfp_le`

English:
theorem gfp_le
  given: {a : α} (h : forall b, b <= f b -> b <= a)
  statement: f.gfp <= a
  proof: sSup_le h

中文:
定理 gfp_le
  条件: {a : α} (h : 对任意 b, b <= f b -> b <= a)
  结论: f.gfp <= a
  证明: sSup_le h

Depends on / 依赖: sSup_le
-/
theorem gfp_le {a : α} (h : forall b, b <= f b -> b <= a) : f.gfp <= a :=
  sSup_le h

/--
theorem `isFixedPt_gfp` / 定理 `isFixedPt_gfp`

English:
theorem isFixedPt_gfp
  statement: IsFixedPt f f.gfp
  proof: f.dual.isFixedPt_lfp

@[simp]

中文:
定理 isFixedPt_gfp
  结论: IsFixedPt f f.gfp
  证明: f.dual.isFixedPt_lfp

@[simp]

Depends on / 依赖: f.dual.isFixedPt_lfp, isFixedPt_lfp
-/
theorem isFixedPt_gfp : IsFixedPt f f.gfp :=
  f.dual.isFixedPt_lfp

@[simp]
/--
theorem `map_gfp` / 定理 `map_gfp`

English:
theorem map_gfp
  statement: f f.gfp = f.gfp
  proof: f.dual.map_lfp

中文:
定理 map_gfp
  结论: f f.gfp = f.gfp
  证明: f.dual.map_lfp

Depends on / 依赖: f.dual.map_lfp, map_lfp
-/
theorem map_gfp : f f.gfp = f.gfp :=
  f.dual.map_lfp

/--
theorem `map_le_gfp` / 定理 `map_le_gfp`

English:
theorem map_le_gfp
  given: {a : α} (ha : a <= f.gfp)
  statement: f a <= f.gfp
  proof: f.dual.lfp_le_map ha

中文:
定理 map_le_gfp
  条件: {a : α} (ha : a <= f.gfp)
  结论: f a <= f.gfp
  证明: f.dual.lfp_le_map ha

Depends on / 依赖: f.dual.lfp_le_map, lfp_le_map
-/
theorem map_le_gfp {a : α} (ha : a <= f.gfp) : f a <= f.gfp :=
  f.dual.lfp_le_map ha

/--
theorem `gfp_le_map` / 定理 `gfp_le_map`

English:
theorem gfp_le_map
  given: {a : α} (ha : f.gfp <= a)
  statement: f.gfp <= f a
  proof: f.dual.map_le_lfp ha

中文:
定理 gfp_le_map
  条件: {a : α} (ha : f.gfp <= a)
  结论: f.gfp <= f a
  证明: f.dual.map_le_lfp ha

Depends on / 依赖: f.dual.map_le_lfp, map_le_lfp
-/
theorem gfp_le_map {a : α} (ha : f.gfp <= a) : f.gfp <= f a :=
  f.dual.map_le_lfp ha

/--
theorem `isGreatest_gfp_le` / 定理 `isGreatest_gfp_le`

English:
theorem isGreatest_gfp_le
  statement: IsGreatest { a | a <= f a } f.gfp
  proof: f.dual.isLeast_lfp_le

中文:
定理 isGreatest_gfp_le
  结论: IsGreatest { a | a <= f a } f.gfp
  证明: f.dual.isLeast_lfp_le

Depends on / 依赖: f.dual.isLeast_lfp_le, isLeast_lfp_le
-/
theorem isGreatest_gfp_le : IsGreatest { a | a <= f a } f.gfp :=
  f.dual.isLeast_lfp_le

/--
theorem `isGreatest_gfp` / 定理 `isGreatest_gfp`

English:
theorem isGreatest_gfp
  statement: IsGreatest (fixedPoints f) f.gfp
  proof: f.dual.isLeast_lfp

中文:
定理 isGreatest_gfp
  结论: IsGreatest (fixedPoints f) f.gfp
  证明: f.dual.isLeast_lfp

Depends on / 依赖: f.dual.isLeast_lfp, isLeast_lfp
-/
theorem isGreatest_gfp : IsGreatest (fixedPoints f) f.gfp :=
  f.dual.isLeast_lfp

/--
theorem `gfp_induction` / 定理 `gfp_induction`

English:
theorem gfp_induction
  statement: {p : α -> Prop} (step : forall a, p a -> f.gfp <= a -> p (f a))
  proof: f.dual.lfp_induction step hInf

中文:
定理 gfp_induction
  结论: {p : α -> 命题} (step : 对任意 a, p a -> f.gfp <= a -> p (f a))
  证明: f.dual.lfp_induction step hInf

Depends on / 依赖: f.dual.lfp_induction, lfp_induction
-/
theorem gfp_induction {p : α -> Prop} (step : forall a, p a -> f.gfp <= a -> p (f a))
    (hInf : forall s, (forall a in s, p a) -> p (sInf s)) : p f.gfp :=
  f.dual.lfp_induction step hInf

/--
theorem `lfp_le_gfp` / 定理 `lfp_le_gfp`

English:
theorem lfp_le_gfp
  statement: f.lfp <= f.gfp
  proof: f.lfp_le_fixed f.isFixedPt_gfp

中文:
定理 lfp_le_gfp
  结论: f.lfp <= f.gfp
  证明: f.lfp_le_fixed f.isFixedPt_gfp

Depends on / 依赖: f.isFixedPt_gfp, f.lfp_le_fixed, isFixedPt_gfp, lfp_le_fixed
-/
theorem lfp_le_gfp : f.lfp <= f.gfp :=
  f.lfp_le_fixed f.isFixedPt_gfp

end Basic

section Eqn

variable [CompleteLattice α] [CompleteLattice β] (f : β ->o α) (g : α ->o β)

-- Rolling rule
/--
theorem `map_lfp_comp` / 定理 `map_lfp_comp`

English:
theorem map_lfp_comp
  statement: f (g.comp f).lfp = (f.comp g).lfp
  proof: le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp))
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le

中文:
定理 map_lfp_comp
  结论: f (g.comp f).lfp = (f.comp g).lfp
  证明: le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp))
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le

Depends on / 依赖: congr_arg, f.comp, f.mono, g.comp, le_antisymm, lfp_le, lfp_le_fixed, map_lfp
-/
theorem map_lfp_comp : f (g.comp f).lfp = (f.comp g).lfp :=
le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp))
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le

/--
theorem `map_gfp_comp` / 定理 `map_gfp_comp`

English:
theorem map_gfp_comp
  statement: f (g.comp f).gfp = (f.comp g).gfp
  proof: f.dual.map_lfp_comp g.dual

中文:
定理 map_gfp_comp
  结论: f (g.comp f).gfp = (f.comp g).gfp
  证明: f.dual.map_lfp_comp g.dual

Depends on / 依赖: f.dual.map_lfp_comp, g.dual, map_lfp_comp
-/
theorem map_gfp_comp : f (g.comp f).gfp = (f.comp g).gfp :=
  f.dual.map_lfp_comp g.dual

-- Diagonal rule
/--
theorem `lfp_lfp` / 定理 `lfp_lfp`

English:
theorem lfp_lfp
  given: (h : α ->o α ->o α)
  statement: (lfp.comp h).lfp = h.onDiag.lfp
  proof: by
  let a := (lfp.comp h).lfp
  refine (lfp_le _ ?_).antisymm (lfp_le _ (Eq.le ?_))
  · exact lfp_le _ h.onDiag.map_lfp.le
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc
    h a a = h a (h a).lfp := congr_arg (h a) ha.symm
    _ = (h a).lfp := (h a).map_lfp
    _ = a := ha

中文:
定理 lfp_lfp
  条件: (h : α ->o α ->o α)
  结论: (lfp.comp h).lfp = h.onDiag.lfp
  证明: by
  let a := (lfp.comp h).lfp
  refine (lfp_le _ ?_).antisymm (lfp_le _ (Eq.le ?_))
  · exact lfp_le _ h.onDiag.map_lfp.le
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc
    h a a = h a (h a).lfp := congr_arg (h a) ha.symm
    _ = (h a).lfp := (h a).map_lfp
    _ = a := ha

Depends on / 依赖: Eq.le, antisymm, congr_arg, h.onDiag.map_lfp.le, ha.symm, lfp.comp, lfp_le, map_lfp, onDiag
-/
theorem lfp_lfp (h : α ->o α ->o α) : (lfp.comp h).lfp = h.onDiag.lfp := by
  let a := (lfp.comp h).lfp
  refine (lfp_le _ ?_).antisymm (lfp_le _ (Eq.le ?_))
  · exact lfp_le _ h.onDiag.map_lfp.le
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc
    h a a = h a (h a).lfp := congr_arg (h a) ha.symm
    _ = (h a).lfp := (h a).map_lfp
    _ = a := ha

/--
theorem `gfp_gfp` / 定理 `gfp_gfp`

English:
theorem gfp_gfp
  given: (h : α ->o α ->o α)
  statement: (gfp.comp h).gfp = h.onDiag.gfp
  proof: @lfp_lfp αᵒᵈ _ (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual

中文:
定理 gfp_gfp
  条件: (h : α ->o α ->o α)
  结论: (gfp.comp h).gfp = h.onDiag.gfp
  证明: @lfp_lfp αᵒᵈ _ (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual

Depends on / 依赖: OrderHom, OrderHom.dualIso, dualIso, h.dual, lfp_lfp, symm.toOrderEmbedding.toOrderHom.comp, toOrderEmbedding, toOrderHom
-/
theorem gfp_gfp (h : α ->o α ->o α) : (gfp.comp h).gfp = h.onDiag.gfp :=
@lfp_lfp αᵒᵈ _ (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual

end Eqn

section PrevNext

variable [CompleteLattice α] (f : α ->o α)

/--
theorem `gfp_const_inf_le` / 定理 `gfp_const_inf_le`

English:
theorem gfp_const_inf_le
  given: (x : α)
  statement: (const α x ⊓ f).gfp <= x
  proof: (gfp_le _) fun _ hb => hb.trans inf_le_left

中文:
定理 gfp_const_inf_le
  条件: (x : α)
  结论: (const α x ⊓ f).gfp <= x
  证明: (gfp_le _) fun _ hb => hb.trans inf_le_left

Depends on / 依赖: gfp_le, hb.trans, inf_le_left
-/
theorem gfp_const_inf_le (x : α) : (const α x ⊓ f).gfp <= x :=
  (gfp_le _) fun _ hb => hb.trans inf_le_left

/--
Definition of `prevFixed` / `prevFixed` 的定义

English:
definition prevFixed
  signature: (x : α) (hx : f x <= x)
  body: ⟨(const α x ⊓ f).gfp,
    calc
      f (const α x ⊓ f).gfp = x ⊓ f (const α x ⊓ f).gfp :=
Eq.symm inf_of_le_right (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = (const α x ⊓ f).gfp := (const α x ⊓ f).map_gfp
      ⟩

中文:
定义 prevFixed
  签名: (x : α) (hx : f x <= x)
  定义体: ⟨(const α x ⊓ f).gfp,
    calc
      f (const α x ⊓ f).gfp = x ⊓ f (const α x ⊓ f).gfp :=
Eq.symm inf_of_le_right (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = (const α x ⊓ f).gfp := (const α x ⊓ f).map_gfp
      ⟩

Depends on / 依赖: Eq.symm, f.gfp_const_inf_le, f.mono, gfp_const_inf_le, inf_of_le_right, map_gfp
-/
def prevFixed (x : α) (hx : f x <= x) : fixedPoints f :=
  ⟨(const α x ⊓ f).gfp,
    calc
      f (const α x ⊓ f).gfp = x ⊓ f (const α x ⊓ f).gfp :=
Eq.symm inf_of_le_right (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = (const α x ⊓ f).gfp := (const α x ⊓ f).map_gfp
      ⟩

/--
Definition of `nextFixed` / `nextFixed` 的定义

English:
definition nextFixed
  signature: (x : α) (hx : x <= f x)
  body: { f.dual.prevFixed x hx with val := (const α x ⊔ f).lfp }

中文:
定义 nextFixed
  签名: (x : α) (hx : x <= f x)
  定义体: { f.dual.prevFixed x hx with val := (const α x ⊔ f).lfp }

Depends on / 依赖: f.dual.prevFixed, prevFixed
-/
def nextFixed (x : α) (hx : x <= f x) : fixedPoints f :=
  { f.dual.prevFixed x hx with val := (const α x ⊔ f).lfp }

/--
theorem `prevFixed_le` / 定理 `prevFixed_le`

English:
theorem prevFixed_le
  given: {x : α} (hx : f x <= x)
  statement: ↑(f.prevFixed x hx) <= x
  proof: f.gfp_const_inf_le x

中文:
定理 prevFixed_le
  条件: {x : α} (hx : f x <= x)
  结论: ↑(f.prevFixed x hx) <= x
  证明: f.gfp_const_inf_le x

Depends on / 依赖: f.gfp_const_inf_le, gfp_const_inf_le
-/
theorem prevFixed_le {x : α} (hx : f x <= x) : ↑(f.prevFixed x hx) <= x :=
  f.gfp_const_inf_le x

/--
theorem `le_nextFixed` / 定理 `le_nextFixed`

English:
theorem le_nextFixed
  given: {x : α} (hx : x <= f x)
  statement: x <= f.nextFixed x hx
  proof: f.dual.prevFixed_le hx

中文:
定理 le_nextFixed
  条件: {x : α} (hx : x <= f x)
  结论: x <= f.nextFixed x hx
  证明: f.dual.prevFixed_le hx

Depends on / 依赖: f.dual.prevFixed_le, prevFixed_le
-/
theorem le_nextFixed {x : α} (hx : x <= f x) : x <= f.nextFixed x hx :=
  f.dual.prevFixed_le hx

/--
theorem `nextFixed_le` / 定理 `nextFixed_le`

English:
theorem nextFixed_le
  given: {x : α} (hx : x <= f x) {y : fixedPoints f} (h : x <= y)
  proof: Subtype.coe_le_coe.1 lfp_le _ sup_le h y.2.le

@[simp]

中文:
定理 nextFixed_le
  条件: {x : α} (hx : x <= f x) {y : fixedPoints f} (h : x <= y)
  证明: Subtype.coe_le_coe.1 lfp_le _ sup_le h y.2.le

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_le_coe, coe_le_coe, lfp_le, sup_le
-/
theorem nextFixed_le {x : α} (hx : x <= f x) {y : fixedPoints f} (h : x <= y) :
    f.nextFixed x hx <= y :=
Subtype.coe_le_coe.1 lfp_le _ sup_le h y.2.le

@[simp]
/--
theorem `nextFixed_le_iff` / 定理 `nextFixed_le_iff`

English:
theorem nextFixed_le_iff
  given: {x : α} (hx : x <= f x) {y : fixedPoints f}
  proof: ⟨fun h => (f.le_nextFixed hx).trans h, f.nextFixed_le hx⟩

@[simp]

中文:
定理 nextFixed_le_iff
  条件: {x : α} (hx : x <= f x) {y : fixedPoints f}
  证明: ⟨fun h => (f.le_nextFixed hx).trans h, f.nextFixed_le hx⟩

@[simp]

Depends on / 依赖: f.le_nextFixed, f.nextFixed_le, le_nextFixed, nextFixed_le
-/
theorem nextFixed_le_iff {x : α} (hx : x <= f x) {y : fixedPoints f} :
    f.nextFixed x hx <= y ↔ x <= y :=
  ⟨fun h => (f.le_nextFixed hx).trans h, f.nextFixed_le hx⟩

@[simp]
/--
theorem `le_prevFixed_iff` / 定理 `le_prevFixed_iff`

English:
theorem le_prevFixed_iff
  given: {x : α} (hx : f x <= x) {y : fixedPoints f}
  proof: f.dual.nextFixed_le_iff hx

中文:
定理 le_prevFixed_iff
  条件: {x : α} (hx : f x <= x) {y : fixedPoints f}
  证明: f.dual.nextFixed_le_iff hx

Depends on / 依赖: f.dual.nextFixed_le_iff, nextFixed_le_iff
-/
theorem le_prevFixed_iff {x : α} (hx : f x <= x) {y : fixedPoints f} :
    y <= f.prevFixed x hx ↔ ↑y <= x :=
  f.dual.nextFixed_le_iff hx

/--
theorem `le_prevFixed` / 定理 `le_prevFixed`

English:
theorem le_prevFixed
  given: {x : α} (hx : f x <= x) {y : fixedPoints f} (h : ↑y <= x)
  proof: (f.le_prevFixed_iff hx).2 h

中文:
定理 le_prevFixed
  条件: {x : α} (hx : f x <= x) {y : fixedPoints f} (h : ↑y <= x)
  证明: (f.le_prevFixed_iff hx).2 h

Depends on / 依赖: f.le_prevFixed_iff, le_prevFixed_iff
-/
theorem le_prevFixed {x : α} (hx : f x <= x) {y : fixedPoints f} (h : ↑y <= x) :
    y <= f.prevFixed x hx :=
  (f.le_prevFixed_iff hx).2 h

/--
theorem `le_map_sup_fixedPoints` / 定理 `le_map_sup_fixedPoints`

English:
theorem le_map_sup_fixedPoints
  given: (x y : fixedPoints f)
  statement: (x ⊔ y : α) <= f (x ⊔ y)
  proof: calc
    (x ⊔ y : α) = f x ⊔ f y := congr_arg₂ (· ⊔ ·) x.2.symm y.2.symm
    _ <= f (x ⊔ y) := f.mono.le_map_sup x y

中文:
定理 le_map_sup_fixedPoints
  条件: (x y : fixedPoints f)
  结论: (x ⊔ y : α) <= f (x ⊔ y)
  证明: calc
    (x ⊔ y : α) = f x ⊔ f y := congr_arg₂ (· ⊔ ·) x.2.symm y.2.symm
    _ <= f (x ⊔ y) := f.mono.le_map_sup x y

Depends on / 依赖: f.mono.le_map_sup, le_map_sup
-/
theorem le_map_sup_fixedPoints (x y : fixedPoints f) : (x ⊔ y : α) <= f (x ⊔ y) :=
  calc
    (x ⊔ y : α) = f x ⊔ f y := congr_arg₂ (· ⊔ ·) x.2.symm y.2.symm
    _ <= f (x ⊔ y) := f.mono.le_map_sup x y

-- Porting note: `x ⊓ y` without the `.val`s fails to synthesize `Inf` instance
/--
theorem `map_inf_fixedPoints_le` / 定理 `map_inf_fixedPoints_le`

English:
theorem map_inf_fixedPoints_le
  given: (x y : fixedPoints f)
  statement: f (x ⊓ y) <= x.val ⊓ y.val
  proof: f.dual.le_map_sup_fixedPoints x y

中文:
定理 map_inf_fixedPoints_le
  条件: (x y : fixedPoints f)
  结论: f (x ⊓ y) <= x.val ⊓ y.val
  证明: f.dual.le_map_sup_fixedPoints x y

Depends on / 依赖: f.dual.le_map_sup_fixedPoints, le_map_sup_fixedPoints
-/
theorem map_inf_fixedPoints_le (x y : fixedPoints f) : f (x ⊓ y) <= x.val ⊓ y.val :=
  f.dual.le_map_sup_fixedPoints x y

/--
theorem `le_map_sSup_subset_fixedPoints` / 定理 `le_map_sSup_subset_fixedPoints`

English:
theorem le_map_sSup_subset_fixedPoints
  given: (A : Set α) (hA : A subseteq fixedPoints f)
  proof: sSup_le fun _ hx => hA hx ▸ (f.mono <| le_sSup hx)

中文:
定理 le_map_sSup_subset_fixedPoints
  条件: (A : 集合 α) (hA : A subseteq fixedPoints f)
  证明: sSup_le fun _ hx => hA hx ▸ (f.mono <| le_sSup hx)

Depends on / 依赖: f.mono, le_sSup, sSup_le
-/
theorem le_map_sSup_subset_fixedPoints (A : Set α) (hA : A subseteq fixedPoints f) :
    sSup A <= f (sSup A) :=
  sSup_le fun _ hx => hA hx ▸ (f.mono <| le_sSup hx)

/--
theorem `map_sInf_subset_fixedPoints_le` / 定理 `map_sInf_subset_fixedPoints_le`

English:
theorem map_sInf_subset_fixedPoints_le
  given: (A : Set α) (hA : A subseteq fixedPoints f)
  proof: le_sInf fun _ hx => hA hx ▸ (f.mono <| sInf_le hx)

中文:
定理 map_sInf_subset_fixedPoints_le
  条件: (A : 集合 α) (hA : A subseteq fixedPoints f)
  证明: le_sInf fun _ hx => hA hx ▸ (f.mono <| sInf_le hx)

Depends on / 依赖: f.mono, le_sInf, sInf_le
-/
theorem map_sInf_subset_fixedPoints_le (A : Set α) (hA : A subseteq fixedPoints f) :
    f (sInf A) <= sInf A :=
  le_sInf fun _ hx => hA hx ▸ (f.mono <| sInf_le hx)

end PrevNext

end OrderHom

namespace fixedPoints

open OrderHom

variable [CompleteLattice α] (f : α ->o α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (fixedPoints f)
  body: ⟨f.gfp, f.isFixedPt_gfp⟩
  bot := ⟨f.lfp, f.isFixedPt_lfp⟩
  le_top x := f.le_gfp x.2.ge
  bot_le x := f.lfp_le x.2.le

中文:
实例 :
  签名: 有界序 (fixedPoints f)
  定义体: ⟨f.gfp, f.isFixedPt_gfp⟩
  bot := ⟨f.lfp, f.isFixedPt_lfp⟩
  le_top x := f.le_gfp x.2.ge
  bot_le x := f.lfp_le x.2.le

Depends on / 依赖: f.gfp, f.isFixedPt_gfp, isFixedPt_gfp
-/
instance : BoundedOrder (fixedPoints f) where
  top := ⟨f.gfp, f.isFixedPt_gfp⟩
  bot := ⟨f.lfp, f.isFixedPt_lfp⟩
  le_top x := f.le_gfp x.2.ge
  bot_le x := f.lfp_le x.2.le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (fixedPoints f)
  body: f.nextFixed (x ⊔ y) (f.le_map_sup_fixedPoints x y)
le_sup_left _ _ := Subtype.coe_le_coe.1 le_sup_left.trans (f.le_nextFixed _)
le_sup_right _ _ := Subtype.coe_le_coe.1 le_sup_right.trans (f.le_nextFixed _)
sup_le _ _ _ hxz hyz := f.nextFixed_le _ sup_le hxz hyz

中文:
实例 :
  签名: SemilatticeSup (fixedPoints f)
  定义体: f.nextFixed (x ⊔ y) (f.le_map_sup_fixedPoints x y)
le_sup_left _ _ := Subtype.coe_le_coe.1 le_sup_left.trans (f.le_nextFixed _)
le_sup_right _ _ := Subtype.coe_le_coe.1 le_sup_right.trans (f.le_nextFixed _)
sup_le _ _ _ hxz hyz := f.nextFixed_le _ sup_le hxz hyz

Depends on / 依赖: f.le_map_sup_fixedPoints, f.nextFixed, le_map_sup_fixedPoints, nextFixed
-/
instance : SemilatticeSup (fixedPoints f) where
  sup x y := f.nextFixed (x ⊔ y) (f.le_map_sup_fixedPoints x y)
le_sup_left _ _ := Subtype.coe_le_coe.1 le_sup_left.trans (f.le_nextFixed _)
le_sup_right _ _ := Subtype.coe_le_coe.1 le_sup_right.trans (f.le_nextFixed _)
sup_le _ _ _ hxz hyz := f.nextFixed_le _ sup_le hxz hyz

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (fixedPoints f)
  body: inferInstance
  inf x y := f.prevFixed (x ⊓ y) (f.map_inf_fixedPoints_le x y)
  __ := OrderDual.instSemilatticeInf (fixedPoints f.dual)

中文:
实例 :
  签名: SemilatticeInf (fixedPoints f)
  定义体: inferInstance
  inf x y := f.prevFixed (x ⊓ y) (f.map_inf_fixedPoints_le x y)
  __ := OrderDual.instSemilatticeInf (fixedPoints f.dual)
-/
instance : SemilatticeInf (fixedPoints f) where
  __ : PartialOrder (fixedPoints f) := inferInstance
  inf x y := f.prevFixed (x ⊓ y) (f.map_inf_fixedPoints_le x y)
  __ := OrderDual.instSemilatticeInf (fixedPoints f.dual)

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (fixedPoints f) where
  body: f.nextFixed (sSup (Subtype.val '' s))
      (f.le_map_sSup_subset_fixedPoints (Subtype.val '' s)
        fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
  isLUB_sSup _ :=
    ⟨fun _ hx => (le_sSup <| Set.mem_image_of_mem _ hx).trans (f.le_nextFixed _),
fun _ hx => f.nextFixed_le _ sSup_le Set.forall_mem_image.2 hx⟩
  

中文:
实例 completeLattice
  签名: : 完备格 (fixedPoints f) where
  定义体: f.nextFixed (sSup (Subtype.val '' s))
      (f.le_map_sSup_subset_fixedPoints (Subtype.val '' s)
        fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
  isLUB_sSup _ :=
    ⟨fun _ hx => (le_sSup <| Set.mem_image_of_mem _ hx).trans (f.le_nextFixed _),
fun _ hx => f.nextFixed_le _ sSup_le Set.forall_mem_image.2 hx⟩
  

Depends on / 依赖: Set.forall_mem_image, Set.mem_image_of_mem, Subtype, Subtype.val, f.le_map_sSup_subset_fixedPoints, f.le_nextFixed, f.map_sInf_subset_fixedPoints_le, f.nextFixed, f.nextFixed_le, f.prevFixed, f.prevFixed_le, forall_mem_image, isGLB_sInf, isLUB_sSup, le_map_sSup_subset_fixedPoints, le_nextFixed, le_sSup, map_sInf_subset_fixedPoints_le, mem_image_of_mem, nextFixed
-/
instance completeLattice : CompleteLattice (fixedPoints f) where
  sSup s :=
    f.nextFixed (sSup (Subtype.val '' s))
      (f.le_map_sSup_subset_fixedPoints (Subtype.val '' s)
        fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
  isLUB_sSup _ :=
    ⟨fun _ hx => (le_sSup <| Set.mem_image_of_mem _ hx).trans (f.le_nextFixed _),
fun _ hx => f.nextFixed_le _ sSup_le Set.forall_mem_image.2 hx⟩
  sInf s :=
    f.prevFixed (sInf (Subtype.val '' s))
      (f.map_sInf_subset_fixedPoints_le (Subtype.val '' s) fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
  isGLB_sInf _ :=
    ⟨fun _ hx => (f.prevFixed_le _).trans (sInf_le <| Set.mem_image_of_mem _ hx),
fun _ hx => f.le_prevFixed _ le_sInf Set.forall_mem_image.2 hx⟩

open OmegaCompletePartialOrder fixedPoints

/--
theorem `lfp_eq_sSup_iterate` / 定理 `lfp_eq_sSup_iterate`

English:
theorem lfp_eq_sSup_iterate
  given: (h : ωScottContinuous f)
  proof: by
  apply le_antisymm
  · apply lfp_le_fixed
    exact Function.mem_fixedPoints.mp (ωSup_iterate_mem_fixedPoint
      ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le)
  · apply le_lfp
    intro a h_a
    exact ωSup_iterate_le_prefixedPoint ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le h_a bot_le

中文:
定理 lfp_eq_sSup_iterate
  条件: (h : ωScottContinuous f)
  证明: by
  apply le_antisymm
  · apply lfp_le_fixed
    exact Function.mem_fixedPoints.mp (ωSup_iterate_mem_fixedPoint
      ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le)
  · apply le_lfp
    intro a h_a
    exact ωSup_iterate_le_prefixedPoint ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le h_a bot_le

Depends on / 依赖: Function, Function.mem_fixedPoints.mp, bot_le, h.map_, le_antisymm, le_lfp, lfp_le_fixed, mem_fixedPoints
-/
theorem lfp_eq_sSup_iterate (h : ωScottContinuous f) :
    f.lfp = ⨆ n, f^[n] ⊥ := by
  apply le_antisymm
  · apply lfp_le_fixed
    exact Function.mem_fixedPoints.mp (ωSup_iterate_mem_fixedPoint
      ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le)
  · apply le_lfp
    intro a h_a
    exact ωSup_iterate_le_prefixedPoint ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le h_a bot_le

/--
theorem `gfp_eq_sInf_iterate` / 定理 `gfp_eq_sInf_iterate`

English:
theorem gfp_eq_sInf_iterate
  given: (h : ωScottContinuous f.dual)
  proof: lfp_eq_sSup_iterate f.dual h

中文:
定理 gfp_eq_sInf_iterate
  条件: (h : ωScottContinuous f.dual)
  证明: lfp_eq_sSup_iterate f.dual h

Depends on / 依赖: f.dual, lfp_eq_sSup_iterate
-/
theorem gfp_eq_sInf_iterate (h : ωScottContinuous f.dual) :
    f.gfp = ⨅ n, f^[n] ⊤ :=
  lfp_eq_sSup_iterate f.dual h

end fixedPoints
