/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Quot
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.Substs

import Mathlib.Tactic.Attr.Register

/-!
# Equivalence between types

In this file we define two types:

* `Equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `Equiv.Perm α`: the group of permutations `α ≃ α`. More lemmas about `Equiv.Perm` can be found in
  `Mathlib/GroupTheory/Perm/`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `Equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `Equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `Equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `Equiv.inhabited` takes `e : α ≃ β` and `[Inhabited β]` and returns `Inhabited α`;
  - `Equiv.unique` takes `e : α ≃ β` and `[Unique β]` and returns `Unique α`;
  - `Equiv.decidableEq` takes `e : α ≃ β` and `[DecidableEq β]` and returns `DecidableEq α`.

  More definitions of this kind can be found in other files.
  E.g., `Mathlib/Algebra/Group/TransferInstance.lean` does it for `Group`,
  `Mathlib/Algebra/Module/TransferInstance.lean` does it for `Module`, and similar files exist for
  other algebraic type classes.

Many more such isomorphisms and operations are defined in `Mathlib/Logic/Equiv/Basic.lean`.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: (α β : Sort*)
  axioms and operations (4):
    - toFun : α -> β
    - invFun : β -> α
    - left_inv : LeftInverse invFun toFun  [default: by intro; first | rfl | ext <;> rfl]
    - right_inv : RightInverse invFun toFun  [default: by intro; first | rfl | ext <;> rfl]

中文:
结构 Equiv
  参数: (α β : Sort*)
  公理与运算 (4 个):
    - toFun : α -> β
    - invFun : β -> α
    - left_inv : LeftInverse invFun toFun  [默认: by intro; first | rfl | ext <;> rfl]
    - right_inv : RightInverse invFun toFun  [默认: by intro; first | rfl | ext <;> rfl]

Depends on / 依赖: RightInverse, invFun, protected, right_inv
-/
structure Equiv (α β : Sort*) where
  /-- The forward map of an equivalence.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : α -> β
  /-- The backward map of an equivalence.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  protected invFun : β -> α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
infixl:25 " ≃ " => Equiv

/-- Turn an element of a type `F` satisfying `EquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`. -/
@[coe]
/--
Definition of `EquivLike.toEquiv` / `EquivLike.toEquiv` 的定义

English:
definition EquivLike.toEquiv
  signature: {F} [EquivLike F α β] (f : F)
  body: f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f

中文:
定义 EquivLike.toEquiv
  签名: {F} [EquivLike F α β] (f : F)
  定义体: f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f
-/
def EquivLike.toEquiv {F} [EquivLike F α β] (f : F) : α ≃ β where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f

/-- Any type satisfying `EquivLike` can be cast into `Equiv` via `EquivLike.toEquiv`. -/
instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨EquivLike.toEquiv⟩

/--
Definition of `Equiv.Perm` / `Equiv.Perm` 的定义

English:
abbreviation Equiv.Perm
  signature: (α : Sort*)
  body: Equiv α α

中文:
缩写 Equiv.Perm
  签名: (α : Sort*)
  定义体: Equiv α α
-/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α

namespace Equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (α ≃ β) α β
  body: Equiv.toFun
  inv := Equiv.invFun
  left_inv := Equiv.left_inv
  right_inv := Equiv.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by cases e₁; cases e₂; congr

@[simp, norm_cast]

中文:
实例 :
  签名: EquivLike (α ≃ β) α β
  定义体: Equiv.toFun
  inv := Equiv.invFun
  left_inv := Equiv.left_inv
  right_inv := Equiv.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by cases e₁; cases e₂; congr

@[simp, norm_cast]

Depends on / 依赖: Equiv.toFun
-/
instance : EquivLike (α ≃ β) α β where
  coe := Equiv.toFun
  inv := Equiv.invFun
  left_inv := Equiv.left_inv
  right_inv := Equiv.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by cases e₁; cases e₂; congr

@[simp, norm_cast]
/--
lemma `_root_.EquivLike.coe_coe` / 引理 `_root_.EquivLike.coe_coe`

English:
lemma _root_.EquivLike.coe_coe
  given: {F} [EquivLike F α β] (e : F)
  proof: rfl

中文:
引理 _root_.EquivLike.coe_coe
  条件: {F} [EquivLike F α β] (e : F)
  证明: rfl
-/
lemma _root_.EquivLike.coe_coe {F} [EquivLike F α β] (e : F) :
    ((e : α ≃ β) : α -> β) = e := rfl

/--
theorem `coe_fn_mk` / 定理 `coe_fn_mk`

English:
theorem coe_fn_mk
  given: (f : α -> β) (g l r)
  statement: (Equiv.mk f g l r : α -> β) = f
  proof: rfl

中文:
定理 coe_fn_mk
  条件: (f : α -> β) (g l r)
  结论: (Equiv.mk f g l r : α -> β) = f
  证明: rfl
-/
@[simp, grind =] theorem coe_fn_mk (f : α -> β) (g l r) : (Equiv.mk f g l r : α -> β) = f :=
  rfl

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: @Function.Injective (α ≃ β) (α -> β) (fun e => e)
  proof: DFunLike.coe_injective

中文:
定理 coe_fn_injective
  结论: @Function.Injective (α ≃ β) (α -> β) (fun e => e)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α -> β) (fun e => e) :=
  DFunLike.coe_injective

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {e₁ e₂ : α ≃ β}
  statement: (e₁ : α -> β) = e₂ ↔ e₁ = e₂
  proof: @DFunLike.coe_fn_eq _ _ _ _ e₁ e₂

中文:
定理 coe_inj
  条件: {e₁ e₂ : α ≃ β}
  结论: (e₁ : α -> β) = e₂ ↔ e₁ = e₂
  证明: @DFunLike.coe_fn_eq _ _ _ _ e₁ e₂
-/
protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α -> β) = e₂ ↔ e₁ = e₂ :=
  @DFunLike.coe_fn_eq _ _ _ _ e₁ e₂

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Equiv α β} (H : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g H

中文:
定理 ext
  条件: {f g : Equiv α β} (H : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g H
-/
@[ext, grind ext] theorem ext {f g : Equiv α β} (H : forall x, f x = g x) : f = g := DFunLike.ext f g H

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {f : Equiv α β} {x x' : α}
  statement: x = x' -> f x = f x'
  proof: DFunLike.congr_arg f

中文:
定理 congr_arg
  条件: {f : Equiv α β} {x x' : α}
  结论: x = x' -> f x = f x'
  证明: DFunLike.congr_arg f
-/
protected theorem congr_arg {f : Equiv α β} {x x' : α} : x = x' -> f x = f x' :=
  DFunLike.congr_arg f

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : Equiv α β} (h : f = g) (x : α)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: {f g : Equiv α β} (h : f = g) (x : α)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

/--
theorem `Perm.ext` / 定理 `Perm.ext`

English:
theorem Perm.ext
  given: {σ τ : Equiv.Perm α} (H : forall x, σ x = τ x)
  statement: σ = τ
  proof: Equiv.ext H

中文:
定理 Perm.ext
  条件: {σ τ : Equiv.Perm α} (H : 对任意 x, σ x = τ x)
  结论: σ = τ
  证明: Equiv.ext H
-/
@[ext] theorem Perm.ext {σ τ : Equiv.Perm α} (H : forall x, σ x = τ x) : σ = τ := Equiv.ext H

/--
theorem `Perm.congr_arg` / 定理 `Perm.congr_arg`

English:
theorem Perm.congr_arg
  given: {f : Equiv.Perm α} {x x' : α}
  statement: x = x' -> f x = f x'
  proof: Equiv.congr_arg

中文:
定理 Perm.congr_arg
  条件: {f : Equiv.Perm α} {x x' : α}
  结论: x = x' -> f x = f x'
  证明: Equiv.congr_arg
-/
protected theorem Perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' -> f x = f x' :=
  Equiv.congr_arg

/--
theorem `Perm.congr_fun` / 定理 `Perm.congr_fun`

English:
theorem Perm.congr_fun
  given: {f g : Equiv.Perm α} (h : f = g) (x : α)
  statement: f x = g x
  proof: Equiv.congr_fun h x

中文:
定理 Perm.congr_fun
  条件: {f g : Equiv.Perm α} (h : f = g) (x : α)
  结论: f x = g x
  证明: Equiv.congr_fun h x
-/
protected theorem Perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Sort*)
  body: ⟨id, id, fun _ => rfl, fun _ => rfl⟩

中文:
定义 refl
  签名: (α : Sort*)
  定义体: ⟨id, id, fun _ => rfl, fun _ => rfl⟩
-/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/--
Instance `inhabited'` / 实例 `inhabited'`

English:
instance inhabited'
  signature: : Inhabited (α ≃ α)
  body: ⟨Equiv.refl α⟩

中文:
实例 inhabited'
  签名: : Inhabited (α ≃ α)
  定义体: ⟨Equiv.refl α⟩

Depends on / 依赖: Equiv.refl
-/
instance inhabited' : Inhabited (α ≃ α) := ⟨Equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm, implicit_reducible]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : α ≃ β)
  body: ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

中文:
定义 symm
  签名: (e : α ≃ β)
  定义体: ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
-/
protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : α ≃ β)
  body: e.symm

initialize_simps_projections Equiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : α ≃ β)
  定义体: e.symm

initialize_simps_projections Equiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (e : α ≃ β) : β -> α := e.symm

initialize_simps_projections Equiv (toFun -> apply, invFun -> symm_apply)

/--
theorem `left_inv'` / 定理 `left_inv'`

English:
theorem left_inv'
  given: (e : α ≃ β)
  statement: Function.LeftInverse e.symm e
  proof: e.left_inv

中文:
定理 left_inv'
  条件: (e : α ≃ β)
  结论: Function.LeftInverse e.symm e
  证明: e.left_inv

Depends on / 依赖: e.left_inv, left_inv
-/
theorem left_inv' (e : α ≃ β) : Function.LeftInverse e.symm e := e.left_inv
/--
theorem `right_inv'` / 定理 `right_inv'`

English:
theorem right_inv'
  given: (e : α ≃ β)
  statement: Function.RightInverse e.symm e
  proof: e.right_inv

中文:
定理 right_inv'
  条件: (e : α ≃ β)
  结论: Function.RightInverse e.symm e
  证明: e.right_inv

Depends on / 依赖: e.right_inv, right_inv
-/
theorem right_inv' (e : α ≃ β) : Function.RightInverse e.symm e := e.right_inv

/--
lemma `symm_mk` / 引理 `symm_mk`

English:
lemma symm_mk
  given: (f : α -> β) (g hl hr)
  statement: (mk f g hl hr).symm = mk g f hr hl
  proof: rfl

中文:
引理 symm_mk
  条件: (f : α -> β) (g hl hr)
  结论: (mk f g hl hr).symm = mk g f hr hl
  证明: rfl
-/
@[simp] lemma symm_mk (f : α -> β) (g hl hr) : (mk f g hl hr).symm = mk g f hr hl := rfl

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  body: ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simps]

中文:
定义 trans
  签名: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  定义体: ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simps]
-/
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans Equiv Equiv Equiv
  body: Equiv.trans

中文:
实例 :
  签名: Trans Equiv Equiv Equiv
  定义体: Equiv.trans

Depends on / 依赖: Equiv.trans
-/
instance : Trans Equiv Equiv Equiv where
  trans := Equiv.trans

/-- `Equiv.symm` defines an equivalence between `α ≃ β` and `β ≃ α`. -/
@[simps! (attr := grind =)]
/--
Definition of `symmEquiv` / `symmEquiv` 的定义

English:
definition symmEquiv
  signature: (α β : Sort*)
  body: .symm
  invFun := .symm

中文:
定义 symmEquiv
  签名: (α β : Sort*)
  定义体: .symm
  invFun := .symm
-/
def symmEquiv (α β : Sort*) : (α ≃ β) ≃ (β ≃ α) where
  toFun := .symm
  invFun := .symm

/--
theorem `toFun_as_coe` / 定理 `toFun_as_coe`

English:
theorem toFun_as_coe
  given: (e : α ≃ β)
  statement: e.toFun = e
  proof: rfl

中文:
定理 toFun_as_coe
  条件: (e : α ≃ β)
  结论: e.toFun = e
  证明: rfl
-/
@[simp, mfld_simps] theorem toFun_as_coe (e : α ≃ β) : e.toFun = e := rfl

/--
theorem `invFun_as_coe` / 定理 `invFun_as_coe`

English:
theorem invFun_as_coe
  given: (e : α ≃ β)
  statement: e.invFun = e.symm
  proof: rfl

中文:
定理 invFun_as_coe
  条件: (e : α ≃ β)
  结论: e.invFun = e.symm
  证明: rfl
-/
@[simp, mfld_simps] theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm := rfl

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : α ≃ β)
  statement: Injective e
  proof: EquivLike.injective e

中文:
定理 injective
  条件: (e : α ≃ β)
  结论: Injective e
  证明: EquivLike.injective e
-/
protected theorem injective (e : α ≃ β) : Injective e := EquivLike.injective e

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : α ≃ β)
  statement: Surjective e
  proof: EquivLike.surjective e

中文:
定理 surjective
  条件: (e : α ≃ β)
  结论: Surjective e
  证明: EquivLike.surjective e
-/
protected theorem surjective (e : α ≃ β) : Surjective e := EquivLike.surjective e

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : α ≃ β)
  statement: Bijective e
  proof: EquivLike.bijective e

中文:
定理 bijective
  条件: (e : α ≃ β)
  结论: Bijective e
  证明: EquivLike.bijective e
-/
protected theorem bijective (e : α ≃ β) : Bijective e := EquivLike.bijective e

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (e : α ≃ β) [Subsingleton β]
  statement: Subsingleton α
  proof: e.injective.subsingleton

中文:
定理 subsingleton
  条件: (e : α ≃ β) [Subsingleton β]
  结论: Subsingleton α
  证明: e.injective.subsingleton
-/
protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.injective.subsingleton

/--
theorem `subsingleton.symm` / 定理 `subsingleton.symm`

English:
theorem subsingleton.symm
  given: (e : α ≃ β) [Subsingleton α]
  statement: Subsingleton β
  proof: e.symm.injective.subsingleton

中文:
定理 subsingleton.symm
  条件: (e : α ≃ β) [Subsingleton α]
  结论: Subsingleton β
  证明: e.symm.injective.subsingleton
-/
protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.injective.subsingleton

/--
theorem `subsingleton_congr` / 定理 `subsingleton_congr`

English:
theorem subsingleton_congr
  given: (e : α ≃ β)
  statement: Subsingleton α ↔ Subsingleton β
  proof: ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩

中文:
定理 subsingleton_congr
  条件: (e : α ≃ β)
  结论: Subsingleton α ↔ Subsingleton β
  证明: ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩

Depends on / 依赖: e.subsingleton, e.symm.subsingleton, subsingleton
-/
theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩

/--
Instance `equiv_subsingleton_cod` / 实例 `equiv_subsingleton_cod`

English:
instance equiv_subsingleton_cod
  signature: [Subsingleton β]
  body: ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩

中文:
实例 equiv_subsingleton_cod
  签名: [Subsingleton β]
  定义体: ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩

Depends on / 依赖: Equiv.ext, Subsingleton, Subsingleton.elim
-/
instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩

/--
Instance `equiv_subsingleton_dom` / 实例 `equiv_subsingleton_dom`

English:
instance equiv_subsingleton_dom
  signature: [Subsingleton α]
  body: ⟨fun f _ => Equiv.ext fun _ => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩

中文:
实例 equiv_subsingleton_dom
  签名: [Subsingleton α]
  定义体: ⟨fun f _ => Equiv.ext fun _ => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩

Depends on / 依赖: Equiv.ext, Equiv.subsingleton.symm, Subsingleton, Subsingleton.elim, subsingleton
-/
instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f _ => Equiv.ext fun _ => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩

/--
Instance `permUnique` / 实例 `permUnique`

English:
instance permUnique
  signature: [Subsingleton α]
  body: uniqueOfSubsingleton (Equiv.refl α)

中文:
实例 permUnique
  签名: [Subsingleton α]
  定义体: uniqueOfSubsingleton (Equiv.refl α)

Depends on / 依赖: Equiv.refl, uniqueOfSubsingleton
-/
instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)

/--
theorem `Perm.subsingleton_eq_refl` / 定理 `Perm.subsingleton_eq_refl`

English:
theorem Perm.subsingleton_eq_refl
  given: [Subsingleton α] (e : Perm α)
  statement: e = Equiv.refl α
  proof: Subsingleton.elim _ _

中文:
定理 Perm.subsingleton_eq_refl
  条件: [Subsingleton α] (e : Perm α)
  结论: e = Equiv.refl α
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equiv.refl α :=
  Subsingleton.elim _ _

/--
theorem `nontrivial` / 定理 `nontrivial`

English:
theorem nontrivial
  given: {α β} (e : α ≃ β) [Nontrivial β]
  statement: Nontrivial α
  proof: e.surjective.nontrivial

中文:
定理 nontrivial
  条件: {α β} (e : α ≃ β) [Nontrivial β]
  结论: Nontrivial α
  证明: e.surjective.nontrivial
-/
protected theorem nontrivial {α β} (e : α ≃ β) [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial

/--
theorem `nontrivial_congr` / 定理 `nontrivial_congr`

English:
theorem nontrivial_congr
  given: {α β} (e : α ≃ β)
  statement: Nontrivial α ↔ Nontrivial β
  proof: ⟨fun _ => e.symm.nontrivial, fun _ => e.nontrivial⟩

中文:
定理 nontrivial_congr
  条件: {α β} (e : α ≃ β)
  结论: Nontrivial α ↔ Nontrivial β
  证明: ⟨fun _ => e.symm.nontrivial, fun _ => e.nontrivial⟩

Depends on / 依赖: e.nontrivial, e.symm.nontrivial, nontrivial
-/
theorem nontrivial_congr {α β} (e : α ≃ β) : Nontrivial α ↔ Nontrivial β :=
  ⟨fun _ => e.symm.nontrivial, fun _ => e.nontrivial⟩

/--
Definition of `decidableEq` / `decidableEq` 的定义

English:
abbreviation decidableEq
  signature: (e : α ≃ β) [DecidableEq β]
  body: e.injective.decidableEq

中文:
缩写 decidableEq
  签名: (e : α ≃ β) [DecidableEq β]
  定义体: e.injective.decidableEq
-/
protected abbrev decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.injective.decidableEq

/--
theorem `nonempty_congr` / 定理 `nonempty_congr`

English:
theorem nonempty_congr
  given: (e : α ≃ β)
  statement: Nonempty α ↔ Nonempty β
  proof: Nonempty.congr e e.symm

中文:
定理 nonempty_congr
  条件: (e : α ≃ β)
  结论: Nonempty α ↔ Nonempty β
  证明: Nonempty.congr e e.symm

Depends on / 依赖: Nonempty, Nonempty.congr, e.symm
-/
theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β := Nonempty.congr e e.symm

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (e : α ≃ β) [Nonempty β]
  statement: Nonempty α
  proof: e.nonempty_congr.mpr ‹_›

中文:
定理 nonempty
  条件: (e : α ≃ β) [Nonempty β]
  结论: Nonempty α
  证明: e.nonempty_congr.mpr ‹_›
-/
protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α := e.nonempty_congr.mpr ‹_›

/--
Definition of `inhabited` / `inhabited` 的定义

English:
abbreviation inhabited
  signature: [Inhabited β] (e : α ≃ β)
  body: ⟨e.symm default⟩

中文:
缩写 inhabited
  签名: [Inhabited β] (e : α ≃ β)
  定义体: ⟨e.symm default⟩
-/
protected abbrev inhabited [Inhabited β] (e : α ≃ β) : Inhabited α := ⟨e.symm default⟩

/--
Definition of `unique` / `unique` 的定义

English:
abbreviation unique
  signature: [Unique β] (e : α ≃ β)
  body: e.symm.surjective.unique

中文:
缩写 unique
  签名: [Unique β] (e : α ≃ β)
  定义体: e.symm.surjective.unique
-/
protected abbrev unique [Unique β] (e : α ≃ β) : Unique α := e.symm.surjective.unique

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {α β : Sort _} (h : α = β)
  body: cast h
  invFun := cast h.symm
  left_inv := by grind
  right_inv := by grind

中文:
定义 cast
  签名: {α β : Sort _} (h : α = β)
  定义体: cast h
  invFun := cast h.symm
  left_inv := by grind
  right_inv := by grind
-/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β where
  toFun := cast h
  invFun := cast h.symm
  left_inv := by grind
  right_inv := by grind

/--
theorem `coe_fn_symm_mk` / 定理 `coe_fn_symm_mk`

English:
theorem coe_fn_symm_mk
  given: (f : α -> β) (g l r)
  statement: ((Equiv.mk f g l r).symm : β -> α) = g
  proof: rfl

中文:
定理 coe_fn_symm_mk
  条件: (f : α -> β) (g l r)
  结论: ((Equiv.mk f g l r).symm : β -> α) = g
  证明: rfl
-/
@[simp] theorem coe_fn_symm_mk (f : α -> β) (g l r) : ((Equiv.mk f g l r).symm : β -> α) = g := rfl

/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: (Equiv.refl α : α -> α) = id
  proof: rfl

中文:
定理 coe_refl
  结论: (Equiv.refl α : α -> α) = id
  证明: rfl
-/
@[simp] theorem coe_refl : (Equiv.refl α : α -> α) = id := rfl

/--
theorem `Perm.coe_subsingleton` / 定理 `Perm.coe_subsingleton`

English:
theorem Perm.coe_subsingleton
  given: {α : Type*} [Subsingleton α] (e : Perm α)
  statement: (e : α -> α) = id
  proof: by
  rw [Perm.subsingleton_eq_refl e]; rw [coe_refl]

中文:
定理 Perm.coe_subsingleton
  条件: {α : 类型} [Subsingleton α] (e : Perm α)
  结论: (e : α -> α) = id
  证明: by
  rw [Perm.subsingleton_eq_refl e]; rw [coe_refl]

Depends on / 依赖: Perm.subsingleton_eq_refl, coe_refl, subsingleton_eq_refl
-/
theorem Perm.coe_subsingleton {α : Type*} [Subsingleton α] (e : Perm α) : (e : α -> α) = id := by
  rw [Perm.subsingleton_eq_refl e]; rw [coe_refl]

/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : α)
  statement: Equiv.refl α x = x
  proof: rfl

中文:
定理 refl_apply
  条件: (x : α)
  结论: Equiv.refl α x = x
  证明: rfl
-/
@[simp, grind =] theorem refl_apply (x : α) : Equiv.refl α x = x := rfl

/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (f : α ≃ β) (g : β ≃ γ)
  statement: (f.trans g : α -> γ) = g ∘ f
  proof: rfl

中文:
定理 coe_trans
  条件: (f : α ≃ β) (g : β ≃ γ)
  结论: (f.trans g : α -> γ) = g ∘ f
  证明: rfl
-/
@[simp] theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g : α -> γ) = g ∘ f := rfl

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (f : α ≃ β) (g : β ≃ γ) (a : α)
  proof: rfl

中文:
定理 trans_apply
  条件: (f : α ≃ β) (g : β ≃ γ) (a : α)
  证明: rfl
-/
@[simp, grind =] theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) :
    (f.trans g) a = g (f a) := rfl

/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : α ≃ β) (x : β)
  statement: e (e.symm x) = x
  proof: e.right_inv x

中文:
定理 apply_symm_apply
  条件: (e : α ≃ β) (x : β)
  结论: e (e.symm x) = x
  证明: e.right_inv x
-/
@[simp, grind =] theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x := e.right_inv x

/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : α ≃ β) (x : α)
  statement: e.symm (e x) = x
  proof: e.left_inv x

中文:
定理 symm_apply_apply
  条件: (e : α ≃ β) (x : α)
  结论: e.symm (e x) = x
  证明: e.left_inv x
-/
@[simp, grind =] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := e.left_inv x

/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : α ≃ β)
  statement: e.symm ∘ e = id
  proof: funext e.symm_apply_apply

中文:
定理 symm_comp_self
  条件: (e : α ≃ β)
  结论: e.symm ∘ e = id
  证明: funext e.symm_apply_apply
-/
@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id := funext e.symm_apply_apply

/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : α ≃ β)
  statement: e ∘ e.symm = id
  proof: funext e.apply_symm_apply

中文:
定理 self_comp_symm
  条件: (e : α ≃ β)
  结论: e ∘ e.symm = id
  证明: funext e.apply_symm_apply
-/
@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id := funext e.apply_symm_apply

/--
lemma `_root_.EquivLike.apply_coe_symm_apply` / 引理 `_root_.EquivLike.apply_coe_symm_apply`

English:
lemma _root_.EquivLike.apply_coe_symm_apply
  given: {F} [EquivLike F α β] (e : F) (x : β)
  proof: (e : α ≃ β).apply_symm_apply x

中文:
引理 _root_.EquivLike.apply_coe_symm_apply
  条件: {F} [EquivLike F α β] (e : F) (x : β)
  证明: (e : α ≃ β).apply_symm_apply x
-/
@[simp] lemma _root_.EquivLike.apply_coe_symm_apply {F} [EquivLike F α β] (e : F) (x : β) :
    e ((e : α ≃ β).symm x) = x :=
  (e : α ≃ β).apply_symm_apply x

/--
lemma `_root_.EquivLike.coe_symm_apply_apply` / 引理 `_root_.EquivLike.coe_symm_apply_apply`

English:
lemma _root_.EquivLike.coe_symm_apply_apply
  given: {F} [EquivLike F α β] (e : F) (x : α)
  proof: (e : α ≃ β).symm_apply_apply x

中文:
引理 _root_.EquivLike.coe_symm_apply_apply
  条件: {F} [EquivLike F α β] (e : F) (x : α)
  证明: (e : α ≃ β).symm_apply_apply x
-/
@[simp] lemma _root_.EquivLike.coe_symm_apply_apply {F} [EquivLike F α β] (e : F) (x : α) :
    (e : α ≃ β).symm (e x) = x :=
  (e : α ≃ β).symm_apply_apply x

/--
lemma `_root_.EquivLike.coe_symm_comp_self` / 引理 `_root_.EquivLike.coe_symm_comp_self`

English:
lemma _root_.EquivLike.coe_symm_comp_self
  given: {F} [EquivLike F α β] (e : F)
  proof: (e : α ≃ β).symm_comp_self

中文:
引理 _root_.EquivLike.coe_symm_comp_self
  条件: {F} [EquivLike F α β] (e : F)
  证明: (e : α ≃ β).symm_comp_self
-/
@[simp] lemma _root_.EquivLike.coe_symm_comp_self {F} [EquivLike F α β] (e : F) :
    (e : α ≃ β).symm ∘ e = id :=
  (e : α ≃ β).symm_comp_self

/--
lemma `_root_.EquivLike.self_comp_coe_symm` / 引理 `_root_.EquivLike.self_comp_coe_symm`

English:
lemma _root_.EquivLike.self_comp_coe_symm
  given: {F} [EquivLike F α β] (e : F)
  proof: (e : α ≃ β).self_comp_symm

中文:
引理 _root_.EquivLike.self_comp_coe_symm
  条件: {F} [EquivLike F α β] (e : F)
  证明: (e : α ≃ β).self_comp_symm
-/
@[simp] lemma _root_.EquivLike.self_comp_coe_symm {F} [EquivLike F α β] (e : F) :
    e ∘ (e : α ≃ β).symm = id :=
  (e : α ≃ β).self_comp_symm

/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (f : α ≃ β) (g : β ≃ γ) (a : γ)
  proof: rfl

@[simp, grind =]

中文:
定理 symm_trans_apply
  条件: (f : α ≃ β) (g : β ≃ γ) (a : γ)
  证明: rfl

@[simp, grind =]
-/
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl

@[simp, grind =]
/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (f : α ≃ β) (g : β ≃ γ)
  statement: (f.trans g).symm = g.symm.trans f.symm
  proof: rfl

中文:
定理 symm_trans
  条件: (f : α ≃ β) (g : β ≃ γ)
  结论: (f.trans g).symm = g.symm.trans f.symm
  证明: rfl
-/
theorem symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = g.symm.trans f.symm := rfl

/--
theorem `symm_symm_apply` / 定理 `symm_symm_apply`

English:
theorem symm_symm_apply
  given: (f : α ≃ β) (b : α)
  statement: f.symm.symm b = f b
  proof: rfl

中文:
定理 symm_symm_apply
  条件: (f : α ≃ β) (b : α)
  结论: f.symm.symm b = f b
  证明: rfl
-/
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b := rfl

/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (f : α ≃ β) {x y : α}
  statement: f x = f y ↔ x = y
  proof: EquivLike.apply_eq_iff_eq f

中文:
定理 apply_eq_iff_eq
  条件: (f : α ≃ β) {x y : α}
  结论: f x = f y ↔ x = y
  证明: EquivLike.apply_eq_iff_eq f

Depends on / 依赖: EquivLike, EquivLike.apply_eq_iff_eq, apply_eq_iff_eq
-/
theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f

/--
theorem `cast_apply` / 定理 `cast_apply`

English:
theorem cast_apply
  given: {α β} (h : α = β) (x : α)
  statement: Equiv.cast h x = cast h x
  proof: rfl

中文:
定理 cast_apply
  条件: {α β} (h : α = β) (x : α)
  结论: Equiv.cast h x = cast h x
  证明: rfl
-/
@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x := rfl

/--
theorem `cast_symm` / 定理 `cast_symm`

English:
theorem cast_symm
  given: {α β} (h : α = β)
  statement: Equiv.cast h.symm = (Equiv.cast h).symm
  proof: rfl

中文:
定理 cast_symm
  条件: {α β} (h : α = β)
  结论: Equiv.cast h.symm = (Equiv.cast h).symm
  证明: rfl
-/
theorem cast_symm {α β} (h : α = β) : Equiv.cast h.symm = (Equiv.cast h).symm := rfl

/--
theorem `cast_refl` / 定理 `cast_refl`

English:
theorem cast_refl
  given: {α} (h : α = α := rfl)
  statement: Equiv.cast h = Equiv.refl α
  proof: rfl

中文:
定理 cast_refl
  条件: {α} (h : α = α := rfl)
  结论: Equiv.cast h = Equiv.refl α
  证明: rfl
-/
@[simp] theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α := rfl

/--
theorem `cast_trans` / 定理 `cast_trans`

English:
theorem cast_trans
  given: {α β γ} (h : α = β) (h2 : β = γ)
  proof: ext fun x => by subst h h2; rfl

中文:
定理 cast_trans
  条件: {α β γ} (h : α = β) (h2 : β = γ)
  证明: ext fun x => by subst h h2; rfl
-/
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
    Equiv.cast (h.trans h2) = (Equiv.cast h).trans (Equiv.cast h2) :=
  ext fun x => by subst h h2; rfl

/--
theorem `cast_eq_iff_heq` / 定理 `cast_eq_iff_heq`

English:
theorem cast_eq_iff_heq
  given: {α β} (h : α = β) {a : α} {b : β}
  statement: Equiv.cast h a = b ↔ a ≍ b
  proof: by
  subst h; simp

中文:
定理 cast_eq_iff_heq
  条件: {α β} (h : α = β) {a : α} {b : β}
  结论: Equiv.cast h a = b ↔ a ≍ b
  证明: by
  subst h; simp
-/
theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ a ≍ b := by
  subst h; simp

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: {α β} (e : α ≃ β) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: by grind

中文:
定理 symm_apply_eq
  条件: {α β} (e : α ≃ β) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: by grind
-/
theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y := by grind

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {α β} (e : α ≃ β) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: by grind

@[deprecated eq_symm_apply (since := "2026-07-26")]

中文:
定理 eq_symm_apply
  条件: {α β} (e : α ≃ β) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: by grind

@[deprecated eq_symm_apply (since := "2026-07-26")]
-/
theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x := by grind

@[deprecated eq_symm_apply (since := "2026-07-26")]
/--
theorem `apply_eq_iff_eq_symm_apply` / 定理 `apply_eq_iff_eq_symm_apply`

English:
theorem apply_eq_iff_eq_symm_apply
  given: {x : α} {y : β} (f : α ≃ β)
  statement: f x = y ↔ x = f.symm y
  proof: f.eq_symm_apply.symm

中文:
定理 apply_eq_iff_eq_symm_apply
  条件: {x : α} {y : β} (f : α ≃ β)
  结论: f x = y ↔ x = f.symm y
  证明: f.eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, f.eq_symm_apply.symm
-/
theorem apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : α ≃ β) : f x = y ↔ x = f.symm y :=
  f.eq_symm_apply.symm

/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : α ≃ β)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : α ≃ β)
  结论: e.symm.symm = e
  证明: rfl
-/
@[simp, grind =] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (Equiv.symm : (α ≃ β) -> β ≃ α)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (Equiv.symm : (α ≃ β) -> β ≃ α)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (Equiv.symm : (α ≃ β) -> β ≃ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (e : α ≃ β)
  statement: e.trans (Equiv.refl β) = e
  proof: by grind

中文:
定理 trans_refl
  条件: (e : α ≃ β)
  结论: e.trans (Equiv.refl β) = e
  证明: by grind
-/
@[simp] theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e := by grind

/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (Equiv.refl α).symm = Equiv.refl α
  proof: rfl

中文:
定理 refl_symm
  结论: (Equiv.refl α).symm = Equiv.refl α
  证明: rfl
-/
@[simp, grind =] theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α := rfl

/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (e : α ≃ β)
  statement: (Equiv.refl α).trans e = e
  proof: by cases e; rfl

中文:
定理 refl_trans
  条件: (e : α ≃ β)
  结论: (Equiv.refl α).trans e = e
  证明: by cases e; rfl
-/
@[simp] theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e := by cases e; rfl

/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : α ≃ β)
  statement: e.symm.trans e = Equiv.refl β
  proof: by grind

中文:
定理 symm_trans_self
  条件: (e : α ≃ β)
  结论: e.symm.trans e = Equiv.refl β
  证明: by grind
-/
@[simp] theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β := by grind

/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : α ≃ β)
  statement: e.trans e.symm = Equiv.refl α
  proof: by grind

中文:
定理 self_trans_symm
  条件: (e : α ≃ β)
  结论: e.trans e.symm = Equiv.refl α
  证明: by grind
-/
@[simp] theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α := by grind

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ)
  proof: by grind

中文:
定理 trans_assoc
  条件: {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ)
  证明: by grind
-/
theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := by grind

/--
theorem `trans_cancel_left` / 定理 `trans_cancel_left`

English:
theorem trans_cancel_left
  given: (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ)
  proof: by
  grind

中文:
定理 trans_cancel_left
  条件: (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ)
  证明: by
  grind
-/
theorem trans_cancel_left (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ f = e.symm.trans g := by
  grind

/--
theorem `trans_cancel_right` / 定理 `trans_cancel_right`

English:
theorem trans_cancel_right
  given: (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ)
  proof: by
  grind

中文:
定理 trans_cancel_right
  条件: (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ)
  证明: by
  grind
-/
theorem trans_cancel_right (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ e = g.trans f.symm := by
  grind

/--
theorem `leftInverse_symm` / 定理 `leftInverse_symm`

English:
theorem leftInverse_symm
  given: (f : α ≃ β)
  statement: LeftInverse f.symm f
  proof: f.left_inv

中文:
定理 leftInverse_symm
  条件: (f : α ≃ β)
  结论: LeftInverse f.symm f
  证明: f.left_inv

Depends on / 依赖: f.left_inv, left_inv
-/
theorem leftInverse_symm (f : α ≃ β) : LeftInverse f.symm f := f.left_inv

/--
theorem `rightInverse_symm` / 定理 `rightInverse_symm`

English:
theorem rightInverse_symm
  given: (f : α ≃ β)
  statement: Function.RightInverse f.symm f
  proof: f.right_inv

中文:
定理 rightInverse_symm
  条件: (f : α ≃ β)
  结论: Function.RightInverse f.symm f
  证明: f.right_inv

Depends on / 依赖: f.right_inv, right_inv
-/
theorem rightInverse_symm (f : α ≃ β) : Function.RightInverse f.symm f := f.right_inv

/--
theorem `injective_comp` / 定理 `injective_comp`

English:
theorem injective_comp
  given: (e : α ≃ β) (f : β -> γ)
  statement: Injective (f ∘ e) ↔ Injective f
  proof: EquivLike.injective_comp e f

中文:
定理 injective_comp
  条件: (e : α ≃ β) (f : β -> γ)
  结论: Injective (f ∘ e) ↔ Injective f
  证明: EquivLike.injective_comp e f

Depends on / 依赖: EquivLike, EquivLike.injective_comp, injective_comp
-/
theorem injective_comp (e : α ≃ β) (f : β -> γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f

/--
theorem `comp_injective` / 定理 `comp_injective`

English:
theorem comp_injective
  given: (f : α -> β) (e : β ≃ γ)
  statement: Injective (e ∘ f) ↔ Injective f
  proof: EquivLike.comp_injective f e

中文:
定理 comp_injective
  条件: (f : α -> β) (e : β ≃ γ)
  结论: Injective (e ∘ f) ↔ Injective f
  证明: EquivLike.comp_injective f e

Depends on / 依赖: EquivLike, EquivLike.comp_injective, comp_injective
-/
theorem comp_injective (f : α -> β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e

/--
theorem `surjective_comp` / 定理 `surjective_comp`

English:
theorem surjective_comp
  given: (e : α ≃ β) (f : β -> γ)
  statement: Surjective (f ∘ e) ↔ Surjective f
  proof: EquivLike.surjective_comp e f

中文:
定理 surjective_comp
  条件: (e : α ≃ β) (f : β -> γ)
  结论: Surjective (f ∘ e) ↔ Surjective f
  证明: EquivLike.surjective_comp e f

Depends on / 依赖: EquivLike, EquivLike.surjective_comp, surjective_comp
-/
theorem surjective_comp (e : α ≃ β) (f : β -> γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f

/--
theorem `comp_surjective` / 定理 `comp_surjective`

English:
theorem comp_surjective
  given: (f : α -> β) (e : β ≃ γ)
  statement: Surjective (e ∘ f) ↔ Surjective f
  proof: EquivLike.comp_surjective f e

中文:
定理 comp_surjective
  条件: (f : α -> β) (e : β ≃ γ)
  结论: Surjective (e ∘ f) ↔ Surjective f
  证明: EquivLike.comp_surjective f e

Depends on / 依赖: EquivLike, EquivLike.comp_surjective, comp_surjective
-/
theorem comp_surjective (f : α -> β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e

/--
theorem `bijective_comp` / 定理 `bijective_comp`

English:
theorem bijective_comp
  given: (e : α ≃ β) (f : β -> γ)
  statement: Bijective (f ∘ e) ↔ Bijective f
  proof: EquivLike.bijective_comp e f

中文:
定理 bijective_comp
  条件: (e : α ≃ β) (f : β -> γ)
  结论: Bijective (f ∘ e) ↔ Bijective f
  证明: EquivLike.bijective_comp e f

Depends on / 依赖: EquivLike, EquivLike.bijective_comp, bijective_comp
-/
theorem bijective_comp (e : α ≃ β) (f : β -> γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f

/--
theorem `comp_bijective` / 定理 `comp_bijective`

English:
theorem comp_bijective
  given: (f : α -> β) (e : β ≃ γ)
  statement: Bijective (e ∘ f) ↔ Bijective f
  proof: EquivLike.comp_bijective f e

@[simp]

中文:
定理 comp_bijective
  条件: (f : α -> β) (e : β ≃ γ)
  结论: Bijective (e ∘ f) ↔ Bijective f
  证明: EquivLike.comp_bijective f e

@[simp]

Depends on / 依赖: EquivLike, EquivLike.comp_bijective, comp_bijective
-/
theorem comp_bijective (f : α -> β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e

@[simp]
/--
theorem `extend_apply` / 定理 `extend_apply`

English:
theorem extend_apply
  given: {f : α ≃ β} (g : α -> γ) (e' : β -> γ) (b : β)
  proof: by
  rw [← f.apply_symm_apply b]; rw [f.injective.extend_apply]; rw [apply_symm_apply]

中文:
定理 extend_apply
  条件: {f : α ≃ β} (g : α -> γ) (e' : β -> γ) (b : β)
  证明: by
  rw [← f.apply_symm_apply b]; rw [f.injective.extend_apply]; rw [apply_symm_apply]

Depends on / 依赖: apply_symm_apply, extend_apply, f.apply_symm_apply, f.injective.extend_apply, injective
-/
theorem extend_apply {f : α ≃ β} (g : α -> γ) (e' : β -> γ) (b : β) :
    extend f g e' b = g (f.symm b) := by
  rw [← f.apply_symm_apply b]; rw [f.injective.extend_apply]; rw [apply_symm_apply]

/--
Definition of `equivCongr` / `equivCongr` 的定义

English:
definition equivCongr
  signature: {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ)
  body: (ab.symm.trans ac).trans cd
invFun bd := ab.trans bd.trans cd.symm
  left_inv ac := by grind
  right_inv ac := by grind

中文:
定义 equivCongr
  签名: {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ)
  定义体: (ab.symm.trans ac).trans cd
invFun bd := ab.trans bd.trans cd.symm
  left_inv ac := by grind
  right_inv ac := by grind

Depends on / 依赖: ab.symm.trans
-/
def equivCongr {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) where
  toFun ac := (ab.symm.trans ac).trans cd
invFun bd := ab.trans bd.trans cd.symm
  left_inv ac := by grind
  right_inv ac := by grind

/--
theorem `equivCongr_apply_apply` / 定理 `equivCongr_apply_apply`

English:
theorem equivCongr_apply_apply
  given: {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x)
  proof: rfl

中文:
定理 equivCongr_apply_apply
  条件: {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x)
  证明: rfl
-/
@[simp, grind =] theorem equivCongr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) := rfl

/--
theorem `equivCongr_symm` / 定理 `equivCongr_symm`

English:
theorem equivCongr_symm
  given: {δ} (ab : α ≃ β) (cd : γ ≃ δ)
  proof: by ext; rfl

中文:
定理 equivCongr_symm
  条件: {δ} (ab : α ≃ β) (cd : γ ≃ δ)
  证明: by ext; rfl
-/
@[simp, grind =] theorem equivCongr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
    (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm := by ext; rfl

/--
theorem `equivCongr_refl` / 定理 `equivCongr_refl`

English:
theorem equivCongr_refl
  given: {α β}
  proof: by grind

中文:
定理 equivCongr_refl
  条件: {α β}
  证明: by grind
-/
@[simp] theorem equivCongr_refl {α β} :
    (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) := by grind

/--
theorem `equivCongr_trans` / 定理 `equivCongr_trans`

English:
theorem equivCongr_trans
  given: {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ)
  proof: by
  grind

中文:
定理 equivCongr_trans
  条件: {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ)
  证明: by
  grind
-/
@[simp] theorem equivCongr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) := by
  grind

/--
theorem `equivCongr_refl_left` / 定理 `equivCongr_refl_left`

English:
theorem equivCongr_refl_left
  given: {α β γ} (bg : β ≃ γ) (e : α ≃ β)
  proof: rfl

中文:
定理 equivCongr_refl_left
  条件: {α β γ} (bg : β ≃ γ) (e : α ≃ β)
  证明: rfl
-/
@[simp] theorem equivCongr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
    (Equiv.refl α).equivCongr bg e = e.trans bg := rfl

/--
theorem `equivCongr_refl_right` / 定理 `equivCongr_refl_right`

English:
theorem equivCongr_refl_right
  given: {α β} (ab e : α ≃ β)
  proof: rfl

中文:
定理 equivCongr_refl_right
  条件: {α β} (ab e : α ≃ β)
  证明: rfl
-/
@[simp] theorem equivCongr_refl_right {α β} (ab e : α ≃ β) :
    ab.equivCongr (Equiv.refl β) e = ab.symm.trans e := rfl
section permCongr

variable {α' β' : Type*} (e : α' ≃ β')

/--
Definition of `permCongr` / `permCongr` 的定义

English:
definition permCongr
  signature: : Perm α' ≃ Perm β'
  body: equivCongr e e

中文:
定义 permCongr
  签名: : Perm α' ≃ Perm β'
  定义体: equivCongr e e

Depends on / 依赖: equivCongr
-/
def permCongr : Perm α' ≃ Perm β' := equivCongr e e

/--
theorem `permCongr_def` / 定理 `permCongr_def`

English:
theorem permCongr_def
  given: (p : Equiv.Perm α')
  statement: e.permCongr p = (e.symm.trans p).trans e
  proof: rfl

中文:
定理 permCongr_def
  条件: (p : Equiv.Perm α')
  结论: e.permCongr p = (e.symm.trans p).trans e
  证明: rfl
-/
theorem permCongr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e := rfl

/--
theorem `permCongr_refl` / 定理 `permCongr_refl`

English:
theorem permCongr_refl
  statement: e.permCongr (Equiv.refl _) = Equiv.refl _
  proof: by
  simp [permCongr_def]

中文:
定理 permCongr_refl
  结论: e.permCongr (Equiv.refl _) = Equiv.refl _
  证明: by
  simp [permCongr_def]
-/
@[simp] theorem permCongr_refl : e.permCongr (Equiv.refl _) = Equiv.refl _ := by
  simp [permCongr_def]

/--
theorem `permCongr_symm` / 定理 `permCongr_symm`

English:
theorem permCongr_symm
  statement: e.permCongr.symm = e.symm.permCongr
  proof: rfl

中文:
定理 permCongr_symm
  结论: e.permCongr.symm = e.symm.permCongr
  证明: rfl
-/
@[simp, grind =] theorem permCongr_symm : e.permCongr.symm = e.symm.permCongr := rfl

/--
theorem `permCongr_apply` / 定理 `permCongr_apply`

English:
theorem permCongr_apply
  given: (p : Equiv.Perm α') (x)
  proof: rfl

中文:
定理 permCongr_apply
  条件: (p : Equiv.Perm α') (x)
  证明: rfl
-/
@[simp, grind =] theorem permCongr_apply (p : Equiv.Perm α') (x) :
    e.permCongr p x = e (p (e.symm x)) := rfl

/--
theorem `permCongr_symm_apply` / 定理 `permCongr_symm_apply`

English:
theorem permCongr_symm_apply
  given: (p : Equiv.Perm β') (x)
  proof: rfl

中文:
定理 permCongr_symm_apply
  条件: (p : Equiv.Perm β') (x)
  证明: rfl
-/
theorem permCongr_symm_apply (p : Equiv.Perm β') (x) :
    e.permCongr.symm p x = e.symm (p (e x)) := rfl

/--
theorem `permCongr_trans` / 定理 `permCongr_trans`

English:
theorem permCongr_trans
  given: (p p' : Equiv.Perm α')
  proof: by grind

中文:
定理 permCongr_trans
  条件: (p p' : Equiv.Perm α')
  证明: by grind
-/
theorem permCongr_trans (p p' : Equiv.Perm α') :
    (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') := by grind

end permCongr

/--
Definition of `equivOfIsEmpty` / `equivOfIsEmpty` 的定义

English:
definition equivOfIsEmpty
  signature: (α β : Sort*) [IsEmpty α] [IsEmpty β]
  body: ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

中文:
定义 equivOfIsEmpty
  签名: (α β : Sort*) [IsEmpty α] [IsEmpty β]
  定义体: ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

Depends on / 依赖: isEmptyElim
-/
def equivOfIsEmpty (α β : Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/--
Definition of `equivEmpty` / `equivEmpty` 的定义

English:
definition equivEmpty
  signature: (α : Sort u) [IsEmpty α]
  body: equivOfIsEmpty α _

中文:
定义 equivEmpty
  签名: (α : Sort u) [IsEmpty α]
  定义体: equivOfIsEmpty α _

Depends on / 依赖: equivOfIsEmpty
-/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty := equivOfIsEmpty α _

/--
Definition of `equivPEmpty` / `equivPEmpty` 的定义

English:
definition equivPEmpty
  signature: (α : Sort v) [IsEmpty α]
  body: equivOfIsEmpty α _

中文:
定义 equivPEmpty
  签名: (α : Sort v) [IsEmpty α]
  定义体: equivOfIsEmpty α _

Depends on / 依赖: equivOfIsEmpty
-/
def equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} := equivOfIsEmpty α _

/--
Definition of `equivEmptyEquiv` / `equivEmptyEquiv` 的定义

English:
definition equivEmptyEquiv
  signature: (α : Sort u)
  body: ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩

中文:
定义 equivEmptyEquiv
  签名: (α : Sort u)
  定义体: ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩

Depends on / 依赖: Function, Function.isEmpty, equivEmpty, isEmpty
-/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩

/--
Definition of `propEquivPEmpty` / `propEquivPEmpty` 的定义

English:
definition propEquivPEmpty
  signature: {p : Prop} (h : ¬p)
  body: @equivPEmpty p IsEmpty.prop_iff.2 h

中文:
定义 propEquivPEmpty
  签名: {p : 命题} (h : ¬p)
  定义体: @equivPEmpty p IsEmpty.prop_iff.2 h

Depends on / 依赖: IsEmpty, IsEmpty.prop_iff, equivPEmpty, prop_iff
-/
def propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty := @equivPEmpty p IsEmpty.prop_iff.2 h

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
@[simps (attr := grind =)]
/--
Definition of `ofUnique` / `ofUnique` 的定义

English:
definition ofUnique
  signature: (α β : Sort _) [Unique.{u} α] [Unique.{v} β]
  body: default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 ofUnique
  签名: (α β : Sort _) [Unique.{u} α] [Unique.{v} β]
  定义体: default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
-/
def ofUnique (α β : Sort _) [Unique.{u} α] [Unique.{v} β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` has a unique element, then it is equivalent to any `PUnit`. -/
@[simps! (attr := grind =)]
/--
Definition of `equivPUnit` / `equivPUnit` 的定义

English:
definition equivPUnit
  signature: (α : Sort u) [Unique α]
  body: ofUnique α _

中文:
定义 equivPUnit
  签名: (α : Sort u) [Unique α]
  定义体: ofUnique α _

Depends on / 依赖: ofUnique
-/
def equivPUnit (α : Sort u) [Unique α] : α ≃ PUnit.{v} := ofUnique α _

/--
Definition of `propEquivPUnit` / `propEquivPUnit` 的定义

English:
definition propEquivPUnit
  signature: {p : Prop} (h : p)
  body: @equivPUnit p uniqueProp h

中文:
定义 propEquivPUnit
  签名: {p : 命题} (h : p)
  定义体: @equivPUnit p uniqueProp h

Depends on / 依赖: equivPUnit, uniqueProp
-/
def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0} := @equivPUnit p uniqueProp h

/-- `ULift α` is equivalent to `α`. -/
@[simps (attr := grind =) -fullyApplied apply symm_apply]
/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: {α : Type v}
  body: ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩

中文:
定义 ulift
  签名: {α : 类型v}
  定义体: ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩
-/
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩

/-- `PLift α` is equivalent to `α`. -/
@[simps (attr := grind =) -fullyApplied apply symm_apply]
/--
Definition of `plift` / `plift` 的定义

English:
definition plift
  signature: : PLift α ≃ α
  body: ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩

中文:
定义 plift
  签名: : PLift α ≃ α
  定义体: ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩
-/
protected def plift : PLift α ≃ α := ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩

/--
Definition of `ofIff` / `ofIff` 的定义

English:
definition ofIff
  signature: {P Q : Prop} (h : P ↔ Q)
  body: ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩

中文:
定义 ofIff
  签名: {P Q : 命题} (h : P ↔ Q)
  定义体: ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩

Depends on / 依赖: h.mp, h.mpr
-/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q := ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[simps (attr := grind =) apply]
/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  body: e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := by grind
  right_inv f := by grind

中文:
定义 arrowCongr
  签名: {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  定义体: e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := by grind
  right_inv f := by grind
-/
def arrowCongr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ -> β₁) ≃ (α₂ -> β₂) where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := by grind
  right_inv f := by grind

/--
theorem `arrowCongr_comp` / 定理 `arrowCongr_comp`

English:
theorem arrowCongr_comp
  statement: {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
  proof: by grind

中文:
定理 arrowCongr_comp
  结论: {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
  证明: by grind
-/
theorem arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ -> β₁) (g : β₁ -> γ₁) :
    arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f := by grind

/--
theorem `arrowCongr_refl` / 定理 `arrowCongr_refl`

English:
theorem arrowCongr_refl
  given: {α β : Sort*}
  proof: rfl

中文:
定理 arrowCongr_refl
  条件: {α β : Sort*}
  证明: rfl
-/
@[simp] theorem arrowCongr_refl {α β : Sort*} :
    arrowCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α -> β) := rfl

/--
theorem `arrowCongr_trans` / 定理 `arrowCongr_trans`

English:
theorem arrowCongr_trans
  statement: {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
  proof: rfl

中文:
定理 arrowCongr_trans
  结论: {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
  证明: rfl
-/
@[simp] theorem arrowCongr_trans {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := rfl

/--
theorem `arrowCongr_symm` / 定理 `arrowCongr_symm`

English:
theorem arrowCongr_symm
  given: {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  proof: rfl

中文:
定理 arrowCongr_symm
  条件: {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  证明: rfl
-/
@[simp, grind =] theorem arrowCongr_symm {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := rfl

/-- A version of `Equiv.arrowCongr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `Equiv.arrowCongr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[simps! (attr := grind =) apply]
/--
Definition of `arrowCongr'` / `arrowCongr'` 的定义

English:
definition arrowCongr'
  signature: {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂)
  body: Equiv.arrowCongr hα hβ

中文:
定义 arrowCongr'
  签名: {α₁ β₁ α₂ β₂ : 类型} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂)
  定义体: Equiv.arrowCongr hα hβ

Depends on / 依赖: Equiv.arrowCongr, arrowCongr
-/
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ -> β₁) ≃ (α₂ -> β₂) :=
  Equiv.arrowCongr hα hβ

/--
theorem `arrowCongr'_refl` / 定理 `arrowCongr'_refl`

English:
theorem arrowCongr'_refl
  given: {α β : Type*}
  proof: rfl

中文:
定理 arrowCongr'_refl
  条件: {α β : 类型}
  证明: rfl
-/
@[simp] theorem arrowCongr'_refl {α β : Type*} :
    arrowCongr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α -> β) := rfl

/--
theorem `arrowCongr'_trans` / 定理 `arrowCongr'_trans`

English:
theorem arrowCongr'_trans
  statement: {α₁ α₂ β₁ β₂ α₃ β₃ : Type*}
  proof: rfl

中文:
定理 arrowCongr'_trans
  结论: {α₁ α₂ β₁ β₂ α₃ β₃ : 类型}
  证明: rfl
-/
@[simp] theorem arrowCongr'_trans {α₁ α₂ β₁ β₂ α₃ β₃ : Type*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

/--
theorem `arrowCongr'_symm` / 定理 `arrowCongr'_symm`

English:
theorem arrowCongr'_symm
  given: {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  proof: rfl

中文:
定理 arrowCongr'_symm
  条件: {α₁ α₂ β₁ β₂ : 类型} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  证明: rfl
-/
@[simp, grind =] theorem arrowCongr'_symm {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm := rfl

/--
Definition of `conj` / `conj` 的定义

English:
definition conj
  signature: (e : α ≃ β)
  body: arrowCongr e e

中文:
定义 conj
  签名: (e : α ≃ β)
  定义体: arrowCongr e e
-/
@[simps! (attr := grind =) apply] def conj (e : α ≃ β) : (α -> α) ≃ (β -> β) := arrowCongr e e

/--
theorem `conj_refl` / 定理 `conj_refl`

English:
theorem conj_refl
  statement: conj (Equiv.refl α) = Equiv.refl (α -> α)
  proof: rfl

中文:
定理 conj_refl
  结论: conj (Equiv.refl α) = Equiv.refl (α -> α)
  证明: rfl
-/
@[simp] theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α -> α) := rfl

/--
theorem `conj_symm` / 定理 `conj_symm`

English:
theorem conj_symm
  given: (e : α ≃ β)
  statement: e.conj.symm = e.symm.conj
  proof: rfl

中文:
定理 conj_symm
  条件: (e : α ≃ β)
  结论: e.conj.symm = e.symm.conj
  证明: rfl
-/
@[simp, grind =] theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj := rfl

/--
theorem `conj_trans` / 定理 `conj_trans`

English:
theorem conj_trans
  given: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  proof: rfl

中文:
定理 conj_trans
  条件: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  证明: rfl
-/
@[simp] theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (e₁.trans e₂).conj = e₁.conj.trans e₂.conj := rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := fun x ↦ x`. This causes nontermination.
/--
theorem `conj_comp` / 定理 `conj_comp`

English:
theorem conj_comp
  given: (e : α ≃ β) (f₁ f₂ : α -> α)
  statement: e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂
  proof: by
  apply arrowCongr_comp

中文:
定理 conj_comp
  条件: (e : α ≃ β) (f₁ f₂ : α -> α)
  结论: e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂
  证明: by
  apply arrowCongr_comp

Depends on / 依赖: arrowCongr_comp
-/
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α -> α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by
  apply arrowCongr_comp

/--
theorem `eq_comp_symm` / 定理 `eq_comp_symm`

English:
theorem eq_comp_symm
  given: {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ)
  statement: f = g ∘ e.symm ↔ f ∘ e = g
  proof: (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm

中文:
定理 eq_comp_symm
  条件: {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ)
  结论: f = g ∘ e.symm ↔ f ∘ e = g
  证明: (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm

Depends on / 依赖: Equiv.refl, arrowCongr, e.arrowCongr, symm_apply_eq, symm_apply_eq.symm
-/
theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm

/--
theorem `comp_symm_eq` / 定理 `comp_symm_eq`

English:
theorem comp_symm_eq
  given: {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ)
  statement: g ∘ e.symm = f ↔ g = f ∘ e
  proof: (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm

中文:
定理 comp_symm_eq
  条件: {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ)
  结论: g ∘ e.symm = f ↔ g = f ∘ e
  证明: (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm

Depends on / 依赖: Equiv.refl, arrowCongr, e.arrowCongr, eq_symm_apply, eq_symm_apply.symm
-/
theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm

/--
theorem `eq_symm_comp` / 定理 `eq_symm_comp`

English:
theorem eq_symm_comp
  given: {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β)
  statement: f = e.symm ∘ g ↔ e ∘ f = g
  proof: ((Equiv.refl γ).arrowCongr e).eq_symm_apply

中文:
定理 eq_symm_comp
  条件: {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β)
  结论: f = e.symm ∘ g ↔ e ∘ f = g
  证明: ((Equiv.refl γ).arrowCongr e).eq_symm_apply

Depends on / 依赖: Equiv.refl, arrowCongr, eq_symm_apply
-/
theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equiv.refl γ).arrowCongr e).eq_symm_apply

/--
theorem `symm_comp_eq` / 定理 `symm_comp_eq`

English:
theorem symm_comp_eq
  given: {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β)
  statement: e.symm ∘ g = f ↔ g = e ∘ f
  proof: ((Equiv.refl γ).arrowCongr e).symm_apply_eq

中文:
定理 symm_comp_eq
  条件: {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β)
  结论: e.symm ∘ g = f ↔ g = e ∘ f
  证明: ((Equiv.refl γ).arrowCongr e).symm_apply_eq

Depends on / 依赖: Equiv.refl, arrowCongr, symm_apply_eq
-/
theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equiv.refl γ).arrowCongr e).symm_apply_eq

/--
theorem `trans_eq_refl_iff_eq_symm` / 定理 `trans_eq_refl_iff_eq_symm`

English:
theorem trans_eq_refl_iff_eq_symm
  given: {f : α ≃ β} {g : β ≃ α}
  proof: by
  rw [← Equiv.coe_inj]; rw [coe_trans]; rw [coe_refl]; rw [← eq_symm_comp]; rw [comp_id]; rw [Equiv.coe_inj]

中文:
定理 trans_eq_refl_iff_eq_symm
  条件: {f : α ≃ β} {g : β ≃ α}
  证明: by
  rw [← Equiv.coe_inj]; rw [coe_trans]; rw [coe_refl]; rw [← eq_symm_comp]; rw [comp_id]; rw [Equiv.coe_inj]

Depends on / 依赖: Equiv.coe_inj, coe_inj, coe_refl, coe_trans, comp_id, eq_symm_comp
-/
theorem trans_eq_refl_iff_eq_symm {f : α ≃ β} {g : β ≃ α} :
    f.trans g = Equiv.refl α ↔ f = g.symm := by
  rw [← Equiv.coe_inj]; rw [coe_trans]; rw [coe_refl]; rw [← eq_symm_comp]; rw [comp_id]; rw [Equiv.coe_inj]

/--
theorem `trans_eq_refl_iff_symm_eq` / 定理 `trans_eq_refl_iff_symm_eq`

English:
theorem trans_eq_refl_iff_symm_eq
  given: {f : α ≃ β} {g : β ≃ α}
  proof: by
  rw [trans_eq_refl_iff_eq_symm]
  exact ⟨fun h => h ▸ rfl, fun h => h ▸ rfl⟩

中文:
定理 trans_eq_refl_iff_symm_eq
  条件: {f : α ≃ β} {g : β ≃ α}
  证明: by
  rw [trans_eq_refl_iff_eq_symm]
  exact ⟨fun h => h ▸ rfl, fun h => h ▸ rfl⟩

Depends on / 依赖: trans_eq_refl_iff_eq_symm
-/
theorem trans_eq_refl_iff_symm_eq {f : α ≃ β} {g : β ≃ α} :
    f.trans g = Equiv.refl α ↔ f.symm = g := by
  rw [trans_eq_refl_iff_eq_symm]
  exact ⟨fun h => h ▸ rfl, fun h => h ▸ rfl⟩

/--
theorem `eq_symm_iff_trans_eq_refl` / 定理 `eq_symm_iff_trans_eq_refl`

English:
theorem eq_symm_iff_trans_eq_refl
  given: {f : α ≃ β} {g : β ≃ α}
  proof: trans_eq_refl_iff_eq_symm.symm

中文:
定理 eq_symm_iff_trans_eq_refl
  条件: {f : α ≃ β} {g : β ≃ α}
  证明: trans_eq_refl_iff_eq_symm.symm

Depends on / 依赖: trans_eq_refl_iff_eq_symm, trans_eq_refl_iff_eq_symm.symm
-/
theorem eq_symm_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} :
    f = g.symm ↔ f.trans g = Equiv.refl α :=
  trans_eq_refl_iff_eq_symm.symm

/--
theorem `symm_eq_iff_trans_eq_refl` / 定理 `symm_eq_iff_trans_eq_refl`

English:
theorem symm_eq_iff_trans_eq_refl
  given: {f : α ≃ β} {g : β ≃ α}
  proof: trans_eq_refl_iff_symm_eq.symm

中文:
定理 symm_eq_iff_trans_eq_refl
  条件: {f : α ≃ β} {g : β ≃ α}
  证明: trans_eq_refl_iff_symm_eq.symm

Depends on / 依赖: trans_eq_refl_iff_symm_eq, trans_eq_refl_iff_symm_eq.symm
-/
theorem symm_eq_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} :
    f.symm = g ↔ f.trans g = Equiv.refl α :=
  trans_eq_refl_iff_symm_eq.symm

/--
Definition of `punitEquivPUnit` / `punitEquivPUnit` 的定义

English:
definition punitEquivPUnit
  signature: : PUnit.{v} ≃ PUnit.{w} where
  body: .unit
  invFun _ := .unit

中文:
定义 punitEquivPUnit
  签名: : PUnit.{v} ≃ PUnit.{w} where
  定义体: .unit
  invFun _ := .unit
-/
def punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} where
  toFun _ := .unit
  invFun _ := .unit

/--
Definition of `propEquivBool` / `propEquivBool` 的定义

English:
definition propEquivBool
  signature: : Prop ≃ Bool where
  body: @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp
  right_inv b := by simp

中文:
定义 propEquivBool
  签名: : 命题 ≃ 布尔 where
  定义体: @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp
  right_inv b := by simp

Depends on / 依赖: Classical, Classical.propDecidable, propDecidable
-/
noncomputable def propEquivBool : Prop ≃ Bool where
  toFun p := @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp
  right_inv b := by simp

section

/--
Definition of `arrowPUnitEquivPUnit` / `arrowPUnitEquivPUnit` 的定义

English:
definition arrowPUnitEquivPUnit
  signature: (α : Sort*)
  body: .unit
  invFun _ _ := .unit

中文:
定义 arrowPUnitEquivPUnit
  签名: (α : Sort*)
  定义体: .unit
  invFun _ _ := .unit
-/
def arrowPUnitEquivPUnit (α : Sort*) : (α -> PUnit.{v}) ≃ PUnit.{w} where
  toFun _ := .unit
  invFun _ _ := .unit

/-- The equivalence `(∀ i, β i) ≃ β ⋆` when the domain of `β` only contains `⋆` -/
@[simps (attr := grind =) -fullyApplied]
/--
Definition of `piUnique` / `piUnique` 的定义

English:
definition piUnique
  signature: [Unique α] (β : α -> Sort*)
  body: f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl

中文:
定义 piUnique
  签名: [Unique α] (β : α -> Sort*)
  定义体: f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl
-/
def piUnique [Unique α] (β : α -> Sort*) : (forall i, β i) ≃ β default where
  toFun f := f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps! (attr := grind =) -fullyApplied apply symm_apply]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: (α β) [Unique.{u} α]
  body: piUnique _

中文:
定义 funUnique
  签名: (α β) [Unique.{u} α]
  定义体: piUnique _

Depends on / 依赖: piUnique
-/
def funUnique (α β) [Unique.{u} α] : (α -> β) ≃ β := piUnique _

/--
Definition of `punitArrowEquiv` / `punitArrowEquiv` 的定义

English:
definition punitArrowEquiv
  signature: (α : Sort*)
  body: funUnique PUnit.{u} α

中文:
定义 punitArrowEquiv
  签名: (α : Sort*)
  定义体: funUnique PUnit.{u} α

Depends on / 依赖: funUnique
-/
def punitArrowEquiv (α : Sort*) : (PUnit.{u} -> α) ≃ α := funUnique PUnit.{u} α

/--
Definition of `trueArrowEquiv` / `trueArrowEquiv` 的定义

English:
definition trueArrowEquiv
  signature: (α : Sort*)
  body: funUnique _ _

中文:
定义 trueArrowEquiv
  签名: (α : Sort*)
  定义体: funUnique _ _

Depends on / 依赖: funUnique
-/
def trueArrowEquiv (α : Sort*) : (True -> α) ≃ α := funUnique _ _

/--
Definition of `arrowPUnitOfIsEmpty` / `arrowPUnitOfIsEmpty` 的定义

English:
definition arrowPUnitOfIsEmpty
  signature: (α β : Sort*) [IsEmpty α]
  body: PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim

中文:
定义 arrowPUnitOfIsEmpty
  签名: (α β : Sort*) [IsEmpty α]
  定义体: PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim

Depends on / 依赖: PUnit.unit
-/
def arrowPUnitOfIsEmpty (α β : Sort*) [IsEmpty α] : (α -> β) ≃ PUnit.{u} where
  toFun _ := PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim

/--
Definition of `emptyArrowEquivPUnit` / `emptyArrowEquivPUnit` 的定义

English:
definition emptyArrowEquivPUnit
  signature: (α : Sort*)
  body: arrowPUnitOfIsEmpty _ _

中文:
定义 emptyArrowEquivPUnit
  签名: (α : Sort*)
  定义体: arrowPUnitOfIsEmpty _ _

Depends on / 依赖: arrowPUnitOfIsEmpty
-/
def emptyArrowEquivPUnit (α : Sort*) : (Empty -> α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

/--
Definition of `pemptyArrowEquivPUnit` / `pemptyArrowEquivPUnit` 的定义

English:
definition pemptyArrowEquivPUnit
  signature: (α : Sort*)
  body: arrowPUnitOfIsEmpty _ _

中文:
定义 pemptyArrowEquivPUnit
  签名: (α : Sort*)
  定义体: arrowPUnitOfIsEmpty _ _

Depends on / 依赖: arrowPUnitOfIsEmpty
-/
def pemptyArrowEquivPUnit (α : Sort*) : (PEmpty -> α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

/--
Definition of `falseArrowEquivPUnit` / `falseArrowEquivPUnit` 的定义

English:
definition falseArrowEquivPUnit
  signature: (α : Sort*)
  body: arrowPUnitOfIsEmpty _ _

中文:
定义 falseArrowEquivPUnit
  签名: (α : Sort*)
  定义体: arrowPUnitOfIsEmpty _ _

Depends on / 依赖: arrowPUnitOfIsEmpty
-/
def falseArrowEquivPUnit (α : Sort*) : (False -> α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

end

section

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
/--
Definition of `psigmaEquivSigma` / `psigmaEquivSigma` 的定义

English:
definition psigmaEquivSigma
  signature: {α} (β : α -> Type*)
  body: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

中文:
定义 psigmaEquivSigma
  签名: {α} (β : α -> 类型)
  定义体: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
-/
def psigmaEquivSigma {α} (β : α -> Type*) : (Σ' i, β i) ≃ Σ i, β i where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
/--
Definition of `psigmaEquivSigmaPLift` / `psigmaEquivSigmaPLift` 的定义

English:
definition psigmaEquivSigmaPLift
  signature: {α} (β : α -> Sort*)
  body: ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩

中文:
定义 psigmaEquivSigmaPLift
  签名: {α} (β : α -> Sort*)
  定义体: ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩

Depends on / 依赖: PLift.up
-/
def psigmaEquivSigmaPLift {α} (β : α -> Sort*) : (Σ' i, β i) ≃ Σ i : PLift α, PLift (β i.down) where
  toFun a := ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps (attr := grind =) apply]
/--
Definition of `psigmaCongrRight` / `psigmaCongrRight` 的定义

English:
definition psigmaCongrRight
  signature: {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a)
  body: ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind

中文:
定义 psigmaCongrRight
  签名: {β₁ β₂ : α -> Sort*} (F : 对任意 a, β₁ a ≃ β₂ a)
  定义体: ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind
-/
def psigmaCongrRight {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind

/--
theorem `psigmaCongrRight_trans` / 定理 `psigmaCongrRight_trans`

English:
theorem psigmaCongrRight_trans
  statement: {α} {β₁ β₂ β₃ : α -> Sort*}
  proof: rfl

@[grind =]

中文:
定理 psigmaCongrRight_trans
  结论: {α} {β₁ β₂ β₃ : α -> Sort*}
  证明: rfl

@[grind =]
-/
theorem psigmaCongrRight_trans {α} {β₁ β₂ β₃ : α -> Sort*}
    (F : forall a, β₁ a ≃ β₂ a) (G : forall a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) =
      psigmaCongrRight fun a => (F a).trans (G a) := rfl

@[grind =]
/--
theorem `psigmaCongrRight_symm` / 定理 `psigmaCongrRight_symm`

English:
theorem psigmaCongrRight_symm
  given: {α} {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a)
  proof: rfl

@[simp]

中文:
定理 psigmaCongrRight_symm
  条件: {α} {β₁ β₂ : α -> Sort*} (F : 对任意 a, β₁ a ≃ β₂ a)
  证明: rfl

@[simp]
-/
theorem psigmaCongrRight_symm {α} {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm := rfl

@[simp]
/--
theorem `psigmaCongrRight_refl` / 定理 `psigmaCongrRight_refl`

English:
theorem psigmaCongrRight_refl
  given: {α} {β : α -> Sort*}
  proof: rfl

中文:
定理 psigmaCongrRight_refl
  条件: {α} {β : α -> Sort*}
  证明: rfl
-/
theorem psigmaCongrRight_refl {α} {β : α -> Sort*} :
    (psigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ' a, β a) := rfl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps (attr := grind =) apply]
/--
Definition of `sigmaCongrRight` / `sigmaCongrRight` 的定义

English:
definition sigmaCongrRight
  signature: {α} {β₁ β₂ : α -> Type*} (F : forall a, β₁ a ≃ β₂ a)
  body: ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind

中文:
定义 sigmaCongrRight
  签名: {α} {β₁ β₂ : α -> 类型} (F : 对任意 a, β₁ a ≃ β₂ a)
  定义体: ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind
-/
def sigmaCongrRight {α} {β₁ β₂ : α -> Type*} (F : forall a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind

/--
theorem `sigmaCongrRight_trans` / 定理 `sigmaCongrRight_trans`

English:
theorem sigmaCongrRight_trans
  statement: {α} {β₁ β₂ β₃ : α -> Type*}
  proof: rfl

@[grind =]

中文:
定理 sigmaCongrRight_trans
  结论: {α} {β₁ β₂ β₃ : α -> 类型}
  证明: rfl

@[grind =]
-/
theorem sigmaCongrRight_trans {α} {β₁ β₂ β₃ : α -> Type*}
    (F : forall a, β₁ a ≃ β₂ a) (G : forall a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) =
      sigmaCongrRight fun a => (F a).trans (G a) := rfl

@[grind =]
/--
theorem `sigmaCongrRight_symm` / 定理 `sigmaCongrRight_symm`

English:
theorem sigmaCongrRight_symm
  given: {α} {β₁ β₂ : α -> Type*} (F : forall a, β₁ a ≃ β₂ a)
  proof: rfl

@[simp]

中文:
定理 sigmaCongrRight_symm
  条件: {α} {β₁ β₂ : α -> 类型} (F : 对任意 a, β₁ a ≃ β₂ a)
  证明: rfl

@[simp]
-/
theorem sigmaCongrRight_symm {α} {β₁ β₂ : α -> Type*} (F : forall a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm := rfl

@[simp]
/--
theorem `sigmaCongrRight_refl` / 定理 `sigmaCongrRight_refl`

English:
theorem sigmaCongrRight_refl
  given: {α} {β : α -> Type*}
  proof: rfl

中文:
定理 sigmaCongrRight_refl
  条件: {α} {β : α -> 类型}
  证明: rfl
-/
theorem sigmaCongrRight_refl {α} {β : α -> Type*} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) := rfl

/--
Definition of `psigmaEquivSubtype` / `psigmaEquivSubtype` 的定义

English:
definition psigmaEquivSubtype
  signature: {α : Type v} (P : α -> Prop)
  body: ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

中文:
定义 psigmaEquivSubtype
  签名: {α : 类型v} (P : α -> 命题)
  定义体: ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
-/
def psigmaEquivSubtype {α : Type v} (P : α -> Prop) : (Σ' i, P i) ≃ Subtype P where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

/--
Definition of `sigmaPLiftEquivSubtype` / `sigmaPLiftEquivSubtype` 的定义

English:
definition sigmaPLiftEquivSubtype
  signature: {α : Type v} (P : α -> Prop)
  body: ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)

中文:
定义 sigmaPLiftEquivSubtype
  签名: {α : 类型v} (P : α -> 命题)
  定义体: ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)

Depends on / 依赖: Equiv.plift, psigmaCongrRight, psigmaEquivSigma, psigmaEquivSubtype, symm.trans
-/
def sigmaPLiftEquivSubtype {α : Type v} (P : α -> Prop) : (Σ i, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)

/--
Definition of `sigmaULiftPLiftEquivSubtype` / `sigmaULiftPLiftEquivSubtype` 的定义

English:
definition sigmaULiftPLiftEquivSubtype
  signature: {α : Type v} (P : α -> Prop)
  body: (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)

中文:
定义 sigmaULiftPLiftEquivSubtype
  签名: {α : 类型v} (P : α -> 命题)
  定义体: (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)

Depends on / 依赖: Equiv.ulift, sigmaCongrRight, sigmaPLiftEquivSubtype
-/
def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α -> Prop) :
    (Σ i, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)

namespace Perm

/--
Definition of `sigmaCongrRight` / `sigmaCongrRight` 的定义

English:
abbreviation sigmaCongrRight
  signature: {α} {β : α -> Sort _} (F : forall a, Perm (β a))
  body: Equiv.sigmaCongrRight F

中文:
缩写 sigmaCongrRight
  签名: {α} {β : α -> Sort _} (F : 对任意 a, Perm (β a))
  定义体: Equiv.sigmaCongrRight F

Depends on / 依赖: Equiv.sigmaCongrRight, sigmaCongrRight
-/
abbrev sigmaCongrRight {α} {β : α -> Sort _} (F : forall a, Perm (β a)) : Perm (Σ a, β a) :=
  Equiv.sigmaCongrRight F

/--
theorem `sigmaCongrRight_trans` / 定理 `sigmaCongrRight_trans`

English:
theorem sigmaCongrRight_trans
  statement: {α} {β : α -> Sort _}
  proof: rfl

中文:
定理 sigmaCongrRight_trans
  结论: {α} {β : α -> Sort _}
  证明: rfl
-/
@[simp] theorem sigmaCongrRight_trans {α} {β : α -> Sort _}
    (F : forall a, Perm (β a)) (G : forall a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  rfl

/--
theorem `sigmaCongrRight_symm` / 定理 `sigmaCongrRight_symm`

English:
theorem sigmaCongrRight_symm
  given: {α} {β : α -> Sort _} (F : forall a, Perm (β a))
  proof: rfl

中文:
定理 sigmaCongrRight_symm
  条件: {α} {β : α -> Sort _} (F : 对任意 a, Perm (β a))
  证明: rfl
-/
@[simp] theorem sigmaCongrRight_symm {α} {β : α -> Sort _} (F : forall a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  rfl

/--
theorem `sigmaCongrRight_refl` / 定理 `sigmaCongrRight_refl`

English:
theorem sigmaCongrRight_refl
  given: {α} {β : α -> Sort _}
  proof: rfl

中文:
定理 sigmaCongrRight_refl
  条件: {α} {β : α -> Sort _}
  证明: rfl
-/
@[simp] theorem sigmaCongrRight_refl {α} {β : α -> Sort _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) :=
  rfl

end Perm

/-- `Function.swap` as an equivalence. -/
@[simps (attr := grind =) -fullyApplied]
/--
Definition of `functionSwap` / `functionSwap` 的定义

English:
definition functionSwap
  signature: (α β : Sort*) (γ : α -> β -> Sort*)
  body: Function.swap
  invFun := Function.swap

中文:
定义 functionSwap
  签名: (α β : Sort*) (γ : α -> β -> Sort*)
  定义体: Function.swap
  invFun := Function.swap

Depends on / 依赖: Function, Function.swap
-/
def functionSwap (α β : Sort*) (γ : α -> β -> Sort*) :
    ((a : α) -> (b : β) -> γ a b) ≃ ((b : β) -> (a : α) -> γ a b) where
  toFun := Function.swap
  invFun := Function.swap

/--
theorem `_root_.Function.swap_bijective` / 定理 `_root_.Function.swap_bijective`

English:
theorem _root_.Function.swap_bijective
  given: {α β : Sort*} {γ : α -> β -> Sort*}
  proof: .bijective functionSwap _ _ _

中文:
定理 _root_.Function.swap_bijective
  条件: {α β : Sort*} {γ : α -> β -> Sort*}
  证明: .bijective functionSwap _ _ _

Depends on / 依赖: bijective, functionSwap
-/
theorem _root_.Function.swap_bijective {α β : Sort*} {γ : α -> β -> Sort*} :
    Function.Bijective (@Function.swap _ _ γ) :=
.bijective functionSwap _ _ _

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps (attr := grind =) apply]
/--
Definition of `sigmaCongrLeft` / `sigmaCongrLeft` 的定义

English:
definition sigmaCongrLeft
  signature: {α₁ α₂ : Type*} {β : α₂ -> Sort _} (e : α₁ ≃ α₂)
  body: ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  left_inv := fun ⟨a, b⟩ => by simp
  right_inv := fun ⟨a, b⟩ => by simp

中文:
定义 sigmaCongrLeft
  签名: {α₁ α₂ : 类型} {β : α₂ -> Sort _} (e : α₁ ≃ α₂)
  定义体: ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  left_inv := fun ⟨a, b⟩ => by simp
  right_inv := fun ⟨a, b⟩ => by simp
-/
def sigmaCongrLeft {α₁ α₂ : Type*} {β : α₂ -> Sort _} (e : α₁ ≃ α₂) :
    (Σ a : α₁, β (e a)) ≃ Σ a : α₂, β a where
  toFun a := ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  left_inv := fun ⟨a, b⟩ => by simp
  right_inv := fun ⟨a, b⟩ => by simp

/--
Definition of `sigmaCongrLeft'` / `sigmaCongrLeft'` 的定义

English:
definition sigmaCongrLeft'
  signature: {α₁ α₂} {β : α₁ -> Sort _} (f : α₁ ≃ α₂)
  body: (sigmaCongrLeft f.symm).symm

中文:
定义 sigmaCongrLeft'
  签名: {α₁ α₂} {β : α₁ -> Sort _} (f : α₁ ≃ α₂)
  定义体: (sigmaCongrLeft f.symm).symm

Depends on / 依赖: f.symm, sigmaCongrLeft
-/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ -> Sort _} (f : α₁ ≃ α₂) :
    (Σ a : α₁, β a) ≃ Σ a : α₂, β (f.symm a) := (sigmaCongrLeft f.symm).symm

/--
Definition of `sigmaCongr` / `sigmaCongr` 的定义

English:
definition sigmaCongr
  signature: {α₁ α₂} {β₁ : α₁ -> Sort _} {β₂ : α₂ -> Sort _} (f : α₁ ≃ α₂)
  body: (sigmaCongrRight F).trans (sigmaCongrLeft f)

中文:
定义 sigmaCongr
  签名: {α₁ α₂} {β₁ : α₁ -> Sort _} {β₂ : α₂ -> Sort _} (f : α₁ ≃ α₂)
  定义体: (sigmaCongrRight F).trans (sigmaCongrLeft f)

Depends on / 依赖: sigmaCongrLeft, sigmaCongrRight
-/
def sigmaCongr {α₁ α₂} {β₁ : α₁ -> Sort _} {β₂ : α₂ -> Sort _} (f : α₁ ≃ α₂)
    (F : forall a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)

/-- `Sigma` type with a constant fiber is equivalent to the product. -/
@[simps (attr := mfld_simps, grind =) apply symm_apply]
/--
Definition of `sigmaEquivProd` / `sigmaEquivProd` 的定义

English:
definition sigmaEquivProd
  signature: (α β : Type*)
  body: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

中文:
定义 sigmaEquivProd
  签名: (α β : 类型)
  定义体: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
-/
def sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≃ α × β where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/--
Definition of `sigmaEquivProdOfEquiv` / `sigmaEquivProdOfEquiv` 的定义

English:
definition sigmaEquivProdOfEquiv
  signature: {α β} {β₁ : α -> Sort _} (F : forall a, β₁ a ≃ β)
  body: (sigmaCongrRight F).trans (sigmaEquivProd α β)

中文:
定义 sigmaEquivProdOfEquiv
  签名: {α β} {β₁ : α -> Sort _} (F : 对任意 a, β₁ a ≃ β)
  定义体: (sigmaCongrRight F).trans (sigmaEquivProd α β)

Depends on / 依赖: sigmaCongrRight, sigmaEquivProd
-/
def sigmaEquivProdOfEquiv {α β} {β₁ : α -> Sort _} (F : forall a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)

/--
Definition of `sigmaAssoc` / `sigmaAssoc` 的定义

English:
definition sigmaAssoc
  signature: {α : Type*} {β : α -> Type*} (γ : forall a : α, β a -> Type*)
  body: ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

中文:
定义 sigmaAssoc
  签名: {α : 类型} {β : α -> 类型} (γ : 对任意 a : α, β a -> 类型)
  定义体: ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
-/
def sigmaAssoc {α : Type*} {β : α -> Type*} (γ : forall a : α, β a -> Type*) :
    (Σ ab : Σ a : α, β a, γ ab.1 ab.2) ≃ Σ a : α, Σ b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/--
Definition of `pSigmaAssoc` / `pSigmaAssoc` 的定义

English:
definition pSigmaAssoc
  signature: {α : Sort*} {β : α -> Sort*} (γ : forall a : α, β a -> Sort*)
  body: ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

中文:
定义 pSigmaAssoc
  签名: {α : Sort*} {β : α -> Sort*} (γ : 对任意 a : α, β a -> Sort*)
  定义体: ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
-/
def pSigmaAssoc {α : Sort*} {β : α -> Sort*} (γ : forall a : α, β a -> Sort*) :
    (Σ' ab : Σ' a : α, β a, γ ab.1 ab.2) ≃ Σ' a : α, Σ' b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

end

variable {p : α -> Prop} {q : β -> Prop} (e : α ≃ β)

/--
lemma `forall_congr_right` / 引理 `forall_congr_right`

English:
lemma forall_congr_right
  statement: (forall a, q (e a)) ↔ forall b, q b
  proof: ⟨fun h a => by simpa using h (e.symm a), fun h _ => h _⟩

中文:
引理 forall_congr_right
  结论: (对任意 a, q (e a)) ↔ 对任意 b, q b
  证明: ⟨fun h a => by simpa using h (e.symm a), fun h _ => h _⟩
-/
protected lemma forall_congr_right : (forall a, q (e a)) ↔ forall b, q b :=
  ⟨fun h a => by simpa using h (e.symm a), fun h _ => h _⟩

/--
lemma `forall_congr_left` / 引理 `forall_congr_left`

English:
lemma forall_congr_left
  statement: (forall a, p a) ↔ forall b, p (e.symm b)
  proof: e.symm.forall_congr_right.symm

中文:
引理 forall_congr_left
  结论: (对任意 a, p a) ↔ 对任意 b, p (e.symm b)
  证明: e.symm.forall_congr_right.symm
-/
protected lemma forall_congr_left : (forall a, p a) ↔ forall b, p (e.symm b) :=
  e.symm.forall_congr_right.symm

/--
lemma `forall_congr` / 引理 `forall_congr`

English:
lemma forall_congr
  given: (h : forall a, p a ↔ q (e a))
  statement: (forall a, p a) ↔ forall b, q b
  proof: e.forall_congr_left.trans (by simp [h])

中文:
引理 forall_congr
  条件: (h : 对任意 a, p a ↔ q (e a))
  结论: (对任意 a, p a) ↔ 对任意 b, q b
  证明: e.forall_congr_left.trans (by simp [h])
-/
protected lemma forall_congr (h : forall a, p a ↔ q (e a)) : (forall a, p a) ↔ forall b, q b :=
  e.forall_congr_left.trans (by simp [h])

/--
lemma `forall_congr'` / 引理 `forall_congr'`

English:
lemma forall_congr'
  given: (h : forall b, p (e.symm b) ↔ q b)
  statement: (forall a, p a) ↔ forall b, q b
  proof: e.forall_congr_left.trans (by simp [h])

中文:
引理 forall_congr'
  条件: (h : 对任意 b, p (e.symm b) ↔ q b)
  结论: (对任意 a, p a) ↔ 对任意 b, q b
  证明: e.forall_congr_left.trans (by simp [h])
-/
protected lemma forall_congr' (h : forall b, p (e.symm b) ↔ q b) : (forall a, p a) ↔ forall b, q b :=
  e.forall_congr_left.trans (by simp [h])

/--
lemma `exists_congr_right` / 引理 `exists_congr_right`

English:
lemma exists_congr_right
  statement: (exists a, q (e a)) ↔ exists b, q b
  proof: ⟨fun ⟨_, h⟩ => ⟨_, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by simpa using h⟩⟩

中文:
引理 exists_congr_right
  结论: (存在 a, q (e a)) ↔ 存在 b, q b
  证明: ⟨fun ⟨_, h⟩ => ⟨_, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by simpa using h⟩⟩
-/
protected lemma exists_congr_right : (exists a, q (e a)) ↔ exists b, q b :=
  ⟨fun ⟨_, h⟩ => ⟨_, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by simpa using h⟩⟩

/--
lemma `exists_congr_left` / 引理 `exists_congr_left`

English:
lemma exists_congr_left
  statement: (exists a, p a) ↔ exists b, p (e.symm b)
  proof: e.symm.exists_congr_right.symm

中文:
引理 exists_congr_left
  结论: (存在 a, p a) ↔ 存在 b, p (e.symm b)
  证明: e.symm.exists_congr_right.symm
-/
protected lemma exists_congr_left : (exists a, p a) ↔ exists b, p (e.symm b) :=
  e.symm.exists_congr_right.symm

/--
lemma `exists_congr` / 引理 `exists_congr`

English:
lemma exists_congr
  given: (h : forall a, p a ↔ q (e a))
  statement: (exists a, p a) ↔ exists b, q b
  proof: e.exists_congr_left.trans by simp [h]

中文:
引理 exists_congr
  条件: (h : 对任意 a, p a ↔ q (e a))
  结论: (存在 a, p a) ↔ 存在 b, q b
  证明: e.exists_congr_left.trans by simp [h]
-/
protected lemma exists_congr (h : forall a, p a ↔ q (e a)) : (exists a, p a) ↔ exists b, q b :=
e.exists_congr_left.trans by simp [h]

/--
lemma `exists_congr'` / 引理 `exists_congr'`

English:
lemma exists_congr'
  given: (h : forall b, p (e.symm b) ↔ q b)
  statement: (exists a, p a) ↔ exists b, q b
  proof: e.exists_congr_left.trans by simp [h]

中文:
引理 exists_congr'
  条件: (h : 对任意 b, p (e.symm b) ↔ q b)
  结论: (存在 a, p a) ↔ 存在 b, q b
  证明: e.exists_congr_left.trans by simp [h]
-/
protected lemma exists_congr' (h : forall b, p (e.symm b) ↔ q b) : (exists a, p a) ↔ exists b, q b :=
e.exists_congr_left.trans by simp [h]

/--
lemma `exists_subtype_congr` / 引理 `exists_subtype_congr`

English:
lemma exists_subtype_congr
  given: (e : {a // p a} ≃ {b // q b})
  statement: (exists a, p a) ↔ exists b, q b
  proof: by
  simp [← nonempty_subtype, nonempty_congr e]

中文:
引理 exists_subtype_congr
  条件: (e : {a // p a} ≃ {b // q b})
  结论: (存在 a, p a) ↔ 存在 b, q b
  证明: by
  simp [← nonempty_subtype, nonempty_congr e]
-/
protected lemma exists_subtype_congr (e : {a // p a} ≃ {b // q b}) : (exists a, p a) ↔ exists b, q b := by
  simp [← nonempty_subtype, nonempty_congr e]

/--
lemma `existsUnique_congr_right` / 引理 `existsUnique_congr_right`

English:
lemma existsUnique_congr_right
  statement: (exists! a, q (e a)) ↔ exists! b, q b
  proof: e.exists_congr by simpa using fun _ _ => e.forall_congr (by simp)

中文:
引理 existsUnique_congr_right
  结论: (存在! a, q (e a)) ↔ 存在! b, q b
  证明: e.exists_congr by simpa using fun _ _ => e.forall_congr (by simp)
-/
protected lemma existsUnique_congr_right : (exists! a, q (e a)) ↔ exists! b, q b :=
e.exists_congr by simpa using fun _ _ => e.forall_congr (by simp)

/--
lemma `existsUnique_congr_left` / 引理 `existsUnique_congr_left`

English:
lemma existsUnique_congr_left
  statement: (exists! a, p a) ↔ exists! b, p (e.symm b)
  proof: e.symm.existsUnique_congr_right.symm

中文:
引理 existsUnique_congr_left
  结论: (存在! a, p a) ↔ 存在! b, p (e.symm b)
  证明: e.symm.existsUnique_congr_right.symm
-/
protected lemma existsUnique_congr_left : (exists! a, p a) ↔ exists! b, p (e.symm b) :=
  e.symm.existsUnique_congr_right.symm

/--
lemma `existsUnique_congr` / 引理 `existsUnique_congr`

English:
lemma existsUnique_congr
  given: (h : forall a, p a ↔ q (e a))
  statement: (exists! a, p a) ↔ exists! b, q b
  proof: e.existsUnique_congr_left.trans by simp [h]

中文:
引理 existsUnique_congr
  条件: (h : 对任意 a, p a ↔ q (e a))
  结论: (存在! a, p a) ↔ 存在! b, q b
  证明: e.existsUnique_congr_left.trans by simp [h]
-/
protected lemma existsUnique_congr (h : forall a, p a ↔ q (e a)) : (exists! a, p a) ↔ exists! b, q b :=
e.existsUnique_congr_left.trans by simp [h]

/--
lemma `existsUnique_congr'` / 引理 `existsUnique_congr'`

English:
lemma existsUnique_congr'
  given: (h : forall b, p (e.symm b) ↔ q b)
  statement: (exists! a, p a) ↔ exists! b, q b
  proof: e.existsUnique_congr_left.trans by simp [h]

中文:
引理 existsUnique_congr'
  条件: (h : 对任意 b, p (e.symm b) ↔ q b)
  结论: (存在! a, p a) ↔ 存在! b, q b
  证明: e.existsUnique_congr_left.trans by simp [h]
-/
protected lemma existsUnique_congr' (h : forall b, p (e.symm b) ↔ q b) : (exists! a, p a) ↔ exists! b, q b :=
e.existsUnique_congr_left.trans by simp [h]

/--
lemma `existsUnique_subtype_congr` / 引理 `existsUnique_subtype_congr`

English:
lemma existsUnique_subtype_congr
  given: (e : {a // p a} ≃ {b // q b})
  proof: by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        nonempty_congr e, subsingleton_congr e]

中文:
引理 existsUnique_subtype_congr
  条件: (e : {a // p a} ≃ {b // q b})
  证明: by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        nonempty_congr e, subsingleton_congr e]
-/
protected lemma existsUnique_subtype_congr (e : {a // p a} ≃ {b // q b}) :
    (exists! a, p a) ↔ exists! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        nonempty_congr e, subsingleton_congr e]

-- We next build some higher arity versions of `Equiv.forall_congr`.
-- Although they appear to just be repeated applications of `Equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)

/--
theorem `forall₂_congr` / 定理 `forall₂_congr`

English:
theorem forall₂_congr
  statement: {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ -> β₁ -> Prop} {q : α₂ -> β₂ -> Prop}
  proof: eα.forall_congr fun _ => eβ.forall_congr @h _

中文:
定理 forall₂_congr
  结论: {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ -> β₁ -> 命题} {q : α₂ -> β₂ -> 命题}
  证明: eα.forall_congr fun _ => eβ.forall_congr @h _
-/
protected theorem forall₂_congr {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ -> β₁ -> Prop} {q : α₂ -> β₂ -> Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : forall {x y}, p x y ↔ q (eα x) (eβ y)) :
    (forall x y, p x y) ↔ forall x y, q x y :=
eα.forall_congr fun _ => eβ.forall_congr @h _

/--
theorem `forall₂_congr'` / 定理 `forall₂_congr'`

English:
theorem forall₂_congr'
  statement: {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ -> β₁ -> Prop} {q : α₂ -> β₂ -> Prop}
  proof: (Equiv.forall₂_congr eα.symm eβ.symm h.symm).symm

中文:
定理 forall₂_congr'
  结论: {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ -> β₁ -> 命题} {q : α₂ -> β₂ -> 命题}
  证明: (Equiv.forall₂_congr eα.symm eβ.symm h.symm).symm
-/
protected theorem forall₂_congr' {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ -> β₁ -> Prop} {q : α₂ -> β₂ -> Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : forall {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
    (forall x y, p x y) ↔ forall x y, q x y := (Equiv.forall₂_congr eα.symm eβ.symm h.symm).symm

/--
theorem `forall₃_congr` / 定理 `forall₃_congr`

English:
theorem forall₃_congr
  proof: Equiv.forall₂_congr _ _ Equiv.forall_congr _ @h _ _

中文:
定理 forall₃_congr
  证明: Equiv.forall₂_congr _ _ Equiv.forall_congr _ @h _ _
-/
protected theorem forall₃_congr
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ -> β₁ -> γ₁ -> Prop} {q : α₂ -> β₂ -> γ₂ -> Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : forall {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) :
    (forall x y z, p x y z) ↔ forall x y z, q x y z :=
Equiv.forall₂_congr _ _ Equiv.forall_congr _ @h _ _

/--
theorem `forall₃_congr'` / 定理 `forall₃_congr'`

English:
theorem forall₃_congr'
  proof: (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm h.symm).symm

中文:
定理 forall₃_congr'
  证明: (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm h.symm).symm
-/
protected theorem forall₃_congr'
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ -> β₁ -> γ₁ -> Prop} {q : α₂ -> β₂ -> γ₂ -> Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
    (h : forall {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (forall x y z, p x y z) ↔ forall x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm h.symm).symm

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps (attr := grind =) apply]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : α -> β) (hf : Bijective f)
  body: f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _

中文:
定义 ofBijective
  签名: (f : α -> β) (hf : Bijective f)
  定义体: f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _
-/
noncomputable def ofBijective (f : α -> β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _

/--
lemma `coe_ofBijective` / 引理 `coe_ofBijective`

English:
lemma coe_ofBijective
  given: (f : α -> β) (hf : Bijective f)
  statement: ⇑(ofBijective f hf) = f
  proof: rfl

中文:
引理 coe_ofBijective
  条件: (f : α -> β) (hf : Bijective f)
  结论: ⇑(ofBijective f hf) = f
  证明: rfl
-/
@[simp] lemma coe_ofBijective (f : α -> β) (hf : Bijective f) : ⇑(ofBijective f hf) = f := rfl

/--
lemma `ofBijective_coe` / 引理 `ofBijective_coe`

English:
lemma ofBijective_coe
  given: {f : α ≃ β}
  proof: Equiv.ext (congrFun rfl)

中文:
引理 ofBijective_coe
  条件: {f : α ≃ β}
  证明: Equiv.ext (congrFun rfl)
-/
@[simp] lemma ofBijective_coe {f : α ≃ β} :
    Equiv.ofBijective f f.bijective = f := Equiv.ext (congrFun rfl)

/--
lemma `ofBijective_apply_symm_apply` / 引理 `ofBijective_apply_symm_apply`

English:
lemma ofBijective_apply_symm_apply
  given: (f : α -> β) (hf : Bijective f) (x : β)
  proof: (ofBijective f hf).apply_symm_apply x

@[simp]

中文:
引理 ofBijective_apply_symm_apply
  条件: (f : α -> β) (hf : Bijective f) (x : β)
  证明: (ofBijective f hf).apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, ofBijective
-/
lemma ofBijective_apply_symm_apply (f : α -> β) (hf : Bijective f) (x : β) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
/--
lemma `ofBijective_symm_apply_apply` / 引理 `ofBijective_symm_apply_apply`

English:
lemma ofBijective_symm_apply_apply
  given: (f : α -> β) (hf : Bijective f) (x : α)
  proof: (ofBijective f hf).symm_apply_apply x

中文:
引理 ofBijective_symm_apply_apply
  条件: (f : α -> β) (hf : Bijective f) (x : α)
  证明: (ofBijective f hf).symm_apply_apply x

Depends on / 依赖: ofBijective, symm_apply_apply
-/
lemma ofBijective_symm_apply_apply (f : α -> β) (hf : Bijective f) (x : α) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

/-- Bijective functions are equivalent to equivalences. -/
@[simps]
/--
Definition of `bijectiveEquiv` / `bijectiveEquiv` 的定义

English:
definition bijectiveEquiv
  signature: : { f : α -> β // Bijective f } ≃ (α ≃ β) where
  body: .ofBijective f f.prop
  invFun f := ⟨f, f.bijective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

中文:
定义 bijectiveEquiv
  签名: : { f : α -> β // Bijective f } ≃ (α ≃ β) where
  定义体: .ofBijective f f.prop
  invFun f := ⟨f, f.bijective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

Depends on / 依赖: f.prop, ofBijective
-/
noncomputable def bijectiveEquiv : { f : α -> β // Bijective f } ≃ (α ≃ β) where
  toFun f := .ofBijective f f.prop
  invFun f := ⟨f, f.bijective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

end Equiv

namespace Quot

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {ra : α -> α -> Prop} {rb : β -> β -> Prop} (e : α ≃ β)
  body: Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only

中文:
定义 congr
  签名: {ra : α -> α -> 命题} {rb : β -> β -> 命题} (e : α ≃ β)
  定义体: Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only
-/
protected def congr {ra : α -> α -> Prop} {rb : β -> β -> Prop} (e : α ≃ β)
    (eq : forall a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.apply_symm_apply]

/--
theorem `congr_mk` / 定理 `congr_mk`

English:
theorem congr_mk
  statement: {ra : α -> α -> Prop} {rb : β -> β -> Prop} (e : α ≃ β)
  proof: rfl

中文:
定理 congr_mk
  结论: {ra : α -> α -> 命题} {rb : β -> β -> 命题} (e : α ≃ β)
  证明: rfl
-/
@[simp] theorem congr_mk {ra : α -> α -> Prop} {rb : β -> β -> Prop} (e : α ≃ β)
    (eq : forall a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quot.congr e eq (Quot.mk ra a) = Quot.mk rb (e a) := rfl

/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: {r r' : α -> α -> Prop} (eq : forall a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂)
  body: Quot.congr (Equiv.refl α) eq

中文:
定义 congrRight
  签名: {r r' : α -> α -> 命题} (eq : 对任意 a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂)
  定义体: Quot.congr (Equiv.refl α) eq
-/
protected def congrRight {r r' : α -> α -> Prop} (eq : forall a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ Quot r' := Quot.congr (Equiv.refl α) eq

/--
Definition of `congrLeft` / `congrLeft` 的定义

English:
definition congrLeft
  signature: {r : α -> α -> Prop} (e : α ≃ β)
  body: Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

中文:
定义 congrLeft
  签名: {r : α -> α -> 命题} (e : α ≃ β)
  定义体: Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]
-/
protected def congrLeft {r : α -> α -> Prop} (e : α ≃ β) :
    Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
  body: Quot.congr e eq

中文:
定义 congr
  签名: {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
  定义体: Quot.congr e eq
-/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : forall a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    Quotient ra ≃ Quotient rb := Quot.congr e eq

/--
theorem `congr_mk` / 定理 `congr_mk`

English:
theorem congr_mk
  statement: {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
  proof: rfl

中文:
定理 congr_mk
  结论: {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
  证明: rfl
-/
@[simp] theorem congr_mk {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : forall a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quotient.congr e eq (Quotient.mk ra a) = Quotient.mk rb (e a) := rfl

/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: {r r' : Setoid α}
  body: Quot.congrRight eq

中文:
定义 congrRight
  签名: {r r' : Setoid α}
  定义体: Quot.congrRight eq
-/
protected def congrRight {r r' : Setoid α}
    (eq : forall a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quotient r ≃ Quotient r' :=
  Quot.congrRight eq

end Quotient

/--
Definition of `finZeroEquiv` / `finZeroEquiv` 的定义

English:
definition finZeroEquiv
  signature: : Fin 0 ≃ Empty
  body: .equivEmpty _

中文:
定义 finZeroEquiv
  签名: : Fin 0 ≃ Empty
  定义体: .equivEmpty _

Depends on / 依赖: equivEmpty
-/
def finZeroEquiv : Fin 0 ≃ Empty := .equivEmpty _

/--
Definition of `finZeroEquiv'` / `finZeroEquiv'` 的定义

English:
definition finZeroEquiv'
  signature: : Fin 0 ≃ PEmpty.{u}
  body: .equivPEmpty _

中文:
定义 finZeroEquiv'
  签名: : Fin 0 ≃ PEmpty.{u}
  定义体: .equivPEmpty _

Depends on / 依赖: equivPEmpty
-/
def finZeroEquiv' : Fin 0 ≃ PEmpty.{u} := .equivPEmpty _

/--
Definition of `finOneEquiv` / `finOneEquiv` 的定义

English:
definition finOneEquiv
  signature: : Fin 1 ≃ Unit
  body: .equivPUnit _

中文:
定义 finOneEquiv
  签名: : Fin 1 ≃ Unit
  定义体: .equivPUnit _

Depends on / 依赖: equivPUnit
-/
def finOneEquiv : Fin 1 ≃ Unit := .equivPUnit _

/--
Definition of `finTwoEquiv` / `finTwoEquiv` 的定义

English:
definition finTwoEquiv
  signature: : Fin 2 ≃ Bool where
  body: i == 1
  invFun b := bif b then 1 else 0
  left_inv i := by grind
  right_inv b := by grind

中文:
定义 finTwoEquiv
  签名: : Fin 2 ≃ 布尔 where
  定义体: i == 1
  invFun b := bif b then 1 else 0
  left_inv i := by grind
  right_inv b := by grind
-/
def finTwoEquiv : Fin 2 ≃ Bool where
  toFun i := i == 1
  invFun b := bif b then 1 else 0
  left_inv i := by grind
  right_inv b := by grind

namespace Equiv

variable {α β : Type*}

/-- The left summand of `α ⊕ β` is equivalent to `α`. -/
@[simps (attr := grind =)]
/--
Definition of `sumIsLeft` / `sumIsLeft` 的定义

English:
definition sumIsLeft
  signature: : {x : α oplus β // x.isLeft} ≃ α where
  body: x.1.getLeft x.2
  invFun a := ⟨.inl a, Sum.isLeft_inl⟩
  left_inv | ⟨.inl _a, _⟩ => rfl

中文:
定义 sumIsLeft
  签名: : {x : α oplus β // x.isLeft} ≃ α where
  定义体: x.1.getLeft x.2
  invFun a := ⟨.inl a, Sum.isLeft_inl⟩
  left_inv | ⟨.inl _a, _⟩ => rfl

Depends on / 依赖: getLeft
-/
def sumIsLeft : {x : α oplus β // x.isLeft} ≃ α where
  toFun x := x.1.getLeft x.2
  invFun a := ⟨.inl a, Sum.isLeft_inl⟩
  left_inv | ⟨.inl _a, _⟩ => rfl

/-- The right summand of `α ⊕ β` is equivalent to `β`. -/
@[simps (attr := grind =)]
/--
Definition of `sumIsRight` / `sumIsRight` 的定义

English:
definition sumIsRight
  signature: : {x : α oplus β // x.isRight} ≃ β where
  body: x.1.getRight x.2
  invFun b := ⟨.inr b, Sum.isRight_inr⟩
  left_inv | ⟨.inr _b, _⟩ => rfl

中文:
定义 sumIsRight
  签名: : {x : α oplus β // x.isRight} ≃ β where
  定义体: x.1.getRight x.2
  invFun b := ⟨.inr b, Sum.isRight_inr⟩
  left_inv | ⟨.inr _b, _⟩ => rfl

Depends on / 依赖: getRight
-/
def sumIsRight : {x : α oplus β // x.isRight} ≃ β where
  toFun x := x.1.getRight x.2
  invFun b := ⟨.inr b, Sum.isRight_inr⟩
  left_inv | ⟨.inr _b, _⟩ => rfl

variable (e : α ≃ β)

/--
Definition of `le` / `le` 的定义

English:
abbreviation le
  signature: [LE β]
  body: e a <= e b

中文:
缩写 le
  签名: [LE β]
  定义体: e a <= e b
-/
protected abbrev le [LE β] : LE α where
  le a b := e a <= e b

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: [LE β] (a b : α)
  proof: e.le
    e a <= e b ↔ a <= b := Iff.rfl

中文:
引理 le_def
  条件: [LE β] (a b : α)
  证明: e.le
    e a <= e b ↔ a <= b := Iff.rfl

Depends on / 依赖: e.le
-/
lemma le_def [LE β] (a b : α) :
    letI := e.le
    e a <= e b ↔ a <= b := Iff.rfl

/--
Definition of `lt` / `lt` 的定义

English:
abbreviation lt
  signature: [LT β]
  body: e a < e b

中文:
缩写 lt
  签名: [LT β]
  定义体: e a < e b
-/
protected abbrev lt [LT β] : LT α where
  lt a b := e a < e b

/--
lemma `lt_def` / 引理 `lt_def`

English:
lemma lt_def
  given: [LT β] (a b : α)
  proof: e.lt
    e a < e b ↔ a < b := Iff.rfl

中文:
引理 lt_def
  条件: [LT β] (a b : α)
  证明: e.lt
    e a < e b ↔ a < b := Iff.rfl

Depends on / 依赖: e.lt
-/
lemma lt_def [LT β] (a b : α) :
    letI := e.lt
    e a < e b ↔ a < b := Iff.rfl

/--
Definition of `max` / `max` 的定义

English:
abbreviation max
  signature: [Max β]
  body: e.symm (max (e a) (e b))

中文:
缩写 max
  签名: [Max β]
  定义体: e.symm (max (e a) (e b))
-/
protected abbrev max [Max β] : Max α where
  max a b := e.symm (max (e a) (e b))

/--
lemma `max_def` / 引理 `max_def`

English:
lemma max_def
  given: [Max β] (a b : α)
  proof: e.max
    max a b = e.symm (max (e a) (e b)) := rfl

中文:
引理 max_def
  条件: [Max β] (a b : α)
  证明: e.max
    max a b = e.symm (max (e a) (e b)) := rfl

Depends on / 依赖: e.max
-/
lemma max_def [Max β] (a b : α) :
    letI := e.max
    max a b = e.symm (max (e a) (e b)) := rfl

/--
Definition of `min` / `min` 的定义

English:
abbreviation min
  signature: [Min β]
  body: e.symm (min (e a) (e b))

中文:
缩写 min
  签名: [Min β]
  定义体: e.symm (min (e a) (e b))
-/
protected abbrev min [Min β] : Min α where
  min a b := e.symm (min (e a) (e b))

/--
lemma `min_def` / 引理 `min_def`

English:
lemma min_def
  given: [Min β] (a b : α)
  proof: e.min
    min a b = e.symm (min (e a) (e b)) := rfl

中文:
引理 min_def
  条件: [Min β] (a b : α)
  证明: e.min
    min a b = e.symm (min (e a) (e b)) := rfl

Depends on / 依赖: e.min
-/
lemma min_def [Min β] (a b : α) :
    letI := e.min
    min a b = e.symm (min (e a) (e b)) := rfl

/--
Definition of `ord` / `ord` 的定义

English:
abbreviation ord
  signature: [Ord β]
  body: compare (e a) (e b)

中文:
缩写 ord
  签名: [Ord β]
  定义体: compare (e a) (e b)
-/
protected abbrev ord [Ord β] : Ord α where
  compare a b := compare (e a) (e b)

/--
lemma `ord_def` / 引理 `ord_def`

English:
lemma ord_def
  given: [Ord β] (a b : α)
  proof: e.ord
    compare a b = compare (e a) (e b) := rfl

中文:
引理 ord_def
  条件: [Ord β] (a b : α)
  证明: e.ord
    compare a b = compare (e a) (e b) := rfl

Depends on / 依赖: e.ord
-/
lemma ord_def [Ord β] (a b : α) :
    letI := e.ord
    compare a b = compare (e a) (e b) := rfl

end Equiv
