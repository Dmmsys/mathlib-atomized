/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton,
Anatole Dedecker
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Uniform isomorphisms

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

## Main definitions

* `UniformEquiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/

@[expose] public section


open Set Filter

universe u v

variable {α : Type u} {β : Type*} {γ : Type*} {δ : Type*}

-- not all spaces are homeomorphic to each other
/--
Definition of `UniformEquiv` / `UniformEquiv` 的定义

English:
structure UniformEquiv
  parameters: (α : Type*) (β : Type*) [UniformSpace α] [UniformSpace β]
  axioms and operations (2):
    - uniformContinuous_toFun : UniformContinuous toFun
    - uniformContinuous_invFun : UniformContinuous invFun

中文:
结构 UniformEquiv
  参数: (α : 类型) (β : 类型) [UniformSpace α] [UniformSpace β]
  公理与运算 (2 个):
    - uniformContinuous_toFun : UniformContinuous toFun
    - uniformContinuous_invFun : UniformContinuous invFun
-/
structure UniformEquiv (α : Type*) (β : Type*) [UniformSpace α] [UniformSpace β] extends
  α ≃ β where
  /-- Uniform continuity of the function -/
  uniformContinuous_toFun : UniformContinuous toFun
  /-- Uniform continuity of the inverse -/
  uniformContinuous_invFun : UniformContinuous invFun

/-- Uniform isomorphism between `α` and `β` -/
infixl:25 " ≃ᵤ " => UniformEquiv

namespace UniformEquiv

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Function.Injective (toEquiv : α ≃ᵤ β -> α ≃ β)

中文:
定理 toEquiv_injective
  结论: Function.Injective (toEquiv : α ≃ᵤ β -> α ≃ β)
-/
theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ᵤ β -> α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, h => by simpa only [mk.injEq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (α ≃ᵤ β) α β
  body: h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
coe_injective' _ _ H _ := toEquiv_injective DFunLike.ext' H

@[simp]

中文:
实例 :
  签名: EquivLike (α ≃ᵤ β) α β
  定义体: h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
coe_injective' _ _ H _ := toEquiv_injective DFunLike.ext' H

@[simp]

Depends on / 依赖: h.toEquiv, toEquiv
-/
instance : EquivLike (α ≃ᵤ β) α β where
  coe h := h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
coe_injective' _ _ H _ := toEquiv_injective DFunLike.ext' H

@[simp]
/--
theorem `uniformEquiv_mk_coe` / 定理 `uniformEquiv_mk_coe`

English:
theorem uniformEquiv_mk_coe
  given: (a : Equiv α β) (b c)
  statement: (UniformEquiv.mk a b c : α -> β) = a
  proof: rfl

中文:
定理 uniformEquiv_mk_coe
  条件: (a : Equiv α β) (b c)
  结论: (UniformEquiv.mk a b c : α -> β) = a
  证明: rfl
-/
theorem uniformEquiv_mk_coe (a : Equiv α β) (b c) : (UniformEquiv.mk a b c : α -> β) = a :=
  rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (h : α ≃ᵤ β)
  body: h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm

中文:
定义 symm
  签名: (h : α ≃ᵤ β)
  定义体: h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm
-/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α where
  uniformContinuous_toFun := h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : α ≃ᵤ β)
  body: h

中文:
定义 Simps.apply
  签名: (h : α ≃ᵤ β)
  定义体: h
-/
def Simps.apply (h : α ≃ᵤ β) : α -> β :=
  h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : α ≃ᵤ β)
  body: h.symm

initialize_simps_projections UniformEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (h : α ≃ᵤ β)
  定义体: h.symm

initialize_simps_projections UniformEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply (h : α ≃ᵤ β) : β -> α :=
  h.symm

initialize_simps_projections UniformEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (h : α ≃ᵤ β)
  statement: ⇑h.toEquiv = h
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv
  条件: (h : α ≃ᵤ β)
  结论: ⇑h.toEquiv = h
  证明: rfl

@[simp]
-/
theorem coe_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h :=
  rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  given: (h : α ≃ᵤ β)
  statement: ⇑h.toEquiv.symm = h.symm
  proof: rfl

@[ext]

中文:
定理 coe_symm_toEquiv
  条件: (h : α ≃ᵤ β)
  结论: ⇑h.toEquiv.symm = h.symm
  证明: rfl

@[ext]
-/
theorem coe_symm_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {h h' : α ≃ᵤ β} (H : forall x, h x = h' x)
  statement: h = h'
  proof: toEquiv_injective Equiv.ext H

中文:
定理 ext
  条件: {h h' : α ≃ᵤ β} (H : 对任意 x, h x = h' x)
  结论: h = h'
  证明: toEquiv_injective Equiv.ext H

Depends on / 依赖: Equiv.ext, toEquiv_injective
-/
theorem ext {h h' : α ≃ᵤ β} (H : forall x, h x = h' x) : h = h' :=
toEquiv_injective Equiv.ext H

/-- Identity map as a uniform isomorphism. -/
@[simps! -fullyApplied apply]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Type*) [UniformSpace α]
  body: uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α

中文:
定义 refl
  签名: (α : 类型) [UniformSpace α]
  定义体: uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α
-/
protected def refl (α : Type*) [UniformSpace α] : α ≃ᵤ α where
  uniformContinuous_toFun := uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ)
  body: h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]

中文:
定义 trans
  签名: (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ)
  定义体: h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
-/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ where
  uniformContinuous_toFun := h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α)
  statement: h₁.trans h₂ a = h₂ (h₁ a)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α)
  结论: h₁.trans h₂ a = h₂ (h₁ a)
  证明: rfl

@[simp]
-/
theorem trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl

@[simp]
/--
theorem `uniformEquiv_mk_coe_symm` / 定理 `uniformEquiv_mk_coe_symm`

English:
theorem uniformEquiv_mk_coe_symm
  given: (a : Equiv α β) (b c)
  proof: rfl

@[simp]

中文:
定理 uniformEquiv_mk_coe_symm
  条件: (a : Equiv α β) (b c)
  证明: rfl

@[simp]
-/
theorem uniformEquiv_mk_coe_symm (a : Equiv α β) (b c) :
    ((UniformEquiv.mk a b c).symm : β -> α) = a.symm :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (UniformEquiv.refl α).symm = UniformEquiv.refl α
  proof: rfl

中文:
定理 refl_symm
  结论: (UniformEquiv.refl α).symm = UniformEquiv.refl α
  证明: rfl
-/
theorem refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α :=
  rfl

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (h : α ≃ᵤ β)
  statement: UniformContinuous h
  proof: h.uniformContinuous_toFun

@[continuity]

中文:
定理 uniformContinuous
  条件: (h : α ≃ᵤ β)
  结论: UniformContinuous h
  证明: h.uniformContinuous_toFun

@[continuity]
-/
protected theorem uniformContinuous (h : α ≃ᵤ β) : UniformContinuous h :=
  h.uniformContinuous_toFun

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (h : α ≃ᵤ β)
  statement: Continuous h
  proof: h.uniformContinuous.continuous

中文:
定理 continuous
  条件: (h : α ≃ᵤ β)
  结论: Continuous h
  证明: h.uniformContinuous.continuous
-/
protected theorem continuous (h : α ≃ᵤ β) : Continuous h :=
  h.uniformContinuous.continuous

/--
theorem `uniformContinuous_symm` / 定理 `uniformContinuous_symm`

English:
theorem uniformContinuous_symm
  given: (h : α ≃ᵤ β)
  statement: UniformContinuous h.symm
  proof: h.uniformContinuous_invFun

中文:
定理 uniformContinuous_symm
  条件: (h : α ≃ᵤ β)
  结论: UniformContinuous h.symm
  证明: h.uniformContinuous_invFun
-/
protected theorem uniformContinuous_symm (h : α ≃ᵤ β) : UniformContinuous h.symm :=
  h.uniformContinuous_invFun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
/--
theorem `continuous_symm` / 定理 `continuous_symm`

English:
theorem continuous_symm
  given: (h : α ≃ᵤ β)
  statement: Continuous h.symm
  proof: h.uniformContinuous_symm.continuous

中文:
定理 continuous_symm
  条件: (h : α ≃ᵤ β)
  结论: Continuous h.symm
  证明: h.uniformContinuous_symm.continuous
-/
protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm :=
  h.uniformContinuous_symm.continuous

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (e : α ≃ᵤ β)
  body: { e.toEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }

中文:
定义 toHomeomorph
  签名: (e : α ≃ᵤ β)
  定义体: { e.toEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }
-/
protected def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }

/--
lemma `toHomeomorph_apply` / 引理 `toHomeomorph_apply`

English:
lemma toHomeomorph_apply
  given: (e : α ≃ᵤ β)
  statement: (e.toHomeomorph : α -> β) = e
  proof: rfl

中文:
引理 toHomeomorph_apply
  条件: (e : α ≃ᵤ β)
  结论: (e.toHomeomorph : α -> β) = e
  证明: rfl
-/
lemma toHomeomorph_apply (e : α ≃ᵤ β) : (e.toHomeomorph : α -> β) = e := rfl

/--
lemma `toHomeomorph_symm_apply` / 引理 `toHomeomorph_symm_apply`

English:
lemma toHomeomorph_symm_apply
  given: (e : α ≃ᵤ β)
  statement: (e.toHomeomorph.symm : β -> α) = e.symm
  proof: rfl

@[simp]

中文:
引理 toHomeomorph_symm_apply
  条件: (e : α ≃ᵤ β)
  结论: (e.toHomeomorph.symm : β -> α) = e.symm
  证明: rfl

@[simp]
-/
lemma toHomeomorph_symm_apply (e : α ≃ᵤ β) : (e.toHomeomorph.symm : β -> α) = e.symm := rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (h : α ≃ᵤ β) (x : β)
  statement: h (h.symm x) = x
  proof: h.toEquiv.apply_symm_apply x

@[simp]

中文:
定理 apply_symm_apply
  条件: (h : α ≃ᵤ β) (x : β)
  结论: h (h.symm x) = x
  证明: h.toEquiv.apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, h.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (h : α ≃ᵤ β) (x : α)
  statement: h.symm (h x) = x
  proof: h.toEquiv.symm_apply_apply x

中文:
定理 symm_apply_apply
  条件: (h : α ≃ᵤ β) (x : α)
  结论: h.symm (h x) = x
  证明: h.toEquiv.symm_apply_apply x

Depends on / 依赖: h.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (h : α ≃ᵤ β)
  statement: Function.Bijective h
  proof: h.toEquiv.bijective

中文:
定理 bijective
  条件: (h : α ≃ᵤ β)
  结论: Function.Bijective h
  证明: h.toEquiv.bijective
-/
protected theorem bijective (h : α ≃ᵤ β) : Function.Bijective h :=
  h.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (h : α ≃ᵤ β)
  statement: Function.Injective h
  proof: h.toEquiv.injective

中文:
定理 injective
  条件: (h : α ≃ᵤ β)
  结论: Function.Injective h
  证明: h.toEquiv.injective
-/
protected theorem injective (h : α ≃ᵤ β) : Function.Injective h :=
  h.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (h : α ≃ᵤ β)
  statement: Function.Surjective h
  proof: h.toEquiv.surjective

中文:
定理 surjective
  条件: (h : α ≃ᵤ β)
  结论: Function.Surjective h
  证明: h.toEquiv.surjective
-/
protected theorem surjective (h : α ≃ᵤ β) : Function.Surjective h :=
  h.toEquiv.surjective

/--
Definition of `changeInv` / `changeInv` 的定义

English:
definition changeInv
  signature: (f : α ≃ᵤ β) (g : β -> α) (hg : Function.RightInverse g f)
  body: have : g = f.symm :=
    funext fun x => calc
      g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
      _ = f.symm x := by rw [hg x]
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    uniformContinuous_toFun := f.uniformCont

中文:
定义 changeInv
  签名: (f : α ≃ᵤ β) (g : β -> α) (hg : Function.RightInverse g f)
  定义体: have : g = f.symm :=
    funext fun x => calc
      g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
      _ = f.symm x := by rw [hg x]
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    uniformContinuous_toFun := f.uniformCont

Depends on / 依赖: convert, f.left_inv, f.right_inv, f.symm, f.symm.uniformContinuous, f.uniformContinuous, invFun, left_inv, right_inv, uniformContinuous, uniformContinuous_invFun, uniformContinuous_toFun
-/
def changeInv (f : α ≃ᵤ β) (g : β -> α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
  have : g = f.symm :=
    funext fun x => calc
      g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
      _ = f.symm x := by rw [hg x]
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    uniformContinuous_toFun := f.uniformContinuous
    uniformContinuous_invFun := by convert! f.symm.uniformContinuous }

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (h : α ≃ᵤ β)
  statement: (h.symm : β -> α) ∘ h = id
  proof: funext h.symm_apply_apply

@[simp]

中文:
定理 symm_comp_self
  条件: (h : α ≃ᵤ β)
  结论: (h.symm : β -> α) ∘ h = id
  证明: funext h.symm_apply_apply

@[simp]

Depends on / 依赖: h.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self (h : α ≃ᵤ β) : (h.symm : β -> α) ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (h : α ≃ᵤ β)
  statement: (h : α -> β) ∘ h.symm = id
  proof: funext h.apply_symm_apply

中文:
定理 self_comp_symm
  条件: (h : α ≃ᵤ β)
  结论: (h : α -> β) ∘ h.symm = id
  证明: funext h.apply_symm_apply

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply
-/
theorem self_comp_symm (h : α ≃ᵤ β) : (h : α -> β) ∘ h.symm = id :=
  funext h.apply_symm_apply

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  given: (h : α ≃ᵤ β)
  statement: range h = univ
  proof: by simp

中文:
定理 range_coe
  条件: (h : α ≃ᵤ β)
  结论: range h = univ
  证明: by simp
-/
theorem range_coe (h : α ≃ᵤ β) : range h = univ := by simp

/--
theorem `image_symm` / 定理 `image_symm`

English:
theorem image_symm
  given: (h : α ≃ᵤ β)
  statement: image h.symm = preimage h
  proof: funext h.symm.toEquiv.image_eq_preimage_symm

中文:
定理 image_symm
  条件: (h : α ≃ᵤ β)
  结论: image h.symm = preimage h
  证明: funext h.symm.toEquiv.image_eq_preimage_symm

Depends on / 依赖: h.symm.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_symm (h : α ≃ᵤ β) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage_symm

/--
theorem `preimage_symm` / 定理 `preimage_symm`

English:
theorem preimage_symm
  given: (h : α ≃ᵤ β)
  statement: preimage h.symm = image h
  proof: (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]

中文:
定理 preimage_symm
  条件: (h : α ≃ᵤ β)
  结论: preimage h.symm = image h
  证明: (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]

Depends on / 依赖: h.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem preimage_symm (h : α ≃ᵤ β) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]
/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  given: (h : α ≃ᵤ β) (s : Set β)
  statement: h '' h ⁻¹' s = s
  proof: h.toEquiv.image_preimage s

@[simp]

中文:
定理 image_preimage
  条件: (h : α ≃ᵤ β) (s : Set β)
  结论: h '' h ⁻¹' s = s
  证明: h.toEquiv.image_preimage s

@[simp]

Depends on / 依赖: h.toEquiv.image_preimage, image_preimage, toEquiv
-/
theorem image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' h ⁻¹' s = s :=
  h.toEquiv.image_preimage s

@[simp]
/--
theorem `preimage_image` / 定理 `preimage_image`

English:
theorem preimage_image
  given: (h : α ≃ᵤ β) (s : Set α)
  statement: h ⁻¹' h '' s = s
  proof: h.toEquiv.preimage_image s

中文:
定理 preimage_image
  条件: (h : α ≃ᵤ β) (s : Set α)
  结论: h ⁻¹' h '' s = s
  证明: h.toEquiv.preimage_image s

Depends on / 依赖: h.toEquiv.preimage_image, preimage_image, toEquiv
-/
theorem preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' h '' s = s :=
  h.toEquiv.preimage_image s

/--
theorem `isUniformInducing` / 定理 `isUniformInducing`

English:
theorem isUniformInducing
  given: (h : α ≃ᵤ β)
  statement: IsUniformInducing h
  proof: IsUniformInducing.of_comp h.uniformContinuous h.symm.uniformContinuous by
    simp only [symm_comp_self, IsUniformInducing.id]

中文:
定理 isUniformInducing
  条件: (h : α ≃ᵤ β)
  结论: IsUniformInducing h
  证明: IsUniformInducing.of_comp h.uniformContinuous h.symm.uniformContinuous by
    simp only [symm_comp_self, IsUniformInducing.id]

Depends on / 依赖: IsUniformInducing, IsUniformInducing.id, IsUniformInducing.of_comp, h.symm.uniformContinuous, h.uniformContinuous, of_comp, symm_comp_self, uniformContinuous
-/
theorem isUniformInducing (h : α ≃ᵤ β) : IsUniformInducing h :=
IsUniformInducing.of_comp h.uniformContinuous h.symm.uniformContinuous by
    simp only [symm_comp_self, IsUniformInducing.id]

/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  given: (h : α ≃ᵤ β)
  statement: UniformSpace.comap h ‹_› = ‹_›
  proof: h.isUniformInducing.comap_uniformSpace

中文:
定理 comap_eq
  条件: (h : α ≃ᵤ β)
  结论: UniformSpace.comap h ‹_› = ‹_›
  证明: h.isUniformInducing.comap_uniformSpace

Depends on / 依赖: comap_uniformSpace, h.isUniformInducing.comap_uniformSpace, isUniformInducing
-/
theorem comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_› :=
  h.isUniformInducing.comap_uniformSpace

/--
lemma `isUniformEmbedding` / 引理 `isUniformEmbedding`

English:
lemma isUniformEmbedding
  given: (h : α ≃ᵤ β)
  statement: IsUniformEmbedding h
  proof: ⟨h.isUniformInducing, h.injective⟩

中文:
引理 isUniformEmbedding
  条件: (h : α ≃ᵤ β)
  结论: IsUniformEmbedding h
  证明: ⟨h.isUniformInducing, h.injective⟩

Depends on / 依赖: h.injective, h.isUniformInducing, injective, isUniformInducing
-/
lemma isUniformEmbedding (h : α ≃ᵤ β) : IsUniformEmbedding h := ⟨h.isUniformInducing, h.injective⟩

/--
theorem `completeSpace_iff` / 定理 `completeSpace_iff`

English:
theorem completeSpace_iff
  given: (h : α ≃ᵤ β)
  statement: CompleteSpace α ↔ CompleteSpace β
  proof: completeSpace_congr h.isUniformEmbedding

中文:
定理 completeSpace_iff
  条件: (h : α ≃ᵤ β)
  结论: CompleteSpace α ↔ CompleteSpace β
  证明: completeSpace_congr h.isUniformEmbedding

Depends on / 依赖: completeSpace_congr, h.isUniformEmbedding, isUniformEmbedding
-/
theorem completeSpace_iff (h : α ≃ᵤ β) : CompleteSpace α ↔ CompleteSpace β :=
  completeSpace_congr h.isUniformEmbedding

/--
Definition of `ofIsUniformEmbedding` / `ofIsUniformEmbedding` 的定义

English:
definition ofIsUniformEmbedding
  signature: (f : α -> β) (hf : IsUniformEmbedding f)
  body: hf.isUniformInducing.uniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    rw [hf.isUniformInducing.uniformContinuous_iff]; rw [Equiv.invFun_as_coe]; rw [Equiv.self_comp_ofInjective_symm]
    exact uniformContinuous_subtype_val
  toEquiv := Equiv.ofInjective f hf.injective

中文:
定义 ofIsUniformEmbedding
  签名: (f : α -> β) (hf : IsUniformEmbedding f)
  定义体: hf.isUniformInducing.uniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    rw [hf.isUniformInducing.uniformContinuous_iff]; rw [Equiv.invFun_as_coe]; rw [Equiv.self_comp_ofInjective_symm]
    exact uniformContinuous_subtype_val
  toEquiv := Equiv.ofInjective f hf.injective

Depends on / 依赖: hf.isUniformInducing.uniformContinuous.subtype_mk, isUniformInducing, subtype_mk, uniformContinuous
-/
noncomputable def ofIsUniformEmbedding (f : α -> β) (hf : IsUniformEmbedding f) :
    α ≃ᵤ Set.range f where
  uniformContinuous_toFun := hf.isUniformInducing.uniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    rw [hf.isUniformInducing.uniformContinuous_iff]; rw [Equiv.invFun_as_coe]; rw [Equiv.self_comp_ofInjective_symm]
    exact uniformContinuous_subtype_val
  toEquiv := Equiv.ofInjective f hf.injective

/--
Definition of `setCongr` / `setCongr` 的定义

English:
definition setCongr
  signature: {s t : Set α} (h : s = t)
  body: uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h

中文:
定义 setCongr
  签名: {s t : Set α} (h : s = t)
  定义体: uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h

Depends on / 依赖: subtype_mk, uniformContinuous_subtype_val, uniformContinuous_subtype_val.subtype_mk
-/
def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t where
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h

/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ)
  body: (h₁.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.uniformContinuous.comp uniformContinuous_snd)
  uniformContinuous_invFun :=
    (h₁.symm.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.symm.uniformContinuous.comp uniformContinuous_snd)
  toEquiv := h₁.toEquiv.prodCo

中文:
定义 prodCongr
  签名: (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ)
  定义体: (h₁.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.uniformContinuous.comp uniformContinuous_snd)
  uniformContinuous_invFun :=
    (h₁.symm.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.symm.uniformContinuous.comp uniformContinuous_snd)
  toEquiv := h₁.toEquiv.prodCo

Depends on / 依赖: prodCongr, prodMk, symm.uniformContinuous.comp, toEquiv, toEquiv.prodCongr, uniformContinuous, uniformContinuous.comp, uniformContinuous_fst, uniformContinuous_invFun, uniformContinuous_snd
-/
def prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ where
  uniformContinuous_toFun :=
    (h₁.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.uniformContinuous.comp uniformContinuous_snd)
  uniformContinuous_invFun :=
    (h₁.symm.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.symm.uniformContinuous.comp uniformContinuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  given: (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ)
  proof: rfl

@[simp]

中文:
定理 prodCongr_symm
  条件: (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ)
  证明: rfl

@[simp]
-/
theorem prodCongr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  given: (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ)
  statement: ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂
  proof: rfl

中文:
定理 coe_prodCongr
  条件: (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ)
  结论: ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂
  证明: rfl
-/
theorem coe_prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (α β γ)

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : α × β ≃ᵤ β × α where
  body: uniformContinuous_snd.prodMk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β

@[simp]

中文:
定义 prodComm
  签名: : α × β ≃ᵤ β × α where
  定义体: uniformContinuous_snd.prodMk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β

@[simp]

Depends on / 依赖: prodMk, uniformContinuous_fst, uniformContinuous_snd, uniformContinuous_snd.prodMk
-/
def prodComm : α × β ≃ᵤ β × α where
  uniformContinuous_toFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β

@[simp]
/--
theorem `prodComm_symm` / 定理 `prodComm_symm`

English:
theorem prodComm_symm
  statement: (prodComm α β).symm = prodComm β α
  proof: rfl

@[simp]

中文:
定理 prodComm_symm
  结论: (prodComm α β).symm = prodComm β α
  证明: rfl

@[simp]
-/
theorem prodComm_symm : (prodComm α β).symm = prodComm β α :=
  rfl

@[simp]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  statement: ⇑(prodComm α β) = Prod.swap
  proof: rfl

中文:
定理 coe_prodComm
  结论: ⇑(prodComm α β) = Prod.swap
  证明: rfl
-/
theorem coe_prodComm : ⇑(prodComm α β) = Prod.swap :=
  rfl

/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : (α × β) × γ ≃ᵤ α × β × γ where
  body: (uniformContinuous_fst.comp uniformContinuous_fst).prodMk
      ((uniformContinuous_snd.comp uniformContinuous_fst).prodMk uniformContinuous_snd)
  uniformContinuous_invFun :=
    (uniformContinuous_fst.prodMk (uniformContinuous_fst.comp
      uniformContinuous_snd)).prodMk (uniformContinuous_snd.co

中文:
定义 prodAssoc
  签名: : (α × β) × γ ≃ᵤ α × β × γ where
  定义体: (uniformContinuous_fst.comp uniformContinuous_fst).prodMk
      ((uniformContinuous_snd.comp uniformContinuous_fst).prodMk uniformContinuous_snd)
  uniformContinuous_invFun :=
    (uniformContinuous_fst.prodMk (uniformContinuous_fst.comp
      uniformContinuous_snd)).prodMk (uniformContinuous_snd.co

Depends on / 依赖: Equiv.prodAssoc, prodAssoc, prodMk, toEquiv, uniformContinuous_fst, uniformContinuous_fst.comp, uniformContinuous_fst.prodMk, uniformContinuous_invFun, uniformContinuous_snd, uniformContinuous_snd.comp
-/
def prodAssoc : (α × β) × γ ≃ᵤ α × β × γ where
  uniformContinuous_toFun :=
    (uniformContinuous_fst.comp uniformContinuous_fst).prodMk
      ((uniformContinuous_snd.comp uniformContinuous_fst).prodMk uniformContinuous_snd)
  uniformContinuous_invFun :=
    (uniformContinuous_fst.prodMk (uniformContinuous_fst.comp
      uniformContinuous_snd)).prodMk (uniformContinuous_snd.comp uniformContinuous_snd)
  toEquiv := Equiv.prodAssoc α β γ

/-- `α × {*}` is uniformly isomorphic to `α`. -/
@[simps! -fullyApplied apply]
/--
Definition of `prodPUnit` / `prodPUnit` 的定义

English:
definition prodPUnit
  signature: : α × PUnit ≃ᵤ α where
  body: Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prodMk uniformContinuous_const

@[deprecated (since := "2026-02-08")] alias prodPunit := prodPUnit

中文:
定义 prodPUnit
  签名: : α × PUnit ≃ᵤ α where
  定义体: Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prodMk uniformContinuous_const

@[deprecated (since := "2026-02-08")] alias prodPunit := prodPUnit

Depends on / 依赖: Equiv.prodPUnit, prodPUnit
-/
def prodPUnit : α × PUnit ≃ᵤ α where
  toEquiv := Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prodMk uniformContinuous_const

@[deprecated (since := "2026-02-08")] alias prodPunit := prodPUnit

/--
Definition of `punitProd` / `punitProd` 的定义

English:
definition punitProd
  signature: : PUnit × α ≃ᵤ α
  body: (prodComm _ _).trans (prodPUnit _)

@[simp]

中文:
定义 punitProd
  签名: : PUnit × α ≃ᵤ α
  定义体: (prodComm _ _).trans (prodPUnit _)

@[simp]

Depends on / 依赖: prodComm, prodPUnit
-/
def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPUnit _)

@[simp]
/--
theorem `coe_punitProd` / 定理 `coe_punitProd`

English:
theorem coe_punitProd
  statement: ⇑(punitProd α) = Prod.snd
  proof: rfl

中文:
定理 coe_punitProd
  结论: ⇑(punitProd α) = Prod.snd
  证明: rfl
-/
theorem coe_punitProd : ⇑(punitProd α) = Prod.snd :=
  rfl

/-- `Equiv.piCongrLeft` as a uniform isomorphism: this is the natural isomorphism
`Π i, β (e i) ≃ᵤ Π j, β j` obtained from a bijection `ι ≃ ι'`. -/
@[simps toEquiv, simps! -isSimp apply]
/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: {ι ι' : Type*} {β : ι' -> Type*} [forall j, UniformSpace (β j)]
  body: uniformContinuous_pi.mpr e.forall_congr_right.mp fun i => by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using
      Pi.uniformContinuous_proj _ i
  uniformContinuous_invFun := Pi.uniformContinuous_precomp' _ e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]

中文:
定义 piCongrLeft
  签名: {ι ι' : 类型} {β : ι' -> 类型} [对任意 j, UniformSpace (β j)]
  定义体: uniformContinuous_pi.mpr e.forall_congr_right.mp fun i => by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using
      Pi.uniformContinuous_proj _ i
  uniformContinuous_invFun := Pi.uniformContinuous_precomp' _ e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]

Depends on / 依赖: Equiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, Equiv.toFun_as_coe, Pi.uniformContinuous_precomp, Pi.uniformContinuous_proj, e.forall_congr_right.mp, forall_congr_right, piCongrLeft, piCongrLeft_apply_apply, toEquiv, toFun_as_coe, uniformContinuous_invFun, uniformContinuous_pi, uniformContinuous_pi.mpr, uniformContinuous_precomp, uniformContinuous_proj
-/
def piCongrLeft {ι ι' : Type*} {β : ι' -> Type*} [forall j, UniformSpace (β j)]
    (e : ι ≃ ι') : (forall i, β (e i)) ≃ᵤ forall j, β j where
uniformContinuous_toFun := uniformContinuous_pi.mpr e.forall_congr_right.mp fun i => by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using
      Pi.uniformContinuous_proj _ i
  uniformContinuous_invFun := Pi.uniformContinuous_precomp' _ e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]
/--
lemma `piCongrLeft_refl` / 引理 `piCongrLeft_refl`

English:
lemma piCongrLeft_refl
  given: {ι : Type*} {X : ι -> Type*} [forall i, UniformSpace (X i)]
  proof: rfl

@[simp]

中文:
引理 piCongrLeft_refl
  条件: {ι : 类型} {X : ι -> 类型} [对任意 i, UniformSpace (X i)]
  证明: rfl

@[simp]
-/
lemma piCongrLeft_refl {ι : Type*} {X : ι -> Type*} [forall i, UniformSpace (X i)] :
    piCongrLeft (.refl ι) = .refl (forall i, X i) :=
  rfl

@[simp]
/--
lemma `piCongrLeft_symm_apply` / 引理 `piCongrLeft_symm_apply`

English:
lemma piCongrLeft_symm_apply
  statement: {ι ι' : Type*} {X : ι' -> Type*} [forall j, UniformSpace (X j)]
  proof: rfl

@[simp]

中文:
引理 piCongrLeft_symm_apply
  结论: {ι ι' : 类型} {X : ι' -> 类型} [对任意 j, UniformSpace (X j)]
  证明: rfl

@[simp]
-/
lemma piCongrLeft_symm_apply {ι ι' : Type*} {X : ι' -> Type*} [forall j, UniformSpace (X j)]
    (e : ι ≃ ι') : ⇑(piCongrLeft (β := X) e).symm = (· <| e ·) :=
  rfl

@[simp]
/--
lemma `piCongrLeft_apply_apply` / 引理 `piCongrLeft_apply_apply`

English:
lemma piCongrLeft_apply_apply
  statement: {ι ι' : Type*} {X : ι' -> Type*} [forall j, UniformSpace (X j)]
  proof: Equiv.piCongrLeft_apply_apply ..

中文:
引理 piCongrLeft_apply_apply
  结论: {ι ι' : 类型} {X : ι' -> 类型} [对任意 j, UniformSpace (X j)]
  证明: Equiv.piCongrLeft_apply_apply ..

Depends on / 依赖: Equiv.piCongrLeft_apply_apply, piCongrLeft_apply_apply
-/
lemma piCongrLeft_apply_apply {ι ι' : Type*} {X : ι' -> Type*} [forall j, UniformSpace (X j)]
    (e : ι ≃ ι') (x : forall i, X (e i)) i : piCongrLeft e x (e i) = x i :=
  Equiv.piCongrLeft_apply_apply ..

/-- `Equiv.piCongrRight` as a uniform isomorphism: this is the natural isomorphism
`Π i, β₁ i ≃ᵤ Π j, β₂ i` obtained from uniform isomorphisms `β₁ i ≃ᵤ β₂ i` for each `i`. -/
@[simps! apply toEquiv]
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: {ι : Type*} {β₁ β₂ : ι -> Type*} [forall i, UniformSpace (β₁ i)]
  body: Pi.uniformContinuous_postcomp' _ fun i => (F i).uniformContinuous
  uniformContinuous_invFun := Pi.uniformContinuous_postcomp' _ fun i => (F i).symm.uniformContinuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]

中文:
定义 piCongrRight
  签名: {ι : 类型} {β₁ β₂ : ι -> 类型} [对任意 i, UniformSpace (β₁ i)]
  定义体: Pi.uniformContinuous_postcomp' _ fun i => (F i).uniformContinuous
  uniformContinuous_invFun := Pi.uniformContinuous_postcomp' _ fun i => (F i).symm.uniformContinuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]

Depends on / 依赖: Pi.uniformContinuous_postcomp, uniformContinuous, uniformContinuous_postcomp
-/
def piCongrRight {ι : Type*} {β₁ β₂ : ι -> Type*} [forall i, UniformSpace (β₁ i)]
    [forall i, UniformSpace (β₂ i)] (F : forall i, β₁ i ≃ᵤ β₂ i) : (forall i, β₁ i) ≃ᵤ forall i, β₂ i where
  uniformContinuous_toFun := Pi.uniformContinuous_postcomp' _ fun i => (F i).uniformContinuous
  uniformContinuous_invFun := Pi.uniformContinuous_postcomp' _ fun i => (F i).symm.uniformContinuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
/--
theorem `piCongrRight_symm` / 定理 `piCongrRight_symm`

English:
theorem piCongrRight_symm
  statement: {ι : Type*} {β₁ β₂ : ι -> Type*} [forall i, UniformSpace (β₁ i)]
  proof: rfl

@[simp]

中文:
定理 piCongrRight_symm
  结论: {ι : 类型} {β₁ β₂ : ι -> 类型} [对任意 i, UniformSpace (β₁ i)]
  证明: rfl

@[simp]
-/
theorem piCongrRight_symm {ι : Type*} {β₁ β₂ : ι -> Type*} [forall i, UniformSpace (β₁ i)]
    [forall i, UniformSpace (β₂ i)] (F : forall i, β₁ i ≃ᵤ β₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

@[simp]
/--
theorem `piCongrRight_refl` / 定理 `piCongrRight_refl`

English:
theorem piCongrRight_refl
  given: {ι : Type*} {X : ι -> Type*} [forall i, UniformSpace (X i)]
  proof: rfl

中文:
定理 piCongrRight_refl
  条件: {ι : 类型} {X : ι -> 类型} [对任意 i, UniformSpace (X i)]
  证明: rfl
-/
theorem piCongrRight_refl {ι : Type*} {X : ι -> Type*} [forall i, UniformSpace (X i)] :
    piCongrRight (fun i => .refl (X i)) = .refl (forall i, X i) :=
  rfl

/-- `Equiv.piCongr` as a uniform isomorphism: this is the natural isomorphism
`Π i₁, β₁ i ≃ᵤ Π i₂, β₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and isomorphisms
`β₁ i₁ ≃ᵤ β₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
/--
Definition of `piCongr` / `piCongr` 的定义

English:
definition piCongr
  signature: {ι₁ ι₂ : Type*} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*}
  body: (UniformEquiv.piCongrRight F).trans (UniformEquiv.piCongrLeft e)

中文:
定义 piCongr
  签名: {ι₁ ι₂ : 类型} {β₁ : ι₁ -> 类型} {β₂ : ι₂ -> 类型}
  定义体: (UniformEquiv.piCongrRight F).trans (UniformEquiv.piCongrLeft e)

Depends on / 依赖: UniformEquiv, UniformEquiv.piCongrLeft, UniformEquiv.piCongrRight, piCongrLeft, piCongrRight
-/
def piCongr {ι₁ ι₂ : Type*} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*}
    [forall i₁, UniformSpace (β₁ i₁)] [forall i₂, UniformSpace (β₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : forall i₁, β₁ i₁ ≃ᵤ β₂ (e i₁)) : (forall i₁, β₁ i₁) ≃ᵤ forall i₂, β₂ i₂ :=
  (UniformEquiv.piCongrRight F).trans (UniformEquiv.piCongrLeft e)

/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: : ULift.{v, u} α ≃ᵤ α
  body: { Equiv.ulift with
    uniformContinuous_toFun := uniformContinuous_comap
    uniformContinuous_invFun := by
      have hf : IsUniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniformContinuous_iff]
      exact uniformContinuous_id }

中文:
定义 ulift
  签名: : ULift.{v, u} α ≃ᵤ α
  定义体: { Equiv.ulift with
    uniformContinuous_toFun := uniformContinuous_comap
    uniformContinuous_invFun := by
      have hf : IsUniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniformContinuous_iff]
      exact uniformContinuous_id }

Depends on / 依赖: Equiv.ulift, IsUniformInducing, hf.uniformContinuous_iff, simp_rw, uniformContinuous_comap, uniformContinuous_id, uniformContinuous_iff, uniformContinuous_invFun, uniformContinuous_toFun
-/
def ulift : ULift.{v, u} α ≃ᵤ α :=
  { Equiv.ulift with
    uniformContinuous_toFun := uniformContinuous_comap
    uniformContinuous_invFun := by
      have hf : IsUniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniformContinuous_iff]
      exact uniformContinuous_id }

end

/-- If `ι` has a unique element, then `ι → α` is uniformly isomorphic to `α`. -/
@[simps! -fullyApplied]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: (ι α : Type*) [Unique ι] [UniformSpace α]
  body: Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id

中文:
定义 funUnique
  签名: (ι α : 类型) [Unique ι] [UniformSpace α]
  定义体: Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id

Depends on / 依赖: Equiv.funUnique, funUnique
-/
def funUnique (ι α : Type*) [Unique ι] [UniformSpace α] : (ι -> α) ≃ᵤ α where
  toEquiv := Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id

/-- Uniform isomorphism between dependent functions `Π i : Fin 2, α i` and `α 0 × α 1`. -/
@[simps! -fullyApplied]
/--
Definition of `piFinTwo` / `piFinTwo` 的定义

English:
definition piFinTwo
  signature: (α : Fin 2 -> Type u) [forall i, UniformSpace (α i)]
  body: piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prodMk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
uniformContinuous_pi.mpr Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩

中文:
定义 piFinTwo
  签名: (α : Fin 2 -> 类型u) [对任意 i, UniformSpace (α i)]
  定义体: piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prodMk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
uniformContinuous_pi.mpr Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩

Depends on / 依赖: piFinTwoEquiv
-/
def piFinTwo (α : Fin 2 -> Type u) [forall i, UniformSpace (α i)] : (forall i, α i) ≃ᵤ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prodMk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
uniformContinuous_pi.mpr Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩

/-- Uniform isomorphism between `α² = Fin 2 → α` and `α × α`. -/
@[simps! -fullyApplied]
/--
Definition of `finTwoArrow` / `finTwoArrow` 的定义

English:
definition finTwoArrow
  signature: (α : Type*) [UniformSpace α]
  body: { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

中文:
定义 finTwoArrow
  签名: (α : 类型) [UniformSpace α]
  定义体: { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

Depends on / 依赖: finTwoArrowEquiv, piFinTwo, toEquiv
-/
def finTwoArrow (α : Type*) [UniformSpace α] : (Fin 2 -> α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (e : α ≃ᵤ β) (s : Set α)
  body: (e.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s

中文:
定义 image
  签名: (e : α ≃ᵤ β) (s : Set α)
  定义体: (e.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s

Depends on / 依赖: e.uniformContinuous.comp, subtype_mk, uniformContinuous, uniformContinuous_subtype_val
-/
def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s where
  uniformContinuous_toFun := (e.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s

/-- A uniform isomorphism `e : α ≃ᵤ β` lifts to subtypes `{ a : α // p a } ≃ᵤ { b : β // q b }`
provided `p = q ∘ e`. -/
@[simps!]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {p : α -> Prop} {q : β -> Prop} (e : α ≃ᵤ β) (h : forall a, p a ↔ q (e a))
  body: by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.uniformContinuous.subtype_map _
  uniformContinuous_invFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.symm.uniformContinuous.subtype_map _
  __ := e.subtypeEquiv h

中文:
定义 subtype
  签名: {p : α -> 命题} {q : β -> 命题} (e : α ≃ᵤ β) (h : 对任意 a, p a ↔ q (e a))
  定义体: by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.uniformContinuous.subtype_map _
  uniformContinuous_invFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.symm.uniformContinuous.subtype_map _
  __ := e.subtypeEquiv h

Depends on / 依赖: Equiv.coe_subtypeEquiv_eq_map, coe_subtypeEquiv_eq_map, e.subtypeEquiv, e.symm.uniformContinuous.subtype_map, e.uniformContinuous.subtype_map, subtypeEquiv, subtype_map, uniformContinuous, uniformContinuous_invFun
-/
def subtype {p : α -> Prop} {q : β -> Prop} (e : α ≃ᵤ β) (h : forall a, p a ↔ q (e a)) :
    { a : α // p a } ≃ᵤ { b : β // q b } where
  uniformContinuous_toFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.uniformContinuous.subtype_map _
  uniformContinuous_invFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.symm.uniformContinuous.subtype_map _
  __ := e.subtypeEquiv h

end UniformEquiv

/--
Definition of `Equiv.toUniformEquivOfIsUniformInducing` / `Equiv.toUniformEquivOfIsUniformInducing` 的定义

English:
definition Equiv.toUniformEquivOfIsUniformInducing
  signature: [UniformSpace α] [UniformSpace β] (f : α ≃ β)
  body: { f with
    uniformContinuous_toFun := hf.uniformContinuous
uniformContinuous_invFun := hf.uniformContinuous_iff.2 by simpa using uniformContinuous_id }

中文:
定义 Equiv.toUniformEquivOfIsUniformInducing
  签名: [UniformSpace α] [UniformSpace β] (f : α ≃ β)
  定义体: { f with
    uniformContinuous_toFun := hf.uniformContinuous
uniformContinuous_invFun := hf.uniformContinuous_iff.2 by simpa using uniformContinuous_id }

Depends on / 依赖: hf.uniformContinuous, hf.uniformContinuous_iff, uniformContinuous, uniformContinuous_id, uniformContinuous_iff, uniformContinuous_invFun, uniformContinuous_toFun
-/
def Equiv.toUniformEquivOfIsUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (hf : IsUniformInducing f) : α ≃ᵤ β :=
  { f with
    uniformContinuous_toFun := hf.uniformContinuous
uniformContinuous_invFun := hf.uniformContinuous_iff.2 by simpa using uniformContinuous_id }
