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
/-- Uniform isomorphism between `α` and `β` -/
/-
**UniformEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_4) → (β : Type u_5) → [UniformSpace α] → [UniformSpace β] → Ty
pe (max u_4 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform isomorphism between `α` and `β`
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

/-
**UniformEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β], Function.Injective UniformEquiv.toEquiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.mk.injEq`：∀ {α : Type u_4} {β : Type u_5} [inst : UniformSp
ace α] [inst_1 : UniformSpace β] (toEquiv : α ≃ β)   (uniformContinuous_toFun : 
UniformCont…
-/
theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ᵤ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, h => by simpa only [mk.injEq]
/-
**UniformEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `UniformEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (α ≃ᵤ β) α β where
  coe h := h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
  coe_injective' _ _ H _ := toEquiv_injective <| DFunLike.ext' H

@[simp]
/-
**UniformEquiv.uniformEquiv_mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：uniformEquiv_mk_coe (a : Equiv α β) (b c) : (UniformEquiv.mk a b c : α -> 
β) = a
参数：a : Equiv α β；b c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformEquiv_mk_coe (a : Equiv α β) (b c) : (UniformEquiv.mk a b c : α → β) = a :=
  rfl

/-- Inverse of a uniform isomorphism. -/
/-
**UniformEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：{α : Type u} → {β : Type u_1} → [inst : UniformSpace α] → [inst_1 : Unifor
mSpace β] → α ≃ᵤ β → β ≃ᵤ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `UniformEquiv.uniformContinuous_invFun`：∀ {α : Type u_4} {β : Type u_5} [
inst : UniformSpace α] [inst_1 : UniformSpace β] (self : α ≃ᵤ β),   UniformConti
nuous self.invFun
· 使用定理 `UniformEquiv.uniformContinuous_toFun`：∀ {α : Type u_4} {β : Type u_5} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] (self : α ≃ᵤ β),   UniformContin
uous self.toFun

--- 原说明 ---
Inverse of a uniform isomorphism.
-/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α where
  uniformContinuous_toFun := h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**UniformEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv.Simps`。
形式化陈述：{α : Type u} → {β : Type u_1} → [inst : UniformSpace α] → [inst_1 : Unifor
mSpace β] → α ≃ᵤ β → α → β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (h : α ≃ᵤ β) : α → β :=
  h

/-- See Note [custom simps projection] -/
/-
**UniformEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv.Simps`。
形式化陈述：{α : Type u} → {β : Type u_1} → [inst : UniformSpace α] → [inst_1 : Unifor
mSpace β] → α ≃ᵤ β → β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (h : α ≃ᵤ β) : β → α :=
  h.symm

initialize_simps_projections UniformEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**UniformEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：coe_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h :=
  rfl

@[simp]
/-
**UniformEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：coe_symm_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl

@[ext]
/-
**UniformEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：ext {h h' : α ≃ᵤ β} (H : forall x, h x = h' x) : h = h'
参数：H : forall x, h x = h' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.toEquiv_injective`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β], Function.Injective UniformEquiv.toEquiv
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
-/
theorem ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
  toEquiv_injective <| Equiv.ext H

/-- Identity map as a uniform isomorphism. -/
@[simps! -fullyApplied apply]
/-
**UniformEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：(α : Type u_4) → [inst : UniformSpace α] → α ≃ᵤ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)

--- 原说明 ---
Identity map as a uniform isomorphism.
-/
protected def refl (α : Type*) [UniformSpace α] : α ≃ᵤ α where
  uniformContinuous_toFun := uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α

/-- Composition of two uniform isomorphisms. -/
/-
**UniformEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：{α : Type u} →   {β : Type u_1} →     {γ : Type u_2} →       [inst : Unifo
rmSpace α] → [inst_1 : UniformSpace β] → [inst_2 : UniformSpace γ] → α ≃ᵤ β → β 
≃ᵤ γ → α ≃ᵤ γ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of two uniform isomorphisms.
-/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ where
  uniformContinuous_toFun := h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
/-
**UniformEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a
)
参数：h₁ : α ≃ᵤ β；h₂ : β ≃ᵤ γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl

@[simp]
/-
**UniformEquiv.uniformEquiv_mk_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`
。
形式化陈述：uniformEquiv_mk_coe_symm (a : Equiv α β) (b c) : ((UniformEquiv.mk a b c).
symm : β -> α) = a.symm
参数：a : Equiv α β；b c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformEquiv_mk_coe_symm (a : Equiv α β) (b c) :
    ((UniformEquiv.mk a b c).symm : β → α) = a.symm :=
  rfl

@[simp]
/-
**UniformEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α :=
  rfl
/-
**UniformEquiv.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), UniformContinuous ⇑h
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.uniformContinuous_toFun`：∀ {α : Type u_4} {β : Type u_5} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] (self : α ≃ᵤ β),   UniformContin
uous self.toFun
-/
protected theorem uniformContinuous (h : α ≃ᵤ β) : UniformContinuous h :=
  h.uniformContinuous_toFun

@[continuity]
/-
**UniformEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), Continuous ⇑h
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformEquiv.uniformContinuous`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h
-/
protected theorem continuous (h : α ≃ᵤ β) : Continuous h :=
  h.uniformContinuous.continuous
/-
**UniformEquiv.uniformContinuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), UniformContinuous ⇑h.symm
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.uniformContinuous_invFun`：∀ {α : Type u_4} {β : Type u_5} [
inst : UniformSpace α] [inst_1 : UniformSpace β] (self : α ≃ᵤ β),   UniformConti
nuous self.invFun
-/
protected theorem uniformContinuous_symm (h : α ≃ᵤ β) : UniformContinuous h.symm :=
  h.uniformContinuous_invFun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
/-
**UniformEquiv.continuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), Continuous ⇑h.symm
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformEquiv.uniformContinuous_symm`：∀ {α : Type u} {β : Type u_1} [inst
 : UniformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h.
symm
-/
protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm :=
  h.uniformContinuous_symm.continuous

/-- A uniform isomorphism as a homeomorphism. -/
/-
**UniformEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：{α : Type u} → {β : Type u_1} → [inst : UniformSpace α] → [inst_1 : Unifor
mSpace β] → α ≃ᵤ β → α ≃ₜ β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.continuous`：∀ {α : Type u} {β : Type u_1} [inst : UniformSp
ace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), Continuous ⇑h
· 使用定理 `UniformEquiv.continuous_symm`：∀ {α : Type u} {β : Type u_1} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), Continuous ⇑h.symm

--- 原说明 ---
A uniform isomorphism as a homeomorphism.
-/
protected def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }
/-
**UniformEquiv.toHomeomorph_apply** 是 Mathlib 中的一个引理，位于命名空间 `UniformEquiv`。
形式化陈述：toHomeomorph_apply (e : α ≃ᵤ β) : (e.toHomeomorph : α -> β) = e
参数：e : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHomeomorph_apply (e : α ≃ᵤ β) : (e.toHomeomorph : α → β) = e := rfl
/-
**UniformEquiv.toHomeomorph_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `UniformEquiv`。
形式化陈述：toHomeomorph_symm_apply (e : α ≃ᵤ β) : (e.toHomeomorph.symm : β -> α) = e.
symm
参数：e : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHomeomorph_symm_apply (e : α ≃ᵤ β) : (e.toHomeomorph.symm : β → α) = e.symm := rfl

@[simp]
/-
**UniformEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x
参数：h : α ≃ᵤ β；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
/-
**UniformEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x
参数：h : α ≃ᵤ β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
/-
**UniformEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), Function.Bijective ⇑h
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (h : α ≃ᵤ β) : Function.Bijective h :=
  h.toEquiv.bijective
/-
**UniformEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), Function.Injective ⇑h
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (h : α ≃ᵤ β) : Function.Injective h :=
  h.toEquiv.injective
/-
**UniformEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：∀ {α : Type u} {β : Type u_1} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β] (h : α ≃ᵤ β), Function.Surjective ⇑h
参数：h : α ≃ᵤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (h : α ≃ᵤ β) : Function.Surjective h :=
  h.toEquiv.surjective

/-- Change the uniform equiv `f` to make the inverse function definitionally equal to `g`. -/
/-
**UniformEquiv.changeInv** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：changeInv (f : α ≃ᵤ β) (g : β -> α) (hg : Function.RightInverse g f) : α ≃
ᵤ β
参数：f : α ≃ᵤ β；g : β -> α；hg : Function.RightInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.uniformContinuous`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h

--- 原说明 ---
Change the uniform equiv `f` to make the inverse function definitionally equal t
o `g`.
-/
def changeInv (f : α ≃ᵤ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
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
/-
**UniformEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：symm_comp_self (h : α ≃ᵤ β) : (h.symm : β -> α) ∘ h = id
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformEquiv.symm_apply_apply`：symm_apply_apply (h : α ≃ᵤ β) (x : α) : h
.symm (h x) = x
-/
theorem symm_comp_self (h : α ≃ᵤ β) : (h.symm : β → α) ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
/-
**UniformEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：self_comp_symm (h : α ≃ᵤ β) : (h : α -> β) ∘ h.symm = id
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵤ β) (x : β) : h
 (h.symm x) = x
-/
theorem self_comp_symm (h : α ≃ᵤ β) : (h : α → β) ∘ h.symm = id :=
  funext h.apply_symm_apply
/-
**UniformEquiv.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：range_coe (h : α ≃ᵤ β) : range h = univ
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_coe (h : α ≃ᵤ β) : range h = univ := by simp
/-
**UniformEquiv.image_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：image_symm (h : α ≃ᵤ β) : image h.symm = preimage h
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_symm (h : α ≃ᵤ β) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage_symm
/-
**UniformEquiv.preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：preimage_symm (h : α ≃ᵤ β) : preimage h.symm = image h
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem preimage_symm (h : α ≃ᵤ β) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]
/-
**UniformEquiv.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' h ⁻¹' s = s
参数：h : α ≃ᵤ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
-/
theorem image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' h ⁻¹' s = s :=
  h.toEquiv.image_preimage s

@[simp]
/-
**UniformEquiv.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' h '' s = s
参数：h : α ≃ᵤ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
-/
theorem preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' h '' s = s :=
  h.toEquiv.preimage_image s
/-
**UniformEquiv.isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：isUniformInducing (h : α ≃ᵤ β) : IsUniformInducing h
参数：h : α ≃ᵤ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.of_comp`：IsUniformInducing.of_comp {f : α -> β} {g : β
 -> γ} (hf : UniformContinuous f) (hg : UniformContinuous g) (hgf : IsUniformInd
ucing (g ∘ f)) …
· 使用定理 `UniformEquiv.uniformContinuous`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformEquiv.symm_comp_self`：symm_comp_self (h : α ≃ᵤ β) : (h.symm : β -
> α) ∘ h = id
-/
theorem isUniformInducing (h : α ≃ᵤ β) : IsUniformInducing h :=
  IsUniformInducing.of_comp h.uniformContinuous h.symm.uniformContinuous <| by
    simp only [symm_comp_self, IsUniformInducing.id]
/-
**UniformEquiv.comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_›
参数：h : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.comap_uniformSpace`：∀ {α : Type u} {β : Type v} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 UniformSpace.comap f inst…
· 使用定理 `UniformEquiv.isUniformInducing`：isUniformInducing (h : α ≃ᵤ β) : IsUnifo
rmInducing h
-/
theorem comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_› :=
  h.isUniformInducing.comap_uniformSpace
/-
**UniformEquiv.isUniformEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `UniformEquiv`。
形式化陈述：isUniformEmbedding (h : α ≃ᵤ β) : IsUniformEmbedding h
参数：h : α ≃ᵤ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.isUniformInducing`：isUniformInducing (h : α ≃ᵤ β) : IsUnifo
rmInducing h
· 使用定理 `UniformEquiv.injective`：∀ {α : Type u} {β : Type u_1} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), Function.Injective ⇑h
-/
lemma isUniformEmbedding (h : α ≃ᵤ β) : IsUniformEmbedding h := ⟨h.isUniformInducing, h.injective⟩
/-
**UniformEquiv.completeSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：completeSpace_iff (h : α ≃ᵤ β) : CompleteSpace α ↔ CompleteSpace β
参数：h : α ≃ᵤ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `completeSpace_congr`：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbe
dding e) : CompleteSpace α ↔ CompleteSpace β
· 使用引理 `UniformEquiv.isUniformEmbedding`：isUniformEmbedding (h : α ≃ᵤ β) : IsUni
formEmbedding h
-/
theorem completeSpace_iff (h : α ≃ᵤ β) : CompleteSpace α ↔ CompleteSpace β :=
  completeSpace_congr h.isUniformEmbedding

/-- Uniform equiv given a uniform embedding. -/
/-
**UniformEquiv.ofIsUniformEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：ofIsUniformEmbedding (f : α -> β) (hf : IsUniformEmbedding f) : α ≃ᵤ Set.r
ange f where uniformContinuous_toFun
参数：f : α -> β；hf : IsUniformEmbedding f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f

--- 原说明 ---
Uniform equiv given a uniform embedding.
-/
noncomputable def ofIsUniformEmbedding (f : α → β) (hf : IsUniformEmbedding f) :
    α ≃ᵤ Set.range f where
  uniformContinuous_toFun := hf.isUniformInducing.uniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    rw [hf.isUniformInducing.uniformContinuous_iff, Equiv.invFun_as_coe,
      Equiv.self_comp_ofInjective_symm]
    exact uniformContinuous_subtype_val
  toEquiv := Equiv.ofInjective f hf.injective

/-- If two sets are equal, then they are uniformly equivalent. -/
/-
**UniformEquiv.setCongr** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t where uniformContinuous_toFun
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two sets are equal, then they are uniformly equivalent.
-/
def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t where
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h

/-- Product of two uniform isomorphisms. -/
/-
**UniformEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ where uniformContin
uous_toFun
参数：h₁ : α ≃ᵤ β；h₂ : γ ≃ᵤ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two uniform isomorphisms.
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
/-
**UniformEquiv.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：prodCongr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : (h₁.prodCongr h₂).symm = h₁.s
ymm.prodCongr h₂.symm
参数：h₁ : α ≃ᵤ β；h₂ : γ ≃ᵤ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
/-
**UniformEquiv.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：coe_prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map 
h₁ h₂
参数：h₁ : α ≃ᵤ β；h₂ : γ ≃ᵤ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (α β γ)

/-- `α × β` is uniformly isomorphic to `β × α`. -/
/-
**UniformEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：prodComm : α × β ≃ᵤ β × α where uniformContinuous_toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α × β` is uniformly isomorphic to `β × α`.
-/
def prodComm : α × β ≃ᵤ β × α where
  uniformContinuous_toFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β

@[simp]
/-
**UniformEquiv.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：prodComm_symm : (prodComm α β).symm = prodComm β α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_symm : (prodComm α β).symm = prodComm β α :=
  rfl

@[simp]
/-
**UniformEquiv.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：coe_prodComm : ⇑(prodComm α β) = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm : ⇑(prodComm α β) = Prod.swap :=
  rfl

/-- `(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`. -/
/-
**UniformEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：prodAssoc : (α × β) × γ ≃ᵤ α × β × γ where uniformContinuous_toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`.
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
/-
**UniformEquiv.prodPUnit** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：prodPUnit : α × PUnit ≃ᵤ α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1

--- 原说明 ---
`α × {*}` is uniformly isomorphic to `α`.
-/
def prodPUnit : α × PUnit ≃ᵤ α where
  toEquiv := Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prodMk uniformContinuous_const

@[deprecated (since := "2026-02-08")] alias prodPunit := prodPUnit

/-- `{*} × α` is uniformly isomorphic to `α`. -/
/-
**UniformEquiv.punitProd** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：punitProd : PUnit × α ≃ᵤ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{*} × α` is uniformly isomorphic to `α`.
-/
def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPUnit _)

@[simp]
/-
**UniformEquiv.coe_punitProd** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：coe_punitProd : ⇑(punitProd α) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_punitProd : ⇑(punitProd α) = Prod.snd :=
  rfl

/-- `Equiv.piCongrLeft` as a uniform isomorphism: this is the natural isomorphism
`Π i, β (e i) ≃ᵤ Π j, β j` obtained from a bijection `ι ≃ ι'`. -/
@[simps toEquiv, simps! -isSimp apply]
/-
**UniformEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrLeft {ι ι' : Type*} {β : ι' -> Type*} [forall j, UniformSpace (β j)
] (e : ι ≃ ι') : (forall i, β (e i)) ≃ᵤ forall j, β j where uniformContinuous_to
Fun
参数：β j；e : ι ≃ ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCongrLeft` as a uniform isomorphism: this is the natural isomorphism
`Π i, β (e i) ≃ᵤ Π j, β j` obtained from a bijection `ι ≃ ι'`.
-/
def piCongrLeft {ι ι' : Type*} {β : ι' → Type*} [∀ j, UniformSpace (β j)]
    (e : ι ≃ ι') : (∀ i, β (e i)) ≃ᵤ ∀ j, β j where
  uniformContinuous_toFun := uniformContinuous_pi.mpr <| e.forall_congr_right.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using
      Pi.uniformContinuous_proj _ i
  uniformContinuous_invFun := Pi.uniformContinuous_precomp' _ e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]
/-
**UniformEquiv.piCongrLeft_refl** 是 Mathlib 中的一个引理，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrLeft_refl {ι : Type*} {X : ι -> Type*} [forall i, UniformSpace (X i
)] : piCongrLeft (.refl ι) = .refl (forall i, X i)
参数：X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma piCongrLeft_refl {ι : Type*} {X : ι → Type*} [∀ i, UniformSpace (X i)] :
    piCongrLeft (.refl ι) = .refl (∀ i, X i) :=
  rfl

@[simp]
/-
**UniformEquiv.piCongrLeft_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrLeft_symm_apply {ι ι' : Type*} {X : ι' -> Type*} [forall j, Uniform
Space (X j)] (e : ι ≃ ι') : ⇑(piCongrLeft (β
参数：X j；e : ι ≃ ι'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piCongrLeft_symm_apply {ι ι' : Type*} {X : ι' → Type*} [∀ j, UniformSpace (X j)]
    (e : ι ≃ ι') : ⇑(piCongrLeft (β := X) e).symm = (· <| e ·) :=
  rfl

@[simp]
/-
**UniformEquiv.piCongrLeft_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrLeft_apply_apply {ι ι' : Type*} {X : ι' -> Type*} [forall j, Unifor
mSpace (X j)] (e : ι ≃ ι') (x : forall i, X (e i)) i : piCongrLeft e x (e i) = x
 i
参数：X j；e : ι ≃ ι'；x : forall i, X (e i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.piCongrLeft_apply_apply`：piCongrLeft_apply_apply (f : forall a, P 
(e a)) (a : α) : (piCongrLeft P e) f (e a) = f a
-/
lemma piCongrLeft_apply_apply {ι ι' : Type*} {X : ι' → Type*} [∀ j, UniformSpace (X j)]
    (e : ι ≃ ι') (x : ∀ i, X (e i)) i : piCongrLeft e x (e i) = x i :=
  Equiv.piCongrLeft_apply_apply ..

/-- `Equiv.piCongrRight` as a uniform isomorphism: this is the natural isomorphism
`Π i, β₁ i ≃ᵤ Π j, β₂ i` obtained from uniform isomorphisms `β₁ i ≃ᵤ β₂ i` for each `i`. -/
@[simps! apply toEquiv]
/-
**UniformEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrRight {ι : Type*} {β₁ β₂ : ι -> Type*} [forall i, UniformSpace (β₁ 
i)] [forall i, UniformSpace (β₂ i)] (F : forall i, β₁ i ≃ᵤ β₂ i) : (forall i, β₁
 i) ≃ᵤ forall i, β₂ i where uniformContinuous_toFun
参数：β₁ i；β₂ i；F : forall i, β₁ i ≃ᵤ β₂ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCongrRight` as a uniform isomorphism: this is the natural isomorphism
`Π i, β₁ i ≃ᵤ Π j, β₂ i` obtained from uniform isomorphisms `β₁ i ≃ᵤ β₂ i` for e
ach `i`.
-/
def piCongrRight {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, UniformSpace (β₁ i)]
    [∀ i, UniformSpace (β₂ i)] (F : ∀ i, β₁ i ≃ᵤ β₂ i) : (∀ i, β₁ i) ≃ᵤ ∀ i, β₂ i where
  uniformContinuous_toFun := Pi.uniformContinuous_postcomp' _ fun i ↦ (F i).uniformContinuous
  uniformContinuous_invFun := Pi.uniformContinuous_postcomp' _ fun i ↦ (F i).symm.uniformContinuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
/-
**UniformEquiv.piCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrRight_symm {ι : Type*} {β₁ β₂ : ι -> Type*} [forall i, UniformSpace
 (β₁ i)] [forall i, UniformSpace (β₂ i)] (F : forall i, β₁ i ≃ᵤ β₂ i) : (piCongr
Right F).symm = piCongrRight fun i => (F i).symm
参数：β₁ i；β₂ i；F : forall i, β₁ i ≃ᵤ β₂ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, UniformSpace (β₁ i)]
    [∀ i, UniformSpace (β₂ i)] (F : ∀ i, β₁ i ≃ᵤ β₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

@[simp]
/-
**UniformEquiv.piCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `UniformEquiv`。
形式化陈述：piCongrRight_refl {ι : Type*} {X : ι -> Type*} [forall i, UniformSpace (X 
i)] : piCongrRight (fun i => .refl (X i)) = .refl (forall i, X i)
参数：X i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_refl {ι : Type*} {X : ι → Type*} [∀ i, UniformSpace (X i)] :
    piCongrRight (fun i ↦ .refl (X i)) = .refl (∀ i, X i) :=
  rfl

/-- `Equiv.piCongr` as a uniform isomorphism: this is the natural isomorphism
`Π i₁, β₁ i ≃ᵤ Π i₂, β₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and isomorphisms
`β₁ i₁ ≃ᵤ β₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
/-
**UniformEquiv.piCongr** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：piCongr {ι₁ ι₂ : Type*} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} [forall i₁, 
UniformSpace (β₁ i₁)] [forall i₂, UniformSpace (β₂ i₂)] (e : ι₁ ≃ ι₂) (F : foral
l i₁, β₁ i₁ ≃ᵤ β₂ (e i₁)) : (forall i₁, β₁ i₁) ≃ᵤ forall i₂, β₂ i₂
参数：β₁ i₁；β₂ i₂；e : ι₁ ≃ ι₂；F : forall i₁, β₁ i₁ ≃ᵤ β₂ (e i₁)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCongr` as a uniform isomorphism: this is the natural isomorphism
`Π i₁, β₁ i ≃ᵤ Π i₂, β₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and isomorphisms
`β₁ i₁ ≃ᵤ β₂ (e i₁)` for each `i₁ : ι₁`.
-/
def piCongr {ι₁ ι₂ : Type*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*}
    [∀ i₁, UniformSpace (β₁ i₁)] [∀ i₂, UniformSpace (β₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, β₁ i₁ ≃ᵤ β₂ (e i₁)) : (∀ i₁, β₁ i₁) ≃ᵤ ∀ i₂, β₂ i₂ :=
  (UniformEquiv.piCongrRight F).trans (UniformEquiv.piCongrLeft e)

/-- Uniform equivalence between `ULift α` and `α`. -/
/-
**UniformEquiv.ulift** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：ulift : ULift.{v, u} α ≃ᵤ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform equivalence between `ULift α` and `α`.
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
/-
**UniformEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：funUnique (ι α : Type*) [Unique ι] [UniformSpace α] : (ι -> α) ≃ᵤ α where 
toEquiv
参数：ι α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` has a unique element, then `ι → α` is uniformly isomorphic to `α`.
-/
def funUnique (ι α : Type*) [Unique ι] [UniformSpace α] : (ι → α) ≃ᵤ α where
  toEquiv := Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id

/-- Uniform isomorphism between dependent functions `Π i : Fin 2, α i` and `α 0 × α 1`. -/
@[simps! -fullyApplied]
/-
**UniformEquiv.piFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：piFinTwo (α : Fin 2 -> Type u) [forall i, UniformSpace (α i)] : (forall i,
 α i) ≃ᵤ α 0 × α 1 where toEquiv
参数：α : Fin 2 -> Type u；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform isomorphism between dependent functions `Π i : Fin 2, α i` and `α 0 × α 
1`.
-/
def piFinTwo (α : Fin 2 → Type u) [∀ i, UniformSpace (α i)] : (∀ i, α i) ≃ᵤ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prodMk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
    uniformContinuous_pi.mpr <| Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩

/-- Uniform isomorphism between `α² = Fin 2 → α` and `α × α`. -/
@[simps! -fullyApplied]
/-
**UniformEquiv.finTwoArrow** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：finTwoArrow (α : Type*) [UniformSpace α] : (Fin 2 -> α) ≃ᵤ α × α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform isomorphism between `α² = Fin 2 → α` and `α × α`.
-/
def finTwoArrow (α : Type*) [UniformSpace α] : (Fin 2 → α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

/-- A subset of a uniform space is uniformly isomorphic to its image under a uniform isomorphism.
-/
/-
**UniformEquiv.image** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s where uniformContinuous_toFun
参数：e : α ≃ᵤ β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a uniform space is uniformly isomorphic to its image under a uniform
 isomorphism.
-/
def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s where
  uniformContinuous_toFun := (e.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s

/-- A uniform isomorphism `e : α ≃ᵤ β` lifts to subtypes `{ a : α // p a } ≃ᵤ { b : β // q b }`
provided `p = q ∘ e`. -/
@[simps!]
/-
**UniformEquiv.subtype** 是 Mathlib 中的一个定义，位于命名空间 `UniformEquiv`。
形式化陈述：subtype {p : α -> Prop} {q : β -> Prop} (e : α ≃ᵤ β) (h : forall a, p a ↔ 
q (e a)) : { a : α // p a } ≃ᵤ { b : β // q b } where uniformContinuous_toFun
参数：e : α ≃ᵤ β；h : forall a, p a ↔ q (e a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform isomorphism `e : α ≃ᵤ β` lifts to subtypes `{ a : α // p a } ≃ᵤ { b : 
β // q b }`
provided `p = q ∘ e`.
-/
def subtype {p : α → Prop} {q : β → Prop} (e : α ≃ᵤ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ᵤ { b : β // q b } where
  uniformContinuous_toFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.uniformContinuous.subtype_map _
  uniformContinuous_invFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.symm.uniformContinuous.subtype_map _
  __ := e.subtypeEquiv h

end UniformEquiv

/-- A uniform inducing equiv between uniform spaces is a uniform isomorphism. -/
/-
**Equiv.toUniformEquivOfIsUniformInducing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.toUniformEquivOfIsUniformInducing [UniformSpace α] [UniformSpace β] 
(f : α ≃ β) (hf : IsUniformInducing f) : α ≃ᵤ β
参数：f : α ≃ β；hf : IsUniformInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform inducing equiv between uniform spaces is a uniform isomorphism.
-/
def Equiv.toUniformEquivOfIsUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (hf : IsUniformInducing f) : α ≃ᵤ β :=
  { f with
    uniformContinuous_toFun := hf.uniformContinuous
    uniformContinuous_invFun := hf.uniformContinuous_iff.2 <| by simpa using uniformContinuous_id }
