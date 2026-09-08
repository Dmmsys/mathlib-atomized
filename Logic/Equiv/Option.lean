/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Control.EquivFunctor
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences for `Option α`


We define
* `Equiv.optionCongr`: the `Option α ≃ Option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying `e` elsewhere.
* `Equiv.removeNone`: the `α ≃ β` constructed from `Option α ≃ Option β` by removing `none` from
  both sides.
-/

@[expose] public section

universe u

namespace Equiv

open Option

variable {α β γ : Type*}

section OptionCongr

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv Option e`. -/
@[simps (attr := grind =) apply]
/-
**Equiv.optionCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：optionCongr (e : α ≃ β) : Option α ≃ Option β where toFun
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A universe-polymorphic version of `EquivFunctor.mapEquiv Option e`.
-/
def optionCongr (e : α ≃ β) : Option α ≃ Option β where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := (Option.map_map _ _ _).trans <| e.symm_comp_self.symm ▸ congr_fun Option.map_id x
  right_inv x := (Option.map_map _ _ _).trans <| e.self_comp_symm.symm ▸ congr_fun Option.map_id x

@[simp]
/-
**Equiv.optionCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionCongr_refl : optionCongr (Equiv.refl α) = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Option.map_id`：∀ {α : Type u_1}, Option.map id = id
-/
theorem optionCongr_refl : optionCongr (Equiv.refl α) = Equiv.refl _ :=
  ext <| congr_fun Option.map_id

@[simp, grind =]
/-
**Equiv.optionCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionCongr_symm (e : α ≃ β) : optionCongr e.symm = (optionCongr e).symm
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem optionCongr_symm (e : α ≃ β) : optionCongr e.symm = (optionCongr e).symm :=
  rfl

@[simp]
/-
**Equiv.optionCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : optionCongr (e₁.trans e₂) = 
(optionCongr e₁).trans (optionCongr e₂)
参数：e₁ : α ≃ β；e₂ : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
-/
theorem optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    optionCongr (e₁.trans e₂) = (optionCongr e₁).trans (optionCongr e₂) := by
  ext x : 1
  symm
  apply Option.map_map

/-- When `α` and `β` are in the same universe, this is the same as the result of
`EquivFunctor.mapEquiv`. -/
/-
**Equiv.optionCongr_eq_equivFunctor_mapEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionCongr_eq_equivFunctor_mapEquiv {α β : Type u} (e : α ≃ β) : optionCo
ngr e = EquivFunctor.mapEquiv Option e
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` and `β` are in the same universe, this is the same as the result of
`EquivFunctor.mapEquiv`.
-/
theorem optionCongr_eq_equivFunctor_mapEquiv {α β : Type u} (e : α ≃ β) :
    optionCongr e = EquivFunctor.mapEquiv Option e :=
  rfl

end OptionCongr

section RemoveNone

variable (e : Option α ≃ Option β)

/-- If we have a value on one side of an `Equiv` of `Option`
we also have a value on the other side of the equivalence
-/
/-
**Equiv.removeNoneAux** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：removeNoneAux (x : α) : β
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have a value on one side of an `Equiv` of `Option`
we also have a value on the other side of the equivalence
-/
def removeNoneAux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        exact Option.some_ne_none _ (e.injective h)
/-
**Equiv.removeNoneAux_some** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNoneAux_some {x : α} (h : exists x', e (some x) = some x') : some (r
emoveNoneAux e x) = e (some x)
参数：h : exists x', e (some x) = some x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.isSome_iff_exists`：∀ {α : Type u_1} {x : Option α}, x.isSome = tr
ue ↔ ∃ a, x = some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
-/
theorem removeNoneAux_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNoneAux e x) = e (some x) := by
  simp [removeNoneAux, Option.isSome_iff_exists.mpr h]
/-
**Equiv.removeNoneAux_none** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNoneAux_none {x : α} (h : e (some x) = none) : some (removeNoneAux e
 x) = e none
参数：h : e (some x) = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.not_isSome_iff_eq_none`：∀ {α : Type u_1} {o : Option α}, ¬o.isSom
e = true ↔ o = none
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem removeNoneAux_none {x : α} (h : e (some x) = none) :
    some (removeNoneAux e x) = e none := by
  simp [removeNoneAux, Option.not_isSome_iff_eq_none.mpr h]

-- FIXME: This declaration is misnamed.
/-
**Equiv.removeNoneAux_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNoneAux_inv (x : α) : removeNoneAux e.symm (removeNoneAux e x) = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.removeNoneAux_none`：removeNoneAux_none {x : α} (h : e (some x) = n
one) : some (removeNoneAux e x) = e none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Equiv.removeNoneAux_some`：removeNoneAux_some {x : α} (h : exists x', e (
some x) = some x') : some (removeNoneAux e x) = e (some x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem removeNoneAux_inv (x : α) : removeNoneAux e.symm (removeNoneAux e x) = x :=
  Option.some_injective _
    (by
      cases h1 : e.symm (some (removeNoneAux e x)) <;> cases h2 : e (some x)
      · rw [removeNoneAux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm
      · rw [removeNoneAux_some _ ⟨_, h2⟩] at h1
        simp at h1
      · rw [removeNoneAux_none _ h2] at h1
        simp at h1
      · rw [removeNoneAux_some _ ⟨_, h1⟩]
        rw [removeNoneAux_some _ ⟨_, h2⟩]
        simp)

@[deprecated (since := "2026-06-06")] alias removeNone_aux := removeNoneAux
@[deprecated (since := "2026-06-06")] alias removeNone_aux_none := removeNoneAux_none
@[deprecated (since := "2026-06-06")] alias removeNone_aux_some := removeNoneAux_some
@[deprecated (since := "2026-06-06")] alias removeNone_aux_inv := removeNoneAux_inv

/-- Given an equivalence between two `Option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
/-
**Equiv.removeNone** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：removeNone : α ≃ β where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.removeNoneAux_inv`：removeNoneAux_inv (x : α) : removeNoneAux e.sym
m (removeNoneAux e x) = x

--- 原说明 ---
Given an equivalence between two `Option` types, eliminate `none` from that equi
valence by
mapping `e.symm none` to `e none`.
-/
def removeNone : α ≃ β where
  toFun := removeNoneAux e
  invFun := removeNoneAux e.symm
  left_inv := removeNoneAux_inv e
  right_inv := removeNoneAux_inv e.symm

@[simp]
/-
**Equiv.removeNone_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNone_symm : (removeNone e).symm = removeNone e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem removeNone_symm : (removeNone e).symm = removeNone e.symm :=
  rfl
/-
**Equiv.removeNone_some** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNone_some {x : α} (h : exists x', e (some x) = some x') : some (remo
veNone e x) = e (some x)
参数：h : exists x', e (some x) = some x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.removeNoneAux_some`：removeNoneAux_some {x : α} (h : exists x', e (
some x) = some x') : some (removeNoneAux e x) = e (some x)
-/
theorem removeNone_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone e x) = e (some x) :=
  removeNoneAux_some e h
/-
**Equiv.removeNone_none** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNone_none {x : α} (h : e (some x) = none) : some (removeNone e x) = 
e none
参数：h : e (some x) = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.removeNoneAux_none`：removeNoneAux_none {x : α} (h : e (some x) = n
one) : some (removeNoneAux e x) = e none
-/
theorem removeNone_none {x : α} (h : e (some x) = none) : some (removeNone e x) = e none :=
  removeNoneAux_none e h

@[simp]
/-
**Equiv.option_symm_apply_none_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：option_symm_apply_none_iff : e.symm none = none ↔ e none = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
  ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩
/-
**Equiv.some_removeNone_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：some_removeNone_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none
 = some x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.removeNone_none`：removeNone_none {x : α} (h : e (some x) = none) :
 some (removeNone e x) = e none
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.removeNone_some`：removeNone_some {x : α} (h : exists x', e (some x
) = some x') : some (removeNone e x) = e (some x)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem some_removeNone_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none = some x := by
  rcases h : e (some x) with a | a
  · rw [removeNone_none _ h]
    simpa using (congr_arg e.symm h).symm
  · rw [removeNone_some _ ⟨a, h⟩]
    have h1 := congr_arg e.symm h
    rw [symm_apply_apply] at h1
    simp only [apply_eq_iff_eq, reduceCtorEq]
    simp [h1]

@[simp]
/-
**Equiv.removeNone_optionCongr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：removeNone_optionCongr (e : α ≃ β) : removeNone e.optionCongr = e
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Equiv.removeNone_some`：removeNone_some {x : α} (h : exists x', e (some x
) = some x') : some (removeNone e x) = e (some x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem removeNone_optionCongr (e : α ≃ β) : removeNone e.optionCongr = e :=
  Equiv.ext fun x => Option.some_injective _ <| removeNone_some _ ⟨e x, by simp⟩

end RemoveNone

/-
**Equiv.optionCongr_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionCongr_injective : Function.Injective (optionCongr : α ≃ β -> Option 
α ≃ Option β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Equiv.removeNone_optionCongr`：removeNone_optionCongr (e : α ≃ β) : remov
eNone e.optionCongr = e
-/
theorem optionCongr_injective : Function.Injective (optionCongr : α ≃ β → Option α ≃ Option β) :=
  Function.LeftInverse.injective removeNone_optionCongr

set_option backward.isDefEq.respectTransparency false in
/-- Equivalences between `Option α` and `β` that send `none` to `x` are equivalent to
equivalences between `α` and `{y : β // y ≠ x}`. -/
/-
**Equiv.optionSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：optionSubtype [DecidableEq β] (x : β) : { e : Option α ≃ β // e none = x }
 ≃ (α ≃ { y : β // y != x }) where toFun e
参数：x : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x

--- 原说明 ---
Equivalences between `Option α` and `β` that send `none` to `x` are equivalent t
o
equivalences between `α` and `{y : β // y ≠ x}`.
-/
def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y ≠ x }) where
  toFun e :=
    { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((eq_symm_apply _).2 e.property).symm).2 b.property)),
      left_inv := fun a => by
        rw [← some_inj, some_get]
        exact symm_apply_apply (e : Option α ≃ β) a,
      right_inv := fun b => by
        ext
        simp }
  invFun e :=
    ⟨{  toFun := fun a => casesOn' a x (Subtype.val ∘ e),
        invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩,
        left_inv := fun a => by
          cases a with
          | none => simp
          | some a =>
            simp only [casesOn'_some, Function.comp_apply, Subtype.coe_eta,
              symm_apply_apply, dite_eq_ite]
            exact if_neg (e a).property,
        right_inv := fun b => by
          by_cases h : b = x <;> simp [h] },
      rfl⟩
  left_inv e := by
    ext a
    cases a
    · simpa using e.property.symm
    · simp
  right_inv e := by
    ext a
    rfl

@[simp]
/-
**Equiv.optionSubtype_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionSubtype_apply_apply [DecidableEq β] (x : β) (e : { e : Option α ≃ β 
// e none = x }) (a : α) (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩
参数：x : β；e : { e : Option α ≃ β // e none = x }；a : α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α)
    (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩ := rfl

@[simp]
/-
**Equiv.coe_optionSubtype_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_optionSubtype_apply_apply [DecidableEq β] (x : β) (e : { e : Option α 
≃ β // e none = x }) (a : α) : ↑(optionSubtype x e a) = (e : Option α ≃ β) a
参数：x : β；e : { e : Option α ≃ β // e none = x }；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α) : ↑(optionSubtype x e a) = (e : Option α ≃ β) a := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Equiv.optionSubtype_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionSubtype_apply_symm_apply [DecidableEq β] (x : β) (e : { e : Option α
 ≃ β // e none = x }) (b : { y : β // y != x }) : ↑((optionSubtype x e).symm b) 
= (e : Option α ≃ β).symm b
参数：x : β；e : { e : Option α ≃ β // e none = x }；b : { y : β // y != x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem optionSubtype_apply_symm_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (b : { y : β // y ≠ x }) : ↑((optionSubtype x e).symm b) = (e : Option α ≃ β).symm b := by
  dsimp only [optionSubtype]
  simp

@[simp]
/-
**Equiv.optionSubtype_symm_apply_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionSubtype_symm_apply_apply_coe [DecidableEq β] (x : β) (e : α ≃ { y : 
β // y != x }) (a : α) : ((optionSubtype x).symm e : Option α ≃ β) a = e a
参数：x : β；e : α ≃ { y : β // y != x }；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem optionSubtype_symm_apply_apply_coe [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) a = e a :=
  rfl

@[simp]
/-
**Equiv.optionSubtype_symm_apply_apply_some** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionSubtype_symm_apply_apply_some [DecidableEq β] (x : β) (e : α ≃ { y :
 β // y != x }) (a : α) : ((optionSubtype x).symm e : Option α ≃ β) (some a) = e
 a
参数：x : β；e : α ≃ { y : β // y != x }；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem optionSubtype_symm_apply_apply_some
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y ≠ x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) (some a) = e a :=
  rfl

@[simp]
/-
**Equiv.optionSubtype_symm_apply_apply_none** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionSubtype_symm_apply_apply_none [DecidableEq β] (x : β) (e : α ≃ { y :
 β // y != x }) : ((optionSubtype x).symm e : Option α ≃ β) none = x
参数：x : β；e : α ≃ { y : β // y != x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem optionSubtype_symm_apply_apply_none
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β) none = x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Equiv.optionSubtype_symm_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionSubtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y :
 β // y != x }) (b : { y : β // y != x }) : ((optionSubtype x).symm e : Option α
 ≃ β).symm b = e.symm b
参数：x : β；e : α ≃ { y : β // y != x }；b : { y : β // y != x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem optionSubtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (b : { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β).symm b = e.symm b := by
  simp only [optionSubtype, coe_fn_symm_mk, Subtype.coe_mk,
             Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
  exact fun h => False.elim (b.property h)

variable [DecidableEq α] {a b : α}

/-- Any type with a distinguished element is equivalent to an `Option` type on the subtype excluding
that element. -/
@[simps!]
/-
**Equiv.optionSubtypeNe** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (a : α) → Option { b // b ≠ a } ≃ α
参数：a : α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Any type with a distinguished element is equivalent to an `Option` type on the s
ubtype excluding
that element.
-/
def optionSubtypeNe (a : α) : Option {b // b ≠ a} ≃ α := optionSubtype a |>.symm (.refl _) |>.1
/-
**Equiv.optionSubtypeNe_symm_self** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：optionSubtypeNe_symm_self (a : α) : (optionSubtypeNe a).symm a = none
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.optionSubtypeNe_symm_apply`：∀ {α : Type u_1} [inst : DecidableEq α
] (a b : α),   (Equiv.optionSubtypeNe a).symm b = if h : b = a then none else so
me ⟨b, h⟩
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionSubtypeNe_symm_self (a : α) : (optionSubtypeNe a).symm a = none := by simp
/-
**Equiv.optionSubtypeNe_symm_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：optionSubtypeNe_symm_of_ne (hba : b != a) : (optionSubtypeNe a).symm b = s
ome ⟨b, hba⟩
参数：hba : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.optionSubtypeNe_symm_apply`：∀ {α : Type u_1} [inst : DecidableEq α
] (a b : α),   (Equiv.optionSubtypeNe a).symm b = if h : b = a then none else so
me ⟨b, h⟩
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionSubtypeNe_symm_of_ne (hba : b ≠ a) : (optionSubtypeNe a).symm b = some ⟨b, hba⟩ := by
  simp [hba]
/-
**Equiv.optionSubtypeNe_none** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α), (Equiv.optionSubtypeNe a)
 none = a
参数：a : α；Equiv.optionSubtypeNe a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma optionSubtypeNe_none (a : α) : optionSubtypeNe a none = a := rfl
/-
**Equiv.optionSubtypeNe_some** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (b : { b // b ≠ a }), (Equ
iv.optionSubtypeNe a) (some b) = ↑b
参数：a : α；b : { b // b ≠ a }；Equiv.optionSubtypeNe a；some b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma optionSubtypeNe_some (a : α) (b) : optionSubtypeNe a (some b) = b := rfl

open Sum

/-- `Option α` is equivalent to `α ⊕ PUnit` -/
/-
**Equiv.optionEquivSumPUnit.** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Option α` is equivalent to `α ⊕ PUnit`
-/
def optionEquivSumPUnit.{v, w} (α : Type w) : Option α ≃ α ⊕ PUnit.{v + 1} :=
  ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none,
    fun o => by cases o <;> rfl,
    fun s => by rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩

@[simp]
/-
**Equiv.optionEquivSumPUnit_none** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionEquivSumPUnit_none {α} : optionEquivSumPUnit α none = Sum.inr PUnit.
unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem optionEquivSumPUnit_none {α} : optionEquivSumPUnit α none = Sum.inr PUnit.unit :=
  rfl

@[simp]
/-
**Equiv.optionEquivSumPUnit_some** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionEquivSumPUnit_some {α} (a) : optionEquivSumPUnit α (some a) = Sum.in
l a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem optionEquivSumPUnit_some {α} (a) : optionEquivSumPUnit α (some a) = Sum.inl a :=
  rfl

@[simp]
/-
**Equiv.optionEquivSumPUnit_coe** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionEquivSumPUnit_coe {α} (a : α) : optionEquivSumPUnit α a = Sum.inl a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem optionEquivSumPUnit_coe {α} (a : α) : optionEquivSumPUnit α a = Sum.inl a :=
  rfl

@[simp]
/-
**Equiv.optionEquivSumPUnit_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionEquivSumPUnit_symm_inl {α} (a) : (optionEquivSumPUnit α).symm (Sum.i
nl a) = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem optionEquivSumPUnit_symm_inl {α} (a) : (optionEquivSumPUnit α).symm (Sum.inl a) = a :=
  rfl

@[simp]
/-
**Equiv.optionEquivSumPUnit_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：optionEquivSumPUnit_symm_inr {α} (a) : (optionEquivSumPUnit α).symm (Sum.i
nr a) = none
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem optionEquivSumPUnit_symm_inr {α} (a) : (optionEquivSumPUnit α).symm (Sum.inr a) = none :=
  rfl

/-- The set of `x : Option α` such that `isSome x` is equivalent to `α`. -/
@[simps]
/-
**Equiv.optionIsSomeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：optionIsSomeEquiv (α) : { x : Option α // x.isSome } ≃ α where toFun o
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of `x : Option α` such that `isSome x` is equivalent to `α`.
-/
def optionIsSomeEquiv (α) : { x : Option α // x.isSome } ≃ α where
  toFun o := Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
  left_inv _ := Subtype.ext <| Option.some_get _
  right_inv _ := Option.get_some _ _

/-- The bijection `{ i // i ≠ i₀ } ⊕ PUnit ≃ α` for any `i₀ : α`. -/
/-
**Equiv.subtypeNeSumPUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv`。
形式化陈述：subtypeNeSumPUnit (i₀ : α) : { i // i != i₀ } oplus PUnit.{u + 1} ≃ α
参数：i₀ : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `{ i // i ≠ i₀ } ⊕ PUnit ≃ α` for any `i₀ : α`.
-/
abbrev subtypeNeSumPUnit (i₀ : α) : { i // i ≠ i₀ } ⊕ PUnit.{u + 1} ≃ α :=
  (Equiv.optionEquivSumPUnit.{u} _).symm.trans (Equiv.optionSubtypeNe i₀)

end Equiv

