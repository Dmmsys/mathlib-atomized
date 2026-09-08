/-
Copyright (c) 2024 Ira Fesefeldt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ira Fesefeldt
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal-indexed approximation theory of fixed points
of a monotone function in a complete lattice [Cousot1979].
The proof follows loosely the one from [Echenique2005].

However, the proof given here is not constructive as we use the non-constructive axiomatization of
ordinals from mathlib. It still allows an approximation scheme indexed over the ordinals.

## Main definitions

* `OrdinalApprox.lfpApprox`: The ordinal-indexed approximation of the least fixed point
  greater or equal than an initial value of a bundled monotone function.
* `OrdinalApprox.gfpApprox`: The ordinal-indexed approximation of the greatest fixed point
  less or equal than an initial value of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfp_mem_range_lfpApprox`: The ordinal-indexed approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfp_mem_range_gfpApprox`: The ordinal-indexed approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## References
* [F. Echenique, *A short and constructive proof of Tarski’s fixed-point theorem*][Echenique2005]
* [P. Cousot & R. Cousot, *Constructive Versions of Tarski's Fixed Point Theorems*][Cousot1979]

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/

@[expose] public section

namespace Cardinal

universe u
variable {α : Type u}
variable (g : Ordinal → α)

open Cardinal Ordinal SuccOrder Function Set

/-
**Cardinal.not_injective_limitation_set** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_ofPred, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype, lift_lift, lift_le] at h
  exact not_le_of_gt (Order.lt_succ #α) h

end Cardinal

namespace OrdinalApprox

universe u
variable {α : Type u}
variable [CompleteLattice α] (f : α →o α) {x : α} {a b c : Ordinal.{u}}

open Function fixedPoints Cardinal Order OrderHom

variable (x) in
/-- The ordinal-indexed sequence approximating the least fixed point greater than
an initial value `x`. It is defined in such a way that we have `lfpApprox 0 x = x` and
`lfpApprox a x = ⨆ b < a, f (lfpApprox b x)`. -/
/-
**OrdinalApprox.lfpApprox** 是 Mathlib 中的一个定义，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox (a : Ordinal.{u}) : α
参数：a : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal-indexed sequence approximating the least fixed point greater than
an initial value `x`. It is defined in such a way that we have `lfpApprox 0 x = 
x` and
`lfpApprox a x = ⨆ b < a, f (lfpApprox b x)`.
-/
def lfpApprox (a : Ordinal.{u}) : α :=
  x ⊔ ⨆ b < a, f (lfpApprox b)
termination_by a
/-
**OrdinalApprox.lfpApprox_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox_mono_right : Monotone (lfpApprox f x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
-/
theorem lfpApprox_mono_right : Monotone (lfpApprox f x) := by
  intro a b h
  rw [lfpApprox, lfpApprox]
  apply sup_le_sup_left (iSup₂_mono' _)
  grind

@[deprecated (since := "2026-03-30")] alias lfpApprox_monotone := lfpApprox_mono_right
/-
**OrdinalApprox.lfpApprox_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox_zero : lfpApprox f x 0 = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lfpApprox_zero : lfpApprox f x 0 = x := by
  rw [lfpApprox]
  simp
/-
**OrdinalApprox.le_lfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：le_lfpApprox {a : Ordinal} : x <= lfpApprox f x a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem le_lfpApprox {a : Ordinal} : x ≤ lfpApprox f x a := by
  rw [lfpApprox]
  exact le_sup_left
/-
**OrdinalApprox.apply_lfpApprox_le_lfpApprox_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Or
dinalApprox`。
形式化陈述：apply_lfpApprox_le_lfpApprox_of_lt {a b : Ordinal} (h : a < b) : f (lfpApp
rox f x a) <= lfpApprox f x b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem apply_lfpApprox_le_lfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    f (lfpApprox f x a) ≤ lfpApprox f x b := by
  nth_rw 2 [lfpApprox]
  exact le_sup_of_le_right <| le_iSup₂_of_le a h le_rfl
/-
**OrdinalApprox.lfpApprox_add_one** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox_add_one (hx : x <= f x) (a : Ordinal) : lfpApprox f x (a + 1) = 
f (lfpApprox f x a)
参数：hx : x <= f x；a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `OrdinalApprox.apply_lfpApprox_le_lfpApprox_of_lt`：apply_lfpApprox_le_lfp
Approx_of_lt {a b : Ordinal} (h : a < b) : f (lfpApprox f x a) <= lfpApprox f x 
b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `OrdinalApprox.le_lfpApprox`：le_lfpApprox {a : Ordinal} : x <= lfpApprox 
f x a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `OrdinalApprox.lfpApprox_mono_right`：lfpApprox_mono_right : Monotone (lfp
Approx f x)
-/
theorem lfpApprox_add_one (hx : x ≤ f x) (a : Ordinal) :
    lfpApprox f x (a + 1) = f (lfpApprox f x a) := by
  apply (apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one a)).antisymm'
  rw [lfpApprox]
  apply sup_le <| hx.trans (f.mono (le_lfpApprox f))
  simpa using fun i h ↦ f.monotone.comp (lfpApprox_mono_right f) h
/-
**OrdinalApprox.lfpApprox_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalAppro
x`。
形式化陈述：lfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) : lfpApp
rox f x a = ⨆ b : Set.Iio a, lfpApprox f x b
参数：ha : Order.IsSuccLimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `OrdinalApprox.lfpApprox_mono_right`：lfpApprox_mono_right : Monotone (lfp
Approx f x)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrdinalApprox.lfpApprox_zero`：lfpApprox_zero : lfpApprox f x 0 = x
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `OrdinalApprox.apply_lfpApprox_le_lfpApprox_of_lt`：apply_lfpApprox_le_lfp
Approx_of_lt {a b : Ordinal} (h : a < b) : f (lfpApprox f x a) <= lfpApprox f x 
b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem lfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) :
    lfpApprox f x a = ⨆ b : Set.Iio a, lfpApprox f x b := by
  apply (iSup_le fun b => lfpApprox_mono_right f b.2.le).antisymm'
  rw [lfpApprox, sup_le_iff, iSup_le_iff]
  constructor
  · refine le_iSup_of_le ⟨0, ha.bot_lt⟩ (by simp [lfpApprox_zero])
  · exact fun b => iSup_mono' fun hab => ⟨⟨b + 1, ha.succ_lt hab⟩, (by
    simpa using apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one b))⟩
/-
**OrdinalApprox.lfpApprox_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox_mono_left : Monotone (lfpApprox : (α ->o α) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem lfpApprox_mono_left : Monotone (lfpApprox : (α →o α) → _) := by
  intro f g h x a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox, lfpApprox]
  exact sup_le_sup_left (iSup₂_mono fun j hj ↦ (f.mono (IH j hj)).trans (h _)) _
/-
**OrdinalApprox.lfpApprox_mono_mid** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox_mono_mid : Monotone (lfpApprox f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem lfpApprox_mono_mid : Monotone (lfpApprox f) := by
  intro x₁ x₂ h a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox, lfpApprox]
  exact sup_le_sup h <| iSup₂_mono fun j hj ↦ f.mono (IH j hj)

/-- The approximations of the least fixed point stabilize at a fixed point of `f` -/
/-
**OrdinalApprox.lfpApprox_eq_of_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Ordin
alApprox`。
形式化陈述：lfpApprox_eq_of_mem_fixedPoints (hab : a <= b) (hf : lfpApprox f x a in fi
xedPoints f) : lfpApprox f x b = lfpApprox f x a
参数：hab : a <= b；hf : lfpApprox f x a in fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `OrdinalApprox.lfpApprox_mono_right`：lfpApprox_mono_right : Monotone (lfp
Approx f x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `OrdinalApprox.le_lfpApprox`：le_lfpApprox {a : Ordinal} : x <= lfpApprox 
f x a
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `OrdinalApprox.apply_lfpApprox_le_lfpApprox_of_lt`：apply_lfpApprox_le_lfp
Approx_of_lt {a b : Ordinal} (h : a < b) : f (lfpApprox f x a) <= lfpApprox f x 
b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x

--- 原说明 ---
The approximations of the least fixed point stabilize at a fixed point of `f`
-/
theorem lfpApprox_eq_of_mem_fixedPoints (hab : a ≤ b)
    (hf : lfpApprox f x a ∈ fixedPoints f) : lfpApprox f x b = lfpApprox f x a := by
  rw [mem_fixedPoints_iff] at hf
  induction b using WellFoundedLT.induction with | ind b IH
  apply (lfpApprox_mono_right f hab).antisymm'
  rw [lfpApprox]
  apply sup_le (le_lfpApprox ..)
  rw [iSup₂_le_iff]
  intro i hi
  by_cases! hi' : i < a
  · exact apply_lfpApprox_le_lfpApprox_of_lt f hi'
  · simp [IH i hi hi', hf]
/-
**OrdinalApprox.lfpApprox_eq_all_of_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `Ordina
lApprox`。
形式化陈述：lfpApprox_eq_all_of_fixedPoint (hx : x <= f x) : (forall o, lfpApprox f x 
o = x) ↔ f x = x
参数：hx : x <= f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox_zero`：lfpApprox_zero : lfpApprox f x 0 = x
· 使用定理 `OrdinalApprox.lfpApprox_add_one`：lfpApprox_add_one (hx : x <= f x) (a : 
Ordinal) : lfpApprox f x (a + 1) = f (lfpApprox f x a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `OrdinalApprox.lfpApprox_eq_of_mem_fixedPoints`：lfpApprox_eq_of_mem_fixed
Points (hab : a <= b) (hf : lfpApprox f x a in fixedPoints f) : lfpApprox f x b 
= lfpApprox f x a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem lfpApprox_eq_all_of_fixedPoint (hx : x ≤ f x) :
    (∀ o, lfpApprox f x o = x) ↔ f x = x := by
  refine ⟨fun h ↦ ?_, fun h o ↦ ?_⟩
  · specialize h 1
    rwa [← zero_add 1, lfpApprox_add_one f hx, lfpApprox_zero] at h
  · have : lfpApprox f x 0 ∈ fixedPoints f := by
      rwa [mem_fixedPoints_iff, lfpApprox_zero]
    simpa [lfpApprox_zero] using
      lfpApprox_eq_of_mem_fixedPoints f zero_le this

/-- If the sequence of ordinal-indexed approximations takes a value twice,
then it actually stabilised at that value. -/
/-
**OrdinalApprox.lfpApprox_mem_fixedPoints_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ordin
alApprox`。
形式化陈述：lfpApprox_mem_fixedPoints_of_eq (hx : x <= f x) (hab : a < b) (hac : a <= 
c) (hf : lfpApprox f x a = lfpApprox f x b) : lfpApprox f x c in fixedPoints f
参数：hx : x <= f x；hab : a < b；hac : a <= c；hf : lfpApprox f x a = lfpApprox f x b
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrdinalApprox.lfpApprox_add_one`：lfpApprox_add_one (hx : x <= f x) (a : 
Ordinal) : lfpApprox f x (a + 1) = f (lfpApprox f x a)
· 使用定理 `Monotone.eq_of_ge_of_le`：Monotone.eq_of_ge_of_le {a₁ a₂ : α} (h_mon : Mo
notone f) (h_fa : f a₁ = f a₂) {i : α} (h₁ : a₁ <= i) (h₂ : i <= a₂) : f i = f a
₁
· 使用定理 `OrdinalApprox.lfpApprox_mono_right`：lfpApprox_mono_right : Monotone (lfp
Approx f x)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用定理 `OrdinalApprox.lfpApprox_eq_of_mem_fixedPoints`：lfpApprox_eq_of_mem_fixed
Points (hab : a <= b) (hf : lfpApprox f x a in fixedPoints f) : lfpApprox f x b 
= lfpApprox f x a

--- 原说明 ---
If the sequence of ordinal-indexed approximations takes a value twice,
then it actually stabilised at that value.
-/
lemma lfpApprox_mem_fixedPoints_of_eq (hx : x ≤ f x) (hab : a < b) (hac : a ≤ c)
    (hf : lfpApprox f x a = lfpApprox f x b) : lfpApprox f x c ∈ fixedPoints f := by
  have H : lfpApprox f x a ∈ fixedPoints f := by
    rw [mem_fixedPoints_iff, ← lfpApprox_add_one f hx]
    exact (lfpApprox_mono_right f).eq_of_ge_of_le
      hf (lt_add_one a).le (add_one_le_of_lt hab)
  rwa [lfpApprox_eq_of_mem_fixedPoints f hac H]
/-
**OrdinalApprox.lfpApprox_eq_of_fixedPoint_or_zero** 是 Mathlib 中的一个定理，位于命名空间 `Or
dinalApprox`。
形式化陈述：lfpApprox_eq_of_fixedPoint_or_zero (hx : x <= f x) (o : Ordinal) : lfpAppr
ox f x o = x ↔ f x = x ∨ o = 0
参数：hx : x <= f x；o : Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用引理 `OrdinalApprox.lfpApprox_mem_fixedPoints_of_eq`：lfpApprox_mem_fixedPoints
_of_eq (hx : x <= f x) (hab : a < b) (hac : a <= c) (hf : lfpApprox f x a = lfpA
pprox f x b) : lfpApprox f x c in f…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrdinalApprox.lfpApprox_zero`：lfpApprox_zero : lfpApprox f x 0 = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox_eq_all_of_fixedPoint`：lfpApprox_eq_all_of_fixedP
oint (hx : x <= f x) : (forall o, lfpApprox f x o = x) ↔ f x = x
-/
theorem lfpApprox_eq_of_fixedPoint_or_zero (hx : x ≤ f x) (o : Ordinal) :
    lfpApprox f x o = x ↔ f x = x ∨ o = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_or_ne o 0 with (rfl | ho)
    · exact Or.inr rfl
    · have hpos : (0 : Ordinal) < o :=
        zero_lt_one.trans_le (one_le_iff_ne_zero.mpr ho)
      have hmem : lfpApprox f x 0 ∈ fixedPoints f :=
        lfpApprox_mem_fixedPoints_of_eq f hx hpos (le_refl _)
          ((lfpApprox_zero f).trans h.symm)
      have hfx : f x = x :=
        (mem_fixedPoints_iff.mp (by simpa [lfpApprox_zero] using hmem))
      exact Or.inl hfx
  · rcases h with (hf | rfl)
    · exact (lfpApprox_eq_all_of_fixedPoint f hx).mpr hf o
    · exact lfpApprox_zero f

variable (x) in
/-- There are distinct indices smaller than the successor of the domain's cardinality
yielding the same value -/
/-
**OrdinalApprox.exists_lfpApprox_eq_lfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
Approx`。
形式化陈述：exists_lfpApprox_eq_lfpApprox : exists a < ord succ #α, exists b < ord suc
c #α, a != b ∧ lfpApprox f x a = lfpApprox f x b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.not_injective_limitation_set`：not_injective_limitation_set : ¬ 
InjOn g (Iio (ord <| succ #α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.not_injective_iff`：not_injective_iff : ¬ Injective f ↔ exists a
 b, f a = f b ∧ a != b
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b

--- 原说明 ---
There are distinct indices smaller than the successor of the domain's cardinalit
y
yielding the same value
-/
theorem exists_lfpApprox_eq_lfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ lfpApprox f x a = lfpApprox f x b := by
  have h_ninj := not_injective_limitation_set <| lfpApprox f x
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

/-- The approximation at the index of the successor of the domain's cardinality is a fixed point -/
/-
**OrdinalApprox.lfpApprox_ord_mem_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalA
pprox`。
形式化陈述：lfpApprox_ord_mem_fixedPoint (hx : x <= f x) : lfpApprox f x (ord <| succ 
#α) in fixedPoints f
参数：hx : x <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.exists_lfpApprox_eq_lfpApprox`：exists_lfpApprox_eq_lfpAppr
ox : exists a < ord succ #α, exists b < ord succ #α, a != b ∧ lfpApprox f x a = 
lfpApprox f x b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `OrdinalApprox.lfpApprox_mem_fixedPoints_of_eq`：lfpApprox_mem_fixedPoints
_of_eq (hx : x <= f x) (hab : a < b) (hac : a <= c) (hf : lfpApprox f x a = lfpA
pprox f x b) : lfpApprox f x c in f…
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The approximation at the index of the successor of the domain's cardinality is a
 fixed point
-/
theorem lfpApprox_ord_mem_fixedPoint (hx : x ≤ f x) :
    lfpApprox f x (ord <| succ #α) ∈ fixedPoints f := by
  let ⟨a, ha, b, hb, hne, hf⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl hab => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.lt_of_le hab) ha.le hf
  | inr hba => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.symm.lt_of_le hba) hb.le hf.symm

/-- Every value of the approximation is less or equal than every fixed point of `f`
greater or equal than the initial value -/
/-
**OrdinalApprox.lfpApprox_le_of_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Ordin
alApprox`。
形式化陈述：lfpApprox_le_of_mem_fixedPoints {a : α} (ha : a in fixedPoints f) (hxa : x
 <= a) (i : Ordinal) : lfpApprox f x i <= a
参数：ha : a in fixedPoints f；hxa : x <= a；i : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox.eq_1`：∀ {α : Type u} [inst : CompleteLattice α] 
(f : α →o α) (x : α) (a : Ordinal.{u}),   OrdinalApprox.lfpApprox f x a = x ⊔ ⨆ 
b, ⨆ (_ : b < a), …
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f

--- 原说明 ---
Every value of the approximation is less or equal than every fixed point of `f`
greater or equal than the initial value
-/
theorem lfpApprox_le_of_mem_fixedPoints {a : α}
    (ha : a ∈ fixedPoints f) (hxa : x ≤ a) (i : Ordinal) : lfpApprox f x i ≤ a := by
  induction i using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]
  apply sup_le hxa
  rw [iSup₂_le_iff, ← ha.eq]
  exact fun y hy ↦ f.mono (IH y hy)

/-- The approximation sequence converges at the successor of the domain's cardinality
to the least fixed point if starting from `⊥` -/
/-
**OrdinalApprox.lfpApprox_ord_eq_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：lfpApprox_ord_eq_lfp : lfpApprox f ⊥ (ord <| succ #α) = f.lfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.lfpApprox_le_of_mem_fixedPoints`：lfpApprox_le_of_mem_fixed
Points {a : α} (ha : a in fixedPoints f) (hxa : x <= a) (i : Ordinal) : lfpAppro
x f x i <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `OrdinalApprox.lfpApprox_ord_mem_fixedPoint`：lfpApprox_ord_mem_fixedPoint
 (hx : x <= f x) : lfpApprox f x (ord <| succ #α) in fixedPoints f
· 使用定理 `OrderHom.lfp_le_fixed`：lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The approximation sequence converges at the successor of the domain's cardinalit
y
to the least fixed point if starting from `⊥`
-/
theorem lfpApprox_ord_eq_lfp : lfpApprox f ⊥ (ord <| succ #α) = f.lfp := by
  apply le_antisymm
  · have h_lfp : ∃ y : fixedPoints f, f.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints f y.2 bot_le (ord <| succ #α)
  · have h_fix : ∃ y : fixedPoints f, lfpApprox f ⊥ (ord <| succ #α) = y := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_ord_mem_fixedPoint f bot_le
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed f x.prop

/-- Some approximation of the least fixed point starting from `⊥` is the least fixed point. -/
/-
**OrdinalApprox.lfp_mem_range_lfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox
`。
形式化陈述：lfp_mem_range_lfpApprox : f.lfp in Set.range (lfpApprox f ⊥)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_ord_eq_lfp`：lfpApprox_ord_eq_lfp : lfpApprox f ⊥
 (ord <| succ #α) = f.lfp

--- 原说明 ---
Some approximation of the least fixed point starting from `⊥` is the least fixed
 point.
-/
theorem lfp_mem_range_lfpApprox : f.lfp ∈ Set.range (lfpApprox f ⊥) := by
  use ord <| succ #α
  exact lfpApprox_ord_eq_lfp f

/-- If `lfpApprox f x a` is a fixed point, then the supremum of the whole
ordinal-indexed sequence equals the value at `a`. -/
/-
**OrdinalApprox.iSup_lfpApprox_eq_of_mem_fixedPoints** 是 Mathlib 中的一个引理，位于命名空间 `
OrdinalApprox`。
形式化陈述：iSup_lfpApprox_eq_of_mem_fixedPoints (hf : lfpApprox f x a in fixedPoints 
f) : ⨆ i : Ordinal, lfpApprox f x i = lfpApprox f x a
参数：hf : lfpApprox f x a in fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `OrdinalApprox.lfpApprox_mono_right`：lfpApprox_mono_right : Monotone (lfp
Approx f x)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `OrdinalApprox.lfpApprox_eq_of_mem_fixedPoints`：lfpApprox_eq_of_mem_fixed
Points (hab : a <= b) (hf : lfpApprox f x a in fixedPoints f) : lfpApprox f x b 
= lfpApprox f x a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a

--- 原说明 ---
If `lfpApprox f x a` is a fixed point, then the supremum of the whole
ordinal-indexed sequence equals the value at `a`.
-/
lemma iSup_lfpApprox_eq_of_mem_fixedPoints (hf : lfpApprox f x a ∈ fixedPoints f) :
    ⨆ i : Ordinal, lfpApprox f x i = lfpApprox f x a := by
  apply (le_iSup (lfpApprox f x) a).antisymm'
  refine ciSup_le fun i => ?_
  by_cases h : i ≤ a
  · exact lfpApprox_mono_right f h
  · exact (lfpApprox_eq_of_mem_fixedPoints f (le_of_not_ge h) hf).le

/-- The ordinal-indexed supremum of `lfpApprox` equals `nextFixed`: the least fixed point
greater than or equal to `x`. -/
/-
**OrdinalApprox.nextFixed_eq_iSup_lfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalAp
prox`。
形式化陈述：nextFixed_eq_iSup_lfpApprox (hx : x <= f x) : (f.nextFixed x hx).val = ⨆ a
 : Ordinal, lfpApprox f x a
参数：hx : x <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_ord_mem_fixedPoint`：lfpApprox_ord_mem_fixedPoint
 (hx : x <= f x) : lfpApprox f x (ord <| succ #α) in fixedPoints f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OrdinalApprox.iSup_lfpApprox_eq_of_mem_fixedPoints`：iSup_lfpApprox_eq_of
_mem_fixedPoints (hf : lfpApprox f x a in fixedPoints f) : ⨆ i : Ordinal, lfpApp
rox f x i = lfpApprox f x a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OrderHom.nextFixed_le`：nextFixed_le {x : α} (hx : x <= f x) {y : fixedPo
ints f} (h : x <= y) : f.nextFixed x hx <= y
· 使用定理 `OrdinalApprox.le_lfpApprox`：le_lfpApprox {a : Ordinal} : x <= lfpApprox 
f x a
· 使用定理 `OrdinalApprox.lfpApprox_le_of_mem_fixedPoints`：lfpApprox_le_of_mem_fixed
Points {a : α} (ha : a in fixedPoints f) (hxa : x <= a) (i : Ordinal) : lfpAppro
x f x i <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `OrderHom.le_nextFixed`：le_nextFixed {x : α} (hx : x <= f x) : x <= f.nex
tFixed x hx

--- 原说明 ---
The ordinal-indexed supremum of `lfpApprox` equals `nextFixed`: the least fixed 
point
greater than or equal to `x`.
-/
theorem nextFixed_eq_iSup_lfpApprox (hx : x ≤ f x) :
    (f.nextFixed x hx).val = ⨆ a : Ordinal, lfpApprox f x a := by
  let o := (succ #α).ord
  have hfix : lfpApprox f x o ∈ fixedPoints f :=
    lfpApprox_ord_mem_fixedPoint f hx
  rw [iSup_lfpApprox_eq_of_mem_fixedPoints f hfix]
  apply le_antisymm
  · exact f.nextFixed_le hx (y := ⟨lfpApprox f x o, hfix⟩) (le_lfpApprox f)
  · exact lfpApprox_le_of_mem_fixedPoints f (f.nextFixed x hx).2 (f.le_nextFixed hx) o

variable (x) in
/-- The ordinal-indexed sequence approximating the greatest fixed point greater than
an initial value `x`. It is defined in such a way that we have `gfpApprox 0 x = x` and
`gfpApprox a x = ⨅ b < a, f (lfpApprox b x)`. -/
/-
**OrdinalApprox.gfpApprox** 是 Mathlib 中的一个定义，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox (a : Ordinal.{u}) : α
参数：a : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal-indexed sequence approximating the greatest fixed point greater than
an initial value `x`. It is defined in such a way that we have `gfpApprox 0 x = 
x` and
`gfpApprox a x = ⨅ b < a, f (lfpApprox b x)`.
-/
def gfpApprox (a : Ordinal.{u}) : α :=
  x ⊓ ⨅ b < a, f (gfpApprox b)
termination_by a

-- By unsealing these recursive definitions we can relate them
-- by definitional equality
unseal gfpApprox lfpApprox
/-
**OrdinalApprox.gfpApprox_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_zero : gfpApprox f x 0 = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_zero`：lfpApprox_zero : lfpApprox f x 0 = x
-/
theorem gfpApprox_zero : gfpApprox f x 0 = x := by
  exact lfpApprox_zero f.dual
/-
**OrdinalApprox.gfpApprox_anti_right** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_anti_right : Antitone (gfpApprox f x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_mono_right`：lfpApprox_mono_right : Monotone (lfp
Approx f x)
-/
theorem gfpApprox_anti_right : Antitone (gfpApprox f x) :=
  lfpApprox_mono_right f.dual

@[deprecated (since := "2026-03-30")] alias gfpApprox_antitone := gfpApprox_anti_right
/-
**OrdinalApprox.gfpApprox_le** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_le {a : Ordinal} : gfpApprox f x a <= x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.le_lfpApprox`：le_lfpApprox {a : Ordinal} : x <= lfpApprox 
f x a
-/
theorem gfpApprox_le {a : Ordinal} : gfpApprox f x a ≤ x :=
  le_lfpApprox f.dual
/-
**OrdinalApprox.gfpApprox_add_one** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_add_one (hx : f x <= x) (a : Ordinal) : gfpApprox f x (a + 1) = 
f (gfpApprox f x a)
参数：hx : f x <= x；a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_add_one`：lfpApprox_add_one (hx : x <= f x) (a : 
Ordinal) : lfpApprox f x (a + 1) = f (lfpApprox f x a)
-/
theorem gfpApprox_add_one (hx : f x ≤ x) (a : Ordinal) :
    gfpApprox f x (a + 1) = f (gfpApprox f x a) :=
  lfpApprox_add_one f.dual hx a
/-
**OrdinalApprox.gfpApprox_le_apply_gfpApprox_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Or
dinalApprox`。
形式化陈述：gfpApprox_le_apply_gfpApprox_of_lt {a b : Ordinal} (h : a < b) : gfpApprox
 f x b <= f (gfpApprox f x a)
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.apply_lfpApprox_le_lfpApprox_of_lt`：apply_lfpApprox_le_lfp
Approx_of_lt {a b : Ordinal} (h : a < b) : f (lfpApprox f x a) <= lfpApprox f x 
b
-/
theorem gfpApprox_le_apply_gfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    gfpApprox f x b ≤ f (gfpApprox f x a) :=
  apply_lfpApprox_le_lfpApprox_of_lt f.dual h
/-
**OrdinalApprox.gfpApprox_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalAppro
x`。
形式化陈述：gfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) : gfpApp
rox f x a = ⨅ b : Set.Iio a, gfpApprox f x b
参数：ha : Order.IsSuccLimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_of_isSuccLimit`：lfpApprox_of_isSuccLimit {a : Or
dinal} (ha : Order.IsSuccLimit a) : lfpApprox f x a = ⨆ b : Set.Iio a, lfpApprox
 f x b
-/
theorem gfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) :
    gfpApprox f x a = ⨅ b : Set.Iio a, gfpApprox f x b :=
  lfpApprox_of_isSuccLimit f.dual ha
/-
**OrdinalApprox.gfpApprox_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_mono_left : Monotone (gfpApprox : (α ->o α) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_mono_left`：lfpApprox_mono_left : Monotone (lfpAp
prox : (α ->o α) -> _)
-/
theorem gfpApprox_mono_left : Monotone (gfpApprox : (α →o α) → _) := by
  intro f g h
  have : g.dual ≤ f.dual := h
  exact lfpApprox_mono_left this
/-
**OrdinalApprox.gfpApprox_mono_mid** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_mono_mid : Monotone (gfpApprox f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_mono_mid`：lfpApprox_mono_mid : Monotone (lfpAppr
ox f)
-/
theorem gfpApprox_mono_mid : Monotone (gfpApprox f) :=
  fun _ _ h => lfpApprox_mono_mid f.dual h

/-- The approximations of the greatest fixed point stabilize at a fixed point of `f` -/
/-
**OrdinalApprox.gfpApprox_eq_of_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Ordin
alApprox`。
形式化陈述：gfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_ab : a <= b) (h : gfpAp
prox f x a in fixedPoints f) : gfpApprox f x b = gfpApprox f x a
参数：h_ab : a <= b；h : gfpApprox f x a in fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_eq_of_mem_fixedPoints`：lfpApprox_eq_of_mem_fixed
Points (hab : a <= b) (hf : lfpApprox f x a in fixedPoints f) : lfpApprox f x b 
= lfpApprox f x a

--- 原说明 ---
The approximations of the greatest fixed point stabilize at a fixed point of `f`
-/
theorem gfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_ab : a ≤ b)
    (h : gfpApprox f x a ∈ fixedPoints f) : gfpApprox f x b = gfpApprox f x a :=
  lfpApprox_eq_of_mem_fixedPoints f.dual h_ab h
/-
**OrdinalApprox.gfpApprox_eq_all_of_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `Ordina
lApprox`。
形式化陈述：gfpApprox_eq_all_of_fixedPoint (hx : f x <= x) : (forall o, gfpApprox f x 
o = x) ↔ f x = x
参数：hx : f x <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_eq_all_of_fixedPoint`：lfpApprox_eq_all_of_fixedP
oint (hx : x <= f x) : (forall o, lfpApprox f x o = x) ↔ f x = x
-/
theorem gfpApprox_eq_all_of_fixedPoint (hx : f x ≤ x) :
    (∀ o, gfpApprox f x o = x) ↔ f x = x :=
  lfpApprox_eq_all_of_fixedPoint f.dual hx
/-
**OrdinalApprox.gfpApprox_mem_fixedPoints_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ordin
alApprox`。
形式化陈述：gfpApprox_mem_fixedPoints_of_eq (hx : f x <= x) (hab : a < b) (hac : a <= 
c) (hf : gfpApprox f x a = gfpApprox f x b) : gfpApprox f x c in fixedPoints f
参数：hx : f x <= x；hab : a < b；hac : a <= c；hf : gfpApprox f x a = gfpApprox f x b
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrdinalApprox.lfpApprox_mem_fixedPoints_of_eq`：lfpApprox_mem_fixedPoints
_of_eq (hx : x <= f x) (hab : a < b) (hac : a <= c) (hf : lfpApprox f x a = lfpA
pprox f x b) : lfpApprox f x c in f…
-/
lemma gfpApprox_mem_fixedPoints_of_eq (hx : f x ≤ x) (hab : a < b) (hac : a ≤ c)
    (hf : gfpApprox f x a = gfpApprox f x b) : gfpApprox f x c ∈ fixedPoints f :=
  lfpApprox_mem_fixedPoints_of_eq f.dual hx hab hac hf
/-
**OrdinalApprox.gfpApprox_eq_of_fixedPoint_or_zero** 是 Mathlib 中的一个定理，位于命名空间 `Or
dinalApprox`。
形式化陈述：gfpApprox_eq_of_fixedPoint_or_zero (hx : f x <= x) (o : Ordinal) : gfpAppr
ox f x o = x ↔ f x = x ∨ o = 0
参数：hx : f x <= x；o : Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_eq_of_fixedPoint_or_zero`：lfpApprox_eq_of_fixedP
oint_or_zero (hx : x <= f x) (o : Ordinal) : lfpApprox f x o = x ↔ f x = x ∨ o =
 0
-/
theorem gfpApprox_eq_of_fixedPoint_or_zero (hx : f x ≤ x) (o : Ordinal) :
    gfpApprox f x o = x ↔ f x = x ∨ o = 0 :=
  lfpApprox_eq_of_fixedPoint_or_zero f.dual hx o

/-- There are distinct indices smaller than the successor of the domain's cardinality
yielding the same value -/
/-
**OrdinalApprox.exists_gfpApprox_eq_gfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
Approx`。
形式化陈述：exists_gfpApprox_eq_gfpApprox : exists a < ord succ #α, exists b < ord suc
c #α, a != b ∧ gfpApprox f x a = gfpApprox f x b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.exists_lfpApprox_eq_lfpApprox`：exists_lfpApprox_eq_lfpAppr
ox : exists a < ord succ #α, exists b < ord succ #α, a != b ∧ lfpApprox f x a = 
lfpApprox f x b

--- 原说明 ---
There are distinct indices smaller than the successor of the domain's cardinalit
y
yielding the same value
-/
theorem exists_gfpApprox_eq_gfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ gfpApprox f x a = gfpApprox f x b :=
  exists_lfpApprox_eq_lfpApprox f.dual x

/-- The approximation at the index of the successor of the domain's cardinality is a fixed point -/
/-
**OrdinalApprox.gfpApprox_ord_mem_fixedPoint** 是 Mathlib 中的一个引理，位于命名空间 `OrdinalA
pprox`。
形式化陈述：gfpApprox_ord_mem_fixedPoint (hx : f x <= x) : gfpApprox f x (ord <| succ 
#α) in fixedPoints f
参数：hx : f x <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_ord_mem_fixedPoint`：lfpApprox_ord_mem_fixedPoint
 (hx : x <= f x) : lfpApprox f x (ord <| succ #α) in fixedPoints f

--- 原说明 ---
The approximation at the index of the successor of the domain's cardinality is a
 fixed point
-/
lemma gfpApprox_ord_mem_fixedPoint (hx : f x ≤ x) :
    gfpApprox f x (ord <| succ #α) ∈ fixedPoints f :=
  lfpApprox_ord_mem_fixedPoint f.dual hx

/-- Every value of the approximation is greater or equal than every fixed point of `f`
less or equal than the initial value -/
/-
**OrdinalApprox.le_gfpApprox_of_mem_fixedPoints** 是 Mathlib 中的一个引理，位于命名空间 `Ordin
alApprox`。
形式化陈述：le_gfpApprox_of_mem_fixedPoints {a : α} (ha : a in fixedPoints f) (hax : a
 <= x) (i : Ordinal) : a <= gfpApprox f x i
参数：ha : a in fixedPoints f；hax : a <= x；i : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_le_of_mem_fixedPoints`：lfpApprox_le_of_mem_fixed
Points {a : α} (ha : a in fixedPoints f) (hxa : x <= a) (i : Ordinal) : lfpAppro
x f x i <= a

--- 原说明 ---
Every value of the approximation is greater or equal than every fixed point of `
f`
less or equal than the initial value
-/
lemma le_gfpApprox_of_mem_fixedPoints {a : α}
    (ha : a ∈ fixedPoints f) (hax : a ≤ x) (i : Ordinal) : a ≤ gfpApprox f x i :=
  lfpApprox_le_of_mem_fixedPoints f.dual ha hax i

/-- The approximation sequence converges at the successor of the domain's cardinality
to the greatest fixed point if starting from `⊥` -/
/-
**OrdinalApprox.gfpApprox_ord_eq_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox`。
形式化陈述：gfpApprox_ord_eq_gfp : gfpApprox f ⊤ (ord <| succ #α) = f.gfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfpApprox_ord_eq_lfp`：lfpApprox_ord_eq_lfp : lfpApprox f ⊥
 (ord <| succ #α) = f.lfp

--- 原说明 ---
The approximation sequence converges at the successor of the domain's cardinalit
y
to the greatest fixed point if starting from `⊥`
-/
theorem gfpApprox_ord_eq_gfp : gfpApprox f ⊤ (ord <| succ #α) = f.gfp :=
  lfpApprox_ord_eq_lfp f.dual

/-- Some approximation of the least fixed point starting from `⊤` is the greatest fixed point. -/
/-
**OrdinalApprox.gfp_mem_range_gfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalApprox
`。
形式化陈述：gfp_mem_range_gfpApprox : f.gfp in Set.range (gfpApprox f ⊤)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.lfp_mem_range_lfpApprox`：lfp_mem_range_lfpApprox : f.lfp i
n Set.range (lfpApprox f ⊥)

--- 原说明 ---
Some approximation of the least fixed point starting from `⊤` is the greatest fi
xed point.
-/
theorem gfp_mem_range_gfpApprox : f.gfp ∈ Set.range (gfpApprox f ⊤) :=
  lfp_mem_range_lfpApprox f.dual

/-- If `gfpApprox f x a` is a fixed point, then the infimum of the whole
ordinal-indexed sequence equals the value at `a`. -/
/-
**OrdinalApprox.iInf_gfpApprox_eq_of_mem_fixedPoints** 是 Mathlib 中的一个引理，位于命名空间 `
OrdinalApprox`。
形式化陈述：iInf_gfpApprox_eq_of_mem_fixedPoints (hf : gfpApprox f x a in fixedPoints 
f) : ⨅ i : Ordinal, gfpApprox f x i = gfpApprox f x a
参数：hf : gfpApprox f x a in fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrdinalApprox.iSup_lfpApprox_eq_of_mem_fixedPoints`：iSup_lfpApprox_eq_of
_mem_fixedPoints (hf : lfpApprox f x a in fixedPoints f) : ⨆ i : Ordinal, lfpApp
rox f x i = lfpApprox f x a

--- 原说明 ---
If `gfpApprox f x a` is a fixed point, then the infimum of the whole
ordinal-indexed sequence equals the value at `a`.
-/
lemma iInf_gfpApprox_eq_of_mem_fixedPoints (hf : gfpApprox f x a ∈ fixedPoints f) :
    ⨅ i : Ordinal, gfpApprox f x i = gfpApprox f x a :=
  iSup_lfpApprox_eq_of_mem_fixedPoints f.dual hf

/-- The ordinal-indexed infimum of `gfpApprox` equals `prevFixed`: the greatest fixed point
less than or equal to `x`. -/
/-
**OrdinalApprox.prevFixed_eq_iInf_gfpApprox** 是 Mathlib 中的一个定理，位于命名空间 `OrdinalAp
prox`。
形式化陈述：prevFixed_eq_iInf_gfpApprox (hx : f x <= x) : (f.prevFixed x hx).val = ⨅ a
 : Ordinal, gfpApprox f x a
参数：hx : f x <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.nextFixed_eq_iSup_lfpApprox`：nextFixed_eq_iSup_lfpApprox (
hx : x <= f x) : (f.nextFixed x hx).val = ⨆ a : Ordinal, lfpApprox f x a

--- 原说明 ---
The ordinal-indexed infimum of `gfpApprox` equals `prevFixed`: the greatest fixe
d point
less than or equal to `x`.
-/
theorem prevFixed_eq_iInf_gfpApprox (hx : f x ≤ x) :
    (f.prevFixed x hx).val = ⨅ a : Ordinal, gfpApprox f x a :=
  nextFixed_eq_iSup_lfpApprox f.dual hx

end OrdinalApprox

