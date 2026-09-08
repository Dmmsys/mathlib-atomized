/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Infima/suprema in ordered monoids and groups

In this file we prove a few facts like “The infimum of `-s` is `-` the supremum of `s`”.

## TODO

`sSup (s • t) = sSup s • sSup t` and `sInf (s • t) = sInf s • sInf t` hold as well but
`CovariantClass` is currently not polymorphic enough to state it.
-/

public section

open Function Set
open scoped Pointwise

variable {M : Type*}

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice M]

section One
variable [One M]

/-
**csSup_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : ConditionallyCompleteLattice M] [inst_1 : One M],
 sSup 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_singleton`：csSup_singleton (a : α) : sSup {a} = a
-/
@[to_additive (attr := simp)] lemma csSup_one : sSup (1 : Set M) = 1 := csSup_singleton _
/-
**csInf_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : ConditionallyCompleteLattice M] [inst_1 : One M],
 sInf 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_singleton`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOr
derInf α] (a : α), sInf {a} = a
-/
@[to_additive (attr := simp)] lemma csInf_one : sInf (1 : Set M) = 1 := csInf_singleton _

end One

section Group
variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

@[to_additive]
/-
**csSup_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = (sInf s)⁻¹
参数：hs₀ : s.Nonempty；hs₁ : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `OrderIso.map_csInf'`：map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddBelow s) : e (sInf s) = sInf (e '' s)
-/
lemma csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csInf' hs₀ hs₁).symm

@[to_additive]
/-
**csInf_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = (sSup s)⁻¹
参数：hs₀ : s.Nonempty；hs₁ : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `OrderIso.map_csSup'`：map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s)
-/
lemma csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csSup' hs₀ hs₁).symm

@[to_additive]
/-
**csSup_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : 
BddAbove t) : sSup (s * t) = sSup s * sSup t
参数：hs₀ : s.Nonempty；hs₁ : BddAbove s；ht₀ : t.Nonempty；ht₁ : BddAbove t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_image2_eq_csSup_csSup`：csSup_image2_eq_csSup_csSup (h₁ : forall b,
 GaloisConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ 
a)) (hs₀ : s.None…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sSup (s * t) = sSup s * sSup t :=
  csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]
/-
**csInf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : 
BddBelow t) : sInf (s * t) = sInf s * sInf t
参数：hs₀ : s.Nonempty；hs₁ : BddBelow s；ht₀ : t.Nonempty；ht₁ : BddBelow t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_image2_eq_csInf_csInf`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : ConditionallyCompleteLattice α]   [inst_1 : ConditionallyCompleteLat
tice β] [inst_2 :…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma csInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sInf (s * t) = sInf s * sInf t :=
  csInf_image2_eq_csInf_csInf (fun _ => (OrderIso.mulRight _).symm.to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]
/-
**csSup_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : 
BddBelow t) : sSup (s / t) = sSup s / sInf t
参数：hs₀ : s.Nonempty；hs₁ : BddAbove s；ht₀ : t.Nonempty；ht₁ : BddBelow t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `csSup_mul`：csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.None
mpty) (ht₁ : BddAbove t) : sSup (s * t) = sSup s * sSup t
· 使用定理 `Set.Nonempty.inv`：∀ {α : Type u_2} [inst : InvolutiveInv α] {s : Set α},
 s.Nonempty → s⁻¹.Nonempty
· 使用定理 `BddBelow.inv`：BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹
· 使用引理 `csSup_inv`：csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = 
(sInf s)⁻¹
-/
lemma csSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sSup (s / t) = sSup s / sInf t := by
  rw [div_eq_mul_inv, csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, csSup_inv ht₀ ht₁, div_eq_mul_inv]

@[to_additive]
/-
**csInf_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : 
BddAbove t) : sInf (s / t) = sInf s / sSup t
参数：hs₀ : s.Nonempty；hs₁ : BddBelow s；ht₀ : t.Nonempty；ht₁ : BddAbove t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `csInf_mul`：csInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.None
mpty) (ht₁ : BddBelow t) : sInf (s * t) = sInf s * sInf t
· 使用定理 `Set.Nonempty.inv`：∀ {α : Type u_2} [inst : InvolutiveInv α] {s : Set α},
 s.Nonempty → s⁻¹.Nonempty
· 使用定理 `BddAbove.inv`：BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹
· 使用引理 `csInf_inv`：csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = 
(sSup s)⁻¹
-/
lemma csInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sInf (s / t) = sInf s / sSup t := by
  rw [div_eq_mul_inv, csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, csInf_inv ht₀ ht₁, div_eq_mul_inv]

end Group
end ConditionallyCompleteLattice

section CompleteLattice
variable [CompleteLattice M]

section One
variable [One M]

/-
**sSup_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : CompleteLattice M] [inst_1 : One M], sSup 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
-/
@[to_additive] lemma sSup_one : sSup (1 : Set M) = 1 := sSup_singleton
/-
**sInf_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : CompleteLattice M] [inst_1 : One M], sInf 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_singleton`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {a : 
α}, sInf {a} = a
-/
@[to_additive] lemma sInf_one : sInf (1 : Set M) = 1 := sInf_singleton

end One

section Group
variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

@[to_additive]
/-
**sSup_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_inv (s : Set M) : sSup s⁻¹ = (sInf s)⁻¹
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `OrderIso.map_sInf`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α),   f (sInf s) = ⨅ a 
∈ s, f …
-/
lemma sSup_inv (s : Set M) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv, sSup_image]
  exact ((OrderIso.inv M).map_sInf _).symm

@[to_additive]
/-
**sInf_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sInf_inv (s : Set M) : sInf s⁻¹ = (sSup s)⁻¹
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
· 使用定理 `OrderIso.map_sSup`：OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s
 : Set α) : f (sSup s) = ⨆ a in s, f a
-/
lemma sInf_inv (s : Set M) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv, sInf_image]
  exact ((OrderIso.inv M).map_sSup _).symm

@[to_additive]
/-
**sSup_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_mul : sSup (s * t) = sSup s * sSup t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_image2_eq_sSup_sSup`：sSup_image2_eq_sSup_sSup (h₁ : forall b, Galoi
sConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ a)) : 
sSup (image2 l…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma sSup_mul : sSup (s * t) = sSup s * sSup t :=
  (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection

@[to_additive]
/-
**sInf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sInf_mul : sInf (s * t) = sInf s * sInf t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image2_eq_sInf_sInf`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : CompleteLattice α] [inst_1 : CompleteLattice β]   [inst_2 : CompleteLattice γ
] {s : Set α} …
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma sInf_mul : sInf (s * t) = sInf s * sInf t :=
  (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection

@[to_additive]
/-
**sSup_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_div : sSup (s / t) = sSup s / sInf t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `sSup_mul`：sSup_mul : sSup (s * t) = sSup s * sSup t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `sSup_inv`：sSup_inv (s : Set M) : sSup s⁻¹ = (sInf s)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sSup_div : sSup (s / t) = sSup s / sInf t := by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]

@[to_additive]
/-
**sInf_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sInf_div : sInf (s / t) = sInf s / sSup t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `sInf_mul`：sInf_mul : sInf (s * t) = sInf s * sInf t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `sInf_inv`：sInf_inv (s : Set M) : sInf s⁻¹ = (sSup s)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sInf_div : sInf (s / t) = sInf s / sSup t := by simp_rw [div_eq_mul_inv, sInf_mul, sInf_inv]

end Group
end CompleteLattice

