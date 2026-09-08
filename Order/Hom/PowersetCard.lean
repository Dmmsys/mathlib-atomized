/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite sets of an ordered type

This file defines the isomorphism between ordered embeddings into a linearly ordered type and
the finite sets of that type.

## Definitions

* `ofFinEmbEquiv` is the equivalence between `Fin n ↪o I` and `Set.powersetCard I n` when `I` is
  a linearly ordered type.

-/

@[expose] public section

open Finset Function Set

namespace Set.powersetCard

section order

variable {n : ℕ} {I : Type*} [LinearOrder I]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism of `OrderEmbedding`s from `Fin n` into `I` with `Set.powersetCard I n`
when `I` is linearly ordered. -/
/-
**Set.powersetCard.ofFinEmbEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：ofFinEmbEquiv : (Fin n ↪o I) ≃ powersetCard I n where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of `OrderEmbedding`s from `Fin n` into `I` with `Set.powersetCar
d I n`
when `I` is linearly ordered.
-/
def ofFinEmbEquiv : (Fin n ↪o I) ≃ powersetCard I n where
  toFun f := ofFinEmb n I f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by symm; apply Finset.orderEmbOfFin_unique'; simp
  right_inv s := by ext; simp
/-
**Set.powersetCard.ofFinEmbEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set.powersetCa
rd`。
形式化陈述：ofFinEmbEquiv_apply (f : Fin n ↪o I) : ofFinEmbEquiv f = ofFinEmb n I f.to
Embedding
参数：f : Fin n ↪o I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofFinEmbEquiv_apply (f : Fin n ↪o I) :
    ofFinEmbEquiv f = ofFinEmb n I f.toEmbedding :=
  rfl
/-
**Set.powersetCard.ofFinEmbEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set.power
setCard`。
形式化陈述：ofFinEmbEquiv_symm_apply (s : powersetCard I n) : ofFinEmbEquiv.symm s = F
inset.orderEmbOfFin s.val s.prop
参数：s : powersetCard I n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofFinEmbEquiv_symm_apply (s : powersetCard I n) :
    ofFinEmbEquiv.symm s = Finset.orderEmbOfFin s.val s.prop := rfl

@[simp]
/-
**Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Se
t.powersetCard`。
形式化陈述：mem_ofFinEmbEquiv_iff_mem_range (f : Fin n ↪o I) (i : I) : i in ofFinEmbEq
uiv f ↔ i in range f
参数：f : Fin n ↪o I；i : I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_ofFinEmbEquiv_iff_mem_range (f : Fin n ↪o I) (i : I) :
    i ∈ ofFinEmbEquiv f ↔ i ∈ range f := by
  simp [ofFinEmbEquiv_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem** 是 Mathlib 中的一个引理，位于命名空
间 `Set.powersetCard`。
形式化陈述：mem_range_ofFinEmbEquiv_symm_iff_mem (s : powersetCard I n) (i : I) : i in
 range (ofFinEmbEquiv.symm s) ↔ i in s
参数：s : powersetCard I n；i : I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_range_ofFinEmbEquiv_symm_iff_mem (s : powersetCard I n) (i : I) :
    i ∈ range (ofFinEmbEquiv.symm s) ↔ i ∈ s := by
  simp [ofFinEmbEquiv_symm_apply]

/-- The natural enumeration of the elements of linearly-ordered type. -/
/-
**Set.powersetCard.orderIsoOfFin** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：{n : ℕ} → {I : Type u_2} → [inst : LinearOrder I] → (s : ↑(Set.powersetCar
d I n)) → Fin n ≃o ↥↑s
参数：s : ↑(Set.powersetCard I n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural enumeration of the elements of linearly-ordered type.
-/
@[simps!] def orderIsoOfFin {n : ℕ} {I : Type*} [LinearOrder I] (s : powersetCard I n) :
    Fin n ≃o s.val :=
  s.val.orderIsoOfFin s.prop

/-- The permutation of `Fin (m + n)` corresponding to adjoining a `Finset` of card `m`
to a `Finset` of card `n` and sorting the resulting set. In other words, given `s₁ < s₂ < ⋯ < sₘ`
and `t₁ < t₂ < ⋯ < tₙ` (disjoint) this is the permutation obtained by sorting
`s₁, s₂, …, sₘ, t₁, t₂, …, tₙ`. -/
/-
**Set.powersetCard.permOfDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：permOfDisjoint {m n : Nat} {I : Type*} [LinearOrder I] {s : powersetCard I
 m} {t : powersetCard I n} (h : Disjoint s.val t.val) : Equiv.Perm (Fin (m + n))
参数：h : Disjoint s.val t.val。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The permutation of `Fin (m + n)` corresponding to adjoining a `Finset` of card `
m`
to a `Finset` of card `n` and sorting the resulting set. In other words, given `
s₁ < s₂ < ⋯ < sₘ`
and `t₁ < t₂ < ⋯ < tₙ` (disjoint) this is the permutation obtained by sorting
`s₁, s₂, …, sₘ, t₁, t₂, …, tₙ`.
-/
def permOfDisjoint {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val) :
    Equiv.Perm (Fin (m + n)) :=
  letI e₁ : Fin (m + n) ≃ Fin m ⊕ Fin n := finSumFinEquiv.symm
  letI e₂ : Fin m ⊕ Fin n ≃ s.val ⊕ t.val := (orderIsoOfFin s).sumCongr (orderIsoOfFin t)
  letI e₃ : s.val ⊕ t.val ≃ disjUnion h := Equiv.Finset.disjUnionEquiv _ _ h
  letI e₄ : disjUnion h ≃o Fin (m + n) := (orderIsoOfFin (disjUnion h)).symm
  e₁.trans <| e₂.trans <| e₃.trans <| e₄

end order

end Set.powersetCard

