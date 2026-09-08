/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Infinite pigeonhole principle

This file proves variants of the infinite pigeonhole principle.

## TODO

Generalize universes of results.
-/

public section

open Order Ordinal Set

universe u

namespace Cardinal

/-- The infinite pigeonhole principle -/
/-
**Cardinal.infinite_pigeonhole** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：infinite_pigeonhole {β α : Type u} (f : β -> α) (h₁ : ℵ₀ <= #β) (h₂ : #α <
 (#β).ord.cof) : exists a : α, #(f ⁻¹' {a}) = #β
参数：f : β -> α；h₁ : ℵ₀ <= #β；h₂ : #α < (#β).ord.cof。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.iUnion_of_singleton`：iUnion_of_singleton (α : Type*) : (⋃ x, {x} : S
et α) = univ
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk`：mk_iUnion_le_sum_mk {α ι : Type u} {f : ι 
-> Set α} : #(⋃ i, f i) <= sum fun i => #(f i)
· 使用定理 `Cardinal.sum_le_mk_mul_iSup`：sum_le_mk_mul_iSup {ι : Type u} (f : ι -> C
ardinal.{u}) : sum f <= #ι * ⨆ i, f i
· 使用定理 `Cardinal.mul_lt_of_lt`：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
a : a < c) (hb : b < c) : a * b < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.cof_ord_le`：cof_ord_le (c : Cardinal) : c.ord.cof <= c
· 使用定理 `Cardinal.iSup_lt_of_lt_cof_ord`：∀ {α : Type u} {f : α → Cardinal.{u}} {a
 : Cardinal.{u}},   Cardinal.mk α < a.ord.cof → (∀ (i : α), f i < a) → ⨆ i, f i 
< a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c

--- 原说明 ---
The infinite pigeonhole principle
-/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ #β) (h₂ : #α < (#β).ord.cof) :
    ∃ a : α, #(f ⁻¹' {a}) = #β := by
  have : ∃ a, #β ≤ #(f ⁻¹' {a}) := by
    by_contra! h
    apply mk_univ.not_lt
    rw [← preimage_univ, ← iUnion_of_singleton, preimage_iUnion]
    exact
      mk_iUnion_le_sum_mk.trans_lt <| (sum_le_mk_mul_iSup _).trans_lt <|
        mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt_of_lt_cof_ord h₂ h)
  obtain ⟨x, h⟩ := this
  refine ⟨x, h.antisymm' ?_⟩
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
/-
**Cardinal.infinite_pigeonhole_card** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：infinite_pigeonhole_card {β α : Type u} (f : β -> α) (θ : Cardinal) (hθ : 
θ <= #β) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.cof) : exists a : α, θ <= #(f ⁻¹' {a})
参数：f : β -> α；θ : Cardinal；hθ : θ <= #β；h₁ : ℵ₀ <= θ；h₂ : #α < θ.ord.cof。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c
· 使用定理 `Cardinal.infinite_pigeonhole`：infinite_pigeonhole {β α : Type u} (f : β 
-> α) (h₁ : ℵ₀ <= #β) (h₂ : #α < (#β).ord.cof) : exists a : α, #(f ⁻¹' {a}) = #β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Cardinal.mk_preimage_of_injective`：mk_preimage_of_injective (f : α -> β)
 (s : Set β) (h : Injective f) : #(f ⁻¹' s) <= #s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
Pigeonhole principle for a cardinality below the cardinality of the domain
-/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ #β)
    (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) : ∃ a : α, θ ≤ #(f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective
/-
**Cardinal.infinite_pigeonhole_set** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s -> α) (θ : Cardi
nal) (hθ : θ <= #s) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.cof) : exists (a : α) (t : S
et β) (h : t subseteq s), θ <= #t ∧ forall ⦃x⦄ (hx : x in t), f ⟨x, h hx⟩ = a
参数：f : s -> α；θ : Cardinal；hθ : θ <= #s；h₁ : ℵ₀ <= θ；h₂ : #α < θ.ord.cof。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.infinite_pigeonhole_card`：infinite_pigeonhole_card {β α : Type 
u} (f : β -> α) (θ : Cardinal) (hθ : θ <= #β) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.co
f) : exists a : α, θ <=…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal)
    (hθ : θ ≤ #s) (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) :
    ∃ (a : α) (t : Set β) (h : t ⊆ s), θ ≤ #t ∧ ∀ ⦃x⦄ (hx : x ∈ t), f ⟨x, h hx⟩ = a := by
  obtain ⟨a, ha⟩ := infinite_pigeonhole_card f θ hθ h₁ h₂
  refine ⟨a, { x | ∃ h, f ⟨x, h⟩ = a }, ?_, ?_, ?_⟩
  · rintro x ⟨hx, _⟩
    exact hx
  · refine
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_ofPred_eq]
    rfl
  rintro x ⟨_, hx'⟩; exact hx'

/-- A function whose domain's cardinality is infinite and strictly greater than its codomain's
has a fiber with cardinality strictly great than the codomain. -/
/-
**Cardinal.infinite_pigeonhole_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：infinite_pigeonhole_card_lt {β α : Type u} (f : β -> α) (h : #α < #β) (hβ 
: ℵ₀ <= #β) : exists a : α, #α < #(f ⁻¹' {a})
参数：f : β -> α；h : #α < #β；hβ : ℵ₀ <= #β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Cardinal.infinite_pigeonhole_card`：infinite_pigeonhole_card {β α : Type 
u} (f : β -> α) (θ : Cardinal) (hθ : θ <= #β) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.co
f) : exists a : α, θ <=…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Cardinal.isRegular_aleph0`：isRegular_aleph0 : IsRegular ℵ₀
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `LE.le.ge`：∀ {α : Type u_2} [inst : LE α] {a b : α}, a ≤ b → b ≥ a
· 使用定理 `Cardinal.IsRegular.le_cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c ≤
 c.ord.cof
· 使用定理 `Cardinal.isRegular_succ`：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : 
IsRegular (succ c)

--- 原说明 ---
A function whose domain's cardinality is infinite and strictly greater than its 
codomain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (h : #α < #β) (hβ : ℵ₀ ≤ #β) :
    ∃ a : α, #α < #(f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card f ℵ₀ hβ le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
    exact ⟨a, ha.trans' (succ_le_of_lt hα)⟩
  · exact infinite_pigeonhole_card f (succ #α) (succ_le_of_lt h) (hα.trans (le_succ _))
      ((lt_succ _).trans_le (isRegular_succ hα).2.ge)

/-- A function whose domain's cardinality is infinite and strictly greater than its codomain's
has an infinite fiber. -/
/-
**Cardinal.exists_infinite_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_infinite_fiber {β α : Type u} (f : β -> α) (h : #α < #β) [Infinite 
β] : exists a : α, Infinite (f ⁻¹' {a})
参数：f : β -> α；h : #α < #β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Cardinal.infinite_pigeonhole_card`：infinite_pigeonhole_card {β α : Type 
u} (f : β -> α) (θ : Cardinal) (hθ : θ <= #β) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.co
f) : exists a : α, θ <=…
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Cardinal.isRegular_aleph0`：isRegular_aleph0 : IsRegular ℵ₀
· 使用定理 `Cardinal.infinite_pigeonhole_card_lt`：infinite_pigeonhole_card_lt {β α :
 Type u} (f : β -> α) (h : #α < #β) (hβ : ℵ₀ <= #β) : exists a : α, #α < #(f ⁻¹'
 {a})
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A function whose domain's cardinality is infinite and strictly greater than its 
codomain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type u} (f : β → α) (h : #α < #β) [Infinite β] :
    ∃ a : α, Infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₀ (aleph0_le_mk β) le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (aleph0_le_mk β)
    exact ⟨a, hα.trans ha.le⟩

/-- A weaker version of `exists_infinite_fiber` that requires codomain to be infinite. -/
/-
**Cardinal.exists_infinite_fiber'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_infinite_fiber' {β α : Type u} (f : β -> α) (h : #α < #β) [Infinite
 α] : exists a : α, Infinite (f ⁻¹' {a})
参数：f : β -> α；h : #α < #β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_cardinalMk_le`：∀ {α β : Type u} [Infinite α], Cardinal.mk α 
≤ Cardinal.mk β → Infinite β
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.exists_infinite_fiber`：exists_infinite_fiber {β α : Type u} (f 
: β -> α) (h : #α < #β) [Infinite β] : exists a : α, Infinite (f ⁻¹' {a})

--- 原说明 ---
A weaker version of `exists_infinite_fiber` that requires codomain to be infinit
e.
-/
theorem exists_infinite_fiber' {β α : Type u} (f : β → α) (h : #α < #β) [Infinite α] :
    ∃ a : α, Infinite (f ⁻¹' {a}) := by
  suffices Infinite β from exists_infinite_fiber f h
  exact .of_cardinalMk_le h.le

/-- A function whose domain's cardinality is uncountable and strictly greater than its codomain's
has an uncountable fiber. -/
/-
**Cardinal.exists_uncountable_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_uncountable_fiber {β α : Type u} (f : β -> α) (h : #α < #β) [Uncoun
table β] : exists a : α, Uncountable (f ⁻¹' {a})
参数：f : β -> α；h : #α < #β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Cardinal.infinite_pigeonhole_card`：infinite_pigeonhole_card {β α : Type 
u} (f : β -> α) (θ : Cardinal) (hθ : θ <= #β) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.co
f) : exists a : α, θ <=…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.aleph0_lt_aleph_one`：aleph0_lt_aleph_one : ℵ₀ < ℵ₁
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Cardinal.isRegular_aleph_one`：isRegular_aleph_one : IsRegular ℵ₁
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.infinite_pigeonhole_card_lt`：infinite_pigeonhole_card_lt {β α :
 Type u} (f : β -> α) (h : #α < #β) (hβ : ℵ₀ <= #β) : exists a : α, #α < #(f ⁻¹'
 {a})
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `instInfiniteOfUncountable`：∀ {α : Sort u} [Uncountable α], Infinite α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.succ_aleph0`：succ_aleph0 : succ ℵ₀ = ℵ₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_succ_iff`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 
: SuccOrder α] {a b : α} [NoMaxOrder α],   Order.succ a ≤ Order.succ b ↔ a ≤ b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b

--- 原说明 ---
A function whose domain's cardinality is uncountable and strictly greater than i
ts codomain's
has an uncountable fiber.
-/
theorem exists_uncountable_fiber {β α : Type u} (f : β → α) (h : #α < #β) [Uncountable β] :
    ∃ a : α, Uncountable (f ⁻¹' {a}) := by
  simp_rw [← Cardinal.aleph0_lt_mk_iff, ← aleph_one_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₁ (by simp) aleph0_lt_aleph_one.le
      (by rw [isRegular_aleph_one.cof_ord]; exact hα.trans aleph0_lt_aleph_one)
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (aleph0_le_mk β)
    rw [← Order.succ_le_succ_iff, succ_aleph0] at hα
    exact ⟨a, hα.trans (succ_le_of_lt ha)⟩

/-- If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`. -/
/-
**Cardinal.le_range_of_union_finset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：le_range_of_union_finset_eq_univ {α β : Type*} [Infinite β] (f : α -> Fins
et β) (w : ⋃ a, (f a : Set β) = Set.univ) : #β <= #(range f)
参数：f : α -> Finset β；w : ⋃ a, (f a : Set β) = Set.univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Cardinal.exists_infinite_fiber`：exists_infinite_fiber {β α : Type u} (f 
: β -> α) (h : #α < #β) [Infinite β] : exists a : α, Infinite (f ⁻¹' {a})
· 使用定理 `Infinite.false`：∀ {α : Sort u_1} [Finite α], Infinite α → False
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective

--- 原说明 ---
If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
theorem le_range_of_union_finset_eq_univ {α β : Type*} [Infinite β] (f : α → Finset β)
    (w : ⋃ a, (f a : Set β) = Set.univ) : #β ≤ #(range f) := by
  by_contra h
  simp only [not_le] at h
  let u : ∀ b, ∃ a, b ∈ f a := fun b => by simpa using (w.ge :) (Set.mem_univ b)
  let u' : β → range f := fun b => ⟨f (u b).choose, by simp⟩
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a := by
    rintro a p m
    have m : f (u p).choose = f a := by simpa [u'] using m
    rw [← m]
    apply fun b => (u b).choose_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false

@[deprecated (since := "2026-01-17")] alias le_range_of_union_finset_eq_top :=
  le_range_of_union_finset_eq_univ

end Cardinal

