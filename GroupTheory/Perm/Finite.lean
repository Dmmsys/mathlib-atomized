/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations on `Fintype`s

This file contains miscellaneous lemmas about `Equiv.Perm` and `Equiv.swap`, building on top
of those in `Mathlib/Logic/Equiv/Basic.lean` and other files in `Mathlib/GroupTheory/Perm/*`.
-/

public section

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} {β : Type v}

-- An example on how to determine the order of an element of a finite group.
-- import Mathlib.Data.Int.Order.Units
-- example : orderOf (-1 : ℤˣ) = 2 :=
--   orderOf_eq_prime (Int.units_sq _) (by decide)

namespace Equiv.Perm

section Conjugation

variable [DecidableEq α] [Fintype α] {σ τ : Perm α}

/-
**Equiv.Perm.isConj_of_support_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isConj_of_support_equiv (f : { x // x in (σ.support : Set α) } ≃ { x // x 
in (τ.support : Set α) }) (hf : forall (x : α) (hx : x in (σ.support : Set α)), 
(f ⟨σ x, apply_mem_support.2 hx⟩ : α) = τ ↑(f ⟨x, hx⟩)) : IsConj σ τ
参数：f : { x // x in (σ.support : Set α) } ≃ { x // x in (τ.support : Set α) }；hf 
: forall (x : α) (hx : x in (σ.support : Set α)), (f ⟨σ x, apply_mem_support.2 h
x⟩ : α) = τ ↑(f ⟨x, hx⟩)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Equiv.extendSubtype_apply_of_mem`：extendSubtype_apply_of_mem (e : { x //
 p x } ≃ { x // q x }) (x) (hx : p x) : e.extendSubtype x = e ⟨x, hx⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.extendSubtype_not_mem`：extendSubtype_not_mem (e : { x // p x } ≃ {
 x // q x }) (x) (hx : ¬p x) : ¬q (e.extendSubtype x)
-/
theorem isConj_of_support_equiv
    (f : { x // x ∈ (σ.support : Set α) } ≃ { x // x ∈ (τ.support : Set α) })
    (hf : ∀ (x : α) (hx : x ∈ (σ.support : Set α)),
      (f ⟨σ x, apply_mem_support.2 hx⟩ : α) = τ ↑(f ⟨x, hx⟩)) :
    IsConj σ τ := by
  refine isConj_iff.2 ⟨Equiv.extendSubtype f, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ σ.support
  · rw [Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_apply_of_mem]
    · exact hf x (Finset.mem_coe.2 hx)
  · rwa [Classical.not_not.1 ((not_congr mem_support).1 (Equiv.extendSubtype_not_mem f _ _)),
      Classical.not_not.1 ((not_congr mem_support).mp hx)]

end Conjugation

/-
**Equiv.Perm.perm_symm_on_of_perm_on_finset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：perm_symm_on_of_perm_on_finset {s : Finset α} {f : Perm α} (h : forall x i
n s, f x in s) {y : α} (hy : y in s) : f.symm y in s
参数：h : forall x in s, f x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.surj_on_of_inj_on_of_card_le`：surj_on_of_inj_on_of_card_le (f : f
orall a in s, β) (hf : forall a ha, f a ha in t) (hinj : forall a₁ a₂ ha₁ ha₂, f
 a₁ ha₁ = f a₂ ha₂ -> a₁ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem perm_symm_on_of_perm_on_finset {s : Finset α} {f : Perm α} (h : ∀ x ∈ s, f x ∈ s) {y : α}
    (hy : y ∈ s) : f.symm y ∈ s := by
  have h0 : ∀ y ∈ s, ∃ (x : _) (hx : x ∈ s), y = (fun i (_ : i ∈ s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i _ => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp heq) rfl.ge
  obtain ⟨y2, hy2, rfl⟩ := h0 y hy
  simpa using hy2
/-
**Equiv.Perm.perm_symm_mapsTo_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：perm_symm_mapsTo_of_mapsTo (f : Perm α) {s : Set α} [Finite s] (h : Set.Ma
psTo f s s) : Set.MapsTo f.symm s s
参数：f : Perm α；h : Set.MapsTo f s s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Equiv.Perm.perm_symm_on_of_perm_on_finset`：perm_symm_on_of_perm_on_finse
t {s : Finset α} {f : Perm α} (h : forall x in s, f x in s) {y : α} (hy : y in s
) : f.symm y in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem perm_symm_mapsTo_of_mapsTo (f : Perm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s) :
    Set.MapsTo f.symm s s := by
  cases nonempty_fintype s
  exact fun x hx =>
    Set.mem_toFinset.mp <|
      perm_symm_on_of_perm_on_finset
        (fun a ha => Set.mem_toFinset.mpr (h (Set.mem_toFinset.mp ha)))
        (Set.mem_toFinset.mpr hx)

@[simp]
/-
**Equiv.Perm.perm_symm_mapsTo_iff_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：perm_symm_mapsTo_iff_mapsTo {f : Perm α} {s : Set α} [Finite s] : Set.Maps
To f.symm s s ↔ Set.MapsTo f s s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.perm_symm_mapsTo_of_mapsTo`：perm_symm_mapsTo_of_mapsTo (f : P
erm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s) : Set.MapsTo f.symm s s
-/
theorem perm_symm_mapsTo_iff_mapsTo {f : Perm α} {s : Set α} [Finite s] :
    Set.MapsTo f.symm s s ↔ Set.MapsTo f s s :=
  ⟨perm_symm_mapsTo_of_mapsTo f⁻¹, perm_symm_mapsTo_of_mapsTo f⟩
/-
**Equiv.Perm.perm_symm_on_of_perm_on_finite** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：perm_symm_on_of_perm_on_finite {f : Perm α} {p : α -> Prop} [Finite { x //
 p x }] (h : forall x, p x -> p (f x)) {x : α} (hx : p x) : p (f.symm x)
参数：h : forall x, p x -> p (f x)；hx : p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.perm_symm_mapsTo_of_mapsTo`：perm_symm_mapsTo_of_mapsTo (f : P
erm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s) : Set.MapsTo f.symm s s
-/
theorem perm_symm_on_of_perm_on_finite {f : Perm α} {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) {x : α} (hx : p x) : p (f.symm x) := by
  have : Finite { x | p x } := by simpa
  simpa using perm_symm_mapsTo_of_mapsTo (s := {x | p x}) f h hx

/-- If the permutation `f` maps `{x // p x}` into itself, then this returns the permutation
  on `{x // p x}` induced by `f`. Note that the `h` hypothesis is weaker than for
  `Equiv.Perm.subtypePerm`. -/
/-
**Equiv.Perm.subtypePermOfFintype** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePermOfFintype (f : Perm α) {p : α -> Prop} [Finite { x // p x }] (h
 : forall x, p x -> p (f x)) : Perm { x // p x }
参数：f : Perm α；h : forall x, p x -> p (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the permutation `f` maps `{x // p x}` into itself, then this returns the perm
utation
  on `{x // p x}` induced by `f`. Note that the `h` hypothesis is weaker than fo
r
  `Equiv.Perm.subtypePerm`.
-/
abbrev subtypePermOfFintype (f : Perm α) {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) : Perm { x // p x } :=
  f.subtypePerm fun x => ⟨fun h₂ => f.symm_apply_apply x ▸ perm_symm_on_of_perm_on_finite h h₂, h x⟩

@[simp]
/-
**Equiv.Perm.subtypePermOfFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePermOfFintype_apply (f : Perm α) {p : α -> Prop} [Finite { x // p x
 }] (h : forall x, p x -> p (f x)) (x : { x // p x }) : subtypePermOfFintype f h
 x = ⟨f x, h x x.2⟩
参数：f : Perm α；h : forall x, p x -> p (f x)；x : { x // p x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypePermOfFintype_apply (f : Perm α) {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) (x : { x // p x }) : subtypePermOfFintype f h x = ⟨f x, h x x.2⟩ :=
  rfl
/-
**Equiv.Perm.subtypePermOfFintype_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePermOfFintype_one (p : α -> Prop) [Finite { x // p x }] (h : forall
 x, p x -> p ((1 : Perm α) x)) : @subtypePermOfFintype α 1 p _ h = 1
参数：p : α -> Prop；h : forall x, p x -> p ((1 : Perm α) x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypePermOfFintype_one (p : α → Prop) [Finite { x // p x }]
    (h : ∀ x, p x → p ((1 : Perm α) x)) : @subtypePermOfFintype α 1 p _ h = 1 :=
  rfl
/-
**Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：perm_mapsTo_inl_iff_mapsTo_inr {m n : Type*} [Finite m] [Finite n] (σ : Pe
rm (m oplus n)) : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) ↔ Set.Map
sTo σ (Set.range Sum.inr) (Set.range Sum.inr)
参数：σ : Perm (m oplus n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.perm_symm_mapsTo_iff_mapsTo`：perm_symm_mapsTo_iff_mapsTo {f :
 Perm α} {s : Set α} [Finite s] : Set.MapsTo f.symm s s ↔ Set.MapsTo f s s
-/
theorem perm_mapsTo_inl_iff_mapsTo_inr {m n : Type*} [Finite m] [Finite n] (σ : Perm (m ⊕ n)) :
    Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) ↔
      Set.MapsTo σ (Set.range Sum.inr) (Set.range Sum.inr) := by
  constructor <;>
    ( intro h
      classical
        rw [← perm_symm_mapsTo_iff_mapsTo] at h
        intro x
        rcases hx : σ x with l | r)
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
    grind
  · rintro _; exact ⟨r, rfl⟩
  · rintro _; exact ⟨l, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
    grind

set_option backward.isDefEq.respectTransparency.types false in
/-
**Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm`。
形式化陈述：mem_sumCongrHom_range_of_perm_mapsTo_inl {m n : Type*} [Finite m] [Finite 
n] {σ : Perm (m oplus n)} (h : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.i
nl)) : σ in (sumCongrHom m n).range
参数：m oplus n；h : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr`：perm_mapsTo_inl_iff_mapsTo_in
r {m n : Type*} [Finite m] [Finite n] (σ : Perm (m oplus n)) : Set.MapsTo σ (Set
.range Sum.inl) (Set.range Sum.…
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mem_range`：mem_range {f : G ->* N} {y : N} : y in f.range ↔ ex
ists x, f x = y
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
· 使用定理 `Equiv.Perm.sumCongrHom_apply`：∀ (α : Type u_7) (β : Type u_8) (a : Equiv
.Perm α × Equiv.Perm β), (Equiv.Perm.sumCongrHom α β) a = a.1.sumCongr a.2
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `Sum.map_inl`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_3} {β' : Type 
u_4} (f : α → α') (g : β → β') (x : α),   Sum.map f g (Sum.inl x) = Sum.inl (f x
)
· 使用定理 `Equiv.permCongr_apply`：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β') (
p : Equiv.Perm α') (x : β'), (e.permCongr p) x = e (p (e.symm x))
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
· 使用定理 `Equiv.apply_ofInjective_symm`：apply_ofInjective_symm {α β} {f : α -> β} 
(hf : Injective f) (b : range f) : f ((ofInjective f hf).symm b) = b
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `Sum.map_inr`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_3} {β' : Type 
u_4} (f : α → α') (g : β → β') (x : β),   Sum.map f g (Sum.inr x) = Sum.inr (g x
)
-/
theorem mem_sumCongrHom_range_of_perm_mapsTo_inl {m n : Type*} [Finite m] [Finite n]
    {σ : Perm (m ⊕ n)} (h : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl)) :
    σ ∈ (sumCongrHom m n).range := by
  have h1 : ∀ x : m ⊕ n, (∃ a : m, Sum.inl a = x) → ∃ a : m, Sum.inl a = σ x := by
    rintro _ ⟨a, rfl⟩; exact h ⟨a, rfl⟩
  have h3 : ∀ x : m ⊕ n, (∃ b : n, Sum.inr b = x) → ∃ b : n, Sum.inr b = σ x := by
    rintro _ ⟨b, rfl⟩; exact (perm_mapsTo_inl_iff_mapsTo_inr σ).mp h ⟨b, rfl⟩
  let σ₁' := subtypePermOfFintype σ h1
  let σ₂' := subtypePermOfFintype σ h3
  let σ₁ := permCongr (Equiv.ofInjective _ Sum.inl_injective).symm σ₁'
  let σ₂ := permCongr (Equiv.ofInjective _ Sum.inr_injective).symm σ₂'
  rw [MonoidHom.mem_range, Prod.exists]
  use σ₁, σ₂
  rw [Perm.sumCongrHom_apply]
  ext (a | b)
  · rw [Equiv.sumCongr_apply, Sum.map_inl, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inl_injective, ofInjective_apply]
    rfl
  · rw [Equiv.sumCongr_apply, Sum.map_inr, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inr_injective, ofInjective_apply]
    rfl

nonrec theorem Disjoint.orderOf {σ τ : Perm α} (hστ : Disjoint σ τ) :
    orderOf (σ * τ) = Nat.lcm (orderOf σ) (orderOf τ) :=
  haveI h : ∀ n : ℕ, (σ * τ) ^ n = 1 ↔ σ ^ n = 1 ∧ τ ^ n = 1 := fun n => by
    rw [hστ.commute.mul_pow, Disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n)]
  Nat.dvd_antisymm hστ.commute.orderOf_mul_dvd_lcm
    (Nat.lcm_dvd
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).1)
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).2))
/-
**Equiv.Perm.Disjoint.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoin
t`。
形式化陈述：∀ {α : Type u} {β : Type v} {p : β → Prop} [inst : DecidablePred p] (f : α
 ≃ Subtype p) {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ.extendDomain f).Disjoint
 (τ.extendDomain f)
参数：f : α ≃ Subtype p；σ.extendDomain f；τ.extendDomain f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
-/
theorem Disjoint.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)
    {σ τ : Perm α} (h : Disjoint σ τ) : Disjoint (σ.extendDomain f) (τ.extendDomain f) := by
  intro b
  by_cases pb : p b
  · refine (h (f.symm ⟨b, pb⟩)).imp ?_ ?_ <;>
      · intro h
        rw [extendDomain_apply_subtype _ _ pb, h, apply_symm_apply, Subtype.coe_mk]
  · left
    rw [extendDomain_apply_not_subtype _ _ pb]

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.Disjoint.isConj_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`
。
形式化陈述：∀ {α : Type u} [Finite α] {σ τ π ρ : Equiv.Perm α},   IsConj σ π → IsConj 
τ ρ → σ.Disjoint τ → π.Disjoint ρ → IsConj (σ * τ) (π * ρ)
参数：σ * τ；π * ρ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Equiv.Perm.Disjoint.support_mul`：∀ {α : Type u_1} [inst : DecidableEq α]
 [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).support = f
.support ∪ g.support
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
· 使用定理 `Equiv.Perm.isConj_of_support_equiv`：isConj_of_support_equiv (f : { x // 
x in (σ.support : Set α) } ≃ { x // x in (τ.support : Set α) }) (hf : forall (x 
: α) (hx : x in (σ.suppo…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.support_conj`：support_conj : (σ * τ * σ⁻¹).support = τ.suppor
t.map σ.toEmbedding
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.setCongr_apply`：∀ {α : Type u_3} {s t : Set α} (h : s = t) (a : { 
a // (fun x => x ∈ s) a }), (Equiv.setCongr h) a = ⟨↑a, ⋯⟩
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `Equiv.setCongr_symm_apply`：∀ {α : Type u_3} {s t : Set α} (h : s = t) (b
 : { b // (fun x => x ∈ t) b }), (Equiv.setCongr h).symm b = ⟨↑b, ⋯⟩
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
（共 41 条，此处仅展示前 30 条）
-/
theorem Disjoint.isConj_mul [Finite α] {σ τ π ρ : Perm α} (hc1 : IsConj σ π)
    (hc2 : IsConj τ ρ) (hd1 : Disjoint σ τ) (hd2 : Disjoint π ρ) : IsConj (σ * τ) (π * ρ) := by
  classical
  cases nonempty_fintype α
  obtain ⟨f, rfl⟩ := isConj_iff.1 hc1
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc2
  have hd1' := coe_inj.2 hd1.support_mul
  have hd2' := coe_inj.2 hd2.support_mul
  rw [coe_union] at *
  have hd1'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd1)
  have hd2'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd2)
  refine isConj_of_support_equiv ?_ ?_
  · refine ((Equiv.setCongr hd1').trans (Equiv.Set.union hd1'')).trans <|
      (Equiv.sumCongr (subtypeEquiv f fun a => ?_) <| subtypeEquiv g fun a => ?_).trans
        ((Equiv.setCongr hd2').trans (Equiv.Set.union hd2'')).symm <;>
      simp only [Set.mem_image, toEmbedding_apply, exists_eq_right, support_conj, coe_map,
        apply_eq_iff_eq]
  intro x hx
  simp only [trans_apply, symm_trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply,
    Equiv.sumCongr_apply]
  rw [hd1', Set.mem_union] at hx
  rcases hx with hxσ | hxτ
  · rw [mem_coe, mem_support] at hxσ
    rw [Set.union_apply_left, Set.union_apply_left]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inl, comp_apply,
        Set.union_symm_apply_left, Subtype.coe_mk, apply_eq_iff_eq, coe_inv]
      have h := (hd2 (f x)).resolve_left ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [h, symm_apply_apply, (hd1 x).resolve_left hxσ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 x).resolve_left hxσ, mem_coe,
        apply_mem_support, mem_support]
  · rw [mem_coe, ← apply_mem_support, mem_support] at hxτ
    rw [Set.union_apply_right, Set.union_apply_right]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inr, comp_apply,
        Set.union_symm_apply_right, Subtype.coe_mk]
      have h := (hd2 (g (τ x))).resolve_right ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [coe_inv, coe_inv, symm_apply_apply, h, (hd1 (τ x)).resolve_right hxτ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, ← apply_mem_support, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 (τ x)).resolve_right hxτ,
        mem_coe, mem_support]
/-
**Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer** 是 Mathlib 中的一个定理
，位于命名空间 `Equiv.Perm`。
形式化陈述：apply_mem_fixedPoints_iff_mem_of_mem_centralizer {g p : Perm α} (hp : p in
 Subgroup.centralizer {g}) {x : α} : p x in Function.fixedPoints g ↔ x in Functi
on.fixedPoints g
参数：hp : p in Subgroup.centralizer {g}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_mem_fixedPoints_iff_mem_of_mem_centralizer {g p : Perm α}
    (hp : p ∈ Subgroup.centralizer {g}) {x : α} :
    p x ∈ Function.fixedPoints g ↔ x ∈ Function.fixedPoints g := by
  simp only [Subgroup.mem_centralizer_singleton_iff] at hp
  simp only [Function.mem_fixedPoints_iff]
  rw [← mul_apply, ← hp, mul_apply, EmbeddingLike.apply_eq_iff_eq]

variable [DecidableEq α]
/-
**Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self** 是 Mathlib 中的一个引理，位于命名空间
 `Equiv.Perm`。
形式化陈述：disjoint_ofSubtype_of_memFixedPoints_self {g : Perm α} (u : Perm (Function
.fixedPoints g)) : Disjoint (ofSubtype u) g
参数：u : Perm (Function.fixedPoints g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.disjoint_iff_eq_or_eq`：disjoint_iff_eq_or_eq : Disjoint f g ↔
 forall x : α, f x = x ∨ g x = x
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
-/
lemma disjoint_ofSubtype_of_memFixedPoints_self {g : Perm α}
    (u : Perm (Function.fixedPoints g)) :
    Disjoint (ofSubtype u) g := by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x ∈ Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

section Fintype

variable [Fintype α]

/-
**Equiv.Perm.support_pow_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_pow_coprime {σ : Perm α} {n : Nat} (h : Nat.Coprime n (orderOf σ))
 : (σ ^ n).support = σ.support
参数：h : Nat.Coprime n (orderOf σ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pow_eq_self_of_coprime`：exists_pow_eq_self_of_coprime (h : n.Copr
ime (orderOf x)) : exists m : Nat, (x ^ n) ^ m = x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.Perm.support_pow_le`：support_pow_le (σ : Perm α) (n : Nat) : (σ ^ 
n).support <= σ.support
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem support_pow_coprime {σ : Perm α} {n : ℕ} (h : Nat.Coprime n (orderOf σ)) :
    (σ ^ n).support = σ.support := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  exact
    le_antisymm (support_pow_le σ n)
      (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m))
/-
**Equiv.Perm.ofSubtype_support_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_support_disjoint {σ : Perm α} (x : Perm (Function.fixedPoints σ)
) : _root_.Disjoint x.ofSubtype.support σ.support
参数：x : Perm (Function.fixedPoints σ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_iff_ne`：disjoint_iff_ne : Disjoint s t ↔ forall a in s, 
forall b in t, a != b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
-/
lemma ofSubtype_support_disjoint {σ : Perm α} (x : Perm (Function.fixedPoints σ)) :
    _root_.Disjoint x.ofSubtype.support σ.support := by
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  rw [mem_support] at ha hb
  exact ha (ofSubtype_apply_of_not_mem x (mt Function.mem_fixedPoints_iff.mp hb))

open Subgroup
/-
**Equiv.Perm.disjoint_of_disjoint_support** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`
。
形式化陈述：disjoint_of_disjoint_support {H K : Subgroup (Perm α)} (h : forall a in H,
 forall b in K, _root_.Disjoint a.support b.support) : _root_.Disjoint H K
参数：Perm α；h : forall a in H, forall b in K, _root_.Disjoint a.support b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Equiv.Perm.support_eq_empty_iff`：support_eq_empty_iff {σ : Perm α} : σ.s
upport = ∅ ↔ σ = 1
· 使用定理 `Finset.bot_eq_empty`：bot_eq_empty : (⊥ : Finset α) = ∅
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
-/
lemma disjoint_of_disjoint_support {H K : Subgroup (Perm α)}
    (h : ∀ a ∈ H, ∀ b ∈ K, _root_.Disjoint a.support b.support) :
    _root_.Disjoint H K := by
  rw [disjoint_iff_inf_le]
  intro x ⟨hx1, hx2⟩
  specialize h x hx1 x hx2
  rwa [disjoint_self, Finset.bot_eq_empty, support_eq_empty_iff] at h
/-
**Equiv.Perm.support_closure_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`
。
形式化陈述：support_closure_subset_union (S : Set (Perm α)) : forall a in closure S, (
a.support : Set α) subseteq ⋃ b in S, b.support
参数：S : Set (Perm α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_induction`：closure_induction {p : (g : G) -> g in closu
re k -> Prop} (mem : forall x (hx : x in k), p x (subset_closure hx)) (one : p 1
 (one_mem _)) (m…
· 使用定理 `Set.subset_iUnion₂_of_subset`：subset_iUnion₂_of_subset {s : Set α} {t : 
forall i, κ i -> Set α} (i : ι) (j : κ i) (h : s subseteq t i j) : s subseteq ⋃ 
(i) (j), t i j
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Equiv.Perm.support_mul_le`：support_mul_le (f g : Perm α) : (f * g).suppo
rt <= f.support ⊔ g.support
· 使用定理 `Finset.sup_eq_union`：sup_eq_union {s t : Finset α} : s ⊔ t = s union t
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.Perm.support_inv`：support_inv (σ : Perm α) : support σ⁻¹ = σ.suppo
rt
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma support_closure_subset_union (S : Set (Perm α)) :
    ∀ a ∈ closure S, (a.support : Set α) ⊆ ⋃ b ∈ S, b.support := by
  apply closure_induction
  · exact fun x hx ↦ Set.subset_iUnion₂_of_subset x hx subset_rfl
  · simp
  · intro a b ha hb hc hd
    refine (Finset.coe_subset.mpr (support_mul_le a b)).trans ?_
    rw [Finset.sup_eq_union, Finset.coe_union, Set.union_subset_iff]
    exact ⟨hc, hd⟩
  · simp only [support_inv, imp_self, implies_true]
/-
**Equiv.Perm.disjoint_support_closure_of_disjoint_support** 是 Mathlib 中的一个引理，位于命
名空间 `Equiv.Perm`。
形式化陈述：disjoint_support_closure_of_disjoint_support {S T : Set (Perm α)} (h : for
all a in S, forall b in T, _root_.Disjoint a.support b.support) : forall a in cl
osure S, forall b in closure T, _root_.Disjoint a.support b.support
参数：Perm α；h : forall a in S, forall b in T, _root_.Disjoint a.support b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.Perm.support_closure_subset_union`：support_closure_subset_union (S
 : Set (Perm α)) : forall a in closure S, (a.support : Set α) subseteq ⋃ b in S,
 b.support
· 使用引理 `Set.disjoint_of_subset`：disjoint_of_subset (hs : s₁ subseteq s₂) (ht : t
₁ subseteq t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma disjoint_support_closure_of_disjoint_support {S T : Set (Perm α)}
    (h : ∀ a ∈ S, ∀ b ∈ T, _root_.Disjoint a.support b.support) :
    ∀ a ∈ closure S, ∀ b ∈ closure T, _root_.Disjoint a.support b.support := by
  intro a ha b hb
  have key1 := support_closure_subset_union S a ha
  have key2 := support_closure_subset_union T b hb
  have key := Set.disjoint_of_subset key1 key2
  simp_rw [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Finset.disjoint_coe] at key
  exact key h
/-
**Equiv.Perm.disjoint_closure_of_disjoint_support** 是 Mathlib 中的一个引理，位于命名空间 `Equ
iv.Perm`。
形式化陈述：disjoint_closure_of_disjoint_support {S T : Set (Perm α)} (h : forall a in
 S, forall b in T, _root_.Disjoint a.support b.support) : _root_.Disjoint (closu
re S) (closure T)
参数：Perm α；h : forall a in S, forall b in T, _root_.Disjoint a.support b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.Perm.disjoint_of_disjoint_support`：disjoint_of_disjoint_support {H
 K : Subgroup (Perm α)} (h : forall a in H, forall b in K, _root_.Disjoint a.sup
port b.support) : _root_.Disj…
· 使用引理 `Equiv.Perm.disjoint_support_closure_of_disjoint_support`：disjoint_suppor
t_closure_of_disjoint_support {S T : Set (Perm α)} (h : forall a in S, forall b 
in T, _root_.Disjoint a.support b.support) : …
-/
lemma disjoint_closure_of_disjoint_support {S T : Set (Perm α)}
    (h : ∀ a ∈ S, ∀ b ∈ T, _root_.Disjoint a.support b.support) :
    _root_.Disjoint (closure S) (closure T) := by
  apply disjoint_of_disjoint_support
  apply disjoint_support_closure_of_disjoint_support
  exact h
/-
**Equiv.Perm.mem_range_ofSubtype_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_range_ofSubtype_iff {p : α -> Prop} [DecidablePred p] {g : Perm α} : g
 in (ofSubtype : Perm (Subtype p) ->* Perm α).range ↔ (g.support : Set α) subset
eq Set.ofPred p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Equiv.Perm.ofSubtype_subtypePerm`：ofSubtype_subtypePerm {f : Perm α} (h₁
 : forall x, p (f x) ↔ p x) (h₂ : forall x, f x != x -> p x) : ofSubtype (subtyp
ePerm f h₁) = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
-/
theorem mem_range_ofSubtype_iff {p : α → Prop} [DecidablePred p] {g : Perm α} :
    g ∈ (ofSubtype : Perm (Subtype p) →* Perm α).range ↔ (g.support : Set α) ⊆ Set.ofPred p := by
  constructor
  · rintro ⟨k, rfl⟩ x
    simp only [Finset.mem_coe, mem_support_ofSubtype, Set.mem_ofPred_eq]
    exact fun ⟨hx, _⟩ ↦ hx
  · intro hg
    refine ⟨g.subtypePerm fun x ↦ ?_, ofSubtype_subtypePerm _ fun x hx ↦ hg (mem_support.mpr hx)⟩
    by_cases hx : g x = x
    · rw [hx]
    · refine iff_of_true (hg ?_) (hg ?_) <;> simpa

end Fintype

end Equiv.Perm

