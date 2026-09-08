/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Interval.Finset.Defs

/-!
# `Filter.atTop` and `Filter.atBot` filters and finite sets.
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

/-
**Filter.tendsto_finset_range** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_finset_range : Tendsto Finset.range atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Finset.range_mono`：range_mono : Monotone range
· 使用定理 `Finset.exists_nat_subset_range`：exists_nat_subset_range (s : Finset Nat)
 : exists n : Nat, s subseteq range n
-/
theorem tendsto_finset_range : Tendsto Finset.range atTop atTop :=
  Finset.range_mono.tendsto_atTop_atTop Finset.exists_nat_subset_range
/-
**Filter.atTop_finset_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_finset_eq_iInf : (atTop : Filter (Finset α)) = ⨅ x : α, 𝓟 (Ici {x})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_atTop`：mem_atTop [Preorder α] (a : α) : { b : α | a <= b } in
 @atTop α _
· 使用定理 `Filter.mem_iInf_of_iInter`：mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U
 : Set α} {I : Set ι} (I_fin : I.Finite) {V : I -> Set α} (hV : forall (i : I), 
V i in s i) (hU…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem atTop_finset_eq_iInf : (atTop : Filter (Finset α)) = ⨅ x : α, 𝓟 (Ici {x}) := by
  refine le_antisymm (le_iInf fun i => le_principal_iff.2 <| mem_atTop ({i} : Finset α)) ?_
  refine
    le_iInf fun s =>
      le_principal_iff.2 <| mem_iInf_of_iInter s.finite_toSet (fun i => mem_principal_self _) ?_
  simp only [subset_def, mem_iInter, SetCoe.forall, mem_Ici,
    Finset.mem_singleton, Finset.subset_iff, forall_eq]
  exact fun t => id

/-- If `f` is a monotone sequence of `Finset`s and each `x` belongs to one of `f n`, then
`Tendsto f atTop atTop`. -/
/-
**Filter.tendsto_atTop_finset_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_finset_of_monotone [Preorder β] {f : β -> Finset α} (h : Mon
otone f) (h' : forall x : α, exists n, x in f n) : Tendsto f atTop atTop
参数：h : Monotone f；h' : forall x : α, exists n, x in f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.atTop_finset_eq_iInf`：atTop_finset_eq_iInf : (atTop : Filter (Fin
set α)) = ⨅ x : α, 𝓟 (Ici {x})
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s

--- 原说明 ---
If `f` is a monotone sequence of `Finset`s and each `x` belongs to one of `f n`,
 then
`Tendsto f atTop atTop`.
-/
theorem tendsto_atTop_finset_of_monotone [Preorder β] {f : β → Finset α} (h : Monotone f)
    (h' : ∀ x : α, ∃ n, x ∈ f n) : Tendsto f atTop atTop := by
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro a
  rcases h' a with ⟨b, hb⟩
  exact (eventually_ge_atTop b).mono fun b' hb' => (Finset.singleton_subset_iff.2 hb).trans (h hb')

alias _root_.Monotone.tendsto_atTop_finset := tendsto_atTop_finset_of_monotone
/-
**Filter.tendsto_finset_image_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_finset_image_atTop_atTop [DecidableEq β] {i : β -> γ} {j : γ -> β}
 (h : Function.LeftInverse j i) : Tendsto (Finset.image j) atTop atTop
参数：h : Function.LeftInverse j i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_finset`：∀ {α : Type u_3} {β : Type u_4} [inst : P
reorder β] {f : β → Finset α},   Monotone f → (∀ (x : α), ∃ n, x ∈ f n) → Filter
.Tendsto f Filter.a…
· 使用定理 `Finset.image_mono`：image_mono (f : α -> β) : Monotone (Finset.image f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tendsto_finset_image_atTop_atTop [DecidableEq β] {i : β → γ} {j : γ → β}
    (h : Function.LeftInverse j i) : Tendsto (Finset.image j) atTop atTop :=
  (Finset.image_mono j).tendsto_atTop_finset fun a =>
    ⟨{i a}, by simp only [Finset.image_singleton, h a, Finset.mem_singleton]⟩
/-
**Filter.tendsto_finset_preimage_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_finset_preimage_atTop_atTop {f : α -> β} (hf : Function.Injective 
f) : Tendsto (fun s : Finset β => s.preimage f (hf.injOn)) atTop atTop
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_finset`：∀ {α : Type u_3} {β : Type u_4} [inst : P
reorder β] {f : β → Finset α},   Monotone f → (∀ (x : α), ∃ n, x ∈ f n) → Filter
.Tendsto f Filter.a…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.monotone_preimage`：monotone_preimage {f : α -> β} (h : Injective 
f) : Monotone fun s => preimage s f h.injOn
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem tendsto_finset_preimage_atTop_atTop {f : α → β} (hf : Function.Injective f) :
    Tendsto (fun s : Finset β => s.preimage f (hf.injOn)) atTop atTop :=
  (Finset.monotone_preimage hf).tendsto_atTop_finset fun x =>
    ⟨{f x}, Finset.mem_preimage.2 <| Finset.mem_singleton_self _⟩
/-
**Filter.tendsto_toLeft_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_toLeft_atTop : Tendsto (Finset.toLeft (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.disjSum_empty`：disjSum_empty : s.disjSum (∅ : Finset β) = s.map E
mbedding.inl
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Embedding.inl_apply`：∀ {α : Type u_1} {β : Type u_2} (val : α),
 Function.Embedding.inl val = Sum.inl val
-/
lemma tendsto_toLeft_atTop :
    Tendsto (Finset.toLeft (α := α) (β := β)) atTop atTop := by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨t.disjSum ∅, fun b hb ↦ H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩
/-
**Filter.tendsto_toRight_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_toRight_atTop : Tendsto (Finset.toRight (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.empty_disjSum`：empty_disjSum : (∅ : Finset α).disjSum t = t.map E
mbedding.inr
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Embedding.inr_apply`：∀ {α : Type u_1} {β : Type u_2} (val : β),
 Function.Embedding.inr val = Sum.inr val
-/
lemma tendsto_toRight_atTop :
    Tendsto (Finset.toRight (α := α) (β := β)) atTop atTop := by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨.disjSum ∅ t, fun b hb ↦ H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩
/-
**Filter.tendsto_finset_powerset_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_finset_powerset_atTop_atTop : Tendsto (Finset.powerset (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup_of_le`：le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) :
 a <= s.sup f
-/
theorem tendsto_finset_powerset_atTop_atTop : Tendsto (Finset.powerset (α := α)) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.mpr fun t ↦ ⟨t.sup id, fun _ hu _ hv ↦ ?_⟩
  exact Finset.mem_powerset.mpr <| (Finset.le_sup_of_le hv fun _ h ↦ h).trans hu
/-
**Filter.tendsto_finset_Iic_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_finset_Iic_atTop_atTop [Preorder α] [LocallyFiniteOrderBot α] : Te
ndsto (Finset.Iic (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Filter.tendsto_of_isEmpty`：tendsto_of_isEmpty [IsEmpty α] {f : α -> β} {
la : Filter α} {lb : Filter β} : Tendsto f la lb
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
· 使用定理 `Finset.exists_le`：Finset.exists_le [Nonempty α] [Preorder α] [IsDirected
Order α] (s : Finset α) : exists M, forall i in s, i <= M
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_finset_Iic_atTop_atTop [Preorder α] [LocallyFiniteOrderBot α] :
    Tendsto (Finset.Iic (α := α)) atTop atTop := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact tendsto_of_isEmpty
  by_cases h : IsDirectedOrder α
  · refine tendsto_atTop_atTop.mpr fun s ↦ ?_
    obtain ⟨a, ha⟩ := Finset.exists_le s
    exact ⟨a, fun b hb c hc ↦ by simpa using (ha c hc).trans hb⟩
  · obtain h := Filter.atTop_neBot_iff.not.mpr (fun h' ↦ h h'.2)
    simp [not_ne_iff.mp <| Filter.neBot_iff.not.mp h]
/-
**Filter.tendsto_finset_Ici_atBot_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_finset_Ici_atBot_atTop [Preorder α] [LocallyFiniteOrderTop α] : Te
ndsto (Finset.Ici (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_finset_Iic_atTop_atTop`：tendsto_finset_Iic_atTop_atTop [P
reorder α] [LocallyFiniteOrderBot α] : Tendsto (Finset.Iic (α
-/
theorem tendsto_finset_Ici_atBot_atTop [Preorder α] [LocallyFiniteOrderTop α] :
    Tendsto (Finset.Ici (α := α)) atBot atTop :=
  tendsto_finset_Iic_atTop_atTop (α := αᵒᵈ)

section Card

/-- Every finset is eventually a subset of `s` along `atTop`. -/
/-
**Filter.eventually_finset_atTop_subset** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventually_finset_atTop_subset (i : Finset α) : forallᶠ s : Finset α in at
Top, i subseteq s
参数：i : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x

--- 原说明 ---
Every finset is eventually a subset of `s` along `atTop`.
-/
lemma eventually_finset_atTop_subset (i : Finset α) : ∀ᶠ s : Finset α in atTop, i ⊆ s :=
  eventually_ge_atTop _

/-- Every element of `α` is eventually a member of `s` along `atTop` on `Finset α`. -/
/-
**Filter.eventually_finset_mem_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventually_finset_mem_atTop (i : α) : forallᶠ s : Finset α in atTop, i in 
s
参数：i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Filter.eventually_finset_atTop_subset`：eventually_finset_atTop_subset (i
 : Finset α) : forallᶠ s : Finset α in atTop, i subseteq s

--- 原说明 ---
Every element of `α` is eventually a member of `s` along `atTop` on `Finset α`.
-/
lemma eventually_finset_mem_atTop (i : α) : ∀ᶠ s : Finset α in atTop, i ∈ s := by
  simpa using eventually_finset_atTop_subset {i}

/-- The pushforward of `atTop` on `Finset α` along `Finset.card` is `atTop` on `ℕ`, when `α` is
infinite. -/
/-
**Filter.map_card_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：map_card_atTop [Infinite α] : map (Finset.card (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_atTop_eq`：map_atTop_eq {f : α -> β} : atTop.map f = ⨅ a, 𝓟 (f
 '' { a' | a <= a' })
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.atTop.eq_1`：∀ {α : Type u_3} [inst : Preorder α], Filter.atTop = 
⨅ a, Filter.principal (Set.Ici a)
· 使用定理 `Function.Surjective.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : InfSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用引理 `Finset.exists_card_eq`：exists_card_eq [Infinite α] : forall n : Nat, exi
sts s : Finset α, s.card = n | 0 => ⟨∅, card_empty⟩ | n + 1 => by classical obta
in ⟨s, rfl⟩
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Infinite.exists_superset_card_eq`：exists_superset_card_eq [Infinite α] (
s : Finset α) (n : Nat) (hn : #s <= n) : exists t : Finset α, s subseteq t ∧ #t 
= n
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t

--- 原说明 ---
The pushforward of `atTop` on `Finset α` along `Finset.card` is `atTop` on `ℕ`, 
when `α` is
infinite.
-/
lemma map_card_atTop [Infinite α] :
    map (Finset.card (α := α)) atTop = atTop := by
  rw [map_atTop_eq, atTop]
  refine Function.Surjective.iInf_congr Finset.card Finset.exists_card_eq fun s ↦ congr(𝓟 $(?_))
  ext
  refine ⟨Infinite.exists_superset_card_eq _ _, ?_⟩
  aesop (add safe apply Finset.card_le_card)

/-- The pushforward of `atTop` on `Finset α` along `Finset.card` is `pure (Fintype.card α)`, when
`α` is finite. -/
/-
**Filter.map_card_atTop_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：map_card_atTop_of_fintype [Fintype α] : map (Finset.card : Finset α -> Nat
) atTop = pure (Fintype.card α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.OrderTop.atTop_eq`：∀ (α : Type u_6) [inst : PartialOrder α] [inst
_1 : OrderTop α], Filter.atTop = pure ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The pushforward of `atTop` on `Finset α` along `Finset.card` is `pure (Fintype.c
ard α)`, when
`α` is finite.
-/
lemma map_card_atTop_of_fintype [Fintype α] :
    map (Finset.card : Finset α → ℕ) atTop = pure (Fintype.card α) := by
  simp [OrderTop.atTop_eq]

/-- `Finset.card` tends to `atTop` along `atTop` on `Finset α`, when `α` is infinite. -/
/-
**Filter.tendsto_card_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_card_atTop_atTop [Infinite α] : Tendsto (Finset.card (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用引理 `Filter.map_card_atTop`：map_card_atTop [Infinite α] : map (Finset.card (α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
`Finset.card` tends to `atTop` along `atTop` on `Finset α`, when `α` is infinite
.
-/
lemma tendsto_card_atTop_atTop [Infinite α] :
    Tendsto (Finset.card (α := α)) atTop atTop := by
  rw [Tendsto, map_card_atTop]

/-- `Finset.card` tends to `pure (Fintype.card α)`, when `α` is finite. -/
/-
**Filter.tendsto_card_atTop_pure_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_card_atTop_pure_of_fintype [Fintype α] : Tendsto (Finset.card : Fi
nset α -> Nat) atTop (pure (Fintype.card α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用引理 `Filter.map_card_atTop_of_fintype`：map_card_atTop_of_fintype [Fintype α] 
: map (Finset.card : Finset α -> Nat) atTop = pure (Fintype.card α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
`Finset.card` tends to `pure (Fintype.card α)`, when `α` is finite.
-/
lemma tendsto_card_atTop_pure_of_fintype [Fintype α] :
    Tendsto (Finset.card : Finset α → ℕ) atTop (pure (Fintype.card α)) := by
  rw [Tendsto, map_card_atTop_of_fintype]

/-- `Tendsto` along `atTop` for a function precomposed with `Finset.card` reduces to `Tendsto` along
`atTop` on `ℕ`, when `α` is infinite. -/
/-
**Filter.tendsto_comp_card_atTop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_comp_card_atTop_iff [Infinite α] {f : Nat -> β} {l : Filter β} : T
endsto (fun s : Finset α => f s.card) atTop l ↔ Tendsto f atTop l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.map_card_atTop`：map_card_atTop [Infinite α] : map (Finset.card (α
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`Tendsto` along `atTop` for a function precomposed with `Finset.card` reduces to
 `Tendsto` along
`atTop` on `ℕ`, when `α` is infinite.
-/
lemma tendsto_comp_card_atTop_iff [Infinite α] {f : ℕ → β} {l : Filter β} :
    Tendsto (fun s : Finset α ↦ f s.card) atTop l ↔ Tendsto f atTop l := by
  rw [← map_card_atTop (α := α), tendsto_map'_iff]
  rfl

/-- `Tendsto` along `atTop` for a function precomposed with `Finset.card` reduces to `Tendsto` along
`pure (Fintype.card α)`, when `α` is finite. -/
/-
**Filter.tendsto_comp_card_atTop_iff_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `Filte
r`。
形式化陈述：tendsto_comp_card_atTop_iff_of_fintype [Fintype α] {f : Nat -> β} {l : Fil
ter β} : Tendsto (fun s : Finset α => f s.card) atTop l ↔ Tendsto f (pure (Finty
pe.card α)) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.map_card_atTop_of_fintype`：map_card_atTop_of_fintype [Fintype α] 
: map (Finset.card : Finset α -> Nat) atTop = pure (Fintype.card α)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`Tendsto` along `atTop` for a function precomposed with `Finset.card` reduces to
 `Tendsto` along
`pure (Fintype.card α)`, when `α` is finite.
-/
lemma tendsto_comp_card_atTop_iff_of_fintype [Fintype α] {f : ℕ → β} {l : Filter β} :
    Tendsto (fun s : Finset α ↦ f s.card) atTop l ↔ Tendsto f (pure (Fintype.card α)) l := by
  rw [← map_card_atTop_of_fintype, tendsto_map'_iff]
  rfl

end Card

end Filter

