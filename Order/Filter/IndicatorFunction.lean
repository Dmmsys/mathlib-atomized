/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Tendsto

/-!
# Indicator function and filters

Properties of additive and multiplicative indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/

public section

variable {α β M E : Type*}

open Set Filter

section One

variable [One M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

@[to_additive]
/-
**mulIndicator_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulIndicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t) : mulInd
icator s f =ᶠ[l] mulIndicator t g
参数：hf : f =ᶠ[l ⊓ 𝓟 s] g；hs : s =ᶠ[l] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyEq.mem_iff`：∀ {α : Type u} {s t : Set α} {l : Filter α}
, s =ᶠ[l] t → ∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mulIndicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t) :
    mulIndicator s f =ᶠ[l] mulIndicator t g :=
  (eventually_inf_principal.1 hf).mp <| hs.mem_iff.mono fun x hst hfg =>
    by_cases
      (fun hxs : x ∈ s => by simp only [*, hst.1 hxs, mulIndicator_of_mem])
      (fun hxs => by simp only [mulIndicator_of_notMem, hxs, mt hst.2 hxs, not_false_eq_true])

end One

section Monoid

variable [Monoid M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

@[to_additive]
/-
**mulIndicator_union_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulIndicator_union_eventuallyEq (h : forallᶠ a in l, a ∉ s inter t) : mulI
ndicator (s union t) f =ᶠ[l] mulIndicator s f * mulIndicator t f
参数：h : forallᶠ a in l, a ∉ s inter t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Set.mulIndicator_union_of_notMem_inter`：mulIndicator_union_of_notMem_int
er (h : a ∉ s inter t) (f : α -> M) : mulIndicator (s union t) f a = mulIndicato
r s f a * mulIndicator t f a
-/
theorem mulIndicator_union_eventuallyEq (h : ∀ᶠ a in l, a ∉ s ∩ t) :
    mulIndicator (s ∪ t) f =ᶠ[l] mulIndicator s f * mulIndicator t f :=
  h.mono fun _a ha => mulIndicator_union_of_notMem_inter ha _

end Monoid

section Order

variable [One β] [Preorder β] {s t : Set α} {f g : α → β} {a : α} {l : Filter α}

@[to_additive]
/-
**mulIndicator_eventuallyLE_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulIndicator_eventuallyLE_mulIndicator (h : f <=ᶠ[l ⊓ 𝓟 s] g) : mulIndicat
or s f <=ᶠ[l] mulIndicator s g
参数：h : f <=ᶠ[l ⊓ 𝓟 s] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用引理 `Set.mulIndicator_rel_mulIndicator`：mulIndicator_rel_mulIndicator {r : M 
-> M -> Prop} (h1 : r 1 1) (ha : a in s -> r (f a) (g a)) : r (mulIndicator s f 
a) (mulIndicator s g a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mulIndicator_eventuallyLE_mulIndicator (h : f ≤ᶠ[l ⊓ 𝓟 s] g) :
    mulIndicator s f ≤ᶠ[l] mulIndicator s g :=
  (eventually_inf_principal.1 h).mono fun _ => mulIndicator_rel_mulIndicator le_rfl

end Order

@[to_additive]
/-
**Monotone.mulIndicator_eventuallyEq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.mulIndicator_eventuallyEq_iUnion {ι} [Preorder ι] [One β] (s : ι 
-> Set α) (hs : Monotone s) (f : α -> β) (a : α) : (fun i => mulIndicator (s i) 
f a) =ᶠ[atTop] fun _ => mulIndicator (⋃ i, s i) f a
参数：s : ι -> Set α；hs : Monotone s；f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.piecewise_eventually_eq_iUnion`：Monotone.piecewise_eventually_e
q_iUnion {β : α -> Type*} [Preorder ι] {s : ι -> Set α} [forall i, DecidablePred
 (· in s i)] [DecidablePred (…
-/
theorem Monotone.mulIndicator_eventuallyEq_iUnion {ι} [Preorder ι] [One β] (s : ι → Set α)
    (hs : Monotone s) (f : α → β) (a : α) :
    (fun i => mulIndicator (s i) f a) =ᶠ[atTop] fun _ ↦ mulIndicator (⋃ i, s i) f a := by
  classical exact hs.piecewise_eventually_eq_iUnion f 1 a

@[to_additive]
/-
**Monotone.tendsto_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.tendsto_mulIndicator {ι} [Preorder ι] [One β] (s : ι -> Set α) (h
s : Monotone s) (f : α -> β) (a : α) : Tendsto (fun i => mulIndicator (s i) f a)
 atTop (pure <| mulIndicator (⋃ i, s i) f a)
参数：s : ι -> Set α；hs : Monotone s；f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Monotone.mulIndicator_eventuallyEq_iUnion`：Monotone.mulIndicator_eventua
llyEq_iUnion {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Monotone s) (f : α 
-> β) (a : α) : (fun i => mulIn…
-/
theorem Monotone.tendsto_mulIndicator {ι} [Preorder ι] [One β] (s : ι → Set α) (hs : Monotone s)
    (f : α → β) (a : α) :
    Tendsto (fun i => mulIndicator (s i) f a) atTop (pure <| mulIndicator (⋃ i, s i) f a) :=
  tendsto_pure.2 <| hs.mulIndicator_eventuallyEq_iUnion s f a

@[to_additive]
/-
**Antitone.mulIndicator_eventuallyEq_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mulIndicator_eventuallyEq_iInter {ι} [Preorder ι] [One β] (s : ι 
-> Set α) (hs : Antitone s) (f : α -> β) (a : α) : (fun i => mulIndicator (s i) 
f a) =ᶠ[atTop] fun _ => mulIndicator (⋂ i, s i) f a
参数：s : ι -> Set α；hs : Antitone s；f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.piecewise_eventually_eq_iInter`：Antitone.piecewise_eventually_e
q_iInter {β : α -> Type*} [Preorder ι] {s : ι -> Set α} [forall i, DecidablePred
 (· in s i)] [DecidablePred (…
-/
theorem Antitone.mulIndicator_eventuallyEq_iInter {ι} [Preorder ι] [One β] (s : ι → Set α)
    (hs : Antitone s) (f : α → β) (a : α) :
    (fun i => mulIndicator (s i) f a) =ᶠ[atTop] fun _ ↦ mulIndicator (⋂ i, s i) f a := by
  classical exact hs.piecewise_eventually_eq_iInter f 1 a

@[to_additive]
/-
**Antitone.tendsto_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.tendsto_mulIndicator {ι} [Preorder ι] [One β] (s : ι -> Set α) (h
s : Antitone s) (f : α -> β) (a : α) : Tendsto (fun i => mulIndicator (s i) f a)
 atTop (pure <| mulIndicator (⋂ i, s i) f a)
参数：s : ι -> Set α；hs : Antitone s；f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Antitone.mulIndicator_eventuallyEq_iInter`：Antitone.mulIndicator_eventua
llyEq_iInter {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Antitone s) (f : α 
-> β) (a : α) : (fun i => mulIn…
-/
theorem Antitone.tendsto_mulIndicator {ι} [Preorder ι] [One β] (s : ι → Set α) (hs : Antitone s)
    (f : α → β) (a : α) :
    Tendsto (fun i => mulIndicator (s i) f a) atTop (pure <| mulIndicator (⋂ i, s i) f a) :=
  tendsto_pure.2 <| hs.mulIndicator_eventuallyEq_iInter s f a

@[to_additive]
/-
**mulIndicator_biUnion_finset_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulIndicator_biUnion_finset_eventuallyEq {ι} [One β] (s : ι -> Set α) (f :
 α -> β) (a : α) : (fun n : Finset ι => mulIndicator (⋃ i in n, s i) f a) =ᶠ[atT
op] fun _ => mulIndicator (iUnion s) f a
参数：s : ι -> Set α；f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_eq_iUnion_finset`：iUnion_eq_iUnion_finset (s : ι -> Set α) : 
⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
· 使用定理 `Monotone.mulIndicator_eventuallyEq_iUnion`：Monotone.mulIndicator_eventua
llyEq_iUnion {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Monotone s) (f : α 
-> β) (a : α) : (fun i => mulIn…
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
-/
theorem mulIndicator_biUnion_finset_eventuallyEq {ι} [One β] (s : ι → Set α) (f : α → β) (a : α) :
    (fun n : Finset ι => mulIndicator (⋃ i ∈ n, s i) f a) =ᶠ[atTop]
      fun _ ↦ mulIndicator (iUnion s) f a := by
  rw [iUnion_eq_iUnion_finset s]
  apply Monotone.mulIndicator_eventuallyEq_iUnion
  exact fun _ _ ↦ biUnion_subset_biUnion_left

@[to_additive]
/-
**tendsto_mulIndicator_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mulIndicator_biUnion_finset {ι} [One β] (s : ι -> Set α) (f : α ->
 β) (a : α) : Tendsto (fun n : Finset ι => mulIndicator (⋃ i in n, s i) f a) atT
op (pure <| mulIndicator (iUnion s) f a)
参数：s : ι -> Set α；f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `mulIndicator_biUnion_finset_eventuallyEq`：mulIndicator_biUnion_finset_ev
entuallyEq {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α) : (fun n : Finset ι
 => mulIndicator (⋃ i in n, s …
-/
theorem tendsto_mulIndicator_biUnion_finset {ι} [One β] (s : ι → Set α) (f : α → β) (a : α) :
    Tendsto (fun n : Finset ι => mulIndicator (⋃ i ∈ n, s i) f a) atTop
      (pure <| mulIndicator (iUnion s) f a) :=
  tendsto_pure.2 <| mulIndicator_biUnion_finset_eventuallyEq s f a

@[to_additive]
/-
**Filter.EventuallyEq.mulSupport** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : One β] {f g : α → β} {l : Filter α
},   f =ᶠ[l] g → Function.mulSupport f =ᶠ[l] Function.mulSupport g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.preimage`：∀ {α : Type u} {β : Type v} {l : Filter α}
 {f g : α → β}, f =ᶠ[l] g → ∀ (s : Set β), f ⁻¹' s =ᶠ[l] g ⁻¹' s
-/
protected theorem Filter.EventuallyEq.mulSupport [One β] {f g : α → β} {l : Filter α}
    (h : f =ᶠ[l] g) :
    Function.mulSupport f =ᶠ[l] Function.mulSupport g :=
  h.preimage ({1}ᶜ : Set β)

@[to_additive]
/-
**Filter.EventuallyEq.mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyE
q`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : One β] {l : Filter α} {f g : α → β
} {s : Set α},   f =ᶠ[l] g → s.mulIndicator f =ᶠ[l] s.mulIndicator g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulIndicator_eventuallyEq`：mulIndicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s]
 g) (hs : s =ᶠ[l] t) : mulIndicator s f =ᶠ[l] mulIndicator t g
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
protected theorem Filter.EventuallyEq.mulIndicator [One β] {l : Filter α} {f g : α → β} {s : Set α}
    (hfg : f =ᶠ[l] g) : s.mulIndicator f =ᶠ[l] s.mulIndicator g :=
  mulIndicator_eventuallyEq (hfg.filter_mono inf_le_left) EventuallyEq.rfl

@[to_additive]
/-
**Filter.EventuallyEq.mulIndicator_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mulIndicator_one [One β] {l : Filter α} {f : α -> β} {
s : Set α} (hf : f =ᶠ[l] 1) : s.mulIndicator f =ᶠ[l] 1
参数：hf : f =ᶠ[l] 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.mulIndicator`：∀ {α : Type u_1} {β : Type u_2} [inst 
: One β] {l : Filter α} {f g : α → β} {s : Set α},   f =ᶠ[l] g → s.mulIndicator 
f =ᶠ[l] s.mulIndicator…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_one'`：mulIndicator_one' {s : Set α} : s.mulIndicator (1
 : α -> M) = 1
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem Filter.EventuallyEq.mulIndicator_one [One β] {l : Filter α} {f : α → β} {s : Set α}
    (hf : f =ᶠ[l] 1) : s.mulIndicator f =ᶠ[l] 1 :=
  hf.mulIndicator.trans <| by rw [mulIndicator_one']

@[to_additive]
/-
**Filter.EventuallyEq.of_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.of_mulIndicator [One β] {l : Filter α} {f : α -> β} (h
f : forallᶠ x in l, f x != 1) {s t : Set α} (h : s.mulIndicator f =ᶠ[l] t.mulInd
icator f) : s =ᶠ[l] t
参数：hf : forallᶠ x in l, f x != 1；h : s.mulIndicator f =ᶠ[l] t.mulIndicator f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulSupport_mulIndicator`：mulSupport_mulIndicator : Function.mulSuppo
rt (s.mulIndicator f) = s inter Function.mulSupport f
· 使用定理 `Filter.Eventually.set_eq`：∀ {α : Type u} {s t : Set α} {l : Filter α}, (
∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t) → s =ᶠ[l] t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.mulSupport`：∀ {α : Type u_1} {β : Type u_2} [inst : 
One β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → Function.mulSupport f =ᶠ[l] F
unction.mulSupport g
-/
theorem Filter.EventuallyEq.of_mulIndicator [One β] {l : Filter α} {f : α → β}
    (hf : ∀ᶠ x in l, f x ≠ 1) {s t : Set α} (h : s.mulIndicator f =ᶠ[l] t.mulIndicator f) :
    s =ᶠ[l] t := by
  have : ∀ {s : Set α}, Function.mulSupport (s.mulIndicator f) =ᶠ[l] s := fun {s} ↦ by
    rw [mulSupport_mulIndicator]
    exact (hf.mono fun x hx ↦ and_iff_left hx).set_eq
  exact this.symm.trans <| h.mulSupport.trans this

@[to_additive]
/-
**Filter.EventuallyEq.of_mulIndicator_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.of_mulIndicator_const [One β] {l : Filter α} {c : β} (
hc : c != 1) {s t : Set α} (h : s.mulIndicator (fun _ => c) =ᶠ[l] t.mulIndicator
 fun _ => c) : s =ᶠ[l] t
参数：hc : c != 1；h : s.mulIndicator (fun _ => c) =ᶠ[l] t.mulIndicator fun _ => c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_mulIndicator`：Filter.EventuallyEq.of_mulIndicator
 [One β] {l : Filter α} {f : α -> β} (hf : forallᶠ x in l, f x != 1) {s t : Set 
α} (h : s.mulIndicator f …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Filter.EventuallyEq.of_mulIndicator_const [One β] {l : Filter α} {c : β} (hc : c ≠ 1)
    {s t : Set α} (h : s.mulIndicator (fun _ ↦ c) =ᶠ[l] t.mulIndicator fun _ ↦ c) : s =ᶠ[l] t :=
  .of_mulIndicator (Eventually.of_forall fun _ ↦ hc) h

@[to_additive]
/-
**Filter.mulIndicator_const_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.mulIndicator_const_eventuallyEq [One β] {l : Filter α} {c : β} (hc 
: c != 1) {s t : Set α} : s.mulIndicator (fun _ => c) =ᶠ[l] t.mulIndicator (fun 
_ => c) ↔ s =ᶠ[l] t
参数：hc : c != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_mulIndicator_const`：Filter.EventuallyEq.of_mulInd
icator_const [One β] {l : Filter α} {c : β} (hc : c != 1) {s t : Set α} (h : s.m
ulIndicator (fun _ => c) =ᶠ[l] …
· 使用定理 `mulIndicator_eventuallyEq`：mulIndicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s]
 g) (hs : s =ᶠ[l] t) : mulIndicator s f =ᶠ[l] mulIndicator t g
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem Filter.mulIndicator_const_eventuallyEq [One β] {l : Filter α} {c : β} (hc : c ≠ 1)
    {s t : Set α} : s.mulIndicator (fun _ ↦ c) =ᶠ[l] t.mulIndicator (fun _ ↦ c) ↔ s =ᶠ[l] t :=
  ⟨.of_mulIndicator_const hc, mulIndicator_eventuallyEq .rfl⟩
