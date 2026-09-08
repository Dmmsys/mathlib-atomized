/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.Bases.Basic

/-!
# Lift filters along filter and set functions
-/

assert_not_exists Set.Finite

public section

open Set Filter Function

namespace Filter

variable {α β γ : Type*} {ι : Sort*}

section lift

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Set α → Filter β}

@[simp]
/-
**Filter.lift_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_top (g : Set α -> Filter β) : (⊤ : Filter α).lift g = g univ
参数：g : Set α -> Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_iInf_eq_left`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] {b : β} {f : (x : β) → x = b → α},   ⨅ x, ⨅ (h : x = b), f x h = f b ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_top (g : Set α → Filter β) : (⊤ : Filter α).lift g = g univ := by simp [Filter.lift]

/-- If `(p : ι → Prop, s : ι → Set α)` is a basis of a filter `f`, `g` is a monotone function
`Set α → Filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → Set α)` is a basis
of the filter `g (s i)`, then
`(fun (i : ι) (x : β i) ↦ p i ∧ pg i x, fun (i : ι) (x : β i) ↦ sg i x)` is a basis
of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`Filter.HasBasis` one has to use `Σ i, β i` as the index type, see `Filter.HasBasis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
/-
**Filter.HasBasis.mem_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {ι : Sort u_6} {p : ι → Prop} {s : ι → Set
 α} {f : Filter α},   f.HasBasis p s →     ∀ {β : ι → Type u_5} {pg : (i : ι) → 
β i → Prop} {sg : (i : ι) → β i → Set γ} {g : Set α → Filter γ},       (∀ (i : ι
), (g (s i)).HasBasis (pg i) (sg i)) →         Monotone g → ∀ {s : Set γ}, s ∈ f
.lift g ↔ ∃ i, p i ∧ ∃ x, pg i x ∧ sg i x ⊆ s
参数：i : ι；i : ι；∀ (i : ι), (g (s i)).HasBasis (pg i) (sg i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.mem_biInf_of_directed`：mem_biInf_of_directed {f : β -> Filter α} 
{s : Set β} (h : DirectedOn (f ⁻¹'o (· >= ·)) s) (ne : s.Nonempty) {t : Set α} :
 (t in ⨅ i in s, f…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.univ_sets`：∀ {α : Type u_1} (self : Filter α), Set.univ ∈ self.se
ts
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …

--- 原说明 ---
If `(p : ι → Prop, s : ι → Set α)` is a basis of a filter `f`, `g` is a monotone
 function
`Set α → Filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → Set α)` is a
 basis
of the filter `g (s i)`, then
`(fun (i : ι) (x : β i) ↦ p i ∧ pg i x, fun (i : ι) (x : β i) ↦ sg i x)` is a ba
sis
of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate th
is fact using
`Filter.HasBasis` one has to use `Σ i, β i` as the index type, see `Filter.HasBa
sis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma ty
pe.
-/
theorem HasBasis.mem_lift_iff {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (hf : f.HasBasis p s) {β : ι → Type*} {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ}
    {g : Set α → Filter γ} (hg : ∀ i, (g <| s i).HasBasis (pg i) (sg i)) (gm : Monotone g)
    {s : Set γ} : s ∈ f.lift g ↔ ∃ i, p i ∧ ∃ x, pg i x ∧ sg i x ⊆ s := by
  refine (mem_biInf_of_directed ?_ ⟨univ, univ_sets _⟩).trans ?_
  · intro t₁ ht₁ t₂ ht₂
    exact ⟨t₁ ∩ t₂, inter_mem ht₁ ht₂, gm inter_subset_left, gm inter_subset_right⟩
  · simp only [← (hg _).mem_iff]
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H

/-- If `(p : ι → Prop, s : ι → Set α)` is a basis of a filter `f`, `g` is a monotone function
`Set α → Filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → Set α)` is a basis
of the filter `g (s i)`, then
`(fun (i : ι) (x : β i) ↦ p i ∧ pg i x, fun (i : ι) (x : β i) ↦ sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `Filter.HasBasis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
/-
**Filter.HasBasis.lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {ι : Type u_6} {p : ι → Prop} {s : ι → Set
 α} {f : Filter α},   f.HasBasis p s →     ∀ {β : ι → Type u_5} {pg : (i : ι) → 
β i → Prop} {sg : (i : ι) → β i → Set γ} {g : Set α → Filter γ},       (∀ (i : ι
), (g (s i)).HasBasis (pg i) (sg i)) →         Monotone g → (f.lift g).HasBasis 
(fun i => p i.fst ∧ pg i.fst i.snd) fun i => sg i.fst i.snd
参数：i : ι；i : ι；∀ (i : ι), (g (s i)).HasBasis (pg i) (sg i)；f.lift g；fun i => p i
.fst ∧ pg i.fst i.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_lift_iff`：∀ {α : Type u_1} {γ : Type u_3} {ι : Sort 
u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasBasis p s →     ∀ {β 
: ι → Type u_5} {p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `(p : ι → Prop, s : ι → Set α)` is a basis of a filter `f`, `g` is a monotone
 function
`Set α → Filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → Set α)` is a
 basis
of the filter `g (s i)`, then
`(fun (i : ι) (x : β i) ↦ p i ∧ pg i x, fun (i : ι) (x : β i) ↦ sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate th
is fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `Filter.HasBas
is.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type.
-/
theorem HasBasis.lift {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α} (hf : f.HasBasis p s)
    {β : ι → Type*} {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ} {g : Set α → Filter γ}
    (hg : ∀ i, (g (s i)).HasBasis (pg i) (sg i)) (gm : Monotone g) :
    (f.lift g).HasBasis
      (fun i : Σ i, β i => p i.1 ∧ pg i.1 i.2)
      fun i : Σ i, β i => sg i.1 i.2 := by
  refine ⟨fun t => (hf.mem_lift_iff hg gm).trans ?_⟩
  simp [Sigma.exists, and_assoc, exists_and_left]
/-
**Filter.mem_lift_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_lift_sets (hg : Monotone g) {s : Set β} : s in f.lift g ↔ exists t in 
f, s in g t
参数：hg : Monotone g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_lift_iff`：∀ {α : Type u_1} {γ : Type u_3} {ι : Sort 
u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasBasis p s →     ∀ {β 
: ι → Type u_5} {p…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_lift_sets (hg : Monotone g) {s : Set β} : s ∈ f.lift g ↔ ∃ t ∈ f, s ∈ g t :=
  (f.basis_sets.mem_lift_iff (fun s => (g s).basis_sets) hg).trans <| by
    simp only [id, exists_mem_subset_iff]
/-
**Filter.sInter_lift_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sInter_lift_sets (hg : Monotone g) : ⋂₀ { s | s in f.lift g } = ⋂ s in f, 
⋂₀ { t | t in g s }
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `Set.iInter_comm`：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i'
 = ⋂ (i') (i), s i i'
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInter_lift_sets (hg : Monotone g) :
    ⋂₀ { s | s ∈ f.lift g } = ⋂ s ∈ f, ⋂₀ { t | t ∈ g s } := by
  simp only [sInter_eq_biInter, mem_ofPred_eq, mem_lift_sets hg, iInter_exists,
    iInter_and, @iInter_comm _ (Set β)]
/-
**Filter.mem_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_lift {s : Set β} {t : Set α} (ht : t in f) (hs : s in g t) : s in f.li
ft g
参数：ht : t in f；hs : s in g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mem_lift {s : Set β} {t : Set α} (ht : t ∈ f) (hs : s ∈ g t) : s ∈ f.lift g :=
  le_principal_iff.mp <|
    show f.lift g ≤ 𝓟 s from iInf_le_of_le t <| iInf_le_of_le ht <| le_principal_iff.mpr hs
/-
**Filter.lift_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filter β} {s : Set α} 
(hs : s in f) (hg : g s <= h) : f.lift g <= h
参数：hs : s in f；hg : g s <= h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
-/
theorem lift_le {f : Filter α} {g : Set α → Filter β} {h : Filter β} {s : Set α} (hs : s ∈ f)
    (hg : g s ≤ h) : f.lift g ≤ h :=
  iInf₂_le_of_le s hs hg
/-
**Filter.le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filter β} : h <= f.lif
t g ↔ forall s in f, h <= g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂_iff`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLattice α] {a : α} {f : (i : ι) → κ i → α},   a ≤ ⨅ i, ⨅ j, f i j ↔ ∀ (
i …
-/
theorem le_lift {f : Filter α} {g : Set α → Filter β} {h : Filter β} :
    h ≤ f.lift g ↔ ∀ s ∈ f, h ≤ g s :=
  le_iInf₂_iff
/-
**Filter.lift_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁ <= f₂.lift g₂
参数：hf : f₁ <= f₂；hg : g₁ <= g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `iInf_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Comp
leteLattice α] {f : ι → α} {g : ι' → α},   (∀ (i : ι), ∃ i', g i' ≤ f i) → iInf 
…
-/
theorem lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
  iInf_mono fun s => iInf_mono' fun hs => ⟨hf hs, hg s⟩
/-
**Filter.lift_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_mono' (hg : forall s in f, g₁ s <= g₂ s) : f.lift g₁ <= f.lift g₂
参数：hg : forall s in f, g₁ s <= g₂ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
-/
theorem lift_mono' (hg : ∀ s ∈ f, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ := iInf₂_mono hg
/-
**Filter.tendsto_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_lift {m : γ -> β} {l : Filter γ} : Tendsto m l (f.lift g) ↔ forall
 s in f, Tendsto m l (g s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_lift {m : γ → β} {l : Filter γ} :
    Tendsto m l (f.lift g) ↔ ∀ s ∈ f, Tendsto m l (g s) := by
  simp only [Filter.lift, tendsto_iInf]
/-
**Filter.map_lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_lift_eq {m : β -> γ} (hg : Monotone g) : map m (f.lift g) = f.lift (ma
p m ∘ g)
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_lift_eq {m : β → γ} (hg : Monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
  have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, mem_map, Function.comp_apply]
/-
**Filter.comap_lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_lift_eq {m : γ -> β} : comap m (f.lift g) = f.lift (comap m ∘ g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem comap_lift_eq {m : γ → β} : comap m (f.lift g) = f.lift (comap m ∘ g) := by
  simp only [Filter.lift, comap_iInf]; rfl
/-
**Filter.comap_lift_eq2** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_lift_eq2 {m : β -> α} {g : Set β -> Filter γ} (hg : Monotone g) : (c
omap m f).lift g = f.lift (g ∘ preimage m)
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
-/
theorem comap_lift_eq2 {m : β → α} {g : Set β → Filter γ} (hg : Monotone g) :
    (comap m f).lift g = f.lift (g ∘ preimage m) :=
  le_antisymm (le_iInf₂ fun s hs => iInf₂_le (m ⁻¹' s) ⟨s, hs, Subset.rfl⟩)
    (le_iInf₂ fun _s ⟨s', hs', h_sub⟩ => iInf₂_le_of_le s' hs' <| hg h_sub)
/-
**Filter.lift_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_map_le {g : Set β -> Filter γ} {m : α -> β} : (map m f).lift g <= f.l
ift (g ∘ image m)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift`：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} : h <= f.lift g ↔ forall s in f, h <= g s
· 使用定理 `Filter.lift_le`：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} {s : Set α} (hs : s in f) (hg : g s <= h) : f.lift g <= h
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lift_map_le {g : Set β → Filter γ} {m : α → β} : (map m f).lift g ≤ f.lift (g ∘ image m) :=
  le_lift.2 fun _s hs => lift_le (image_mem_map hs) le_rfl
/-
**Filter.map_lift_eq2** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_lift_eq2 {g : Set β -> Filter γ} {m : α -> β} (hg : Monotone g) : (map
 m f).lift g = f.lift (g ∘ image m)
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.lift_map_le`：lift_map_le {g : Set β -> Filter γ} {m : α -> β} : (
map m f).lift g <= f.lift (g ∘ image m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift`：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} : h <= f.lift g ↔ forall s in f, h <= g s
· 使用定理 `Filter.lift_le`：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} {s : Set α} (hs : s in f) (hg : g s <= h) : f.lift g <= h
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem map_lift_eq2 {g : Set β → Filter γ} {m : α → β} (hg : Monotone g) :
    (map m f).lift g = f.lift (g ∘ image m) :=
  lift_map_le.antisymm <| le_lift.2 fun _s hs => lift_le hs <| hg <| image_preimage_subset _ _
/-
**Filter.lift_comm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_comm {g : Filter β} {h : Set α -> Set β -> Filter γ} : (f.lift fun s 
=> g.lift (h s)) = g.lift fun t => f.lift fun s => h s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem lift_comm {g : Filter β} {h : Set α → Set β → Filter γ} :
    (f.lift fun s => g.lift (h s)) = g.lift fun t => f.lift fun s => h s t :=
  le_antisymm
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
      iInf_le_of_le j <| iInf_le_of_le hj <| iInf_le_of_le i <| iInf_le _ hi)
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
      iInf_le_of_le j <| iInf_le_of_le hj <| iInf_le_of_le i <| iInf_le _ hi)
/-
**Filter.lift_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_assoc {h : Set β -> Filter γ} (hg : Monotone g) : (f.lift g).lift h =
 f.lift fun s => (g s).lift h
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem lift_assoc {h : Set β → Filter γ} (hg : Monotone g) :
    (f.lift g).lift h = f.lift fun s => (g s).lift h :=
  le_antisymm
    (le_iInf₂ fun _s hs => le_iInf₂ fun t ht =>
      iInf_le_of_le t <| iInf_le _ <| (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_iInf₂ fun t ht =>
      let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
      iInf_le_of_le s <| iInf_le_of_le hs <| iInf_le_of_le t <| iInf_le _ h')
/-
**Filter.lift_lift_same_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_lift_same_le_lift {g : Set α -> Set α -> Filter β} : (f.lift fun s =>
 f.lift (g s)) <= f.lift fun s => g s s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift`：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} : h <= f.lift g ↔ forall s in f, h <= g s
· 使用定理 `Filter.lift_le`：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} {s : Set α} (hs : s in f) (hg : g s <= h) : f.lift g <= h
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lift_lift_same_le_lift {g : Set α → Set α → Filter β} :
    (f.lift fun s => f.lift (g s)) ≤ f.lift fun s => g s s :=
  le_lift.2 fun _s hs => lift_le hs <| lift_le hs le_rfl
/-
**Filter.lift_lift_same_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_lift_same_eq_lift {g : Set α -> Set α -> Filter β} (hg₁ : forall s, M
onotone fun t => g s t) (hg₂ : forall t, Monotone fun s => g s t) : (f.lift fun 
s => f.lift (g s)) = f.lift fun s => g s s
参数：hg₁ : forall s, Monotone fun t => g s t；hg₂ : forall t, Monotone fun s => g s
 t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.lift_lift_same_le_lift`：lift_lift_same_le_lift {g : Set α -> Set 
α -> Filter β} : (f.lift fun s => f.lift (g s)) <= f.lift fun s => g s s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift`：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} : h <= f.lift g ↔ forall s in f, h <= g s
· 使用定理 `Filter.lift_le`：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} {s : Set α} (hs : s in f) (hg : g s <= h) : f.lift g <= h
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem lift_lift_same_eq_lift {g : Set α → Set α → Filter β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) : (f.lift fun s => f.lift (g s)) = f.lift fun s => g s s :=
  lift_lift_same_le_lift.antisymm <|
    le_lift.2 fun s hs => le_lift.2 fun t ht => lift_le (inter_mem hs ht) <|
      calc
        g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) := hg₂ (s ∩ t) inter_subset_left
        _ ≤ g s t := hg₁ s inter_subset_right
/-
**Filter.lift_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_principal {s : Set α} (hg : Monotone g) : (𝓟 s).lift g = g s
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.lift_le`：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} {s : Set α} (hs : s in f) (hg : g s <= h) : f.lift g <= h
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift`：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} : h <= f.lift g ↔ forall s in f, h <= g s
-/
theorem lift_principal {s : Set α} (hg : Monotone g) : (𝓟 s).lift g = g s :=
  (lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 fun _t ht => hg ht)
/-
**Filter.monotone_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：monotone_lift [Preorder γ] {f : γ -> Filter α} {g : γ -> Set α -> Filter β
} (hf : Monotone f) (hg : Monotone g) : Monotone fun c => (f c).lift (g c)
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_mono`：lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁
 <= f₂.lift g₂
-/
theorem monotone_lift [Preorder γ] {f : γ → Filter α} {g : γ → Set α → Filter β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift (g c) := fun _ _ h => lift_mono (hf h) (hg h)
/-
**Filter.lift_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_neBot_iff (hm : Monotone g) : (NeBot (f.lift g)) ↔ forall s in f, NeB
ot (g s)
参数：hm : Monotone g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_neBot_iff (hm : Monotone g) : (NeBot (f.lift g)) ↔ ∀ s ∈ f, NeBot (g s) := by
  simp only [neBot_iff, Ne, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists, not_and]

@[simp]
/-
**Filter.lift_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_const {f : Filter α} {g : Filter β} : (f.lift fun _ => g) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `iInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
a : α} [Nonempty ι], ⨅ x, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem lift_const {f : Filter α} {g : Filter β} : (f.lift fun _ => g) = g :=
  iInf_subtype'.trans iInf_const

@[simp]
/-
**Filter.lift_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_inf {f : Filter α} {g h : Set α -> Filter β} : (f.lift fun x => g x ⊓
 h x) = f.lift g ⊓ f.lift h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_inf_eq`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f g : ι → α}, ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_inf {f : Filter α} {g h : Set α → Filter β} :
    (f.lift fun x => g x ⊓ h x) = f.lift g ⊓ f.lift h := by simp only [Filter.lift, iInf_inf_eq]

@[simp]
/-
**Filter.lift_principal2** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_principal2 {f : Filter α} : f.lift 𝓟 = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.mem_lift`：mem_lift {s : Set β} {t : Set α} (ht : t in f) (hs : s 
in g t) : s in f.lift g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem lift_principal2 {f : Filter α} : f.lift 𝓟 = f :=
  le_antisymm (fun s hs => mem_lift hs (mem_principal_self s))
    (le_iInf fun s => le_iInf fun hs => by simp only [hs, le_principal_iff])
/-
**Filter.lift_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_iInf_le {f : ι -> Filter α} {g : Set α -> Filter β} : (iInf f).lift g
 <= ⨅ i, (f i).lift g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Filter.lift_mono`：lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁
 <= f₂.lift g₂
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lift_iInf_le {f : ι → Filter α} {g : Set α → Filter β} :
    (iInf f).lift g ≤ ⨅ i, (f i).lift g :=
  le_iInf fun _ => lift_mono (iInf_le _ _) le_rfl
/-
**Filter.lift_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_iInf [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Filter β} (hg : f
orall s t, g (s inter t) = g s ⊓ g t) : (iInf f).lift g = ⨅ i, (f i).lift g
参数：hg : forall s t, g (s inter t) = g s ⊓ g t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.lift_iInf_le`：lift_iInf_le {f : ι -> Filter α} {g : Set α -> Filt
er β} : (iInf f).lift g <= ⨅ i, (f i).lift g
· 使用定理 `Filter.iInf_sets_induct`：iInf_sets_induct {f : ι -> Filter α} {s : Set α
} (hs : s in iInf f) {p : Set α -> Prop} (uni : p univ) (ins : forall {i s₁ s₂},
 s₁ in f i ->…
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `Monotone.of_map_inf`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   (∀ (x y : α), f (x ⊓ y) = f x ⊓ f 
y) → Mono…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem lift_iInf [Nonempty ι] {f : ι → Filter α} {g : Set α → Filter β}
    (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) : (iInf f).lift g = ⨅ i, (f i).lift g := by
  refine lift_iInf_le.antisymm fun s => ?_
  have H : ∀ t ∈ iInf f, ⨅ i, (f i).lift g ≤ g t := by
    intro t ht
    refine iInf_sets_induct ht ?_ fun hs ht => ?_
    · inhabit ι
      exact iInf₂_le_of_le default univ (iInf_le _ univ_mem)
    · rw [hg]
      exact le_inf (iInf₂_le_of_le _ _ <| iInf_le _ hs) ht
  simp only [mem_lift_sets (Monotone.of_map_inf hg), exists_imp, and_imp]
  exact fun t ht hs => H t ht hs
/-
**Filter.lift_iInf_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_iInf_of_directed [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Filte
r β} (hf : Directed (· >= ·) f) (hg : Monotone g) : (iInf f).lift g = ⨅ i, (f i)
.lift g
参数：hf : Directed (· >= ·) f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.lift_iInf_le`：lift_iInf_le {f : ι -> Filter α} {g : Set α -> Filt
er β} : (iInf f).lift g <= ⨅ i, (f i).lift g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Filter.mem_lift`：mem_lift {s : Set β} {t : Set α} (ht : t in f) (hs : s 
in g t) : s in f.lift g
-/
theorem lift_iInf_of_directed [Nonempty ι] {f : ι → Filter α} {g : Set α → Filter β}
    (hf : Directed (· ≥ ·) f) (hg : Monotone g) : (iInf f).lift g = ⨅ i, (f i).lift g :=
  lift_iInf_le.antisymm fun s => by
    simp only [mem_lift_sets hg, exists_imp, and_imp, mem_iInf_of_directed hf]
    exact fun t i ht hs => mem_iInf_of_mem i <| mem_lift ht hs
/-
**Filter.lift_iInf_of_map_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lift_iInf_of_map_univ {f : ι -> Filter α} {g : Set α -> Filter β} (hg : fo
rall s t, g (s inter t) = g s ⊓ g t) (hg' : g univ = ⊤) : (iInf f).lift g = ⨅ i,
 (f i).lift g
参数：hg : forall s t, g (s inter t) = g s ⊓ g t；hg' : g univ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
· 使用定理 `Filter.lift_top`：lift_top (g : Set α -> Filter β) : (⊤ : Filter α).lift 
g = g univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.lift_iInf`：lift_iInf [Nonempty ι] {f : ι -> Filter α} {g : Set α 
-> Filter β} (hg : forall s t, g (s inter t) = g s ⊓ g t) : (iInf f).lift g = ⨅ 
i, (f …
-/
theorem lift_iInf_of_map_univ {f : ι → Filter α} {g : Set α → Filter β}
    (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) (hg' : g univ = ⊤) :
    (iInf f).lift g = ⨅ i, (f i).lift g := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_empty, hg']
  · exact lift_iInf hg

end lift

section Lift'

variable {f f₁ f₂ : Filter α} {h h₁ h₂ : Set α → Set β}

@[simp]
/-
**Filter.lift'_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (h : Set α → Set β), ⊤.lift' h = Filter.pr
incipal (h Set.univ)
参数：h : Set α → Set β；h Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_top`：lift_top (g : Set α -> Filter β) : (⊤ : Filter α).lift 
g = g univ
-/
theorem lift'_top (h : Set α → Set β) : (⊤ : Filter α).lift' h = 𝓟 (h univ) :=
  lift_top _
/-
**Filter.mem_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
参数：ht : t in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mem_lift' {t : Set α} (ht : t ∈ f) : h t ∈ f.lift' h :=
  le_principal_iff.mp <| show f.lift' h ≤ 𝓟 (h t) from iInf_le_of_le t <| iInf_le_of_le ht <| le_rfl
/-
**Filter.tendsto_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_lift' {m : γ -> β} {l : Filter γ} : Tendsto m l (f.lift' h) ↔ fora
ll s in f, forallᶠ a in l, m a in h s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_lift' {m : γ → β} {l : Filter γ} :
    Tendsto m l (f.lift' h) ↔ ∀ s ∈ f, ∀ᶠ a in l, m a ∈ h s := by
  simp only [Filter.lift', tendsto_lift, tendsto_principal, comp]
/-
**Filter.HasBasis.lift'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.lift'_interior {l : Filter X} {p : ι -> Prop} {s : ι -> Se
t X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis p fun i => interior (s i
)
参数：h : l.HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_lift_iff`：∀ {α : Type u_1} {γ : Type u_3} {ι : Sort 
u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasBasis p s →     ∀ {β 
: ι → Type u_5} {p…
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.lift' {ι} {p : ι → Prop} {s} (hf : f.HasBasis p s) (hh : Monotone h) :
    (f.lift' h).HasBasis p (h ∘ s) :=
  ⟨fun t => (hf.mem_lift_iff (fun i => hasBasis_principal (h (s i)))
    (monotone_principal.comp hh)).trans <| by simp only [exists_const, true_and, comp]⟩
/-
**Filter.mem_lift'_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h : Set α → Set β},   Mono
tone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_lift_sets`：mem_lift_sets (hg : Monotone g) {s : Set β} : s in
 f.lift g ↔ exists t in f, s in g t
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem mem_lift'_sets (hh : Monotone h) {s : Set β} : s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ s :=
  mem_lift_sets <| monotone_principal.comp hh
/-
**Filter.eventually_lift'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h : Set α → Set β},   Mono
tone h → ∀ {p : β → Prop}, (∀ᶠ (y : β) in f.lift' h, p y) ↔ ∃ t ∈ f, ∀ y ∈ h t, 
p y
参数：∀ᶠ (y : β) in f.lift' h, p y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
-/
theorem eventually_lift'_iff (hh : Monotone h) {p : β → Prop} :
    (∀ᶠ y in f.lift' h, p y) ↔ ∃ t ∈ f, ∀ y ∈ h t, p y :=
  mem_lift'_sets hh
/-
**Filter.sInter_lift'_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h : Set α → Set β}, Monoto
ne h → ⋂₀ {s | s ∈ f.lift' h} = ⋂ s ∈ f, h s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.sInter_lift_sets`：sInter_lift_sets (hg : Monotone g) : ⋂₀ { s | s
 in f.lift g } = ⋂ s in f, ⋂₀ { t | t in g s }
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用引理 `Set.iInter₂_congr`：iInter₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋂ (i) (j), s i j = ⋂ (i) (j), t i j
· 使用定理 `csInf_Ici`：csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a : α} : sInf (Ici a) = a
-/
theorem sInter_lift'_sets (hh : Monotone h) : ⋂₀ { s | s ∈ f.lift' h } = ⋂ s ∈ f, h s :=
  (sInter_lift_sets (monotone_principal.comp hh)).trans <| iInter₂_congr fun _ _ => csInf_Ici
/-
**Filter.lift'_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Set α → Set β} {h : Fi
lter β} {s : Set α},   s ∈ f → Filter.principal (g s) ≤ h → f.lift' g ≤ h
参数：g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_le`：lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} {s : Set α} (hs : s in f) (hg : g s <= h) : f.lift g <= h
-/
theorem lift'_le {f : Filter α} {g : Set α → Set β} {h : Filter β} {s : Set α} (hs : s ∈ f)
    (hg : 𝓟 (g s) ≤ h) : f.lift' g ≤ h :=
  lift_le hs hg
/-
**Filter.lift'_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {h₁ h₂ : Set α → Set β}
,   f₁ ≤ f₂ → h₁ ≤ h₂ → f₁.lift' h₁ ≤ f₂.lift' h₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_mono`：lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁
 <= f₂.lift g₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
  lift_mono hf fun s => principal_mono.mpr <| hh s
/-
**Filter.lift'_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h₁ h₂ : Set α → Set β}, (∀
 s ∈ f, h₁ s ⊆ h₂ s) → f.lift' h₁ ≤ f.lift' h₂
参数：∀ s ∈ f, h₁ s ⊆ h₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem lift'_mono' (hh : ∀ s ∈ f, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
  iInf₂_mono fun s hs => principal_mono.mpr <| hh s hs
/-
**Filter.lift'_cong** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h₁ h₂ : Set α → Set β}, (∀
 s ∈ f, h₁ s = h₂ s) → f.lift' h₁ = f.lift' h₂
参数：∀ s ∈ f, h₁ s = h₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.lift'_mono'`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h₁ h
₂ : Set α → Set β}, (∀ s ∈ f, h₁ s ⊆ h₂ s) → f.lift' h₁ ≤ f.lift' h₂
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lift'_cong (hh : ∀ s ∈ f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
  le_antisymm (lift'_mono' fun s hs => le_of_eq <| hh s hs)
    (lift'_mono' fun s hs => le_of_eq <| (hh s hs).symm)
/-
**Filter.map_lift'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {h : Set α →
 Set β} {m : β → γ},   Monotone h → Filter.map m (f.lift' h) = f.lift' (Set.imag
e m ∘ h)
参数：f.lift' h；Set.image m ∘ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.map_lift_eq`：map_lift_eq {m : β -> γ} (hg : Monotone g) : map m (
f.lift g) = f.lift (map m ∘ g)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_lift'_eq {m : β → γ} (hh : Monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
  calc
    map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq <| monotone_principal.comp hh
    _ = f.lift' (image m ∘ h) := by simp only [comp_def, Filter.lift', map_principal]
/-
**Filter.lift'_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Set β →
 Set γ} {m : α → β},   (Filter.map m f).lift' g ≤ f.lift' (g ∘ Set.image m)
参数：Filter.map m f；g ∘ Set.image m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_map_le`：lift_map_le {g : Set β -> Filter γ} {m : α -> β} : (
map m f).lift g <= f.lift (g ∘ image m)
-/
theorem lift'_map_le {g : Set β → Set γ} {m : α → β} : (map m f).lift' g ≤ f.lift' (g ∘ image m) :=
  lift_map_le
/-
**Filter.map_lift'_eq2** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Set β →
 Set γ} {m : α → β},   Monotone g → (Filter.map m f).lift' g = f.lift' (g ∘ Set.
image m)
参数：Filter.map m f；g ∘ Set.image m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_lift_eq2`：map_lift_eq2 {g : Set β -> Filter γ} {m : α -> β} (
hg : Monotone g) : (map m f).lift g = f.lift (g ∘ image m)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem map_lift'_eq2 {g : Set β → Set γ} {m : α → β} (hg : Monotone g) :
    (map m f).lift' g = f.lift' (g ∘ image m) :=
  map_lift_eq2 <| monotone_principal.comp hg
/-
**Filter.comap_lift'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {h : Set α →
 Set β} {m : γ → β},   Filter.comap m (f.lift' h) = f.lift' (Set.preimage m ∘ h)
参数：f.lift' h；Set.preimage m ∘ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_lift_eq`：comap_lift_eq {m : γ -> β} : comap m (f.lift g) = 
f.lift (comap m ∘ g)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_lift'_eq {m : γ → β} : comap m (f.lift' h) = f.lift' (preimage m ∘ h) := by
  simp only [Filter.lift', comap_lift_eq, comp_def, comap_principal]
/-
**Filter.comap_lift'_eq2** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {m : β → α} 
{g : Set β → Set γ},   Monotone g → (Filter.comap m f).lift' g = f.lift' (g ∘ Se
t.preimage m)
参数：Filter.comap m f；g ∘ Set.preimage m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_lift_eq2`：comap_lift_eq2 {m : β -> α} {g : Set β -> Filter 
γ} (hg : Monotone g) : (comap m f).lift g = f.lift (g ∘ preimage m)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem comap_lift'_eq2 {m : β → α} {g : Set β → Set γ} (hg : Monotone g) :
    (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
  comap_lift_eq2 <| monotone_principal.comp hg
/-
**Filter.lift'_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set β} {s : Set α},   Monoton
e h → (Filter.principal s).lift' h = Filter.principal (h s)
参数：Filter.principal s；h s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_principal`：lift_principal {s : Set α} (hg : Monotone g) : (𝓟
 s).lift g = g s
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem lift'_principal {s : Set α} (hh : Monotone h) : (𝓟 s).lift' h = 𝓟 (h s) :=
  lift_principal <| monotone_principal.comp hh
/-
**Filter.lift'_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set β} {a : α}, Monotone h → 
(pure a).lift' h = Filter.principal (h {a})
参数：pure a；h {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.lift'_principal`：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set
 β} {s : Set α},   Monotone h → (Filter.principal s).lift' h = Filter.principal 
(h s)
-/
theorem lift'_pure {a : α} (hh : Monotone h) : (pure a : Filter α).lift' h = 𝓟 (h {a}) := by
  rw [← principal_singleton, lift'_principal hh]
/-
**Filter.lift'_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set β}, Monotone h → ⊥.lift' 
h = Filter.principal (h ∅)
参数：h ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `Filter.lift'_principal`：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set
 β} {s : Set α},   Monotone h → (Filter.principal s).lift' h = Filter.principal 
(h s)
-/
theorem lift'_bot (hh : Monotone h) : (⊥ : Filter α).lift' h = 𝓟 (h ∅) := by
  rw [← principal_empty, lift'_principal hh]
/-
**Filter.le_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_lift' {f : Filter α} {h : Set α -> Set β} {g : Filter β} : g <= f.lift'
 h ↔ forall s in f, h s in g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.le_lift`：le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filt
er β} : h <= f.lift g ↔ forall s in f, h <= g s
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem le_lift' {f : Filter α} {h : Set α → Set β} {g : Filter β} :
    g ≤ f.lift' h ↔ ∀ s ∈ f, h s ∈ g :=
  le_lift.trans <| forall₂_congr fun _ _ => le_principal_iff
/-
**Filter.principal_le_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_le_lift' {t : Set β} : 𝓟 t <= f.lift' h ↔ forall s in f, t subse
teq h s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_lift'`：le_lift' {f : Filter α} {h : Set α -> Set β} {g : Filte
r β} : g <= f.lift' h ↔ forall s in f, h s in g
-/
theorem principal_le_lift' {t : Set β} : 𝓟 t ≤ f.lift' h ↔ ∀ s ∈ f, t ⊆ h s :=
  le_lift'
/-
**Filter.monotone_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：monotone_lift' [Preorder γ] {f : γ -> Filter α} {g : γ -> Set α -> Set β} 
(hf : Monotone f) (hg : Monotone g) : Monotone fun c => (f c).lift' (g c)
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'_mono`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {h
₁ h₂ : Set α → Set β},   f₁ ≤ f₂ → h₁ ≤ h₂ → f₁.lift' h₁ ≤ f₂.lift' h₂
-/
theorem monotone_lift' [Preorder γ] {f : γ → Filter α} {g : γ → Set α → Set β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift' (g c) := fun _ _ h => lift'_mono (hf h) (hg h)
/-
**Filter.lift_lift'_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Set α →
 Set β} {h : Set β → Filter γ},   Monotone g → Monotone h → (f.lift' g).lift h =
 f.lift fun s => h (g s)
参数：f.lift' g；g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.lift_assoc`：lift_assoc {h : Set β -> Filter γ} (hg : Monotone g) 
: (f.lift g).lift h = f.lift fun s => (g s).lift h
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.lift_principal`：lift_principal {s : Set α} (hg : Monotone g) : (𝓟
 s).lift g = g s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_lift'_assoc {g : Set α → Set β} {h : Set β → Filter γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift h = f.lift fun s => h (g s) :=
  calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by simp only [lift_principal, hh]
/-
**Filter.lift'_lift'_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Set α →
 Set β} {h : Set β → Set γ},   Monotone g → Monotone h → (f.lift' g).lift' h = f
.lift' fun s => h (g s)
参数：f.lift' g；g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_lift'_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : Filter α} {g : Set α → Set β} {h : Set β → Filter γ},   Monotone g → Monoto
ne h → (f.lif…
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem lift'_lift'_assoc {g : Set α → Set β} {h : Set β → Set γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift' h = f.lift' fun s => h (g s) :=
  lift_lift'_assoc hg (monotone_principal.comp hh)
/-
**Filter.lift'_lift_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Set α →
 Filter β} {h : Set β → Set γ},   Monotone g → (f.lift g).lift' h = f.lift fun s
 => (g s).lift' h
参数：f.lift g；g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_assoc`：lift_assoc {h : Set β -> Filter γ} (hg : Monotone g) 
: (f.lift g).lift h = f.lift fun s => (g s).lift h
-/
theorem lift'_lift_assoc {g : Set α → Filter β} {h : Set β → Set γ} (hg : Monotone g) :
    (f.lift g).lift' h = f.lift fun s => (g s).lift' h :=
  lift_assoc hg
/-
**Filter.lift_lift'_same_le_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Set α → Set α → Set β}
,   (f.lift fun s => f.lift' (g s)) ≤ f.lift' fun s => g s s
参数：f.lift fun s => f.lift' (g s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_lift_same_le_lift`：lift_lift_same_le_lift {g : Set α -> Set 
α -> Filter β} : (f.lift fun s => f.lift (g s)) <= f.lift fun s => g s s
-/
theorem lift_lift'_same_le_lift' {g : Set α → Set α → Set β} :
    (f.lift fun s => f.lift' (g s)) ≤ f.lift' fun s => g s s :=
  lift_lift_same_le_lift
/-
**Filter.lift_lift'_same_eq_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Set α → Set α → Set β}
,   (∀ (s : Set α), Monotone fun t => g s t) →     (∀ (t : Set α), Monotone fun 
s => g s t) → (f.lift fun s => f.lift' (g s)) = f.lift' fun s => g s s
参数：∀ (s : Set α), Monotone fun t => g s t；∀ (t : Set α), Monotone fun s => g s t
；f.lift fun s => f.lift' (g s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_lift_same_eq_lift`：lift_lift_same_eq_lift {g : Set α -> Set 
α -> Filter β} (hg₁ : forall s, Monotone fun t => g s t) (hg₂ : forall t, Monoto
ne fun s => g s t) …
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem lift_lift'_same_eq_lift' {g : Set α → Set α → Set β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) :
    (f.lift fun s => f.lift' (g s)) = f.lift' fun s => g s s :=
  lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t =>
    monotone_principal.comp (hg₂ t)
/-
**Filter.lift'_inf_principal_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h : Set α → Set β} {s : Se
t β},   f.lift' h ⊓ Filter.principal s = f.lift' fun t => h t ∩ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift'_inf_principal_eq {h : Set α → Set β} {s : Set β} :
    f.lift' h ⊓ 𝓟 s = f.lift' fun t => h t ∩ s := by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, iInf_subtype', ← iInf_inf]
/-
**Filter.lift'_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h : Set α → Set β},   Mono
tone h → ((f.lift' h).NeBot ↔ ∀ s ∈ f, (h s).Nonempty)
参数：(f.lift' h).NeBot ↔ ∀ s ∈ f, (h s).Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.lift_neBot_iff`：lift_neBot_iff (hm : Monotone g) : (NeBot (f.lift
 g)) ↔ forall s in f, NeBot (g s)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift'_neBot_iff (hh : Monotone h) : NeBot (f.lift' h) ↔ ∀ s ∈ f, (h s).Nonempty :=
  calc
    NeBot (f.lift' h) ↔ ∀ s ∈ f, NeBot (𝓟 (h s)) := lift_neBot_iff (monotone_principal.comp hh)
    _ ↔ ∀ s ∈ f, (h s).Nonempty := by simp only [principal_neBot_iff]

@[simp]
/-
**Filter.lift'_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {f : Filter α}, f.lift' id = f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_principal2`：lift_principal2 {f : Filter α} : f.lift 𝓟 = f
-/
theorem lift'_id {f : Filter α} : f.lift' id = f :=
  lift_principal2
/-
**Filter.lift'_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [Nonempty ι] {f : ι → Filte
r α} {g : Set α → Set β},   (∀ (s t : Set α), g (s ∩ t) = g s ∩ g t) → (iInf f).
lift' g = ⨅ i, (f i).lift' g
参数：∀ (s t : Set α), g (s ∩ t) = g s ∩ g t；iInf f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_iInf`：lift_iInf [Nonempty ι] {f : ι -> Filter α} {g : Set α 
-> Filter β} (hg : forall s t, g (s inter t) = g s ⊓ g t) : (iInf f).lift g = ⨅ 
i, (f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift'_iInf [Nonempty ι] {f : ι → Filter α} {g : Set α → Set β}
    (hg : ∀ s t, g (s ∩ t) = g s ∩ g t) : (iInf f).lift' g = ⨅ i, (f i).lift' g :=
  lift_iInf fun s t => by simp only [inf_principal, comp, hg]
/-
**Filter.lift'_iInf_of_map_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {f : ι → Filter α} {g : Set
 α → Set β},   (∀ {s t : Set α}, g (s ∩ t) = g s ∩ g t) → g Set.univ = Set.univ 
→ (iInf f).lift' g = ⨅ i, (f i).lift' g
参数：∀ {s t : Set α}, g (s ∩ t) = g s ∩ g t；iInf f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_iInf_of_map_univ`：lift_iInf_of_map_univ {f : ι -> Filter α} 
{g : Set α -> Filter β} (hg : forall s t, g (s inter t) = g s ⊓ g t) (hg' : g un
iv = ⊤) : (iInf f)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem lift'_iInf_of_map_univ {f : ι → Filter α} {g : Set α → Set β}
    (hg : ∀ {s t}, g (s ∩ t) = g s ∩ g t) (hg' : g univ = univ) :
    (iInf f).lift' g = ⨅ i, (f i).lift' g :=
  lift_iInf_of_map_univ (fun s t => by simp only [inf_principal, comp, hg])
    (by rw [Function.comp_apply, hg', principal_univ])
/-
**Filter.lift'_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f g : Filter α) {s : Set α → Set β},   (∀
 (t₁ t₂ : Set α), s (t₁ ∩ t₂) = s t₁ ∩ s t₂) → (f ⊓ g).lift' s = f.lift' s ⊓ g.l
ift' s
参数：f g : Filter α；∀ (t₁ t₂ : Set α), s (t₁ ∩ t₂) = s t₁ ∩ s t₂；f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `Filter.lift'_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [Nonem
pty ι] {f : ι → Filter α} {g : Set α → Set β},   (∀ (s t : Set α), g (s ∩ t) = g
 s ∩ g …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
-/
theorem lift'_inf (f g : Filter α) {s : Set α → Set β} (hs : ∀ t₁ t₂, s (t₁ ∩ t₂) = s t₁ ∩ s t₂) :
    (f ⊓ g).lift' s = f.lift' s ⊓ g.lift' s := by
  rw [inf_eq_iInf, inf_eq_iInf, lift'_iInf hs]
  refine iInf_congr ?_
  rintro (_ | _) <;> rfl
/-
**Filter.lift'_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f g : Filter α) (s : Set α → Set β), (f ⊓
 g).lift' s ≤ f.lift' s ⊓ g.lift' s
参数：f g : Filter α；s : Set α → Set β；f ⊓ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.lift'_mono`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {h
₁ h₂ : Set α → Set β},   f₁ ≤ f₂ → h₁ ≤ h₂ → f₁.lift' h₁ ≤ f₂.lift' h₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem lift'_inf_le (f g : Filter α) (s : Set α → Set β) :
    (f ⊓ g).lift' s ≤ f.lift' s ⊓ g.lift' s :=
  le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)
/-
**Filter.comap_eq_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_eq_lift' {f : Filter β} {m : α -> β} : comap m f = f.lift' (preimage
 m)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `Set.monotone_preimage`：monotone_preimage {f : α -> β} : Monotone (preima
ge f)
-/
theorem comap_eq_lift' {f : Filter β} {m : α → β} : comap m f = f.lift' (preimage m) :=
  Filter.ext fun _ => (mem_lift'_sets monotone_preimage).symm

end Lift'

section Prod

variable {f : Filter α}

/-
**Filter.prod_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_def {f : Filter α} {g : Filter β} : f ×ˢ g = f.lift fun s => g.lift' 
fun t => s ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `iInf_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comple
teLattice α] {f : β × γ → α}, ⨅ x, f x = ⨅ i, ⨅ j, f (i, j)
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用定理 `iInf_comm`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Compl
eteLattice α] {f : ι → ι' → α},   ⨅ i, ⨅ j, f i j = ⨅ j, ⨅ i, f i j
-/
theorem prod_def {f : Filter α} {g : Filter β} :
    f ×ˢ g = f.lift fun s => g.lift' fun t => s ×ˢ t := by
  simpa only [Filter.lift', Filter.lift, (f.basis_sets.prod g.basis_sets).eq_biInf,
    iInf_prod, iInf_and] using! iInf_congr fun i => iInf_comm

alias mem_prod_same_iff := mem_prod_self_iff
/-
**Filter.prod_same_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_same_eq : f ×ˢ f = f.lift' fun t : Set α => t ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem prod_same_eq : f ×ˢ f = f.lift' fun t : Set α => t ×ˢ t :=
  f.basis_sets.prod_self.eq_biInf
/-
**Filter.tendsto_prod_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_prod_self_iff {f : α × α -> β} {x : Filter α} {y : Filter β} : Fil
ter.Tendsto f (x ×ˢ x) y ↔ forall W in y, exists U in x, forall x x' : α, x in U
 -> x' in U -> f (x, x') in W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_prod_self_iff {f : α × α → β} {x : Filter α} {y : Filter β} :
    Filter.Tendsto f (x ×ˢ x) y ↔ ∀ W ∈ y, ∃ U ∈ x, ∀ x x' : α, x ∈ U → x' ∈ U → f (x, x') ∈ W := by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff]

variable {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
/-
**Filter.prod_lift_lift** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ -> Filter β₁
} {g₂ : Set α₂ -> Filter β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) : f₁.lift g
₁ ×ˢ f₂.lift g₂ = f₁.lift fun s => f₂.lift fun t => g₁ s ×ˢ g₂ t
参数：hg₁ : Monotone g₁；hg₂ : Monotone g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_def`：prod_def {f : Filter α} {g : Filter β} : f ×ˢ g = f.lif
t fun s => g.lift' fun t => s ×ˢ t
· 使用定理 `Filter.lift_assoc`：lift_assoc {h : Set β -> Filter γ} (hg : Monotone g) 
: (f.lift g).lift h = f.lift fun s => (g s).lift h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Filter.lift_comm`：lift_comm {g : Filter β} {h : Set α -> Set β -> Filter
 γ} : (f.lift fun s => g.lift (h s)) = g.lift fun t => f.lift fun s => h s t
· 使用定理 `Filter.lift'_lift_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : Filter α} {g : Set α → Filter β} {h : Set β → Set γ},   Monotone g → (f.lif
t g).lift' h …
-/
theorem prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Filter β₁}
    {g₂ : Set α₂ → Filter β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift g₁ ×ˢ f₂.lift g₂ = f₁.lift fun s => f₂.lift fun t => g₁ s ×ˢ g₂ t := by
  simp only [prod_def, lift_assoc hg₁]
  apply congr_arg; funext x
  rw [lift_comm]
  apply congr_arg; funext y
  apply lift'_lift_assoc hg₂
/-
**Filter.prod_lift'_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α₁ : Type u_5} {α₂ : Type u_6} {β₁ : Type u_7} {β₂ : Type u_8} {f₁ : Fi
lter α₁} {f₂ : Filter α₂}   {g₁ : Set α₁ → Set β₁} {g₂ : Set α₂ → Set β₂},   Mon
otone g₁ → Monotone g₂ → f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift' 
fun t => g₁ s ×ˢ g₂ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.prod_lift_lift`：prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} 
{g₁ : Set α₁ -> Filter β₁} {g₂ : Set α₂ -> Filter β₂} (hg₁ : Monotone g₁) (hg₂ :
 Monotone g…
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_lift'_lift' {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Set β₁}
    {g₂ : Set α₂ → Set β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift' fun t => g₁ s ×ˢ g₂ t :=
  calc
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s) ×ˢ 𝓟 (g₂ t) :=
      prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
    _ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s ×ˢ g₂ t) := by
      { simp only [prod_principal_principal] }

end Prod

end Filter

