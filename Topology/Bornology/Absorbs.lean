/-
Copyright (c) 2020 Jean Lo, Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Topology.Bornology.Basic

/-!
# Absorption of sets

Let `M` act on `α`, let `A` and `B` be sets in `α`.
We say that `A` *absorbs* `B` if for sufficiently large `a : M`, we have `B ⊆ a • A`.
Formally, "for sufficiently large `a : M`" means "for all but a bounded set of `a`".

Traditionally, this definition is formulated
for the action of a (semi)normed ring on a module over that ring.

We formulate it in a more general settings for two reasons:

- this way we don't have to depend on metric spaces, normed rings etc;
- some proofs look nicer with this definition than with something like
  `∃ r : ℝ, ∀ a : R, r ≤ ‖a‖ → B ⊆ a • A`.

If `M` is a `GroupWithZero` (e.g., a division ring),
the sets absorbing a given set form a filter, see `Filter.absorbing`.

## Implementation notes

For now, all theorems assume that we deal with (a generalization of) a module over a division ring.
Some lemmas have multiplicative versions for `MulDistribMulAction`s.
They can be added later when someone needs them.

## Keywords

absorbs, absorbent
-/

@[expose] public section

assert_not_exists Real

open Set Bornology Filter
open scoped Pointwise

section Defs

variable (M : Type*) {α : Type*} [Bornology M] [SMul M α]

/-- A set `s` absorbs another set `t` if `t` is contained in all scalings of `s`
by all but a bounded set of elements. -/
/-
**Absorbs** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Absorbs (s t : Set α) : Prop
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` absorbs another set `t` if `t` is contained in all scalings of `s`
by all but a bounded set of elements.
-/
def Absorbs (s t : Set α) : Prop :=
  ∀ᶠ a in cobounded M, t ⊆ a • s

/-- A set is *absorbent* if it absorbs every singleton. -/
/-
**Absorbent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Absorbent (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is *absorbent* if it absorbs every singleton.
-/
def Absorbent (s : Set α) : Prop :=
  ∀ x, Absorbs M s {x}

end Defs

namespace Absorbs

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s s₁ s₂ t t₁ t₂ : Set α} {S T : Set (Set α)}

/-
**Absorbs.empty** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s : Set α}, Absorbs M s ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected lemma empty : Absorbs M s ∅ := by simp [Absorbs]
/-
**Absorbs.eventually** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s t : Set α},   Absorbs M s t → ∀ᶠ (a : M) in Bornology.cobounded M, t ⊆ a • s
参数：a : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma eventually (h : Absorbs M s t) : ∀ᶠ a in cobounded M, t ⊆ a • s := h
/-
**Absorbs.of_boundedSpace** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s t : Set α} [BoundedSpace M], Absorbs M s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.cobounded_eq_bot`：cobounded_eq_bot : cobounded α = ⊥
-/
@[simp] lemma of_boundedSpace [BoundedSpace M] : Absorbs M s t := by simp [Absorbs]
/-
**Absorbs.mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
形式化陈述：mono_left (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂) : Absorbs M s₂ t
参数：h : Absorbs M s₁ t；hs : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
-/
lemma mono_left (h : Absorbs M s₁ t) (hs : s₁ ⊆ s₂) : Absorbs M s₂ t :=
  h.mono fun _a ha ↦ ha.trans <| smul_set_mono hs
/-
**Absorbs.mono_right** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
形式化陈述：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁) : Absorbs M s t₂
参数：h : Absorbs M s t₁；ht : t₂ subseteq t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma mono_right (h : Absorbs M s t₁) (ht : t₂ ⊆ t₁) : Absorbs M s t₂ :=
  h.mono fun _ ↦ ht.trans
/-
**Absorbs.mono** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
形式化陈述：mono (h : Absorbs M s₁ t₁) (hs : s₁ subseteq s₂) (ht : t₂ subseteq t₁) : A
bsorbs M s₂ t₂
参数：h : Absorbs M s₁ t₁；hs : s₁ subseteq s₂；ht : t₂ subseteq t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.mono_right`：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁
) : Absorbs M s t₂
· 使用引理 `Absorbs.mono_left`：mono_left (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂) 
: Absorbs M s₂ t
-/
lemma mono (h : Absorbs M s₁ t₁) (hs : s₁ ⊆ s₂) (ht : t₂ ⊆ t₁) : Absorbs M s₂ t₂ :=
  (h.mono_left hs).mono_right ht

@[simp]
/-
**Absorbs._root_.absorbs_union** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.absorbs_union : Absorbs M s (t₁ ∪ t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂ := by
  simp [Absorbs]
/-
**Absorbs.union** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s t₁ t₂ : Set α},   Absorbs M s t₁ → Absorbs M s t₂ → Absorbs M s (t₁ ∪ t₂)
参数：t₁ ∪ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `absorbs_union`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [ins
t_1 : SMul M α] {s t₁ t₂ : Set α},   Absorbs M s (t₁ ∪ t₂) ↔ Absorbs M s t₁ ∧ Ab
sor…
-/
protected lemma union (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂) : Absorbs M s (t₁ ∪ t₂) :=
  absorbs_union.2 ⟨h₁, h₂⟩
/-
**Absorbs._root_.Set.Finite.absorbs_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.absorbs_sUnion {T : Set (Set α)} (hT : T.Finite) :
    Absorbs M s (⋃₀ T) ↔ ∀ t ∈ T, Absorbs M s t := by
  simp [Absorbs, hT]
/-
**Absorbs.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s : Set α} {T : Set (Set α)},   T.Finite → (∀ t ∈ T, Absorbs M s t) → Absorbs M 
s (⋃₀ T)
参数：Set α；∀ t ∈ T, Absorbs M s t；⋃₀ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.absorbs_sUnion`：∀ {M : Type u_1} {α : Type u_2} [inst : Borno
logy M] [inst_1 : SMul M α] {s : Set α} {T : Set (Set α)},   T.Finite → (Absorbs
 M s (⋃₀ T) ↔ ∀…
-/
protected lemma sUnion (hT : T.Finite) (hs : ∀ t ∈ T, Absorbs M s t) :
    Absorbs M s (⋃₀ T) :=
  hT.absorbs_sUnion.2 hs

@[simp]
/-
**Absorbs._root_.absorbs_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.absorbs_iUnion {ι : Sort*} [Finite ι] {t : ι → Set α} :
    Absorbs M s (⋃ i, t i) ↔ ∀ i, Absorbs M s (t i) :=
  (finite_range t).absorbs_sUnion.trans forall_mem_range

protected alias ⟨_, iUnion⟩ := absorbs_iUnion
/-
**Absorbs._root_.Set.Finite.absorbs_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.absorbs_biUnion {ι : Type*} {t : ι → Set α} {I : Set ι} (hI : I.Finite) :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) := by
  simp [Absorbs, hI]

protected alias ⟨_, biUnion⟩ := Set.Finite.absorbs_biUnion

@[simp]
/-
**Absorbs._root_.absorbs_biUnion_finset** 是 Mathlib 中的一个引理，位于命名空间 `Absorbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.absorbs_biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι} :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) :=
  I.finite_toSet.absorbs_biUnion

protected alias ⟨_, biUnion_finset⟩ := absorbs_biUnion_finset

end SMul

section AddZero

variable {M E : Type*} [Bornology M] {s₁ s₂ t₁ t₂ : Set E}

/-
**Absorbs.add** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {E : Type u_2} [inst : Bornology M] {s₁ s₂ t₁ t₂ : Set E}
 [inst_1 : AddZeroClass E]   [inst_2 : DistribSMul M E], Absorbs M s₁ t₁ → Absor
bs M s₂ t₂ → Absorbs M (s₁ + s₂) (t₁ + t₂)
参数：s₁ + s₂；t₁ + t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Absorbs.eventually`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M]
 [inst_1 : SMul M α] {s t : Set α},   Absorbs M s t → ∀ᶠ (a : M) in Bornology.co
bounded …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
-/
protected lemma add [AddZeroClass E] [DistribSMul M E]
    (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) : Absorbs M (s₁ + s₂) (t₁ + t₂) :=
  h₂.mp <| h₁.eventually.mono fun x hx₁ hx₂ ↦ by rw [smul_add]; exact add_subset_add hx₁ hx₂
/-
**Absorbs.zero** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {E : Type u_2} [inst : Bornology M] [inst_1 : Zero E] [in
st_2 : SMulZeroClass M E] {s : Set E},   0 ∈ s → Absorbs M s 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.zero_subset`：∀ {α : Type u_2} [inst : Zero α] {s : Set α}, 0 ⊆ s ↔ 0
 ∈ s
· 使用引理 `Set.zero_mem_smul_set`：zero_mem_smul_set (h : (0 : β) in t) : (0 : β) in
 a • t
-/
protected lemma zero [Zero E] [SMulZeroClass M E] {s : Set E} (hs : 0 ∈ s) : Absorbs M s 0 :=
  Eventually.of_forall fun _ ↦ zero_subset.2 <| zero_mem_smul_set hs

end AddZero

end Absorbs

section GroupWithZero

variable {G₀ α : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]
  {s t u : Set α} {S : Set (Set α)}

@[simp]
/-
**Absorbs.univ** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {G₀ : Type u_1} {α : Type u_2} [inst : GroupWithZero G₀] [inst_1 : Borno
logy G₀] [inst_2 : MulAction G₀ α]   {s : Set α}, Absorbs G₀ Set.univ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `Bornology.eventually_ne_cobounded`：eventually_ne_cobounded (a : α) : for
allᶠ x in cobounded α, x != a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.smul_set_univ₀`：smul_set_univ₀ (ha : a != 0) : a • (univ : Set β) = 
univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
protected lemma Absorbs.univ : Absorbs G₀ univ s :=
  (eventually_ne_cobounded 0).mono fun a ha ↦ by rw [smul_set_univ₀ ha]; apply subset_univ
/-
**absorbs_iff_eventually_cobounded_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbs_iff_eventually_cobounded_mapsTo : Absorbs G₀ s t ↔ forallᶠ c in co
bounded G₀, MapsTo (c⁻¹ • ·) t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `Bornology.eventually_ne_cobounded`：eventually_ne_cobounded (a : α) : for
allᶠ x in cobounded α, x != a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.preimage_smul_inv₀`：preimage_smul_inv₀ (ha : a != 0) (t : Set β) : (
fun x => a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma absorbs_iff_eventually_cobounded_mapsTo :
    Absorbs G₀ s t ↔ ∀ᶠ c in cobounded G₀, MapsTo (c⁻¹ • ·) t s :=
  eventually_congr <| (eventually_ne_cobounded 0).mono fun c hc ↦ by
    rw [← preimage_smul_inv₀ hc]; rfl

alias ⟨eventually_cobounded_mapsTo, _⟩ := absorbs_iff_eventually_cobounded_mapsTo

@[simp]
/-
**absorbs_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbs_inter : Absorbs G₀ (s inter t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma absorbs_inter : Absorbs G₀ (s ∩ t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u := by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_inter, eventually_and]
/-
**Absorbs.inter** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {G₀ : Type u_1} {α : Type u_2} [inst : GroupWithZero G₀] [inst_1 : Borno
logy G₀] [inst_2 : MulAction G₀ α]   {s t u : Set α}, Absorbs G₀ s u → Absorbs G
₀ t u → Absorbs G₀ (s ∩ t) u
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `absorbs_inter`：absorbs_inter : Absorbs G₀ (s inter t) u ↔ Absorbs G₀ s u
 ∧ Absorbs G₀ t u
-/
protected lemma Absorbs.inter (hs : Absorbs G₀ s u) (ht : Absorbs G₀ t u) : Absorbs G₀ (s ∩ t) u :=
  absorbs_inter.2 ⟨hs, ht⟩

variable (G₀ u) in
/-- The filter of sets that absorb `u`. -/
/-
**Filter.absorbing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.absorbing : Filter α where sets
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbs.univ`：∀ {G₀ : Type u_1} {α : Type u_2} [inst : GroupWithZero G₀]
 [inst_1 : Bornology G₀] [inst_2 : MulAction G₀ α]   {s : Set α}, Absorbs G₀ Set
.u…
· 使用定理 `Absorbs.inter`：∀ {G₀ : Type u_1} {α : Type u_2} [inst : GroupWithZero G₀
] [inst_1 : Bornology G₀] [inst_2 : MulAction G₀ α]   {s t u : Set α}, Absorbs G
₀ s…

--- 原说明 ---
The filter of sets that absorb `u`.
-/
def Filter.absorbing : Filter α where
  sets := {s | Absorbs G₀ s u}
  univ_sets := .univ
  sets_of_superset h := h.mono_left
  inter_sets := .inter

@[simp]
/-
**Filter.mem_absorbing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.mem_absorbing : s in absorbing G₀ u ↔ Absorbs G₀ s u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Filter.mem_absorbing : s ∈ absorbing G₀ u ↔ Absorbs G₀ s u := .rfl
/-
**Set.Finite.absorbs_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.absorbs_sInter (hS : S.Finite) : Absorbs G₀ (⋂₀ S) t ↔ forall s
 in S, Absorbs G₀ s t
参数：hS : S.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.sInter_mem`：sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s
 in f ↔ forall U in s, U in f
-/
lemma Set.Finite.absorbs_sInter (hS : S.Finite) :
    Absorbs G₀ (⋂₀ S) t ↔ ∀ s ∈ S, Absorbs G₀ s t :=
  sInter_mem (f := absorbing G₀ t) hS

protected alias ⟨_, Absorbs.sInter⟩ := Set.Finite.absorbs_sInter

@[simp]
/-
**absorbs_iInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbs_iInter {ι : Sort*} [Finite ι] {s : ι -> Set α} : Absorbs G₀ (⋂ i, 
s i) t ↔ forall i, Absorbs G₀ (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
-/
lemma absorbs_iInter {ι : Sort*} [Finite ι] {s : ι → Set α} :
    Absorbs G₀ (⋂ i, s i) t ↔ ∀ i, Absorbs G₀ (s i) t :=
  iInter_mem (f := absorbing G₀ t)

protected alias ⟨_, Absorbs.iInter⟩ := absorbs_iInter
/-
**Set.Finite.absorbs_biInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.absorbs_biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι 
-> Set α} : Absorbs G₀ (⋂ i in I, s i) t ↔ forall i in I, Absorbs G₀ (s i) t
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
-/
lemma Set.Finite.absorbs_biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α} :
    Absorbs G₀ (⋂ i ∈ I, s i) t ↔ ∀ i ∈ I, Absorbs G₀ (s i) t :=
  biInter_mem (f := absorbing G₀ t) hI

protected alias ⟨_, Absorbs.biInter⟩ := Set.Finite.absorbs_biInter

@[simp]
/-
**absorbs_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbs_zero_iff [NeBot (cobounded G₀)] {E : Type*} [AddMonoid E] [Distrib
MulAction G₀ E] {s : Set E} : Absorbs G₀ s 0 ↔ 0 in s
参数：cobounded G₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma absorbs_zero_iff [NeBot (cobounded G₀)]
    {E : Type*} [AddMonoid E] [DistribMulAction G₀ E] {s : Set E} :
    Absorbs G₀ s 0 ↔ 0 ∈ s := by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, ← singleton_zero,
    mapsTo_singleton, smul_zero, eventually_const]

end GroupWithZero

section AddGroup

variable {M E : Type*} [Monoid M] [AddGroup E] [DistribMulAction M E] [Bornology M]

@[simp]
/-
**absorbs_neg_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbs_neg_neg {s t : Set E} : Absorbs M (-s) (-t) ↔ Absorbs M s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.smul_set_neg`：smul_set_neg : a • -t = -(a • t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma absorbs_neg_neg {s t : Set E} : Absorbs M (-s) (-t) ↔ Absorbs M s t := by simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg
/-
**Absorbs.sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Absorbs.sub {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s
₂ t₂) : Absorbs M (s₁ - s₂) (t₁ - t₂)
参数：h₁ : Absorbs M s₁ t₁；h₂ : Absorbs M s₂ t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Absorbs.add`：∀ {M : Type u_1} {E : Type u_2} [inst : Bornology M] {s₁ s₂
 t₁ t₂ : Set E} [inst_1 : AddZeroClass E]   [inst_2 : DistribSMul M E], Absorbs 
M…
· 使用定理 `Absorbs.neg_neg`：∀ {M : Type u_1} {E : Type u_2} [inst : Monoid M] [inst
_1 : AddGroup E] [inst_2 : DistribMulAction M E]   [inst_3 : Bornology M] {s t :
 Set …
-/
lemma Absorbs.sub {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
    Absorbs M (s₁ - s₂) (t₁ - t₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg

end AddGroup

namespace Absorbent

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s t : Set α}

/-
**Absorbent.mono** 是 Mathlib 中的一个定理，位于命名空间 `Absorbent`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.mono_left`：mono_left (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂) 
: Absorbs M s₂ t
-/
protected theorem mono (ht : Absorbent M s) (hsub : s ⊆ t) : Absorbent M t := fun x ↦
  (ht x).mono_left hsub
/-
**Absorbent._root_.absorbent_iff_forall_absorbs_singleton** 是 Mathlib 中的一个定理，位于命
名空间 `Absorbent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.absorbent_iff_forall_absorbs_singleton : Absorbent M s ↔ ∀ x, Absorbs M s {x} := .rfl
/-
**Absorbent.absorbs** 是 Mathlib 中的一个定理，位于命名空间 `Absorbent`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [inst_1 : SMul M α] {
s : Set α},   Absorbent M s → ∀ {x : α}, Absorbs M s {x}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem absorbs (hs : Absorbent M s) {x : α} : Absorbs M s {x} := hs x
/-
**Absorbent.absorbs_finite** 是 Mathlib 中的一个定理，位于命名空间 `Absorbent`。
形式化陈述：absorbs_finite (hs : Absorbent M s) (ht : t.Finite) : Absorbs M s t
参数：hs : Absorbent M s；ht : t.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Absorbs.biUnion`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [i
nst_1 : SMul M α] {s : Set α} {ι : Type u_3} {t : ι → Set α}   {I : Set ι}, I.Fi
nite …
· 使用定理 `Absorbent.absorbs`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] 
[inst_1 : SMul M α] {s : Set α},   Absorbent M s → ∀ {x : α}, Absorbs M s {x}
-/
theorem absorbs_finite (hs : Absorbent M s) (ht : t.Finite) : Absorbs M s t := by
  rw [← Set.biUnion_of_singleton t]
  exact .biUnion ht fun _ _ => hs.absorbs

end SMul

/-
**Absorbent.vadd_absorbs** 是 Mathlib 中的一个定理，位于命名空间 `Absorbent`。
形式化陈述：vadd_absorbs {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E
] {s₁ s₂ t : Set E} {x : E} (h₁ : Absorbent M s₁) (h₂ : Absorbs M s₂ t) : Absorb
s M (s₁ + s₂) (x +ᵥ t)
参数：h₁ : Absorbent M s₁；h₂ : Absorbs M s₂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_vadd`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {t
 : Set β} {a : α}, {a} +ᵥ t = a +ᵥ t
· 使用定理 `Absorbs.add`：∀ {M : Type u_1} {E : Type u_2} [inst : Bornology M] {s₁ s₂
 t₁ t₂ : Set E} [inst_1 : AddZeroClass E]   [inst_2 : DistribSMul M E], Absorbs 
M…
-/
theorem vadd_absorbs {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E]
    {s₁ s₂ t : Set E} {x : E} (h₁ : Absorbent M s₁) (h₂ : Absorbs M s₂ t) :
    Absorbs M (s₁ + s₂) (x +ᵥ t) := by
  rw [← singleton_vadd]; exact (h₁ x).add h₂

end Absorbent

section GroupWithZero

variable {G₀ α E : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]

/-
**absorbent_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbent_univ : Absorbent G₀ (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbs.univ`：∀ {G₀ : Type u_1} {α : Type u_2} [inst : GroupWithZero G₀]
 [inst_1 : Bornology G₀] [inst_2 : MulAction G₀ α]   {s : Set α}, Absorbs G₀ Set
.u…
-/
lemma absorbent_univ : Absorbent G₀ (univ : Set α) := fun _ ↦ .univ
/-
**absorbent_iff_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbent_iff_inv_smul {s : Set α} : Absorbent G₀ s ↔ forall x, forallᶠ c 
in cobounded G₀, c⁻¹ • x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
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
lemma absorbent_iff_inv_smul {s : Set α} :
    Absorbent G₀ s ↔ ∀ x, ∀ᶠ c in cobounded G₀, c⁻¹ • x ∈ s :=
  forall_congr' fun x ↦ by simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_singleton]
/-
**Absorbent.zero_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Absorbent.zero_mem [NeBot (cobounded G₀)] [AddMonoid E] [DistribMulAction 
G₀ E] {s : Set E} (hs : Absorbent G₀ s) : (0 : E) in s
参数：cobounded G₀；hs : Absorbent G₀ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `absorbs_zero_iff`：absorbs_zero_iff [NeBot (cobounded G₀)] {E : Type*} [A
ddMonoid E] [DistribMulAction G₀ E] {s : Set E} : Absorbs G₀ s 0 ↔ 0 in s
-/
lemma Absorbent.zero_mem [NeBot (cobounded G₀)] [AddMonoid E] [DistribMulAction G₀ E]
    {s : Set E} (hs : Absorbent G₀ s) : (0 : E) ∈ s :=
  absorbs_zero_iff.1 (hs 0)

end GroupWithZero

/-
**Absorbs.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 `Absorbs`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {α : Type u_3} [inst : Monoid N] [inst_1 :
 SMul M N] [inst_2 : SMul M α]   [inst_3 : MulAction N α] [IsScalarTower M N α] 
[inst_5 : Bornology M] [inst_6 : Bornology N] {s t : Set α},   Absorbs N s t → F
ilter.Tendsto (fun x => x • 1) (Bornology.cobounded M) (Bornology.cobounded N) →
 Absorbs M s t
参数：fun x => x • 1；Bornology.cobounded M；Bornology.cobounded N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
-/
protected theorem Absorbs.restrict_scalars
    {M N α : Type*} [Monoid N] [SMul M N] [SMul M α] [MulAction N α]
    [IsScalarTower M N α] [Bornology M] [Bornology N] {s t : Set α} (h : Absorbs N s t)
    (hbdd : Tendsto (· • 1 : M → N) (cobounded M) (cobounded N)) :
    Absorbs M s t :=
  (hbdd.eventually h).mono <| fun x hx ↦ by rwa [smul_one_smul N x s] at hx
