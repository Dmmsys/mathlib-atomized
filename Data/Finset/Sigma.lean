/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Sigma
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Finite sets in a sigma type

This file defines a few `Finset` constructions on `Σ i, α i`.

## Main declarations

* `Finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
* `Finset.sigmaLift`: Lifts maps `α i → β i → Finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → Finset (Σ i, γ i)`.

## TODO

`Finset.sigmaLift` can be generalized to any alternative functor. But to make the generalization
worth it, we must first refactor the functor library so that the `alternative` instance for `Finset`
is computable and universe-polymorphic.
-/

@[expose] public section


open Function Multiset

variable {ι : Type*}

namespace Finset

section Sigma

variable {α : ι → Type*} {β : Type*} (s s₁ s₂ : Finset ι) (t t₁ t₂ : ∀ i, Finset (α i))

/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
/-
**Finset.sigma** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → Finset ι → ((i : ι) → Finset (α i)) 
→ Finset ((i : ι) × α i)
参数：(i : ι) → Finset (α i)；(i : ι) × α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈
 t i`.
-/
protected def sigma : Finset (Σ i, α i) :=
  ⟨_, s.nodup.sigma fun i => (t i).nodup⟩

variable {s s₁ s₂ t t₁ t₂}

@[simp, grind =]
/-
**Finset.mem_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sigma {a : Σ i, α i} : a in s.sigma t ↔ a.1 in s ∧ a.2 in t a.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_sigma`：∀ {α : Type u_1} {σ : α → Type u_4} {s : Multiset α}
 {t : (a : α) → Multiset (σ a)} {p : (a : α) × σ a},   p ∈ s.sigma t ↔ p.fst ∈ s
 ∧ p.snd…
-/
theorem mem_sigma {a : Σ i, α i} : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 :=
  Multiset.mem_sigma

@[simp, norm_cast]
/-
**Finset.coe_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_sigma (s : Finset ι) (t : forall i, Finset (α i)) : (s.sigma t : Set (
Σ i, α i)) = (s : Set ι).sigma fun i => (t i : Set (α i))
参数：s : Finset ι；t : forall i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_sigma`：mem_sigma {a : Σ i, α i} : a in s.sigma t ↔ a.1 in s ∧
 a.2 in t a.1
-/
theorem coe_sigma (s : Finset ι) (t : ∀ i, Finset (α i)) :
    (s.sigma t : Set (Σ i, α i)) = (s : Set ι).sigma fun i ↦ (t i : Set (α i)) :=
  Set.ext fun _ => mem_sigma

@[simp]
/-
**Finset.sigma_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_nonempty : (s.sigma t).Nonempty ↔ exists i in s, (t i).Nonempty
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sigma_nonempty : (s.sigma t).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty := by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.sigma_nonempty_of_exists_nonempty⟩ := sigma_nonempty

@[simp]
/-
**Finset.sigma_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_eq_empty : s.sigma t = ∅ ↔ forall i in s, t i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sigma_nonempty`：sigma_nonempty : (s.sigma t).Nonempty ↔ exists i 
in s, (t i).Nonempty
-/
theorem sigma_eq_empty : s.sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ := by
  contrapose!; exact sigma_nonempty

@[gcongr, mono]
/-
**Finset.sigma_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_mono (hs : s₁ subseteq s₂) (ht : forall i, t₁ i subseteq t₂ i) : s₁.
sigma t₁ subseteq s₂.sigma t₂
参数：hs : s₁ subseteq s₂；ht : forall i, t₁ i subseteq t₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sigma`：mem_sigma {a : Σ i, α i} : a in s.sigma t ↔ a.1 in s ∧
 a.2 in t a.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
  fun ⟨i, _⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩
/-
**Finset.pairwiseDisjoint_map_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_map_sigmaMk : (s : Set ι).PairwiseDisjoint fun i => (t i)
.map (Embedding.sigmaMk i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sigmaMk_apply`：∀ {α : Type u_1} {β : α → Type u_3} (a
 : α) (snd : β a), (Function.Embedding.sigmaMk a) snd = ⟨a, snd⟩
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pairwiseDisjoint_map_sigmaMk :
    (s : Set ι).PairwiseDisjoint fun i => (t i).map (Embedding.sigmaMk i) := by
  intro i _ j _ hij
  rw [Function.onFun, disjoint_left]
  simp_rw [mem_map, Function.Embedding.sigmaMk_apply]
  rintro _ ⟨y, _, rfl⟩ ⟨z, _, hz'⟩
  exact hij (congr_arg Sigma.fst hz'.symm)

@[simp]
/-
**Finset.disjiUnion_map_sigma_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_map_sigma_mk : s.disjiUnion (fun i => (t i).map (Embedding.sigm
aMk i)) pairwiseDisjoint_map_sigmaMk = s.sigma t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pairwiseDisjoint_map_sigmaMk`：pairwiseDisjoint_map_sigmaMk : (s :
 Set ι).PairwiseDisjoint fun i => (t i).map (Embedding.sigmaMk i)
-/
theorem disjiUnion_map_sigma_mk :
    s.disjiUnion (fun i => (t i).map (Embedding.sigmaMk i)) pairwiseDisjoint_map_sigmaMk =
      s.sigma t :=
  rfl
/-
**Finset.sigma_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_eq_biUnion [DecidableEq (Σ i, α i)] (s : Finset ι) (t : forall i, Fi
nset (α i)) : s.sigma t = s.biUnion fun i => (t i).map Embedding.sigmaMk i
参数：Σ i, α i；s : Finset ι；t : forall i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sigmaMk_apply`：∀ {α : Type u_1} {β : α → Type u_3} (a
 : α) (snd : β a), (Function.Embedding.sigmaMk a) snd = ⟨a, snd⟩
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sigma_eq_biUnion [DecidableEq (Σ i, α i)] (s : Finset ι) (t : ∀ i, Finset (α i)) :
    s.sigma t = s.biUnion fun i => (t i).map <| Embedding.sigmaMk i := by
  ext ⟨x, y⟩
  simp [and_left_comm]
/-
**Finset.filter_sigma** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_sigma (s : Finset ι) (t : forall i, Finset (α i)) (p : (i : ι) × α 
i -> Prop) [DecidablePred p] : (s.sigma t).filter p = s.sigma fun i => (t i).fil
ter fun x => p ⟨i, x⟩
参数：s : Finset ι；t : forall i, Finset (α i)；p : (i : ι) × α i -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma filter_sigma (s : Finset ι) (t : ∀ i, Finset (α i)) (p : (i : ι) × α i → Prop)
    [DecidablePred p] : (s.sigma t).filter p = s.sigma fun i ↦ (t i).filter fun x => p ⟨i, x⟩ := by
  ext ⟨i, a⟩
  simp [Finset.mem_filter, Finset.mem_sigma, and_assoc]
/-
**Finset.filter_sigma'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_sigma' (s : Finset ι) (t : forall i, Finset (α i)) (p : (i : ι) -> 
α i -> Prop) [forall i, DecidablePred (p i)] : (s.sigma t).filter (fun x => p x.
fst x.snd) = s.sigma fun i => (t i).filter (p i)
参数：s : Finset ι；t : forall i, Finset (α i)；p : (i : ι) -> α i -> Prop；p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.filter_sigma`：filter_sigma (s : Finset ι) (t : forall i, Finset (
α i)) (p : (i : ι) × α i -> Prop) [DecidablePred p] : (s.sigma t).filter p = s.s
igma fun …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_sigma' (s : Finset ι) (t : ∀ i, Finset (α i)) (p : (i : ι) → α i → Prop)
    [∀ i, DecidablePred (p i)] :
    (s.sigma t).filter (fun x ↦ p x.fst x.snd) = s.sigma fun i ↦ (t i).filter (p i)  := by
  simp [filter_sigma]

variable (s t) (f : (Σ i, α i) → β)
/-
**Finset.sup_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_sigma [SemilatticeSup β] [OrderBot β] : (s.sigma t).sup f = s.sup fun 
i => (t i).sup fun b => f ⟨i, b⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sigma`：mem_sigma {a : Σ i, α i} : a in s.sigma t ↔ a.1 in s ∧
 a.2 in t a.1
-/
theorem sup_sigma [SemilatticeSup β] [OrderBot β] :
    (s.sigma t).sup f = s.sup fun i => (t i).sup fun b => f ⟨i, b⟩ := by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_sigma, and_imp, Sigma.forall]
  exact
    ⟨fun i a hi ha => (le_sup hi).trans' <| le_sup (f := fun a => f ⟨i, a⟩) ha, fun i hi a ha =>
      le_sup <| mem_sigma.2 ⟨hi, ha⟩⟩
/-
**Finset.inf_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_sigma [SemilatticeInf β] [OrderTop β] : (s.sigma t).inf f = s.inf fun 
i => (t i).inf fun b => f ⟨i, b⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_sigma`：sup_sigma [SemilatticeSup β] [OrderBot β] : (s.sigma t
).sup f = s.sup fun i => (t i).sup fun b => f ⟨i, b⟩
-/
theorem inf_sigma [SemilatticeInf β] [OrderTop β] :
    (s.sigma t).inf f = s.inf fun i => (t i).inf fun b => f ⟨i, b⟩ :=
  @sup_sigma _ _ βᵒᵈ _ _ _ _ _
/-
**Finset._root_.biSup_finsetSigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biSup_finsetSigma [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → β) : ⨆ ij ∈ s.sigma t, f ij = ⨆ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ := by
  simp_rw [← Finset.iSup_coe, Finset.coe_sigma, biSup_sigma]
/-
**Finset._root_.biSup_finsetSigma'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biSup_finsetSigma' [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) : ⨆ (i ∈ s) (j ∈ t i), f i j = ⨆ ij ∈ s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biSup_finsetSigma _ _ _)
/-
**Finset._root_.biInf_finsetSigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biInf_finsetSigma [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → β) : ⨅ ij ∈ s.sigma t, f ij = ⨅ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ :=
  biSup_finsetSigma (β := βᵒᵈ) _ _ _
/-
**Finset._root_.biInf_finsetSigma'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biInf_finsetSigma' [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) : ⨅ (i ∈ s) (j ∈ t i), f i j = ⨅ ij ∈ s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biInf_finsetSigma _ _ _)
/-
**Finset._root_.Set.biUnion_finsetSigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.biUnion_finsetSigma (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → Set β) : ⋃ ij ∈ s.sigma t, f ij = ⋃ i ∈ s, ⋃ j ∈ t i, f ⟨i, j⟩ :=
  biSup_finsetSigma _ _ _
/-
**Finset._root_.Set.biUnion_finsetSigma'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.biUnion_finsetSigma' (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → Set β) : ⋃ i ∈ s, ⋃ j ∈ t i, f i j = ⋃ ij ∈ s.sigma t, f ij.fst ij.snd :=
  biSup_finsetSigma' _ _ _
/-
**Finset._root_.Set.biInter_finsetSigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.biInter_finsetSigma (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → Set β) : ⋂ ij ∈ s.sigma t, f ij = ⋂ i ∈ s, ⋂ j ∈ t i, f ⟨i, j⟩ :=
  biInf_finsetSigma _ _ _
/-
**Finset._root_.Set.biInter_finsetSigma'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.biInter_finsetSigma' (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → Set β) : ⋂ i ∈ s, ⋂ j ∈ t i, f i j = ⋂ ij ∈ s.sigma t, f ij.1 ij.2 :=
  biInf_finsetSigma' _ _ _

end Sigma

section SigmaLift

variable {α β γ : ι → Type*} [DecidableEq ι]

/-- Lifts maps `α i → β i → Finset (γ i)` to a map `Σ i, α i → Σ i, β i → Finset (Σ i, γ i)`. -/
/-
**Finset.sigmaLift** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : 
Sigma β) : Finset (Sigma γ)
参数：f : forall ⦃i⦄, α i -> β i -> Finset (γ i)；a : Sigma α；b : Sigma β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts maps `α i → β i → Finset (γ i)` to a map `Σ i, α i → Σ i, β i → Finset (Σ 
i, γ i)`.
-/
def sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β) :
    Finset (Sigma γ) :=
  dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅
/-
**Finset.mem_sigmaLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (
b : Sigma β) (x : Sigma γ) : x in sigmaLift f a b ↔ exists (ha : a.1 = x.1) (hb 
: b.1 = x.1), x.2 in f (ha ▸ a.2) (hb ▸ b.2)
参数：f : forall ⦃i⦄, α i -> β i -> Finset (γ i)；a : Sigma α；b : Sigma β；x : Sigma 
γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.sigmaMk_apply`：∀ {α : Type u_1} {β : α → Type u_3} (a
 : α) (snd : β a), (Function.Embedding.sigmaMk a) snd = ⟨a, snd⟩
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sigmaLift.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} {β : ι → Type
 u_3} {γ : ι → Type u_4} [inst : DecidableEq ι]   (f : ⦃i : ι⦄ → α i → β i → Fin
set (γ i)) …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem mem_sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β)
    (x : Sigma γ) :
    x ∈ sigmaLift f a b ↔ ∃ (ha : a.1 = x.1) (hb : b.1 = x.1), x.2 ∈ f (ha ▸ a.2) (hb ▸ b.2) := by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigmaLift]
      simp only [dite_eq_ite, ite_true, mem_map, Embedding.sigmaMk_apply, forall_exists_index,
        and_imp]
      rintro x hx rfl
      exact ⟨rfl, rfl, hx⟩
    · rintro ⟨⟨⟩, ⟨⟩, hx⟩
      rw [sigmaLift, dif_pos rfl, mem_map]
      exact ⟨_, hx, by simp⟩
  · rw [sigmaLift, dif_neg h]
    refine iff_of_false (notMem_empty _) ?_
    rintro ⟨⟨⟩, ⟨⟩, _⟩
    exact h rfl
/-
**Finset.mk_mem_sigmaLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mk_mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (i : ι) (a :
 α i) (b : β i) (x : γ i) : (⟨i, x⟩ : Sigma γ) in sigmaLift f ⟨i, a⟩ ⟨i, b⟩ ↔ x 
in f a b
参数：f : forall ⦃i⦄, α i -> β i -> Finset (γ i)；i : ι；a : α i；b : β i；x : γ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sigmaLift.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} {β : ι → Type
 u_3} {γ : ι → Type u_4} [inst : DecidableEq ι]   (f : ⦃i : ι⦄ → α i → β i → Fin
set (γ i)) …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mk_mem_sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (i : ι) (a : α i) (b : β i)
    (x : γ i) : (⟨i, x⟩ : Sigma γ) ∈ sigmaLift f ⟨i, a⟩ ⟨i, b⟩ ↔ x ∈ f a b := by
  rw [sigmaLift, dif_pos rfl, mem_map]
  refine ⟨?_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx
/-
**Finset.notMem_sigmaLift_of_ne_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_sigmaLift_of_ne_left (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (
a : Sigma α) (b : Sigma β) (x : Sigma γ) (h : a.1 != x.1) : x ∉ sigmaLift f a b
参数：f : forall ⦃i⦄, α i -> β i -> Finset (γ i)；a : Sigma α；b : Sigma β；x : Sigma 
γ；h : a.1 != x.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_sigmaLift`：mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finse
t (γ i)) (a : Sigma α) (b : Sigma β) (x : Sigma γ) : x in sigmaLift f a b ↔ exis
ts (ha : a…
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem notMem_sigmaLift_of_ne_left (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α)
    (b : Sigma β) (x : Sigma γ) (h : a.1 ≠ x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigmaLift]
  exact fun H => h H.fst
/-
**Finset.notMem_sigmaLift_of_ne_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_sigmaLift_of_ne_right (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) 
{a : Sigma α} (b : Sigma β) {x : Sigma γ} (h : b.1 != x.1) : x ∉ sigmaLift f a b
参数：f : forall ⦃i⦄, α i -> β i -> Finset (γ i)；b : Sigma β；h : b.1 != x.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_sigmaLift`：mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finse
t (γ i)) (a : Sigma α) (b : Sigma β) (x : Sigma γ) : x in sigmaLift f a b ↔ exis
ts (ha : a…
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
-/
theorem notMem_sigmaLift_of_ne_right (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) {a : Sigma α}
    (b : Sigma β) {x : Sigma γ} (h : b.1 ≠ x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigmaLift]
  exact fun H => h H.snd.fst

variable {f g : ∀ ⦃i⦄, α i → β i → Finset (γ i)} {a : Σ i, α i} {b : Σ i, β i}
/-
**Finset.sigmaLift_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigmaLift_nonempty : (sigmaLift f a b).Nonempty ↔ exists h : a.1 = b.1, (f
 (h ▸ a.2) b.2).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem sigmaLift_nonempty :
    (sigmaLift f a b).Nonempty ↔ ∃ h : a.1 = b.1, (f (h ▸ a.2) b.2).Nonempty := by
  simp_rw [nonempty_iff_ne_empty, sigmaLift]
  split_ifs with h <;> simp [h]
/-
**Finset.sigmaLift_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigmaLift_eq_empty : sigmaLift f a b = ∅ ↔ forall h : a.1 = b.1, f (h ▸ a.
2) b.2 = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem sigmaLift_eq_empty : sigmaLift f a b = ∅ ↔ ∀ h : a.1 = b.1, f (h ▸ a.2) b.2 = ∅ := by
  simp_rw [sigmaLift]
  split_ifs with h
  · simp [h]
  · simp [h]
/-
**Finset.sigmaLift_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigmaLift_mono (h : forall ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b subseteq g a b) 
(a : Σ i, α i) (b : Σ i, β i) : sigmaLift f a b subseteq sigmaLift g a b
参数：h : forall ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b subseteq g a b；a : Σ i, α i；b : Σ i
, β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_sigmaLift`：mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finse
t (γ i)) (a : Sigma α) (b : Sigma β) (x : Sigma γ) : x in sigmaLift f a b ↔ exis
ts (ha : a…
-/
theorem sigmaLift_mono
    (h : ∀ ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b ⊆ g a b) (a : Σ i, α i) (b : Σ i, β i) :
    sigmaLift f a b ⊆ sigmaLift g a b := by
  rintro x hx
  rw [mem_sigmaLift] at hx ⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩

variable (f a b)
/-
**Finset.card_sigmaLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sigmaLift : (sigmaLift f a b).card = dite (a.1 = b.1) (fun h => (f (h
 ▸ a.2) b.2).card) fun _ => 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem card_sigmaLift :
    (sigmaLift f a b).card = dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0 := by
  simp_rw [sigmaLift]
  split_ifs with h <;> simp

end SigmaLift

end Finset

