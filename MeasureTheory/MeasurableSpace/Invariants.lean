/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
/-!
# σ-algebra of sets invariant under a self-map

In this file we define `MeasurableSpace.invariants (f : α → α)`
to be the σ-algebra of sets `s : Set α` such that
- `s` is measurable w.r.t. the canonical σ-algebra on `α`;
- and `f ⁻¹' s = s`.
-/

@[expose] public section

open Set Function
open scoped MeasureTheory

namespace MeasurableSpace

variable {α : Type*}

/-- Given a self-map `f : α → α`,
`invariants f` is the σ-algebra of measurable sets that are invariant under `f`.

A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
@[instance_reducible]
/-
**MeasurableSpace.invariants** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：invariants [m : MeasurableSpace α] (f : α -> α) : MeasurableSpace α
参数：f : α -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_empty`：∀ {α : Type u_7} (self : Measurable
Space α), MeasurableSpace.MeasurableSet' self ∅
· 使用定理 `MeasurableSpace.measurableSet_compl`：∀ {α : Type u_7} (self : Measurable
Space α) (s : Set α),   MeasurableSpace.MeasurableSet' self s → MeasurableSpace.
MeasurableSet' self sᶜ
· 使用定理 `MeasurableSpace.measurableSet_iUnion`：∀ {α : Type u_7} (self : Measurabl
eSpace α) (f : ℕ → Set α),   (∀ (i : ℕ), MeasurableSpace.MeasurableSet' self (f 
i)) → MeasurableSpace.Meas…

--- 原说明 ---
Given a self-map `f : α → α`,
`invariants f` is the σ-algebra of measurable sets that are invariant under `f`.

A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`.
-/
def invariants [m : MeasurableSpace α] (f : α → α) : MeasurableSpace α :=
  { m ⊓ ⟨fun s ↦ f ⁻¹' s = s, by simp, by simp, fun f hf ↦ by simp [hf]⟩ with
    MeasurableSet' := fun s ↦ MeasurableSet[m] s ∧ f ⁻¹' s = s }

variable [MeasurableSpace α]

/-- A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
/-
**MeasurableSpace.measurableSet_invariants** 是 Mathlib 中的一个定理，位于命名空间 `Measurable
Space`。
形式化陈述：measurableSet_invariants {f : α -> α} {s : Set α} : MeasurableSet[invarian
ts f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`.
-/
theorem measurableSet_invariants {f : α → α} {s : Set α} :
    MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s :=
  .rfl

@[simp]
/-
**MeasurableSpace.invariants_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：invariants_id : invariants (id : α -> α) = ‹MeasurableSpace α›
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem invariants_id : invariants (id : α → α) = ‹MeasurableSpace α› :=
  ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, rfl⟩⟩
/-
**MeasurableSpace.invariants_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：invariants_le (f : α -> α) : invariants f <= ‹MeasurableSpace α›
参数：f : α -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem invariants_le (f : α → α) : invariants f ≤ ‹MeasurableSpace α› := fun _ ↦ And.left
/-
**MeasurableSpace.inf_le_invariants_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSp
ace`。
形式化陈述：inf_le_invariants_comp (f g : α -> α) : invariants f ⊓ invariants g <= inv
ariants (f ∘ g)
参数：f g : α -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inf_le_invariants_comp (f g : α → α) :
    invariants f ⊓ invariants g ≤ invariants (f ∘ g) := fun s hs ↦
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩
/-
**MeasurableSpace.le_invariants_iterate** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpa
ce`。
形式化陈述：le_invariants_iterate (f : α -> α) (n : Nat) : invariants f <= invariants 
(f^[n])
参数：f : α -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.invariants_id`：invariants_id : invariants (id : α -> α) 
= ‹MeasurableSpace α›
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasurableSpace.inf_le_invariants_comp`：inf_le_invariants_comp (f g : α 
-> α) : invariants f ⊓ invariants g <= invariants (f ∘ g)
-/
theorem le_invariants_iterate (f : α → α) (n : ℕ) :
    invariants f ≤ invariants (f^[n]) := by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)

variable {β : Type*} [MeasurableSpace β]
/-
**MeasurableSpace.measurable_invariants_dom** 是 Mathlib 中的一个定理，位于命名空间 `Measurabl
eSpace`。
形式化陈述：measurable_invariants_dom {f : α -> α} {g : α -> β} : Measurable[invariant
s f] g ↔ Measurable g ∧ forall s, MeasurableSet s -> (g ∘ f) ⁻¹' s = g ⁻¹' s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurable_invariants_dom {f : α → α} {g : α → β} :
    Measurable[invariants f] g ↔ Measurable g ∧ ∀ s, MeasurableSet s → (g ∘ f) ⁻¹' s = g ⁻¹' s := by
  simp only [Measurable, ← forall_and]; rfl
/-
**MeasurableSpace.measurable_invariants_of_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `M
easurableSpace`。
形式化陈述：measurable_invariants_of_semiconj {fa : α -> α} {fb : β -> β} {g : α -> β}
 (hg : Measurable g) (hfg : Semiconj g fa fb) : @Measurable _ _ (invariants fa) 
(invariants fb) g
参数：hg : Measurable g；hfg : Semiconj g fa fb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measurable_invariants_of_semiconj {fa : α → α} {fb : β → β} {g : α → β} (hg : Measurable g)
    (hfg : Semiconj g fa fb) : @Measurable _ _ (invariants fa) (invariants fb) g := fun s hs ↦
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩
/-
**MeasurableSpace.comp_eq_of_measurable_invariants** 是 Mathlib 中的一个定理，位于命名空间 `Me
asurableSpace`。
形式化陈述：comp_eq_of_measurable_invariants {f : α -> α} {g : α -> β} [MeasurableSing
letonClass β] (h : Measurable[invariants f] g) : g ∘ f = g
参数：h : Measurable[invariants f] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem comp_eq_of_measurable_invariants {f : α → α} {g : α → β} [MeasurableSingletonClass β]
    (h : Measurable[invariants f] g) : g ∘ f = g := by
  funext x
  suffices x ∈ f ⁻¹' g ⁻¹' {g x} by simpa
  rw [(h <| measurableSet_singleton (g x)).2, Set.mem_preimage, Set.mem_singleton_iff]

end MeasurableSpace

