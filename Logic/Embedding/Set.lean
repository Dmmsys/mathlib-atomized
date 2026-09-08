/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Data.Set.Image

/-!
# Interactions between embeddings and sets.

-/

@[expose] public section

assert_not_exists WithTop

universe u v w x

open Set Set.Notation

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

@[simp]
/-
**Equiv.asEmbedding_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.asEmbedding_range {α β : Sort _} {p : β -> Prop} (e : α ≃ Subtype p)
 : Set.range e.asEmbedding = Set.ofPred p
参数：e : α ≃ Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.asEmbedding_apply`：∀ {β : Sort u_1} {α : Sort u_2} {p : β → Prop} 
(e : α ≃ Subtype p) (a : α), e.asEmbedding a = ↑(e a)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Equiv.asEmbedding_range {α β : Sort _} {p : β → Prop} (e : α ≃ Subtype p) :
    Set.range e.asEmbedding = Set.ofPred p :=
  Set.ext fun x ↦ ⟨fun ⟨y, h⟩ ↦ h ▸ Subtype.coe_prop (e y), fun hs ↦ ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

end Equiv

namespace Function

namespace Embedding

/-- Given an embedding `f : α ↪ β` and a point outside of `Set.range f`, construct an embedding
`Option α ↪ β`. -/
@[simps]
/-
**Function.Embedding.optionElim** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f) : Option α ↪ β
参数：f : α ↪ β；x : β；h : x ∉ Set.range f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…

--- 原说明 ---
Given an embedding `f : α ↪ β` and a point outside of `Set.range f`, construct a
n embedding
`Option α ↪ β`.
-/
def optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f) : Option α ↪ β :=
  ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between embeddings of `Option α` and a sigma type over the embeddings of `α`. -/
@[simps]
/-
**Function.Embedding.optionEmbeddingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.Em
bedding`。
形式化陈述：optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σ f : α ↪ β, ↥(Set.range f)ᶜ
 where toFun f
参数：α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between embeddings of `Option α` and a sigma type over the embedding
s of `α`.
-/
def optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σ f : α ↪ β, ↥(Set.range f)ᶜ where
  toFun f := ⟨Embedding.some.trans f, f none, fun ⟨x, hx⟩ ↦ Option.some_ne_none x <| f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
  left_inv f := ext <| by rintro (_ | _) <;> simp
  right_inv := fun ⟨f, y, hy⟩ ↦ by ext <;> simp

/-- Restrict the codomain of an embedding. -/
/-
**Function.Embedding.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：codRestrict {α β} (p : Set β) (f : α ↪ β) (H : forall a, f a in p) : α ↪ p
参数：p : Set β；f : α ↪ β；H : forall a, f a in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of an embedding.
-/
def codRestrict {α β} (p : Set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
  ⟨fun a ↦ ⟨f a, H a⟩, fun _ _ h ↦ f.injective (congr_arg Subtype.val h)⟩

@[simp]
/-
**Function.Embedding.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embed
ding`。
形式化陈述：codRestrict_apply {α β} (p) (f : α ↪ β) (H a) : codRestrict p f H a = ⟨f a
, H a⟩
参数：p；f : α ↪ β；H a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply {α β} (p) (f : α ↪ β) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- `Set.image` as an embedding `Set α ↪ Set β`. -/
@[simps apply]
/-
**Function.Embedding.image** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α ↪ β) → Set α ↪ Set β
参数：α ↪ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.image` as an embedding `Set α ↪ Set β`.
-/
protected def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨image f, f.2.image_injective⟩

end Embedding

end Function

namespace Set

/-- The injection map is an embedding between subsets. -/
@[simps apply_coe]
/-
**Set.embeddingOfSubset** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：embeddingOfSubset {α} (s t : Set α) (h : s subseteq t) : s ↪ t
参数：s t : Set α；h : s subseteq t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection map is an embedding between subsets.
-/
def embeddingOfSubset {α} (s t : Set α) (h : s ⊆ t) : s ↪ t :=
  ⟨fun x ↦ ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ by
    congr
    injection h⟩

end Set

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`Disjoint p q`.

See also `Equiv.sumCompl`, for when `IsCompl p q`. -/
@[simps (attr := grind =) apply]
/-
**subtypeOrEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subtypeOrEquiv (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q) : { 
x // p x ∨ q x } ≃ { x // p x } oplus { x // q x } where toFun
参数：p q : α -> Prop；h : Disjoint p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalen
t to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`Disjoint p q`.

See also `Equiv.sumCompl`, for when `IsCompl p q`.
-/
def subtypeOrEquiv (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) :
    { x // p x ∨ q x } ≃ { x // p x } ⊕ { x // q x } where
  toFun := subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx ↦ (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx ↦ (Or.inr hx : p x ∨ q x))
  left_inv x := by grind
  right_inv x := by
    cases x with
    | inl x => grind
    | inr x =>
      simp only [Sum.elim_inr]
      rw [subtypeOrLeftEmbedding_apply_right]
      · grind
      · suffices ¬p x by simpa
        intro hp
        simpa using h.le_bot x ⟨hp, x.prop⟩

@[simp, grind =]
/-
**subtypeOrEquiv_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtypeOrEquiv_symm_inl (p q : α -> Prop) [DecidablePred p] (h : Disjoint 
p q) (x : { x // p x }) : (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x
.prop⟩
参数：p q : α -> Prop；h : Disjoint p q；x : { x // p x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeOrEquiv_symm_inl (p q : α → Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // p x }) : (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x.prop⟩ :=
  rfl

@[simp, grind =]
/-
**subtypeOrEquiv_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtypeOrEquiv_symm_inr (p q : α -> Prop) [DecidablePred p] (h : Disjoint 
p q) (x : { x // q x }) : (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x
.prop⟩
参数：p q : α -> Prop；h : Disjoint p q；x : { x // q x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subtypeOrEquiv_symm_inr (p q : α → Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // q x }) : (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x.prop⟩ :=
  rfl

end Subtype

section Disjoint

variable {α ι : Type*} {s t r : Set α}

/-- For disjoint `s t : Set α`, the natural injection from `↑s ⊕ ↑t` to `α`. -/
/-
**Function.Embedding.sumSet** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Type u_1} → {s t : Set α} → Disjoint s t → ↑s ⊕ ↑t ↪ α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For disjoint `s t : Set α`, the natural injection from `↑s ⊕ ↑t` to `α`.
-/
@[simps] def Function.Embedding.sumSet (h : Disjoint s t) : s ⊕ t ↪ α where
  toFun := Sum.elim (↑) (↑)
  inj' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp
/-
**Function.Embedding.coe_sumSet** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：∀ {α : Type u_1} {s t : Set α} (h : Disjoint s t), ⇑(Function.Embedding.su
mSet h) = Sum.elim Subtype.val Subtype.val
参数：h : Disjoint s t；Function.Embedding.sumSet h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma Function.Embedding.coe_sumSet (h : Disjoint s t) :
    (Function.Embedding.sumSet h : s ⊕ t → α) = Sum.elim (↑) (↑) := rfl
/-
**Function.Embedding.sumSet_preimage_inl** 是 Mathlib 中的一个定理，位于命名空间 `Function.Emb
edding`。
形式化陈述：∀ {α : Type u_1} {s t r : Set α} (h : Disjoint s t),   Subtype.val '' Sum.
inl ⁻¹' ⇑(Function.Embedding.sumSet h) ⁻¹' r = r ∩ s
参数：h : Disjoint s t；Function.Embedding.sumSet h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sumSet_apply`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t) (a : ↑s ⊕ ↑t),   (Function.Embedding.sumSet h) a = Sum.elim Subtype.v
al Subtype.val a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem Function.Embedding.sumSet_preimage_inl (h : Disjoint s t) :
    .inl ⁻¹' Function.Embedding.sumSet h ⁻¹' r = r ∩ s := by
  simp [Set.ext_iff]
/-
**Function.Embedding.sumSet_preimage_inr** 是 Mathlib 中的一个定理，位于命名空间 `Function.Emb
edding`。
形式化陈述：∀ {α : Type u_1} {s t r : Set α} (h : Disjoint s t),   Subtype.val '' Sum.
inr ⁻¹' ⇑(Function.Embedding.sumSet h) ⁻¹' r = r ∩ t
参数：h : Disjoint s t；Function.Embedding.sumSet h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sumSet_apply`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t) (a : ↑s ⊕ ↑t),   (Function.Embedding.sumSet h) a = Sum.elim Subtype.v
al Subtype.val a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem Function.Embedding.sumSet_preimage_inr (h : Disjoint s t) :
    .inr ⁻¹' Function.Embedding.sumSet h ⁻¹' r = r ∩ t := by
  simp [Set.ext_iff]
/-
**Function.Embedding.sumSet_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`
。
形式化陈述：∀ {α : Type u_1} {s t : Set α} (h : Disjoint s t), Set.range ⇑(Function.Em
bedding.sumSet h) = s ∪ t
参数：h : Disjoint s t；Function.Embedding.sumSet h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sumSet_apply`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t) (a : ↑s ⊕ ↑t),   (Function.Embedding.sumSet h) a = Sum.elim Subtype.v
al Subtype.val a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem Function.Embedding.sumSet_range {s t : Set α} (h : Disjoint s t) :
    range (Function.Embedding.sumSet h) = s ∪ t := by
  simp [Set.ext_iff]

open scoped Function -- required for scoped `on` notation

/-- For an indexed family `s : ι → Set α` of disjoint sets,
the natural injection from the sigma-type `(i : ι) × ↑(s i)` to `α`. -/
/-
**Function.Embedding.sigmaSet** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Type u_1} → {ι : Type u_2} → {s : ι → Set α} → Pairwise (Function.onF
un Disjoint s) → (i : ι) × ↑(s i) ↪ α
参数：Function.onFun Disjoint s；i : ι；s i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an indexed family `s : ι → Set α` of disjoint sets,
the natural injection from the sigma-type `(i : ι) × ↑(s i)` to `α`.
-/
@[simps] def Function.Embedding.sigmaSet {s : ι → Set α} (h : Pairwise (Disjoint on s)) :
    (i : ι) × s i ↪ α where
  toFun x := x.2.1
  inj' := by
    rintro ⟨i, x, hx⟩ ⟨j, -, hx'⟩ rfl
    obtain rfl : i = j := h.eq (not_disjoint_iff.2 ⟨_, hx, hx'⟩)
    rfl

set_option warning.simp.otherHead false in
/-
**Function.Embedding.coe_sigmaSet** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`
。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {s : ι → Set α} (h : Pairwise (Function.on
Fun Disjoint s)),   ⇑(Function.Embedding.sigmaSet h) = fun x => ↑x.snd
参数：h : Pairwise (Function.onFun Disjoint s)；Function.Embedding.sigmaSet h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma Function.Embedding.coe_sigmaSet {s : ι → Set α} (h) :
    (Function.Embedding.sigmaSet h : ((i : ι) × s i) → α) = fun x ↦ x.2.1 := rfl
/-
**Function.Embedding.sigmaSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embed
ding`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {s : ι → Set α} (h : Pairwise (Function.on
Fun Disjoint s)) (i : ι) (r : Set α),   Subtype.val '' Sigma.mk i ⁻¹' ⇑(Function
.Embedding.sigmaSet h) ⁻¹' r = r ∩ s i
参数：h : Pairwise (Function.onFun Disjoint s)；i : ι；r : Set α；Function.Embedding.s
igmaSet h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sigmaSet_apply`：∀ {α : Type u_1} {ι : Type u_2} {s : 
ι → Set α} (h : Pairwise (Function.onFun Disjoint s)) (x : (i : ι) × ↑(s i)),   
(Function.Embedding.sig…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem Function.Embedding.sigmaSet_preimage {s : ι → Set α}
    (h : Pairwise (Disjoint on s)) (i : ι) (r : Set α) :
    Sigma.mk i ⁻¹' Function.Embedding.sigmaSet h ⁻¹' r = r ∩ s i := by
  simp [Set.ext_iff]
/-
**Function.Embedding.sigmaSet_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embeddin
g`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {s : ι → Set α} (h : Pairwise (Function.on
Fun Disjoint s)),   Set.range ⇑(Function.Embedding.sigmaSet h) = ⋃ i, s i
参数：h : Pairwise (Function.onFun Disjoint s)；Function.Embedding.sigmaSet h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sigmaSet_apply`：∀ {α : Type u_1} {ι : Type u_2} {s : 
ι → Set α} (h : Pairwise (Function.onFun Disjoint s)) (x : (i : ι) × ↑(s i)),   
(Function.Embedding.sig…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem Function.Embedding.sigmaSet_range {s : ι → Set α}
    (h : Pairwise (Disjoint on s)) : Set.range (Function.Embedding.sigmaSet h) = ⋃ i, s i := by
  simp [Set.ext_iff]

end Disjoint

