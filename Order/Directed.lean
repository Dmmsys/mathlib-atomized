/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Util.Delaborators

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `Directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `DirectedOn r s`: Predicate stating that the set `s` is `r`-directed.
* `IsDirected α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `Std.Total`.

## TODO

Define connected orders (the transitive symmetric closure of `≤` is everything) and show that
(co)directed orders are connected.

## References
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/

@[expose] public section


open Function

variable {α β : Type*} {ι κ : Sort*} (r r' s : α → α → Prop)

/-- Local notation for a relation -/
local infixl:50 " ≼ " => r

/-- A family of elements of `α` is directed (with respect to a relation `≼` on `α`)
  if there is a member of the family `≼`-above any pair in the family. -/
/-
**Directed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Directed (f : ι -> α)
参数：f : ι -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements of `α` is directed (with respect to a relation `≼` on `α`)
  if there is a member of the family `≼`-above any pair in the family.
-/
def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of `α` is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
/-
**DirectedOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirectedOn (s : Set α)
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of `α` is directed if there is an element of the set `≼`-above any
  pair of elements in the set.
-/
def DirectedOn (s : Set α) :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≼ z ∧ y ≼ z

variable {r r'}
/-
**directedOn_iff_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_iff_directed {s} : @DirectedOn α r s ↔ Directed r (Subtype.val 
: s -> α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem directedOn_iff_directed {s} : @DirectedOn α r s ↔ Directed r (Subtype.val : s → α) := by
  simp only [DirectedOn, Directed, Subtype.exists, exists_and_left, exists_prop, Subtype.forall]
  exact forall₂_congr fun x _ => by simp [And.comm, and_assoc]

alias ⟨DirectedOn.directed_val, _⟩ := directedOn_iff_directed
/-
**directedOn_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_range {f : ι -> α} : DirectedOn r (.range f) ↔ Directed r f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem directedOn_range {f : ι → α} : DirectedOn r (.range f) ↔ Directed r f := by
  simp_rw [Directed, DirectedOn, Set.forall_mem_range, Set.exists_range_iff]

protected alias ⟨_, Directed.directedOn_range⟩ := directedOn_range
/-
**directedOn_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_image {s : Set β} {f : β -> α} : DirectedOn r (f '' s) ↔ Direct
edOn (f ⁻¹'o r) s
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
theorem directedOn_image {s : Set β} {f : β → α} :
    DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [DirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]
/-
**DirectedOn.mono'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.mono' {s : Set α} (hs : DirectedOn r s) (h : forall ⦃a⦄, a in s
 -> forall ⦃b⦄, b in s -> r a b -> r' a b) : DirectedOn r' s
参数：hs : DirectedOn r s；h : forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> r a b -> 
r' a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem DirectedOn.mono' {s : Set α} (hs : DirectedOn r s)
    (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) : DirectedOn r' s := fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩
/-
**DirectedOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : forall ⦃a b⦄, r a b 
-> r' a b) : DirectedOn r' s
参数：h : DirectedOn r s；H : forall ⦃a b⦄, r a b -> r' a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.mono'`：DirectedOn.mono' {s : Set α} (hs : DirectedOn r s) (h 
: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> r a b -> r' a b) : DirectedOn r' s
-/
theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : ∀ ⦃a b⦄, r a b → r' a b) :
    DirectedOn r' s :=
  h.mono' fun _ _ _ _ h ↦ H h
/-
**directed_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directed_comp {ι} {f : ι -> β} {g : β -> α} : Directed r (g ∘ f) ↔ Directe
d (g ⁻¹'o r) f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem directed_comp {ι} {f : ι → β} {g : β → α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl
/-
**directed_comp_iff_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directed_comp_iff_of_surjective {f : ι -> κ} (hf : f.Surjective) {g : κ ->
 α} : Directed r (g ∘ f) ↔ Directed r g
参数：hf : f.Surjective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma directed_comp_iff_of_surjective {f : ι → κ} (hf : f.Surjective) {g : κ → α} :
    Directed r (g ∘ f) ↔ Directed r g := by simp [Directed, hf.forall, hf.exists]

alias ⟨_, Directed.comp_of_surjective⟩ := directed_comp_iff_of_surjective
/-
**Directed.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.mono {s : α -> α -> Prop} {ι} {f : ι -> α} (H : forall a b, r a b
 -> s a b) (h : Directed r f) : Directed s f
参数：H : forall a b, r a b -> s a b；h : Directed r f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Directed.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b)
    (h : Directed r f) : Directed s f := fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩
/-
**Directed.mono_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β -> β -> Prop} {g : α -
> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g y)) (hf : Directed r 
f) : Directed rb (g ∘ f)
参数：r : α -> α -> Prop；hg : forall ⦃x y⦄, r x y -> rb (g x) (g y)；hf : Directed r
 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directed_comp`：directed_comp {ι} {f : ι -> β} {g : β -> α} : Directed r 
(g ∘ f) ↔ Directed (g ⁻¹'o r) f
· 使用定理 `Directed.mono`：Directed.mono {s : α -> α -> Prop} {ι} {f : ι -> α} (H : 
forall a b, r a b -> s a b) (h : Directed r f) : Directed s f
-/
theorem Directed.mono_comp (r : α → α → Prop) {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : Directed r f) : Directed rb (g ∘ f) :=
  directed_comp.2 <| hf.mono hg
/-
**DirectedOn.mono_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β -> β -> Prop} {g : α -> 
β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g y)) (hf : DirectedOn r s
) : DirectedOn rb (g '' s)
参数：hg : forall ⦃x y⦄, r x y -> rb (g x) (g y)；hf : DirectedOn r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directedOn_image`：directedOn_image {s : Set β} {f : β -> α} : DirectedOn
 r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s
· 使用定理 `DirectedOn.mono`：DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : f
orall ⦃a b⦄, r a b -> r' a b) : DirectedOn r' s
-/
theorem DirectedOn.mono_comp {r : α → α → Prop} {rb : β → β → Prop} {g : α → β} {s : Set α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : DirectedOn r s) : DirectedOn rb (g '' s) :=
  directedOn_image.mpr (hf.mono hg)
/-
**directedOn_onFun_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_onFun_iff {r : α -> α -> Prop} {f : β -> α} {s : Set β} : Direc
tedOn (r on f) s ↔ DirectedOn r (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma directedOn_onFun_iff {r : α → α → Prop} {f : β → α} {s : Set β} :
    DirectedOn (r on f) s ↔ DirectedOn r (f '' s) := by
  refine ⟨DirectedOn.mono_comp (by simp), fun h x hx y hy ↦ ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := h (f x) (Set.mem_image_of_mem f hx) (f y)
    (Set.mem_image_of_mem f hy)
  grind

/-- A set stable by supremum is `≤`-directed. -/
/-
**directedOn_of_sup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_of_sup_mem [SemilatticeSup α] {S : Set α} (H : forall ⦃i j⦄, i 
in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S
参数：H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
A set stable by supremum is `≤`-directed.
-/
theorem directedOn_of_sup_mem [SemilatticeSup α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊔ j ∈ S) : DirectedOn (· ≤ ·) S := fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩
/-
**Directed.extend_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.extend_bot [Preorder α] [OrderBot α] {e : ι -> β} {f : ι -> α} (h
f : Directed (· <= ·) f) (he : Function.Injective e) : Directed (· <= ·) (Functi
on.extend e f ⊥)
参数：hf : Directed (· <= ·) f；he : Function.Injective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem Directed.extend_bot [Preorder α] [OrderBot α] {e : ι → β} {f : ι → α}
    (hf : Directed (· ≤ ·) f) (he : Function.Injective e) :
    Directed (· ≤ ·) (Function.extend e f ⊥) := by
  intro a b
  rcases (em (∃ i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [Function.extend_apply' _ _ _ ha]
  rcases (em (∃ i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and]

/-- A set stable by infimum is `≥`-directed. -/
/-
**directedOn_of_inf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_of_inf_mem [SemilatticeInf α] {S : Set α} (H : forall ⦃i j⦄, i 
in S -> j in S -> i ⊓ j in S) : DirectedOn (· >= ·) S
参数：H : forall ⦃i j⦄, i in S -> j in S -> i ⊓ j in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directedOn_of_sup_mem`：directedOn_of_sup_mem [SemilatticeSup α] {S : Set
 α} (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S

--- 原说明 ---
A set stable by infimum is `≥`-directed.
-/
theorem directedOn_of_inf_mem [SemilatticeInf α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊓ j ∈ S) : DirectedOn (· ≥ ·) S :=
  directedOn_of_sup_mem (α := αᵒᵈ) H
/-
**Std.Total.directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Total.directed [Std.Total r] (f : ι -> α) : Directed r f
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Std.instReflOfTotal`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Total r], 
Std.Refl r
-/
theorem Std.Total.directed [Std.Total r] (f : ι → α) : Directed r f := fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩
/-
**Std.Total.directedOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Total.directedOn [Std.Total r] (s : Set α) : DirectedOn r s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Std.instReflOfTotal`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Total r], 
Std.Refl r
-/
theorem Std.Total.directedOn [Std.Total r] (s : Set α) : DirectedOn r s := fun a ha b hb =>
  Or.casesOn (total_of r a b) (fun h => ⟨b, hb, h, refl _⟩) fun h => ⟨a, ha, refl _, h⟩

@[simp]
/-
**DirectedOn.of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.of_linearOrder [LinearOrder α] (s : Set α) : DirectedOn (· <= ·
) s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Total.directedOn`：Std.Total.directedOn [Std.Total r] (s : Set α) : D
irectedOn r s
-/
theorem DirectedOn.of_linearOrder [LinearOrder α] (s : Set α) : DirectedOn (· ≤ ·) s :=
  Std.Total.directedOn s

/-- `IsDirected α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
/-
**IsDirected** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_5) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsDirected α r` states that for any elements `a`, `b` there exists an element `
c` such that
`r a c` and `r b c`.
-/
class IsDirected (α : Sort*) (r : α → α → Prop) : Prop where
  /-- For every pair of elements `a` and `b` there is a `c` such that `r a c` and `r b c` -/
  directed (a b : α) : ∃ c, r a c ∧ r b c

/-- A class for an `IsDirected` relation `≤`. -/
@[to_dual /-- A class for an `IsDirected` relation `≥`. -/]
/-
**IsDirectedOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsDirectedOrder (α : Type*) [LE α] : Prop
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class for an `IsDirected` relation `≤`.
-/
abbrev IsDirectedOrder (α : Type*) [LE α] : Prop := IsDirected α (· ≤ ·)
/-
**directed_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α) : exists c, r 
a c ∧ r b c
参数：r : α -> α -> Prop；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDirected.directed`：∀ {α : Sort u_5} {r : α → α → Prop} [self : IsDirec
ted α r] (a b : α), ∃ c, r a c ∧ r b c
-/
theorem directed_of (r : α → α → Prop) [IsDirected α r] (a b : α) : ∃ c, r a c ∧ r b c :=
  IsDirected.directed _ _
/-
**directed_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α) : exists c, r 
a c ∧ r b c
参数：r : α -> α -> Prop；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDirected.directed`：∀ {α : Sort u_5} {r : α → α → Prop} [self : IsDirec
ted α r] (a b : α), ∃ c, r a c ∧ r b c
-/
theorem directed_of₃ (r : α → α → Prop) [IsDirected α r] [IsTrans α r] (a b c : α) :
    ∃ d, r a d ∧ r b d ∧ r c d :=
  have ⟨e, hae, hbe⟩ := directed_of r a b
  have ⟨f, hef, hcf⟩ := directed_of r e c
  ⟨f, Trans.trans hae hef, Trans.trans hbe hef, hcf⟩
/-
**isDirected_onFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDirected_onFun {f : ι -> α} : IsDirected ι (r on f) ↔ Directed r f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDirected.directed`：∀ {α : Sort u_5} {r : α → α → Prop} [self : IsDirec
ted α r] (a b : α), ∃ c, r a c ∧ r b c
-/
theorem isDirected_onFun {f : ι → α} : IsDirected ι (r on f) ↔ Directed r f :=
  ⟨(·.directed), (⟨·⟩)⟩
/-
**directed_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directed_id [IsDirected α r] : Directed r id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
-/
theorem directed_id [IsDirected α r] : Directed r id := directed_of r
/-
**directed_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directed_id_iff : Directed r id ↔ IsDirected α r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isDirected_onFun`：isDirected_onFun {f : ι -> α} : IsDirected ι (r on f) 
↔ Directed r f
-/
theorem directed_id_iff : Directed r id ↔ IsDirected α r :=
  isDirected_onFun.symm
/-
**directedOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_univ [IsDirected α r] : DirectedOn r Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `trivial`：True
-/
theorem directedOn_univ [IsDirected α r] : DirectedOn r Set.univ := fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivial, hc⟩
/-
**directedOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_univ_iff : DirectedOn r Set.univ ↔ IsDirected α r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `directedOn_univ`：directedOn_univ [IsDirected α r] : DirectedOn r Set.uni
v
-/
theorem directedOn_univ_iff : DirectedOn r Set.univ ↔ IsDirected α r :=
  ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @directedOn_univ _ _⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Std.Total.to_isDirected [Std.Total r] : IsDirected α r :=
  directed_id_iff.1 <| Std.Total.directed _
/-
**isDirected_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDirected_mono [IsDirected α r] (h : forall ⦃a b⦄, r a b -> s a b) : IsDi
rected α s
参数：h : forall ⦃a b⦄, r a b -> s a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDirected.directed`：∀ {α : Sort u_5} {r : α → α → Prop} [self : IsDirec
ted α r] (a b : α), ∃ c, r a c ∧ r b c
-/
theorem isDirected_mono [IsDirected α r] (h : ∀ ⦃a b⦄, r a b → s a b) : IsDirected α s :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩

@[to_dual exists_le_le]
/-
**exists_ge_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists c, a <= c ∧ b <
= c
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
-/
theorem exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  directed_of (· ≤ ·) a b

@[to_dual isDirected_le]
/-
**OrderDual.isDirected_ge** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.isDirected_ge [LE α] [IsDirectedOrder α] : IsCodirectedOrder αᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.isDirected_ge [LE α] [IsDirectedOrder α] : IsCodirectedOrder αᵒᵈ := by
  assumption

/-- A monotone function on an upwards-directed type is directed. -/
@[to_dual (reorder := H (i j)) directed_of_isDirected_ge
/-- An antitone function on a downwards-directed type is directed. -/]
/-
**directed_of_isDirected_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directed_of_isDirected_le [LE α] [IsDirectedOrder α] {f : α -> β} {r : β -
> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (f j)) : Directed r f
参数：H : forall ⦃i j⦄, i <= j -> r (f i) (f j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `directed_id`：directed_id [IsDirected α r] : Directed r id
-/
theorem directed_of_isDirected_le [LE α] [IsDirectedOrder α] {f : α → β} {r : β → β → Prop}
    (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : Directed r f :=
  directed_id.mono_comp _ H

@[to_dual directed_ge]
/-
**Monotone.directed_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.directed_le [Preorder α] [IsDirectedOrder α] [Preorder β] {f : α 
-> β} : Monotone f -> Directed (· <= ·) f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
-/
theorem Monotone.directed_le [Preorder α] [IsDirectedOrder α] [Preorder β] {f : α → β} :
    Monotone f → Directed (· ≤ ·) f :=
  directed_of_isDirected_le

@[to_dual directed_ge]
/-
**Antitone.directed_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.directed_le [Preorder α] [IsCodirectedOrder α] [Preorder β] {f : 
α -> β} (hf : Antitone f) : Directed (· <= ·) f
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of_isDirected_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : LE α]
 [IsCodirectedOrder α] {f : α → β} {r : β → β → Prop},   (∀ ⦃j i : α⦄, j ≤ i → r
 (f i) (f j)) →…
-/
theorem Antitone.directed_le [Preorder α] [IsCodirectedOrder α] [Preorder β] {f : α → β}
    (hf : Antitone f) : Directed (· ≤ ·) f :=
  directed_of_isDirected_ge hf

@[to_dual]
/-
**directedOn_iff_isDirectedOrder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_iff_isDirectedOrder [LE α] {s : Set α} : DirectedOn (· <= ·) s 
↔ IsDirectedOrder s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `IsDirectedOrder.eq_1`：∀ (α : Type u_5) [inst : LE α], IsDirectedOrder α 
= IsDirected α fun x1 x2 => x1 ≤ x2
-/
lemma directedOn_iff_isDirectedOrder [LE α] {s : Set α} :
    DirectedOn (· ≤ ·) s ↔ IsDirectedOrder s := by
  rw [directedOn_iff_directed, IsDirectedOrder]
  exact ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

@[to_dual]
alias ⟨DirectedOn.isDirectedOrder, DirectedOn.of_isDirectedOrder⟩ := directedOn_iff_isDirectedOrder

section Reflexive

/-
**DirectedOn.insert** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Refl r] (a : α) {s : Set α},   Di
rectedOn r s → (∀ b ∈ s, ∃ c ∈ s, r a c ∧ r b c) → DirectedOn r (insert a s)
参数：a : α；∀ b ∈ s, ∃ c ∈ s, r a c ∧ r b c；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
protected theorem DirectedOn.insert [Std.Refl r] (a : α) {s : Set α} (hd : DirectedOn r s)
    (ha : ∀ b ∈ s, ∃ c ∈ s, a ≼ c ∧ b ≼ c) : DirectedOn r (insert a s) := by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, refl _, refl _⟩
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
/-
**directedOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_singleton [Std.Refl r] (a : α) : DirectedOn r ({a} : Set α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem directedOn_singleton [Std.Refl r] (a : α) : DirectedOn r ({a} : Set α) :=
  fun x hx _ hy => ⟨x, hx, refl _, hx.symm ▸ hy.symm ▸ refl _⟩
/-
**directedOn_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_pair [Std.Refl r] {a b : α} (hab : a ≼ b) : DirectedOn r ({a, b
} : Set α)
参数：hab : a ≼ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.insert`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Refl r] (a :
 α) {s : Set α},   DirectedOn r s → (∀ b ∈ s, ∃ c ∈ s, r a c ∧ r b c) → Directed
On r (i…
· 使用定理 `directedOn_singleton`：directedOn_singleton [Std.Refl r] (a : α) : Direct
edOn r ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem directedOn_pair [Std.Refl r] {a b : α} (hab : a ≼ b) : DirectedOn r ({a, b} : Set α) :=
  (directedOn_singleton _).insert _ fun c hc => ⟨c, hc, hc.symm ▸ hab, refl _⟩
/-
**directedOn_pair'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_pair' [Std.Refl r] {a b : α} (hab : a ≼ b) : DirectedOn r ({b, 
a} : Set α)
参数：hab : a ≼ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `directedOn_pair`：directedOn_pair [Std.Refl r] {a b : α} (hab : a ≼ b) : 
DirectedOn r ({a, b} : Set α)
-/
theorem directedOn_pair' [Std.Refl r] {a b : α} (hab : a ≼ b) :
    DirectedOn r ({b, a} : Set α) := by
  rw [Set.pair_comm]
  apply directedOn_pair hab

end Reflexive

section Preorder

variable [Preorder α] {a : α}

@[to_dual]
/-
**IsMax.isTop** 是 Mathlib 中的一个定理，位于命名空间 `IsMax`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α} [IsDirectedOrder α], IsMax a 
→ IsTop a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
protected theorem IsMax.isTop [IsDirectedOrder α] (h : IsMax a) : IsTop a := fun b ↦
  let ⟨_, hca, hcb⟩ := exists_ge_ge a b
  hcb.trans (h hca)

@[to_dual]
/-
**DirectedOn.is_top_of_is_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirectedOn.is_top_of_is_max {s : Set α} (hd : DirectedOn (· <= ·) s) {m} (
hm : m in s) (hmax : forall a in s, m <= a -> a <= m) : forall a in s, a <= m
参数：hd : DirectedOn (· <= ·) s；hm : m in s；hmax : forall a in s, m <= a -> a <= m
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma DirectedOn.is_top_of_is_max {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    {m} (hm : m ∈ s) (hmax : ∀ a ∈ s, m ≤ a → a ≤ m) : ∀ a ∈ s, a ≤ m := fun a as ↦
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  xa.trans (hmax x xs xm)

@[to_dual isBot_or_exists_lt]
/-
**isTop_or_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTop_or_exists_gt [IsDirectedOrder α] (a : α) : IsTop a ∨ exists b, a < b
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `IsMax.isTop`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [IsDirectedOrd
er α], IsMax a → IsTop a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem isTop_or_exists_gt [IsDirectedOrder α] (a : α) : IsTop a ∨ ∃ b, a < b :=
  (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp

@[to_dual]
/-
**isTop_iff_isMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTop_iff_isMax [IsDirectedOrder α] : IsTop a ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTop.isMax`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsTop a → IsMax a
· 使用定理 `IsMax.isTop`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [IsDirectedOrd
er α], IsMax a → IsTop a
-/
theorem isTop_iff_isMax [IsDirectedOrder α] : IsTop a ↔ IsMax a :=
  ⟨IsTop.isMax, IsMax.isTop⟩

/-- If `f` is monotone, `g` is antitone, and `f ≤ g`, then for all `a`, `b` we have `f a ≤ g b`. -/
/-
**Monotone.forall_le_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.forall_le_of_antitone [IsDirectedOrder α] [Preorder β] {f g : α -
> β} (hf : Monotone f) (hg : Antitone g) (h : f <= g) (m n : α) : f m <= g n
参数：hf : Monotone f；hg : Antitone g；h : f <= g；m n : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c

--- 原说明 ---
If `f` is monotone, `g` is antitone, and `f ≤ g`, then for all `a`, `b` we have 
`f a ≤ g b`.
-/
theorem Monotone.forall_le_of_antitone [IsDirectedOrder α] [Preorder β] {f g : α → β}
    (hf : Monotone f) (hg : Antitone g) (h : f ≤ g) (m n : α) : f m ≤ g n := by
  obtain ⟨k, hkm, hkn⟩ := exists_ge_ge m n
  calc
    f m ≤ f k := hf hkm
    _ ≤ g k := h _
    _ ≤ g n := hg hkn

end Preorder

section PartialOrder

variable [PartialOrder β]

section Nontrivial

variable [Nontrivial β]

variable (β) in
@[to_dual exists_lt_of_directed_le]
/-
**exists_lt_of_directed_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_directed_ge [IsCodirectedOrder β] : exists a b : β, a < b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `isBot_or_exists_lt`：∀ {α : Type u_1} [inst : Preorder α] [IsCodirectedOr
der α] (a : α), IsBot a ∨ ∃ b, b < a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem exists_lt_of_directed_ge [IsCodirectedOrder β] :
    ∃ a b : β, a < b := by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]

@[to_dual]
/-
**IsMax.not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `IsMax`。
形式化陈述：∀ {β : Type u_2} [inst : PartialOrder β] [Nontrivial β] [IsDirectedOrder β
] {b : β}, IsMax b → ¬IsMin b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_directed_le`：∀ (β : Type u_2) [inst : PartialOrder β] [Nont
rivial β] [IsDirectedOrder β], ∃ a b, b < a
· 使用定理 `IsMax.isTop`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [IsDirectedOrd
er α], IsMax a → IsTop a
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
protected theorem IsMax.not_isMin [IsDirectedOrder β] {b : β} (hb : IsMax b) : ¬ IsMin b := by
  intro hb'
  obtain ⟨a, c, hac⟩ := exists_lt_of_directed_le β
  have := hb.isTop a
  obtain rfl := (hb' <| this).antisymm this
  exact hb'.not_lt hac

@[to_dual]
/-
**IsMin.not_isMax'** 是 Mathlib 中的一个定理，位于命名空间 `IsMin`。
形式化陈述：∀ {β : Type u_2} [inst : PartialOrder β] [Nontrivial β] [IsDirectedOrder β
] {b : β}, IsMin b → ¬IsMax b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_isMax`：∀ {β : Type u_2} [inst : PartialOrder β] [Nontrivial β]
 [IsCodirectedOrder β] {b : β}, IsMin b → ¬IsMax b
· 使用定理 `OrderDual.instNontrivial`：∀ {α : Type u_1} [h : Nontrivial α], Nontrivia
l αᵒᵈ
· 使用定理 `IsMax.toDual`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsMax a → IsMin (O
rderDual.toDual a)
· 使用定理 `IsMin.toDual`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsMin a → IsMax (O
rderDual.toDual a)
-/
protected theorem IsMin.not_isMax' [IsDirectedOrder β] {b : β} (hb : IsMin b) : ¬ IsMax b :=
  fun hb' ↦ hb'.toDual.not_isMax hb.toDual

end Nontrivial

variable [Preorder α] {f : α → β} {s : Set α}

-- TODO: Generalise the following two lemmas to connected orders

/-- If `f` is monotone and antitone on a directed order, then `f` is constant. -/
/-
**constant_of_monotone_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：constant_of_monotone_antitone [IsDirectedOrder α] (hf : Monotone f) (hf' :
 Antitone f) (a b : α) : f a = f b
参数：hf : Monotone f；hf' : Antitone f；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.forall_le_of_antitone`：Monotone.forall_le_of_antitone [IsDirect
edOrder α] [Preorder β] {f g : α -> β} (hf : Monotone f) (hg : Antitone g) (h : 
f <= g) (m n : α) : …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
If `f` is monotone and antitone on a directed order, then `f` is constant.
-/
lemma constant_of_monotone_antitone [IsDirectedOrder α] (hf : Monotone f) (hf' : Antitone f)
    (a b : α) : f a = f b := by
  have := hf.forall_le_of_antitone hf' le_rfl
  exact le_antisymm (this a b) (this b a)

/-- If `f` is monotone and antitone on a directed set `s`, then `f` is constant on `s`. -/
/-
**constant_of_monotoneOn_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：constant_of_monotoneOn_antitoneOn (hf : MonotoneOn f s) (hf' : AntitoneOn 
f s) (hs : DirectedOn (· <= ·) s) : forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> 
f a = f b
参数：hf : MonotoneOn f s；hf' : AntitoneOn f s；hs : DirectedOn (· <= ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If `f` is monotone and antitone on a directed set `s`, then `f` is constant on `
s`.
-/
lemma constant_of_monotoneOn_antitoneOn (hf : MonotoneOn f s) (hf' : AntitoneOn f s)
    (hs : DirectedOn (· ≤ ·) s) : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → f a = f b := by
  rintro a ha b hb
  obtain ⟨c, hc, hac, hbc⟩ := hs _ ha _ hb
  exact le_antisymm ((hf ha hc hac).trans <| hf' hb hc hbc) ((hf hb hc hbc).trans <| hf' ha hc hac)

end PartialOrder

-- see Note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SemilatticeSup.instIsDirectedOrder [SemilatticeSup α] :
    IsDirectedOrder α :=
  ⟨fun a b => ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩

-- see Note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderTop.instIsDirectedOrder [LE α] [OrderTop α] : IsDirectedOrder α :=
  ⟨fun _ _ => ⟨⊤, le_top _, le_top _⟩⟩

namespace DirectedOn

section Pi

variable {ι : Type*} {α : ι → Type*} {r : (i : ι) → α i → α i → Prop}

/-
**DirectedOn.proj** 是 Mathlib 中的一个引理，位于命名空间 `DirectedOn`。
形式化陈述：proj {d : Set (Π i, α i)} (hd : DirectedOn (fun x y => forall i, r i (x i)
 (y i)) d) (i : ι) : DirectedOn (r i) ((fun a => a i) '' d)
参数：Π i, α i；hd : DirectedOn (fun x y => forall i, r i (x i) (y i)) d；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `DirectedOn.mono`：DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : f
orall ⦃a b⦄, r a b -> r' a b) : DirectedOn r' s
-/
lemma proj {d : Set (Π i, α i)} (hd : DirectedOn (fun x y => ∀ i, r i (x i) (y i)) d) (i : ι) :
    DirectedOn (r i) ((fun a => a i) '' d) :=
  DirectedOn.mono_comp (fun _ _ h => h) (mono hd fun ⦃_ _⦄ h ↦ h i)
/-
**DirectedOn.pi** 是 Mathlib 中的一个引理，位于命名空间 `DirectedOn`。
形式化陈述：pi {d : (i : ι) -> Set (α i)} (hd : forall (i : ι), DirectedOn (r i) (d i)
) : DirectedOn (fun x y => forall i, r i (x i) (y i)) (Set.pi Set.univ d)
参数：i : ι；α i；hd : forall (i : ι), DirectedOn (r i) (d i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `trivial`：True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma pi {d : (i : ι) → Set (α i)} (hd : ∀ (i : ι), DirectedOn (r i) (d i)) :
    DirectedOn (fun x y => ∀ i, r i (x i) (y i)) (Set.pi Set.univ d) := by
  intro a ha b hb
  choose f hfd haf hbf using fun i => hd i (a i) (ha i trivial) (b i) (hb i trivial)
  exact ⟨f, fun i _ => hfd i, haf, hbf⟩

end Pi

section Prod

variable {r₂ : β → β → Prop}

/-- Local notation for a relation -/
local infixl:50 " ≼₁ " => r
/-- Local notation for a relation -/
local infixl:50 " ≼₂ " => r₂

/-
**DirectedOn.fst** 是 Mathlib 中的一个引理，位于命名空间 `DirectedOn`。
形式化陈述：fst {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2
) d) : DirectedOn (· ≼₁ ·) (Prod.fst '' d)
参数：α × β；hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `DirectedOn.mono`：DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : f
orall ⦃a b⦄, r a b -> r' a b) : DirectedOn r' s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma fst {d : Set (α × β)} (hd : DirectedOn (fun p q ↦ p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d) :
    DirectedOn (· ≼₁ ·) (Prod.fst '' d) :=
  DirectedOn.mono_comp (fun ⦃_ _⦄ h ↦ h) (mono hd fun ⦃_ _⦄ h ↦ h.1)
/-
**DirectedOn.snd** 是 Mathlib 中的一个引理，位于命名空间 `DirectedOn`。
形式化陈述：snd {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2
) d) : DirectedOn (· ≼₂ ·) (Prod.snd '' d)
参数：α × β；hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `DirectedOn.mono`：DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : f
orall ⦃a b⦄, r a b -> r' a b) : DirectedOn r' s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma snd {d : Set (α × β)} (hd : DirectedOn (fun p q ↦ p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d) :
    DirectedOn (· ≼₂ ·) (Prod.snd '' d) :=
  DirectedOn.mono_comp (fun ⦃_ _⦄ h ↦ h) (mono hd fun ⦃_ _⦄ h ↦ h.2)
/-
**DirectedOn.prod** 是 Mathlib 中的一个引理，位于命名空间 `DirectedOn`。
形式化陈述：prod {d₁ : Set α} {d₂ : Set β} (h₁ : DirectedOn (· ≼₁ ·) d₁) (h₂ : Directe
dOn (· ≼₂ ·) d₂) : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) (d₁ ×ˢ d₂)
参数：h₁ : DirectedOn (· ≼₁ ·) d₁；h₂ : DirectedOn (· ≼₂ ·) d₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma prod {d₁ : Set α} {d₂ : Set β} (h₁ : DirectedOn (· ≼₁ ·) d₁) (h₂ : DirectedOn (· ≼₂ ·) d₂) :
    DirectedOn (fun p q ↦ p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) (d₁ ×ˢ d₂) := fun _ hpd _ hqd => by
  obtain ⟨r₁, hdr₁, hpr₁, hqr₁⟩ := h₁ _ hpd.1 _ hqd.1
  obtain ⟨r₂, hdr₂, hpr₂, hqr₂⟩ := h₂ _ hpd.2 _ hqd.2
  exact ⟨⟨r₁, r₂⟩, ⟨hdr₁, hdr₂⟩, ⟨hpr₁, hpr₂⟩, ⟨hqr₁, hqr₂⟩⟩

end Prod

end DirectedOn

