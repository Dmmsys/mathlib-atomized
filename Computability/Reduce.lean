/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Computability.Halting

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notation

This file uses the local notation `⊕'` for `Sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/

@[expose] public section


universe u v w

open Function

/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
/-
**ManyOneReducible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q 
: β -> Prop)
参数：p : α -> Prop；q : β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p` is many-one reducible to `q` if there is a computable function translating q
uestions about `p`
to questions about `q`.
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)

@[inherit_doc ManyOneReducible]
infixl:1000 " ≤₀ " => ManyOneReducible
/-
**ManyOneReducible.mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q 
: β -> Prop) (h : Computable f) : (fun a => q (f a)) <=₀ q
参数：q : β -> Prop；h : Computable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) : (fun a => q (f a)) ≤₀ q :=
  ⟨f, h, fun _ => Iff.rfl⟩

@[refl]
/-
**manyOneReducible_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：manyOneReducible_refl {α} [Primcodable α] (p : α -> Prop) : p <=₀ p
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.id`：∀ {α : Type u_1} [inst : Primcodable α], Computable id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem manyOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₀ p :=
  ⟨id, Computable.id, by simp⟩

@[trans]
/-
**ManyOneReducible.trans** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneReducible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → Prop} {q : β → Prop} {r
 : γ → Prop}, p ≤₀ q → q ≤₀ r → p ≤₀ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁,
      fun a => ⟨fun h => by rw [comp_apply, ← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩
/-
**stdRefl_manyOneReducible** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：stdRefl_manyOneReducible {α} [Primcodable α] : Std.Refl (@ManyOneReducible
 α α _ _) where refl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `manyOneReducible_refl`：manyOneReducible_refl {α} [Primcodable α] (p : α 
-> Prop) : p <=₀ p
-/
instance stdRefl_manyOneReducible {α} [Primcodable α] : Std.Refl (@ManyOneReducible α α _ _) where
  refl := manyOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_manyOneReducible := stdRefl_manyOneReducible
/-
**isTrans_manyOneReducible** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isTrans_manyOneReducible {α} [Primcodable α] : IsTrans (α -> Prop) ManyOne
Reducible where trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
-/
instance isTrans_manyOneReducible {α} [Primcodable α] : IsTrans (α → Prop) ManyOneReducible where
  trans _ _ _ := ManyOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_manyOneReducible := isTrans_manyOneReducible

/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
/-
**OneOneReducible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q :
 β -> Prop)
参数：p : α -> Prop；q : β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p` is one-one reducible to `q` if there is an injective computable function tra
nslating questions
about `p` to questions about `q`.
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ Injective f ∧ ∀ a, p a ↔ q (f a)

@[inherit_doc OneOneReducible]
infixl:1000 " ≤₁ " => OneOneReducible
/-
**OneOneReducible.mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q :
 β -> Prop) (h : Computable f) (i : Injective f) : (fun a => q (f a)) <=₁ q
参数：q : β -> Prop；h : Computable f；i : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) (i : Injective f) : (fun a => q (f a)) ≤₁ q :=
  ⟨f, h, i, fun _ => Iff.rfl⟩

@[refl]
/-
**oneOneReducible_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：oneOneReducible_refl {α} [Primcodable α] (p : α -> Prop) : p <=₁ p
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.id`：∀ {α : Type u_1} [inst : Primcodable α], Computable id
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem oneOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₁ p :=
  ⟨id, Computable.id, injective_id, by simp⟩

@[trans]
/-
**OneOneReducible.trans** 是 Mathlib 中的一个定理，位于命名空间 `OneOneReducible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → Prop} {q : β → Prop} {r
 : γ → Prop}, p ≤₁ q → q ≤₁ r → p ≤₁ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by rw [comp_apply, ← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩
/-
**OneOneReducible.to_many_one** 是 Mathlib 中的一个定理，位于命名空间 `OneOneReducible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β] {p : α → Prop} {q : β → Prop},   p ≤₁ q → p ≤₀ q
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ q → p ≤₀ q
  | ⟨f, c, _, h⟩ => ⟨f, c, h⟩
/-
**OneOneReducible.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
 (q : β -> Prop) (h : Computable e) : (q ∘ e) <=₁ q
参数：q : β -> Prop；h : Computable e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.mk`：OneOneReducible.mk {α β} [Primcodable α] [Primcodabl
e β] {f : α -> β} (q : β -> Prop) (h : Computable f) (i : Injective f) : (fun a 
=> q (f …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop)
    (h : Computable e) : (q ∘ e) ≤₁ q :=
  OneOneReducible.mk _ h e.injective
/-
**OneOneReducible.of_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α
 ≃ β} (q : β -> Prop) (h : Computable e.symm) : q <=₁ (q ∘ e)
参数：q : β -> Prop；h : Computable e.symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OneOneReducible.of_equiv`：OneOneReducible.of_equiv {α β} [Primcodable α]
 [Primcodable β] {e : α ≃ β} (q : β -> Prop) (h : Computable e) : (q ∘ e) <=₁ q
-/
theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
    (q : β → Prop) (h : Computable e.symm) : q ≤₁ (q ∘ e) := by
  convert! OneOneReducible.of_equiv _ h; funext; simp
/-
**stdRefl_oneOneReducible** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：stdRefl_oneOneReducible {α} [Primcodable α] : Std.Refl (@OneOneReducible α
 α _ _) where refl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `oneOneReducible_refl`：oneOneReducible_refl {α} [Primcodable α] (p : α ->
 Prop) : p <=₁ p
-/
instance stdRefl_oneOneReducible {α} [Primcodable α] : Std.Refl (@OneOneReducible α α _ _) where
  refl := oneOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_oneOneReducible := stdRefl_oneOneReducible
/-
**isTrans_oneOneReducible** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isTrans_oneOneReducible {α} [Primcodable α] : IsTrans (α -> Prop) OneOneRe
ducible where trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α 
→ Prop} {q …
-/
instance isTrans_oneOneReducible {α} [Primcodable α] : IsTrans (α → Prop) OneOneReducible where
  trans _ _ _ := OneOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_oneOneReducible := isTrans_oneOneReducible

namespace ComputablePred

variable {α : Type*} {β : Type*} [Primcodable α] [Primcodable β]

open Computable

/-
**ComputablePred.computable_of_manyOneReducible** 是 Mathlib 中的一个定理，位于命名空间 `Compu
tablePred`。
形式化陈述：computable_of_manyOneReducible {p : α -> Prop} {q : β -> Prop} (h₁ : p <=₀
 q) (h₂ : ComputablePred q) : ComputablePred p
参数：h₁ : p <=₀ q；h₂ : ComputablePred q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ComputablePred.computable_iff`：computable_iff {p : α -> Prop} : Computab
lePred p ↔ exists f : α -> Bool, Computable f ∧ p = fun a => (f a : Prop)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem computable_of_manyOneReducible {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q)
    (h₂ : ComputablePred q) : ComputablePred p := by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact ⟨by infer_instance, by simpa using hg.comp c⟩
/-
**ComputablePred.computable_of_oneOneReducible** 是 Mathlib 中的一个定理，位于命名空间 `Comput
ablePred`。
形式化陈述：computable_of_oneOneReducible {p : α -> Prop} {q : β -> Prop} (h : p <=₁ q
) : ComputablePred q -> ComputablePred p
参数：h : p <=₁ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComputablePred.computable_of_manyOneReducible`：computable_of_manyOneRedu
cible {p : α -> Prop} {q : β -> Prop} (h₁ : p <=₀ q) (h₂ : ComputablePred q) : C
omputablePred p
· 使用定理 `OneOneReducible.to_many_one`：∀ {α : Type u_1} {β : Type u_2} [inst : Pri
mcodable α] [inst_1 : Primcodable β] {p : α → Prop} {q : β → Prop},   p ≤₁ q → p
 ≤₀ q
-/
theorem computable_of_oneOneReducible {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) :
    ComputablePred q → ComputablePred p :=
  computable_of_manyOneReducible h.to_many_one

end ComputablePred

/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
/-
**ManyOneEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β 
-> Prop)
参数：p : α -> Prop；q : β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p` and `q` are many-one equivalent if each one is many-one reducible to the oth
er.
-/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₀ q ∧ q ≤₀ p

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
/-
**OneOneEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -
> Prop)
参数：p : α -> Prop；q : β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p` and `q` are one-one equivalent if each one is one-one reducible to the other
.
-/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₁ q ∧ q ≤₁ p

@[refl]
/-
**manyOneEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：manyOneEquiv_refl {α} [Primcodable α] (p : α -> Prop) : ManyOneEquiv p p
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `manyOneReducible_refl`：manyOneReducible_refl {α} [Primcodable α] (p : α 
-> Prop) : p <=₀ p
-/
theorem manyOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : ManyOneEquiv p p :=
  ⟨manyOneReducible_refl _, manyOneReducible_refl _⟩

@[symm]
/-
**ManyOneEquiv.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α -> Prop} {q
 : β -> Prop} : ManyOneEquiv p q -> ManyOneEquiv q p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    ManyOneEquiv p q → ManyOneEquiv q p :=
  And.symm

@[trans]
/-
**ManyOneEquiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → Prop} {q : β → Prop} {r
 : γ → Prop}, ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
-/
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
/-
**equivalence_of_manyOneEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivalence_of_manyOneEquiv {α} [Primcodable α] : Equivalence (@ManyOneEqu
iv α α _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `manyOneEquiv_refl`：manyOneEquiv_refl {α} [Primcodable α] (p : α -> Prop)
 : ManyOneEquiv p p
· 使用定理 `ManyOneEquiv.symm`：ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable 
β] {p : α -> Prop} {q : β -> Prop} : ManyOneEquiv p q -> ManyOneEquiv q p
· 使用定理 `ManyOneEquiv.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → P
rop} {q …
-/
theorem equivalence_of_manyOneEquiv {α} [Primcodable α] : Equivalence (@ManyOneEquiv α α _ _) :=
  ⟨manyOneEquiv_refl, fun {_ _} => ManyOneEquiv.symm, fun {_ _ _} => ManyOneEquiv.trans⟩

@[refl]
/-
**oneOneEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：oneOneEquiv_refl {α} [Primcodable α] (p : α -> Prop) : OneOneEquiv p p
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `oneOneReducible_refl`：oneOneReducible_refl {α} [Primcodable α] (p : α ->
 Prop) : p <=₁ p
-/
theorem oneOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : OneOneEquiv p p :=
  ⟨oneOneReducible_refl _, oneOneReducible_refl _⟩

@[symm]
/-
**OneOneEquiv.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α -> Prop} {q 
: β -> Prop} : OneOneEquiv p q -> OneOneEquiv q p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → OneOneEquiv q p :=
  And.symm

@[trans]
/-
**OneOneEquiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `OneOneEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → Prop} {q : β → Prop} {r
 : γ → Prop}, OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α 
→ Prop} {q …
-/
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
/-
**equivalence_of_oneOneEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivalence_of_oneOneEquiv {α} [Primcodable α] : Equivalence (@OneOneEquiv
 α α _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `oneOneEquiv_refl`：oneOneEquiv_refl {α} [Primcodable α] (p : α -> Prop) :
 OneOneEquiv p p
· 使用定理 `OneOneEquiv.symm`：OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β]
 {p : α -> Prop} {q : β -> Prop} : OneOneEquiv p q -> OneOneEquiv q p
· 使用定理 `OneOneEquiv.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → Pr
op} {q …
-/
theorem equivalence_of_oneOneEquiv {α} [Primcodable α] : Equivalence (@OneOneEquiv α α _ _) :=
  ⟨oneOneEquiv_refl, fun {_ _} => OneOneEquiv.symm, fun {_ _ _} => OneOneEquiv.trans⟩
/-
**OneOneEquiv.to_many_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α -> Pr
op} {q : β -> Prop} : OneOneEquiv p q -> ManyOneEquiv p q | ⟨pq, qp⟩ => ⟨pq.to_m
any_one, qp.to_many_one⟩  /-- a computable bijection -/ nonrec def Equiv.Computa
ble {α β} [Primcodable α] [Primcodable β] (e : α ≃ β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.to_many_one`：∀ {α : Type u_1} {β : Type u_2} [inst : Pri
mcodable α] [inst_1 : Primcodable β] {p : α → Prop} {q : β → Prop},   p ≤₁ q → p
 ≤₀ q
-/
theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : OneOneEquiv p q → ManyOneEquiv p q
  | ⟨pq, qp⟩ => ⟨pq.to_many_one, qp.to_many_one⟩

/-- a computable bijection -/
nonrec def Equiv.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm

/-
**Equiv.Computable.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} : 
e.Computable -> e.symm.Computable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
    e.Computable → e.symm.Computable :=
  And.symm
/-
**Equiv.Computable.trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Computable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable γ]   {e₁ : α ≃ β} {e₂ : β ≃ γ}, e₁.Co
mputable → e₂.Computable → (e₁.trans e₂).Computable
参数：e₁.trans e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
-/
theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
    {e₂ : β ≃ γ} : e₁.Computable → e₂.Computable → (e₁.trans e₂).Computable
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => ⟨l₂.comp l₁, r₁.comp r₂⟩
/-
**Computable.eqv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Computable.encode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.encode
· 使用定理 `Computable.ofNat`：∀ (α : Type u_5) [inst : Denumerable α], Computable (D
enumerable.ofNat α)
-/
theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable :=
  ⟨Computable.encode, Computable.ofNat _⟩
/-
**Computable.equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] :
    (Denumerable.equiv₂ α β).Computable :=
  (Computable.eqv _).trans (Computable.eqv _).symm
/-
**OneOneEquiv.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h 
: e.Computable) {p} : OneOneEquiv (p ∘ e) p
参数：h : e.Computable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.of_equiv`：OneOneReducible.of_equiv {α β} [Primcodable α]
 [Primcodable β] {e : α ≃ β} (q : β -> Prop) (h : Computable e) : (q ∘ e) <=₁ q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `OneOneReducible.of_equiv_symm`：OneOneReducible.of_equiv_symm {α β} [Prim
codable α] [Primcodable β] {e : α ≃ β} (q : β -> Prop) (h : Computable e.symm) :
 q <=₁ (q ∘ e)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩
/-
**ManyOneEquiv.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h
 : e.Computable) {p} : ManyOneEquiv (p ∘ e) p
参数：h : e.Computable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneEquiv.to_many_one`：OneOneEquiv.to_many_one {α β} [Primcodable α] [
Primcodable β] {p : α -> Prop} {q : β -> Prop} : OneOneEquiv p q -> ManyOneEquiv
 p q | ⟨pq, q…
· 使用定理 `OneOneEquiv.of_equiv`：OneOneEquiv.of_equiv {α β} [Primcodable α] [Primco
dable β] {e : α ≃ β} (h : e.Computable) {p} : OneOneEquiv (p ∘ e) p
-/
theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : ManyOneEquiv (p ∘ e) p :=
  (OneOneEquiv.of_equiv h).to_many_one
/-
**ManyOneEquiv.le_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primco
dable γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv p q) 
: p <=₀ r ↔ q <=₀ r
参数：h : ManyOneEquiv p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) : p ≤₀ r ↔ q ≤₀ r :=
  ⟨h.2.trans, h.1.trans⟩
/-
**ManyOneEquiv.le_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primc
odable γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv q r)
 : p <=₀ q ↔ p <=₀ r
参数：h : ManyOneEquiv q r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) : p ≤₀ q ↔ p ≤₀ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
/-
**OneOneEquiv.le_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcod
able γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv p q) : 
p <=₁ r ↔ q <=₁ r
参数：h : OneOneEquiv p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α 
→ Prop} {q …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) : p ≤₁ r ↔ q ≤₁ r :=
  ⟨h.2.trans, h.1.trans⟩
/-
**OneOneEquiv.le_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primco
dable γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv q r) :
 p <=₁ q ↔ p <=₁ r
参数：h : OneOneEquiv q r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α 
→ Prop} {q …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) : p ≤₁ q ↔ p ≤₁ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
/-
**ManyOneEquiv.congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodab
le γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv p q) : M
anyOneEquiv p r ↔ ManyOneEquiv q r
参数：h : ManyOneEquiv p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `ManyOneEquiv.le_congr_left`：ManyOneEquiv.le_congr_left {α β γ} [Primcoda
ble α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ ->
 Prop} (h : Many…
· 使用定理 `ManyOneEquiv.le_congr_right`：ManyOneEquiv.le_congr_right {α β γ} [Primco
dable α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ 
-> Prop} (h : Man…
-/
theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) :
    ManyOneEquiv p r ↔ ManyOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
/-
**ManyOneEquiv.congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcoda
ble γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv q r) : 
ManyOneEquiv p q ↔ ManyOneEquiv p r
参数：h : ManyOneEquiv q r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `ManyOneEquiv.le_congr_right`：ManyOneEquiv.le_congr_right {α β γ} [Primco
dable α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ 
-> Prop} (h : Man…
· 使用定理 `ManyOneEquiv.le_congr_left`：ManyOneEquiv.le_congr_left {α β γ} [Primcoda
ble α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ ->
 Prop} (h : Many…
-/
theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) :
    ManyOneEquiv p q ↔ ManyOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
/-
**OneOneEquiv.congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodabl
e γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv p q) : One
OneEquiv p r ↔ OneOneEquiv q r
参数：h : OneOneEquiv p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `OneOneEquiv.le_congr_left`：OneOneEquiv.le_congr_left {α β γ} [Primcodabl
e α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> P
rop} (h : OneOn…
· 使用定理 `OneOneEquiv.le_congr_right`：OneOneEquiv.le_congr_right {α β γ} [Primcoda
ble α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ ->
 Prop} (h : OneO…
-/
theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) :
    OneOneEquiv p r ↔ OneOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
/-
**OneOneEquiv.congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodab
le γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv q r) : On
eOneEquiv p q ↔ OneOneEquiv p r
参数：h : OneOneEquiv q r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `OneOneEquiv.le_congr_right`：OneOneEquiv.le_congr_right {α β γ} [Primcoda
ble α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ ->
 Prop} (h : OneO…
· 使用定理 `OneOneEquiv.le_congr_left`：OneOneEquiv.le_congr_left {α β γ} [Primcodabl
e α] [Primcodable β] [Primcodable γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> P
rop} (h : OneOn…
-/
theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) :
    OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left

@[simp]
/-
**ULower.down_computable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ULower.down_computable {α} [Primcodable α] : (ULower.equiv α).Computable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.ulower_down`：ulower_down : Primrec (ULower.down : α -> ULower α)
· 使用定理 `Primrec.ulower_up`：ulower_up : Primrec (ULower.up : ULower α -> α)
-/
theorem ULower.down_computable {α} [Primcodable α] : (ULower.equiv α).Computable :=
  ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩
/-
**manyOneEquiv_up** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：manyOneEquiv_up {α} [Primcodable α] {p : α -> Prop} : ManyOneEquiv (p ∘ UL
ower.up) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneEquiv.of_equiv`：ManyOneEquiv.of_equiv {α β} [Primcodable α] [Prim
codable β] {e : α ≃ β} (h : e.Computable) {p} : ManyOneEquiv (p ∘ e) p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Computable.symm`：Equiv.Computable.symm {α β} [Primcodable α] [Prim
codable β] {e : α ≃ β} : e.Computable -> e.symm.Computable
· 使用定理 `ULower.down_computable`：ULower.down_computable {α} [Primcodable α] : (UL
ower.equiv α).Computable
-/
theorem manyOneEquiv_up {α} [Primcodable α] {p : α → Prop} : ManyOneEquiv (p ∘ ULower.up) p :=
  ManyOneEquiv.of_equiv ULower.down_computable.symm

local infixl:1001 " ⊕' " => Sum.elim

open Nat.Primrec
/-
**OneOneReducible.disjoin_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α 
-> Prop} {q : β -> Prop} : p <=₁ p oplus' q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.sumInl`：sumInl : Computable (@Sum.inl α β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sum.inl.inj_iff`：∀ {α : Type u_1} {β : Type u_2} {a b : α}, Sum.inl a = 
Sum.inl b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ p ⊕' q :=
  ⟨Sum.inl, Computable.sumInl, fun _ _ => Sum.inl.inj_iff.1, fun _ => Iff.rfl⟩
/-
**OneOneReducible.disjoin_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α
 -> Prop} {q : β -> Prop} : q <=₁ p oplus' q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.sumInr`：sumInr : Computable (@Sum.inr α β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sum.inr.inj_iff`：∀ {α : Type u_1} {β : Type u_2} {a b : β}, Sum.inr a = 
Sum.inr b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : q ≤₁ p ⊕' q :=
  ⟨Sum.inr, Computable.sumInr, fun _ _ => Sum.inr.inj_iff.1, fun _ => Iff.rfl⟩
/-
**disjoin_manyOneReducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α → Prop} {q : β → Prop} {r
 : γ → Prop}, p ≤₀ r → q ≤₀ r → Sum.elim p q ≤₀ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.sumCasesOn`：sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ}
 {h : α -> γ -> σ} (hf : Computable f) (hg : Computable₂ g) (hh : Computable₂ h)
 : @Computa…
· 使用定理 `Computable.id`：∀ {α : Type u_1} [inst : Primcodable α], Computable id
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoin_manyOneReducible {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ r → q ≤₀ r → (p ⊕' q) ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨Sum.elim f g,
      Computable.id.sumCasesOn (c₁.comp Computable.snd).to₂ (c₂.comp Computable.snd).to₂,
      fun x => by cases x <;> [apply h₁; apply h₂]⟩
/-
**disjoin_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α 
-> Prop} {q : β -> Prop} {r : γ -> Prop} : (p oplus' q) <=₀ r ↔ p <=₀ r ∧ q <=₀ 
r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
· 使用定理 `OneOneReducible.to_many_one`：∀ {α : Type u_1} {β : Type u_2} [inst : Pri
mcodable α] [inst_1 : Primcodable β] {p : α → Prop} {q : β → Prop},   p ≤₁ q → p
 ≤₀ q
· 使用定理 `OneOneReducible.disjoin_left`：OneOneReducible.disjoin_left {α β} [Primco
dable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop} : p <=₁ p oplus' q
· 使用定理 `OneOneReducible.disjoin_right`：OneOneReducible.disjoin_right {α β} [Prim
codable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop} : q <=₁ p oplus' q
· 使用定理 `disjoin_manyOneReducible`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 [inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p :
 α → Prop} {q …
-/
theorem disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : (p ⊕' q) ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r :=
  ⟨fun h =>
    ⟨OneOneReducible.disjoin_left.to_many_one.trans h,
      OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_manyOneReducible h₁ h₂⟩

variable {α : Type u} [Primcodable α] [Inhabited α] {β : Type v} [Primcodable β] [Inhabited β]

/-- Computable and injective mapping of predicates to sets of natural numbers.
-/
/-
**toNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toNat (p : Set α) : Set Nat
参数：p : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computable and injective mapping of predicates to sets of natural numbers.
-/
def toNat (p : Set α) : Set ℕ :=
  { n | p ((Encodable.decode (α := α) n).getD default) }

@[simp]
/-
**toNat_manyOneReducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toNat_manyOneReducible {p : Set α} : toNat p <=₀ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.option_getD`：option_getD {f : α -> Option β} {g : α -> β} (hf
 : Computable f) (hg : Computable g) : Computable fun a => (f a).getD (g a)
· 使用定理 `Computable.decode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.decode
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNat_manyOneReducible {p : Set α} : toNat p ≤₀ p :=
  ⟨fun n => (Encodable.decode (α := α) n).getD default,
    Computable.option_getD Computable.decode (Computable.const _), fun _ => Iff.rfl⟩

@[simp]
/-
**manyOneReducible_toNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：manyOneReducible_toNat {p : Set α} : p <=₀ toNat p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.encode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.encode
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem manyOneReducible_toNat {p : Set α} : p ≤₀ toNat p :=
  ⟨Encodable.encode, Computable.encode, by simp [toNat, Set.ofPred]⟩

@[simp]
/-
**manyOneReducible_toNat_toNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：manyOneReducible_toNat_toNat {p : Set α} {q : Set β} : toNat p <=₀ toNat q
 ↔ p <=₀ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
· 使用定理 `manyOneReducible_toNat`：manyOneReducible_toNat {p : Set α} : p <=₀ toNat
 p
· 使用定理 `toNat_manyOneReducible`：toNat_manyOneReducible {p : Set α} : toNat p <=₀
 p
-/
theorem manyOneReducible_toNat_toNat {p : Set α} {q : Set β} : toNat p ≤₀ toNat q ↔ p ≤₀ q :=
  ⟨fun h => manyOneReducible_toNat.trans (h.trans toNat_manyOneReducible), fun h =>
    toNat_manyOneReducible.trans (h.trans manyOneReducible_toNat)⟩

@[simp]
/-
**toNat_manyOneEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toNat_manyOneEquiv {p : Set α} : ManyOneEquiv (toNat p) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem toNat_manyOneEquiv {p : Set α} : ManyOneEquiv (toNat p) p := by simp [ManyOneEquiv]

@[simp]
/-
**manyOneEquiv_toNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：manyOneEquiv_toNat (p : Set α) (q : Set β) : ManyOneEquiv (toNat p) (toNat
 q) ↔ ManyOneEquiv p q
参数：p : Set α；q : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem manyOneEquiv_toNat (p : Set α) (q : Set β) :
    ManyOneEquiv (toNat p) (toNat q) ↔ ManyOneEquiv p q := by simp [ManyOneEquiv]

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
/-
**ManyOneDegree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ManyOneDegree : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A many-one degree is an equivalence class of sets up to many-one equivalence.
-/
def ManyOneDegree : Type :=
  Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set ℕ))

namespace ManyOneDegree

/-- The many-one degree of a set on a primcodable type. -/
/-
**ManyOneDegree.of** 是 Mathlib 中的一个定义，位于命名空间 `ManyOneDegree`。
形式化陈述：of (p : α -> Prop) : ManyOneDegree
参数：p : α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The many-one degree of a set on a primcodable type.
-/
def of (p : α → Prop) : ManyOneDegree :=
  Quotient.mk'' (toNat p)

@[elab_as_elim]
/-
**ManyOneDegree.ind_on** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：∀ {C : ManyOneDegree → Prop} (d : ManyOneDegree), (∀ (p : Set ℕ), C (ManyO
neDegree.of p)) → C d
参数：d : ManyOneDegree；∀ (p : Set ℕ), C (ManyOneDegree.of p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem ind_on {C : ManyOneDegree → Prop} (d : ManyOneDegree)
    (h : ∀ p : Set ℕ, C (of p)) : C d :=
  Quotient.inductionOn' d h

/-- Lifts a function on sets of natural numbers to many-one degrees. -/
/-
**ManyOneDegree.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `ManyOneDegree`。
形式化陈述：{φ : Sort u_1} → ManyOneDegree → (f : Set ℕ → φ) → (∀ (p q : ℕ → Prop), Ma
nyOneEquiv p q → f p = f q) → φ
参数：f : Set ℕ → φ；∀ (p q : ℕ → Prop), ManyOneEquiv p q → f p = f q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a function on sets of natural numbers to many-one degrees.
-/
protected abbrev liftOn {φ} (d : ManyOneDegree) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : φ :=
  Quotient.liftOn' d f h

@[simp]
/-
**ManyOneDegree.liftOn_eq** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：∀ {φ : Sort u_1} (p : Set ℕ) (f : Set ℕ → φ) (h : ∀ (p q : ℕ → Prop), Many
OneEquiv p q → f p = f q),   (ManyOneDegree.of p).liftOn f h = f p
参数：p : Set ℕ；f : Set ℕ → φ；h : ∀ (p q : ℕ → Prop), ManyOneEquiv p q → f p = f q；
ManyOneDegree.of p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem liftOn_eq {φ} (p : Set ℕ) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : (of p).liftOn f h = f p :=
  rfl

/-- Lifts a binary function on sets of natural numbers to many-one degrees. -/
@[reducible, simp]
/-
**ManyOneDegree.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `ManyOneDegree`。
形式化陈述：{φ : Sort u_1} → ManyOneDegree → (f : Set ℕ → φ) → (∀ (p q : ℕ → Prop), Ma
nyOneEquiv p q → f p = f q) → φ
参数：f : Set ℕ → φ；∀ (p q : ℕ → Prop), ManyOneEquiv p q → f p = f q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a binary function on sets of natural numbers to many-one degrees.
-/
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn (fun p => d₂.liftOn (f p) fun _ _ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      · assumption
      · rfl)

@[simp]
/-
**ManyOneDegree.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `ManyOneDegree`。
形式化陈述：{φ : Sort u_1} → ManyOneDegree → (f : Set ℕ → φ) → (∀ (p q : ℕ → Prop), Ma
nyOneEquiv p q → f p = f q) → φ
参数：f : Set ℕ → φ；∀ (p q : ℕ → Prop), ManyOneEquiv p q → f p = f q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem liftOn₂_eq {φ} (p q : Set ℕ) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ManyOneDegree.of_eq_of** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：of_eq_of {p : α -> Prop} {q : β -> Prop} : of p = of q ↔ ManyOneEquiv p q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ManyOneDegree.of.eq_1`：∀ {α : Type u} [inst : Primcodable α] [inst_1 : I
nhabited α] (p : α → Prop),   ManyOneDegree.of p = Quotient.mk'' (toNat p)
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ ManyOneEquiv p q := by
  rw [of, of, Quotient.eq'']
  simp
/-
**ManyOneDegree.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `ManyOneDegree`。
形式化陈述：instInhabited : Inhabited ManyOneDegree
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set ℕ)⟩

/-- For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
/-
**ManyOneDegree.instLE** 是 Mathlib 中的一个实例，位于命名空间 `ManyOneDegree`。
形式化陈述：instLE : LE ManyOneDegree
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one r
educible to the
sets in `d₂`.
-/
instance instLE : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· ≤₀ ·) fun _p₁ _p₂ _q₁ _q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[simp]
/-
**ManyOneDegree.of_le_of** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：of_le_of {p : α -> Prop} {q : β -> Prop} : of p <= of q ↔ p <=₀ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `manyOneReducible_toNat_toNat`：manyOneReducible_toNat_toNat {p : Set α} {
q : Set β} : toNat p <=₀ toNat q ↔ p <=₀ q
-/
theorem of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
  manyOneReducible_toNat_toNat

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-
**ManyOneDegree.le_refl** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_refl (d : ManyOneDegree) : d ≤ d := by
  induction d using ManyOneDegree.ind_on; simp; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-
**ManyOneDegree.le_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and]

set_option backward.privateInPublic true in
/-
**ManyOneDegree.le_trans** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ManyOneDegree.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `ManyOneDegree`。
形式化陈述：instPartialOrder : PartialOrder ManyOneDegree where le_refl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.Reduce.0.ManyOneDegree.le_refl`：∀ (d : Ma
nyOneDegree), d ≤ d
· 使用定理 `_private.Mathlib.Computability.Reduce.0.ManyOneDegree.le_trans`：∀ {d₁ d₂
 d₃ : ManyOneDegree}, d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃
· 使用定理 `_private.Mathlib.Computability.Reduce.0.ManyOneDegree.le_antisymm`：∀ {d₁
 d₂ : ManyOneDegree}, d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂
-/
instance instPartialOrder : PartialOrder ManyOneDegree where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
/-
**ManyOneDegree.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `ManyOneDegree`。
形式化陈述：instAdd : Add ManyOneDegree
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The join of two degrees, induced by the disjoint union of two underlying sets.
-/
instance instAdd : Add ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a ⊕' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hl₂.trans OneOneReducible.disjoin_right.to_many_one),
            disjoin_manyOneReducible (hr₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hr₂.trans OneOneReducible.disjoin_right.to_many_one)⟩)⟩

@[simp]
/-
**ManyOneDegree.add_of** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：add_of (p : Set α) (q : Set β) : of (p oplus' q) = of p + of q
参数：p : Set α；q : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ManyOneDegree.of_eq_of`：of_eq_of {p : α -> Prop} {q : β -> Prop} : of p 
= of q ↔ ManyOneEquiv p q
· 使用定理 `disjoin_manyOneReducible`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 [inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p :
 α → Prop} {q …
· 使用定理 `ManyOneReducible.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [
inst : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {p : α
 → Prop} {q …
· 使用定理 `manyOneReducible_toNat`：manyOneReducible_toNat {p : Set α} : p <=₀ toNat
 p
· 使用定理 `OneOneReducible.to_many_one`：∀ {α : Type u_1} {β : Type u_2} [inst : Pri
mcodable α] [inst_1 : Primcodable β] {p : α → Prop} {q : β → Prop},   p ≤₁ q → p
 ≤₀ q
· 使用定理 `OneOneReducible.disjoin_left`：OneOneReducible.disjoin_left {α β} [Primco
dable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop} : p <=₁ p oplus' q
· 使用定理 `OneOneReducible.disjoin_right`：OneOneReducible.disjoin_right {α β} [Prim
codable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop} : q <=₁ p oplus' q
· 使用定理 `toNat_manyOneReducible`：toNat_manyOneReducible {p : Set α} : toNat p <=₀
 p
-/
theorem add_of (p : Set α) (q : Set β) : of (p ⊕' q) = of p + of q :=
  of_eq_of.mpr
    ⟨disjoin_manyOneReducible
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_left.to_many_one)
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_manyOneReducible
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_left.to_many_one)
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_right.to_many_one)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ManyOneDegree.add_le** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：∀ {d₁ d₂ d₃ : ManyOneDegree}, d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneDegree.ind_on`：∀ {C : ManyOneDegree → Prop} (d : ManyOneDegree), 
(∀ (p : Set ℕ), C (ManyOneDegree.of p)) → C d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `disjoin_le`：disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcoda
ble γ] {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} : (p oplus' q) <=₀ r ↔ p 
…
-/
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le

@[simp]
/-
**ManyOneDegree.le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：∀ (d₁ d₂ : ManyOneDegree), d₁ ≤ d₁ + d₂
参数：d₁ d₂ : ManyOneDegree。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ManyOneDegree.add_le`：∀ {d₁ d₂ d₃ : ManyOneDegree}, d₁ + d₂ ≤ d₃ ↔ d₁ ≤ 
d₃ ∧ d₂ ≤ d₃
· 使用定理 `_private.Mathlib.Computability.Reduce.0.ManyOneDegree.le_refl`：∀ (d : Ma
nyOneDegree), d ≤ d
-/
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (le_refl _)).1

@[simp]
/-
**ManyOneDegree.le_add_right** 是 Mathlib 中的一个定理，位于命名空间 `ManyOneDegree`。
形式化陈述：∀ (d₁ d₂ : ManyOneDegree), d₂ ≤ d₁ + d₂
参数：d₁ d₂ : ManyOneDegree。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ManyOneDegree.add_le`：∀ {d₁ d₂ d₃ : ManyOneDegree}, d₁ + d₂ ≤ d₃ ↔ d₁ ≤ 
d₃ ∧ d₂ ≤ d₃
· 使用定理 `_private.Mathlib.Computability.Reduce.0.ManyOneDegree.le_refl`：∀ (d : Ma
nyOneDegree), d ≤ d
-/
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (le_refl _)).2
/-
**ManyOneDegree.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `ManyOneDegree`。
形式化陈述：instSemilatticeSup : SemilatticeSup ManyOneDegree
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ManyOneDegree.le_add_left`：∀ (d₁ d₂ : ManyOneDegree), d₁ ≤ d₁ + d₂
· 使用定理 `ManyOneDegree.le_add_right`：∀ (d₁ d₂ : ManyOneDegree), d₂ ≤ d₁ + d₂
-/
instance instSemilatticeSup : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun _ _ _ h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

end ManyOneDegree

