/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Countable and uncountable types

In this file we define a typeclass `Countable` saying that a given `Sort*` is countable
and a typeclass `Uncountable` saying that a given `Type*` is uncountable.

See also `Encodable` for a version that singles out
a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of these typeclasses.
More instances can be found in other files.
-/

public section

open Function

universe u v

variable {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/

/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
@[mk_iff countable_iff_exists_injective, wikidata Q66707394]
/-
**Countable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `α` is countable if there exists an injective map `α → ℕ`.
-/
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f
/-
**Countable.exists_injective_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Countable.exists_injective_nat (α : Sort u) [Countable α] : exists f : α -
> Nat, Injective f
参数：α : Sort u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.exists_injective_nat'`：∀ {α : Sort u} [self : Countable α], ∃ 
f, Function.Injective f
-/
lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable ℕ :=
  ⟨⟨id, injective_id⟩⟩

export Countable (exists_injective_nat)
/-
**Function.Injective.countable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [Countable β] {f : α → β}, Function.Injective 
f → Countable α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Countable.exists_injective_nat`：Countable.exists_injective_nat (α : Sort
 u) [Countable α] : exists f : α -> Nat, Injective f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
-/
protected theorem Function.Injective.countable [Countable β] {f : α → β} (hf : Injective f) :
    Countable α :=
  let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩
/-
**Function.Surjective.countable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [Countable α] {f : α → β}, Function.Surjective
 f → Countable β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
protected theorem Function.Surjective.countable [Countable α] {f : α → β} (hf : Surjective f) :
    Countable β :=
  (injective_surjInv hf).countable
/-
**exists_surjective_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : exists f :
 Nat -> α, Surjective f
参数：α : Sort u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Countable.exists_injective_nat`：Countable.exists_injective_nat (α : Sort
 u) [Countable α] : exists f : α -> Nat, Injective f
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
-/
theorem exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : ∃ f : ℕ → α, Surjective f :=
  let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩
/-
**countable_iff_exists_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_iff_exists_surjective [Nonempty α] : Countable α ↔ exists f : Na
t -> α, Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `Function.Surjective.countable`：∀ {α : Sort u} {β : Sort v} [Countable α]
 {f : α → β}, Function.Surjective f → Countable β
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem countable_iff_exists_surjective [Nonempty α] : Countable α ↔ ∃ f : ℕ → α, Surjective f :=
  ⟨@exists_surjective_nat _ _, fun ⟨_, hf⟩ ↦ hf.countable⟩
/-
**Countable.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Countable.of_equiv (α : Sort*) [Countable α] (e : α ≃ β) : Countable β
参数：α : Sort*；e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem Countable.of_equiv (α : Sort*) [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.injective.countable
/-
**Equiv.countable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Countable β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Countable β :=
  ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type v} [Countable β] : Countable (ULift.{u} β) :=
  Countable.of_equiv _ Equiv.ulift.symm

/-!
### Operations on `Sort*`s
-/


/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Operations on `Sort*`s
-/
instance [Countable α] : Countable (PLift α) :=
  Equiv.plift.injective.countable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Subsingleton.to_countable [Subsingleton α] : Countable α :=
  ⟨⟨fun _ => 0, fun x y _ => Subsingleton.elim x y⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 500) Subtype.countable [Countable α] {p : α → Prop} :
    Countable { x // p x } :=
  Subtype.val_injective.countable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Countable (Fin n) :=
  Function.Injective.countable (@Fin.eq_of_val_eq n)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Finite.to_countable [Finite α] : Countable α :=
  let ⟨_, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  Countable.of_equiv _ e.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable PUnit.{u} :=
  Subsingleton.to_countable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Prop.countable (p : Prop) : Countable p :=
  Subsingleton.to_countable
/-
**Bool.countable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.countable : Countable Bool
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.injective_iff`：injective_iff {α : Sort*} {f : Bool -> α} : Function
.Injective f ↔ f false != f true
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
-/
instance Bool.countable : Countable Bool :=
  ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩
/-
**Prop.countable'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.countable' : Countable Prop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Prop.countable' : Countable Prop :=
  Countable.of_equiv Bool Equiv.propEquivBool.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 500) Quotient.countable [Countable α] {r : α → α → Prop} :
    Countable (Quot r) :=
  Quot.mk_surjective.countable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 500) [Countable α] {s : Setoid α} : Countable (Quotient s) :=
  inferInstanceAs <| Countable (@Quot α _)

/-!
### Uncountable types
-/

/-- A type `α` is uncountable if it is not countable. -/
@[mk_iff uncountable_iff_not_countable]
/-
**Uncountable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u_1 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `α` is uncountable if it is not countable.
-/
class Uncountable (α : Sort*) : Prop where
  /-- A type `α` is uncountable if it is not countable. -/
  not_countable : ¬Countable α

@[push]
/-
**not_uncountable_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_uncountable_iff : ¬Uncountable α ↔ Countable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uncountable_iff_not_countable`：∀ (α : Sort u_1), Uncountable α ↔ ¬Counta
ble α
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma not_uncountable_iff : ¬Uncountable α ↔ Countable α := by
  rw [uncountable_iff_not_countable, not_not]

@[push]
/-
**not_countable_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_countable_iff : ¬Countable α ↔ Uncountable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `uncountable_iff_not_countable`：∀ (α : Sort u_1), Uncountable α ↔ ¬Counta
ble α
-/
lemma not_countable_iff : ¬Countable α ↔ Uncountable α := (uncountable_iff_not_countable α).symm

@[simp]
/-
**not_uncountable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_uncountable [Countable α] : ¬Uncountable α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `not_uncountable_iff`：not_uncountable_iff : ¬Uncountable α ↔ Countable α
-/
lemma not_uncountable [Countable α] : ¬Uncountable α := not_uncountable_iff.2 ‹_›

@[simp]
/-
**not_countable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_countable [Uncountable α] : ¬Countable α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Uncountable.not_countable`：∀ {α : Sort u_1} [self : Uncountable α], ¬Cou
ntable α
-/
lemma not_countable [Uncountable α] : ¬Countable α := Uncountable.not_countable
/-
**Function.Injective.uncountable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [Uncountable α] {f : α → β}, Function.Injectiv
e f → Uncountable β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_countable`：not_countable [Uncountable α] : ¬Countable α
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
-/
protected theorem Function.Injective.uncountable [Uncountable α] {f : α → β} (hf : Injective f) :
    Uncountable β :=
  ⟨fun _ ↦ not_countable hf.countable⟩
/-
**Function.Surjective.uncountable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective
`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [Uncountable β] {f : α → β}, Function.Surjecti
ve f → Uncountable α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
protected theorem Function.Surjective.uncountable [Uncountable β] {f : α → β} (hf : Surjective f) :
    Uncountable α := (injective_surjInv hf).uncountable
/-
**not_injective_uncountable_countable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_injective_uncountable_countable [Uncountable α] [Countable β] (f : α -
> β) : ¬Injective f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_countable`：not_countable [Uncountable α] : ¬Countable α
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
-/
lemma not_injective_uncountable_countable [Uncountable α] [Countable β] (f : α → β) :
    ¬Injective f := fun hf ↦ not_countable hf.countable
/-
**not_surjective_countable_uncountable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_surjective_countable_uncountable [Countable α] [Uncountable β] (f : α 
-> β) : ¬Surjective f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_countable`：not_countable [Uncountable α] : ¬Countable α
· 使用定理 `Function.Surjective.countable`：∀ {α : Sort u} {β : Sort v} [Countable α]
 {f : α → β}, Function.Surjective f → Countable β
-/
lemma not_surjective_countable_uncountable [Countable α] [Uncountable β] (f : α → β) :
    ¬Surjective f := fun hf ↦
  not_countable hf.countable
/-
**uncountable_iff_forall_not_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uncountable_iff_forall_not_surjective [Nonempty α] : Uncountable α ↔ foral
l f : Nat -> α, ¬Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_countable_iff`：not_countable_iff : ¬Countable α ↔ Uncountable α
· 使用定理 `countable_iff_exists_surjective`：countable_iff_exists_surjective [Nonemp
ty α] : Countable α ↔ exists f : Nat -> α, Surjective f
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uncountable_iff_forall_not_surjective [Nonempty α] :
    Uncountable α ↔ ∀ f : ℕ → α, ¬Surjective f := by
  rw [← not_countable_iff, countable_iff_exists_surjective, not_exists]
/-
**Uncountable.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Uncountable.of_equiv (α : Sort*) [Uncountable α] (e : α ≃ β) : Uncountable
 β
参数：α : Sort*；e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem Uncountable.of_equiv (α : Sort*) [Uncountable α] (e : α ≃ β) : Uncountable β :=
  e.injective.uncountable
/-
**Equiv.uncountable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.uncountable_iff (e : α ≃ β) : Uncountable α ↔ Uncountable β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Uncountable.of_equiv`：Uncountable.of_equiv (α : Sort*) [Uncountable α] (
e : α ≃ β) : Uncountable β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.uncountable_iff (e : α ≃ β) : Uncountable α ↔ Uncountable β :=
  ⟨fun h => @Uncountable.of_equiv _ _ h e, fun h => @Uncountable.of_equiv _ _ h e.symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type v} [Uncountable β] : Uncountable (ULift.{u} β) :=
  .of_equiv _ Equiv.ulift.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Uncountable α] : Uncountable (PLift α) :=
  .of_equiv _ Equiv.plift.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Uncountable α] : Infinite α :=
  ⟨fun _ ↦ not_countable (α := α) inferInstance⟩
