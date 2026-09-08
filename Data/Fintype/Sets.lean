/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.OfMap

/-!
# Subsets of finite types

In a `Fintype`, all `Set`s are automatically `Finset`s, and there are only finitely many of them.

## Main results

* `Set.toFinset`: convert a subset of a finite type to a `Finset`
* `Finset.fintypeCoeSort`: `((s : Finset α) : Type*)` is a finite type
* `Fintype.finsetEquivSet`: `Finset α` and `Set α` are equivalent if `α` is a `Fintype`
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

/-- Construct a finset enumerating a set `s`, given a `Fintype` instance. -/
/-
**Set.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：toFinset (s : Set α) [Fintype s] : Finset α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a finset enumerating a set `s`, given a `Fintype` instance.
-/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Function.Embedding.subtype _

@[congr]
/-
**Set.toFinset_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) : toFinse
t s = toFinset t
参数：h : s = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
theorem toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) :
    toFinset s = toFinset t := by subst h; congr!

@[simp, grind =]
/-
**Set.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.toFinset ↔ a in s
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_toFinset {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset ↔ a ∈ s := by
  simp [toFinset]

set_option backward.isDefEq.respectTransparency false in
/-- Many `Fintype` instances for sets are defined using an extensionally equal `Finset`.
Rewriting `s.toFinset` with `Set.toFinset_ofFinset` replaces the term with such a `Finset`. -/
/-
**Set.toFinset_ofFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in 
p) : @Set.toFinset _ p (Fintype.ofFinset s H) = s
参数：s : Finset α；H : forall x, x in s ↔ x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Many `Fintype` instances for sets are defined using an extensionally equal `Fins
et`.
Rewriting `s.toFinset` with `Set.toFinset_ofFinset` replaces the term with such 
a `Finset`.
-/
theorem toFinset_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Set.toFinset _ p (Fintype.ofFinset s H) = s :=
  Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]

/-- Membership of a set with a `Fintype` instance is decidable.

Using this as an instance leads to potential loops with `Subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
/-
**Set.decidableMemOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decida
ble (a in s)
参数：s : Set α；a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s

--- 原说明 ---
Membership of a set with a `Fintype` instance is decidable.

Using this as an instance leads to potential loops with `Subtype.fintype` under 
certain decidability
assumptions, so it should only be declared a local instance.
-/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a ∈ s) :=
  decidable_of_iff _ mem_toFinset

@[simp]
/-
**Set.coe_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_toFinset

@[simp]
/-
**Set.toFinset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonemp
ty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, coe_toFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_nonempty⟩ := toFinset_nonempty

@[simp]
/-
**Set.toFinset_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFins
et ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h]⟩

@[gcongr, mono]
/-
**Set.toFinset_subset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset subseteq t.t
oFinset ↔ s subseteq t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp [Finset.subset_iff, Set.subset_def]

@[simp]
/-
**Set.toFinset_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]

@[simp]
/-
**Set.subset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_toFinset {s : Finset α} [Fintype t] : s subseteq t.toFinset ↔ ↑s su
bseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_toFinset {s : Finset α} [Fintype t] : s ⊆ t.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]

@[simp]
/-
**Set.ssubset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]

@[gcongr, mono]
/-
**Set.toFinset_ssubset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinse
t ↔ s ⊂ t
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
theorem toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]

@[simp]
/-
**Set.toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_subset [Fintype s] {t : Finset α} : s.toFinset subseteq t ↔ s sub
seteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_subset [Fintype s] {t : Finset α} : s.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]

@[gcongr]
alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset

@[simp]
/-
**Set.disjoint_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_toFinset [Fintype s] [Fintype t] : Disjoint s.toFinset t.toFinset
 ↔ Disjoint s t
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
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_toFinset [Fintype s] [Fintype t] :
    Disjoint s.toFinset t.toFinset ↔ Disjoint s t := by simp only [← disjoint_coe, coe_toFinset]

@[simp]
/-
**Set.toFinset_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_nontrivial [Fintype s] : s.toFinset.Nontrivial ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nontrivial.eq_1`：∀ {α : Type u_1} (s : Finset α), s.Nontrivial = 
(↑s).Nontrivial
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_nontrivial [Fintype s] : s.toFinset.Nontrivial ↔ s.Nontrivial := by
  rw [Finset.Nontrivial, coe_toFinset]
/-
**Set.subsingleton_toFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_toFinset_iff [Fintype s] : Subsingleton s.toFinset ↔ s.Subsin
gleton
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
theorem subsingleton_toFinset_iff [Fintype s] : Subsingleton s.toFinset ↔ s.Subsingleton := by
  simp

section DecidableEq

variable [DecidableEq α] (s t) [Fintype s] [Fintype t]

@[simp]
/-
**Set.toFinset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_inter [Fintype (s inter t : Set _)] : (s inter t).toFinset = s.to
Finset inter t.toFinset
参数：s inter t : Set _。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_inter [Fintype (s ∩ t : Set _)] : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := by
  ext
  simp

@[simp]
/-
**Set.toFinset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_union [Fintype (s union t : Set _)] : (s union t).toFinset = s.to
Finset union t.toFinset
参数：s union t : Set _。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_union [Fintype (s ∪ t : Set _)] : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext
  simp

@[simp]
/-
**Set.toFinset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).toFinset = s.toFinset \
 t.toFinset
参数：s \ t : Set _。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff

open scoped symmDiff in
@[simp]
/-
**Set.toFinset_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_symmDiff [Fintype (s ∆ t : Set _)] : (s ∆ t).toFinset = s.toFinse
t ∆ t.toFinset
参数：s ∆ t : Set _。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_symmDiff [Fintype (s ∆ t : Set _)] :
    (s ∆ t).toFinset = s.toFinset ∆ t.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

@[simp]
/-
**Set.toFinset_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : sᶜ.toFinset = s.toFins
etᶜ
参数：sᶜ : Set _。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : sᶜ.toFinset = s.toFinsetᶜ := by
  ext
  simp

end DecidableEq

@[simp]
/-
**Set.toFinset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).toFinset = ∅
参数：∅ : Set α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).toFinset = ∅ := by
  ext
  simp

@[simp]
/-
**Set.toFinset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)] : (Set.univ : Set α
).toFinset = Finset.univ
参数：Set.univ : Set α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)] :
    (Set.univ : Set α).toFinset = Finset.univ := by
  ext
  simp

@[simp]
/-
**Set.toFinset_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_empty`：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).t
oFinset = ∅
· 使用定理 `Set.toFinset_inj`：toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s
.toFinset = t.toFinset ↔ s = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  let A : Fintype (∅ : Set α) := Fintype.ofIsEmpty
  rw [← toFinset_empty, toFinset_inj]

@[simp]
/-
**Set.toFinset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = 
univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = univ := by
  rw [← coe_inj, coe_toFinset, coe_univ]

@[simp]
/-
**Set.toFinset_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_ofPred [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype { x
 | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
参数：p : α -> Prop。
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_ofPred [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype { x | p x }] :
    Set.toFinset {x | p x} = Finset.univ.filter p := by
  ext
  simp

@[deprecated (since := "2026-07-09")] alias toFinset_setOf := toFinset_ofPred
/-
**Set.toFinset_ssubset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] : s.toFinset ⊂ F
inset.univ ↔ s ⊂ univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] :
    s.toFinset ⊂ Finset.univ ↔ s ⊂ univ := by simp

@[simp]
/-
**Set.toFinset_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_image [DecidableEq β] (f : α -> β) (s : Set α) [Fintype s] [Finty
pe (f '' s)] : (f '' s).toFinset = s.toFinset.image f
参数：f : α -> β；s : Set α；f '' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinset_image [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] [Fintype (f '' s)] :
    (f '' s).toFinset = s.toFinset.image f :=
  Finset.coe_injective <| by simp

@[simp]
/-
**Set.toFinset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_range [DecidableEq α] [Fintype β] (f : β -> α) [Fintype (Set.rang
e f)] : (Set.range f).toFinset = Finset.univ.image f
参数：f : β -> α；Set.range f。
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.range f)] :
    (Set.range f).toFinset = Finset.univ.image f := by
  ext
  simp

@[simp]
/-
**Set.toFinset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_singleton (a : α) [Fintype ({a} : Set α)] : ({a} : Set α).toFinse
t = {a}
参数：a : α；{a} : Set α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_singleton (a : α) [Fintype ({a} : Set α)] : ({a} : Set α).toFinset = {a} := by
  ext
  simp

@[simp]
/-
**Set.toFinset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s :
 Set α)] [Fintype s] : (insert a s).toFinset = insert a s.toFinset
参数：insert a s : Set α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
    [Fintype s] : (insert a s).toFinset = insert a s.toFinset := by
  ext
  simp
/-
**Set.filter_mem_univ_eq_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [Decidable
Pred (· in s)] : Finset.univ.filter (· in s) = s.toFinset
参数：s : Set α；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· ∈ s)] :
    Finset.univ.filter (· ∈ s) = s.toFinset := by
  ext
  rw [mem_filter_univ, mem_toFinset]

end Set

@[simp]
/-
**Finset.toFinset_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.toFinset_coe (s : Finset α) [Fintype (s : Set α)] : (s : Set α).toF
inset = s
参数：s : Finset α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem Finset.toFinset_coe (s : Finset α) [Fintype (s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_toFinset

section Finset

/-! ### `Fintype (s : Finset α)` -/


/-
**Finset.fintypeCoeSort** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s
参数：s : Finset α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach

--- 原说明 ---
### `Fintype (s : Finset α)`
-/
instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
/-
**Finset.univ_eq_attach** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.
attach
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

end Finset

/-
**Fintype.coe_image_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α -> β} : ↑(Finset
.image f Finset.univ) = Set.range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} :
    ↑(Finset.image f Finset.univ) = Set.range f := by
  simp
/-
**List.Subtype.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x in l 
}
参数：l : List α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_attach`：∀ {α : Type u_1} (l : List α) (x : { x // x ∈ l }), x ∈
 l.attach
-/
instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach
/-
**Multiset.Subtype.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x //
 x in s }
参数：s : Multiset α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_attach`：mem_attach (s : Multiset α) : forall x, x in s.atta
ch
-/
instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach
/-
**Finset.Subtype.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finset.Subtype.fintype (s : Finset α) : Fintype { x // x in s }
参数：s : Finset α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
-/
instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩
/-
**FinsetCoe.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α)
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s
/-
**Finset.attach_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Prop.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.fintype : Fintype Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp⟩, by simpa using em⟩

@[simp]
/-
**Fintype.univ_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False} :=
  Finset.eq_of_veq <| by simp; rfl
/-
**Subtype.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.fintype (p : α -> Prop) [DecidablePred p] [Fintype α] : Fintype { 
x // p x }
参数：p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)

/-- A set on a fintype, when coerced to a type, is a fintype. -/
@[instance_reducible]
/-
**setFintype** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：setFintype [Fintype α] (s : Set α) [DecidablePred (· in s)] : Fintype s
参数：s : Set α；· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set on a fintype, when coerced to a type, is a fintype.
-/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s

namespace Fintype
variable [Fintype α]

/-- Given `Fintype α`, `finsetEquivSet` is the equiv between `Finset α` and `Set α`. (All
sets on a finite type are finite.) -/
/-
**Fintype.finsetEquivSet** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：finsetEquivSet : Finset α ≃ Set α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Fintype α`, `finsetEquivSet` is the equiv between `Finset α` and `Set α`.
 (All
sets on a finite type are finite.)
-/
noncomputable def finsetEquivSet : Finset α ≃ Set α where
  toFun := (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert! Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset
/-
**Fintype.coe_finsetEquivSet** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α], ⇑Fintype.finsetEquivSet = SetLike.coe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_finsetEquivSet : ⇑finsetEquivSet = ((↑) : Finset α → Set α) := rfl
/-
**Fintype.finsetEquivSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] (s : Finset α), Fintype.finsetEquivSet
 s = ↑s
参数：s : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma finsetEquivSet_apply (s : Finset α) : finsetEquivSet s = s := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Fintype.finsetEquivSet_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] (s : Set α) [inst_1 : Fintype ↑s], Fin
type.finsetEquivSet.symm s = s.toFinset
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma finsetEquivSet_symm_apply (s : Set α) [Fintype s] :
    finsetEquivSet.symm s = s.toFinset := by simp [finsetEquivSet]

/-- Given a fintype `α`, `finsetOrderIsoSet` is the order isomorphism between `Finset α` and `Set α`
(all sets on a finite type are finite). -/
@[simps toEquiv]
/-
**Fintype.finsetOrderIsoSet** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：finsetOrderIsoSet : Finset α ≃o Set α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂

--- 原说明 ---
Given a fintype `α`, `finsetOrderIsoSet` is the order isomorphism between `Finse
t α` and `Set α`
(all sets on a finite type are finite).
-/
noncomputable def finsetOrderIsoSet : Finset α ≃o Set α where
  toEquiv := finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]
/-
**Fintype.coe_finsetOrderIsoSet** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：coe_finsetOrderIsoSet : ⇑finsetOrderIsoSet = ((↑) : Finset α -> Set α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_finsetOrderIsoSet : ⇑finsetOrderIsoSet = ((↑) : Finset α → Set α) := rfl
/-
**Fintype.coe_finsetOrderIsoSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α], ⇑Fintype.finsetOrderIsoSet.symm = ⇑Fi
ntype.finsetEquivSet.symm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_finsetOrderIsoSet_symm :
    ⇑(finsetOrderIsoSet : Finset α ≃o Set α).symm = ⇑finsetEquivSet.symm := rfl

end Fintype

/-
**mem_image_univ_iff_mem_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_image_univ_iff_mem_range {α β : Type*} [Fintype α] [DecidableEq β] {f 
: α -> β} {b : β} : b in univ.image f ↔ b in Set.range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_image_univ_iff_mem_range {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} : b ∈ univ.image f ↔ b ∈ Set.range f := by simp

open Batteries.ExtendedBinder Lean Meta

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck finsetStx] meta def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax

