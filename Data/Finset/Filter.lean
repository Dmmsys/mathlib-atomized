/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Multiset.Filter

/-!
# Filtering a finite set

## Main declarations

* `Finset.filter`: Given a decidable predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### filter -/

section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
/-
**Finset.filter** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：filter (s : Finset α) : Finset α
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with 
`t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available).
-/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩

end Finset.Filter

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder

/-- Return `true` if `expectedType?` is `some (Finset ?α)`, throws `throwUnsupportedSyntax` if it is
`some (Set ?α)`, and returns `false` otherwise. -/
meta def knownToBeFinsetNotSet (expectedType? : Option Expr) : TermElabM Bool :=
  -- As we want to reason about the expected type, we would like to wait for it to be available.
  -- However this means that if we fall back on `elabSetBuilder` we will have postponed.
  -- This is undesirable as we want set builder notation to quickly elaborate to a `Set` when no
  -- expected type is available.
  -- tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | some expectedType =>
    match_expr expectedType with
    -- If the expected type is known to be `Finset ?α`, return `true`.
    | Finset _ => pure true
    -- If the expected type is known to be `Set ?α`, give up.
    | Set _ => throwUnsupportedSyntax
    -- If the expected type is known to not be `Finset ?α` or `Set ?α`, return `false`.
    | _ => pure false
  -- If the expected type is not known, return `false`.
  | none => pure false

/-- Elaborate set builder notation for `Finset`.

`{x ∈ s | p x}` is elaborated as `Finset.filter (fun x ↦ p x) s` if either the expected type is
`Finset ?α` or the expected type is not `Set ?α` and `s` has expected type `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator handling syntax of the
  form `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.

TODO: Write a delaborator
-/
@[term_elab setBuilder]
meta def elabFinsetBuilderSep : TermElab
  | `({ $x:ident ∈ $s:term | $p }), expectedType? => do
    -- If the expected type is known to be `Set ?α`, give up. If it is not known to be `Set ?α` or
    -- `Finset ?α`, check the expected type of `s`.
    unless ← knownToBeFinsetNotSet expectedType? do
      let ty ← try whnfR (← inferType (← elabTerm s none)) catch _ => throwUnsupportedSyntax
      -- If the expected type of `s` is not known to be `Finset ?α`, give up.
      match_expr ty with
      | Finset _ => pure ()
      | _ => throwUnsupportedSyntax
    -- Finally, we can elaborate the syntax as a finset.
    -- TODO: Seems a bit wasteful to have computed the expected type but still use `expectedType?`.
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) $s)) expectedType?
  | _, _ => throwUnsupportedSyntax

end Mathlib.Meta

namespace Finset
section Filter
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

@[simp]
/-
**Finset.filter_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] (s : Finset α),  
 (Finset.filter p s).val = Multiset.filter p s.val
参数：p : α → Prop；s : Finset α；Finset.filter p s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl

@[simp]
/-
**Finset.filter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] (s : Finset α), F
inset.filter p s ⊆ s
参数：p : α → Prop；s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.filter_subset`：filter_subset (s : Multiset α) : filter p s subs
eteq s
-/
theorem filter_subset (s : Finset α) : s.filter p ⊆ s :=
  Multiset.filter_subset _ _

variable {p}

@[simp, grind =]
/-
**Finset.mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a
 : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
-/
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Multiset.mem_filter
/-
**Finset.mem_of_mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, ∀
 x ∈ Finset.filter p s, x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_mem_filter`：mem_of_mem_filter {a : α} {s} (h : a in filt
er p s) : a in s
-/
theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x ∈ s.filter p) : x ∈ s :=
  Multiset.mem_of_mem_filter h
/-
**Finset.filter_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, F
inset.filter p s ⊂ s ↔ ∃ x ∈ s, ¬p x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬p x := by grind

variable (p)
/-
**Finset.filter_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p q : α → Prop) [inst : DecidablePred p] [inst_1 : Decid
ablePred q] (s : Finset α),   Finset.filter q (Finset.filter p s) = {a ∈ s | p a
 ∧ q a}
参数：p q : α → Prop；s : Finset α；Finset.filter p s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a := by
  grind
/-
**Finset.filter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p q : α → Prop) [inst : DecidablePred p] [inst_1 : Decid
ablePred q] (s : Finset α),   Finset.filter q (Finset.filter p s) = Finset.filte
r p (Finset.filter q s)
参数：p q : α → Prop；s : Finset α；Finset.filter p s；Finset.filter q s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_comm (s : Finset α) : (s.filter p).filter q = (s.filter q).filter p := by
  grind

-- We can replace an application of filter where the decidability is inferred in "the wrong way".
/-
**Finset.filter_congr_decidable** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α) (p : α → Prop) (h : DecidablePred p) [inst
 : DecidablePred p],   Finset.filter p s = Finset.filter p s
参数：s : Finset α；p : α → Prop；h : DecidablePred p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem filter_congr_decidable (s : Finset α) (p : α → Prop) (h : DecidablePred p)
    [DecidablePred p] : @filter α p h s = s.filter p := by congr

@[simp]
/-
**Finset.filter_true** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {h : DecidablePred fun x => True} (s : Finset α), {x ∈ s 
| True} = s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_true {h} (s : Finset α) : @filter _ (fun _ => True) h s = s := by ext; simp

@[simp]
/-
**Finset.filter_false** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {h : DecidablePred fun x => False} (s : Finset α), {x ∈ s
 | False} = ∅
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_false {h} (s : Finset α) : @filter _ (fun _ => False) h s = ∅ := by ext; simp

variable {p q}

@[simp]
/-
**Finset.filter_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, F
inset.filter p s = s ↔ ∀ x ∈ s, p x
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
lemma filter_eq_self : s.filter p = s ↔ ∀ x ∈ s, p x := by simp [Finset.ext_iff]

@[simp]
/-
**Finset.filter_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, F
inset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬p x := by simp [Finset.ext_iff]
/-
**Finset.filter_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, (
Finset.filter p s).Nonempty ↔ ∃ a ∈ s, p a
参数：Finset.filter p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_nonempty_iff : (s.filter p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]

/-- If all elements of a `Finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
/-
**Finset.filter_true_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, (
∀ x ∈ s, p x) → Finset.filter p s = s
参数：∀ x ∈ s, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_eq_self`：∀ {α : Type u_1} {p : α → Prop} [inst : Decidable
Pred p] {s : Finset α}, Finset.filter p s = s ↔ ∀ x ∈ s, p x

--- 原说明 ---
If all elements of a `Finset` satisfy the predicate `p`, `s.filter p` is `s`.
-/
theorem filter_true_of_mem (h : ∀ x ∈ s, p x) : s.filter p = s := filter_eq_self.2 h

/-- If all elements of a `Finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
/-
**Finset.filter_false_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α}, (
∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
参数：∀ x ∈ s, ¬p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_eq_empty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, Finset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x

--- 原说明 ---
If all elements of a `Finset` fail to satisfy the predicate `p`, `s.filter p` is
 `∅`.
-/
theorem filter_false_of_mem (h : ∀ x ∈ s, ¬p x) : s.filter p = ∅ := filter_eq_empty_iff.2 h

@[simp]
/-
**Finset.filter_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : Prop) [inst : Decidable p] (s : Finset α), {_a ∈ s |
 p} = if p then s else ∅
参数：p : Prop；s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
-/
theorem filter_const (p : Prop) [Decidable p] (s : Finset α) :
    (s.filter fun _a => p) = if p then s else ∅ := by split_ifs <;> simp [*]

@[congr]
/-
**Finset.filter_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p q : α → Prop} [inst : DecidablePred p] [inst_1 : Decid
ablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Finset.filter p s = Finset.
filter q s
参数：∀ x ∈ s, p x ↔ q x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
-/
theorem filter_congr {s : Finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| Multiset.filter_congr H

variable (p q)

@[simp]
/-
**Finset.filter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p], Finset.filter p 
∅ = ∅
参数：p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.subset_empty`：∀ {α : Type u_1} {s : Finset α}, s ⊆ ∅ ↔ s = ∅
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _

@[gcongr]
/-
**Finset.filter_subset_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] {s t : Finset α},
 s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
参数：p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p := fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
/-
**Finset.monotone_filter_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p], Monotone (Finset
.filter p)
参数：p : α → Prop；Finset.filter p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_subset_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Dec
idablePred p] {s t : Finset α}, s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
-/
theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p

@[gcongr]
/-
**Finset.monotone_filter_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α) ⦃p q : α → Prop⦄ [inst : DecidablePred p] 
[inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q a) → Finset.filter p s ⊆ Finset.
filter q s
参数：s : Finset α。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : ∀ a ∈ s, p a → q a) : s.filter p ⊆ s.filter q := by simp +contextual [subset_iff, h]

@[simp, norm_cast]
/-
**Finset.coe_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] (s : Finset α), ↑
(Finset.filter p s) = {x | x ∈ s ∧ p x}
参数：p : α → Prop；s : Finset α；Finset.filter p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter
/-
**Finset.subset_coe_filter_of_subset_forall** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] (s : Finset α) {t
 : Set α},   t ⊆ ↑s → (∀ x ∈ t, p x) → t ⊆ ↑(Finset.filter p s)
参数：p : α → Prop；s : Finset α；∀ x ∈ t, p x；Finset.filter p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
-/
theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s)
    (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩
/-
**Finset.disjoint_filter_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} {p q : α → Prop} [inst : DecidablePred p
] [inst_1 : DecidablePred q],   Disjoint s t → Disjoint (Finset.filter p s) (Fin
set.filter q t)
参数：Finset.filter p s；Finset.filter q t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
theorem disjoint_filter_filter {s t : Finset α}
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint s t → Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)
/-
**Finset._root_.Set.pairwiseDisjoint_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.pairwiseDisjoint_filter [DecidableEq β] (f : α → β) (s : Set β) (t : Finset α) :
    s.PairwiseDisjoint fun x ↦ t.filter (f · = x) := by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = j := by simpa using hj hx
  contradiction
/-
**Finset.disjoint_filter_and_not_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (p q : α → Prop) [inst : DecidablePred p] [inst_1 : Decid
ablePred q] {s : Finset α},   Disjoint ({x ∈ s | p x ∧ ¬q x}) ({x ∈ s | q x ∧ ¬p
 x})
参数：p q : α → Prop；{x ∈ s | p x ∧ ¬q x}；{x ∈ s | q x ∧ ¬p x}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem disjoint_filter_and_not_filter :
    Disjoint (s.filter (fun x ↦ p x ∧ ¬q x)) (s.filter (fun x ↦ q x ∧ ¬p x)) := by
  intro _ htp htq
  simp only [bot_eq_empty, subset_empty]
  by_contra! ⟨_, hx⟩
  exact (mem_filter.mp (htq hx)).2.2 (mem_filter.mp (htp hx)).2.1

variable {p q}
/-
**Finset.filter_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s t : Finset α},
   Finset.filter p s = Finset.filter p t ↔ ∀ ⦃a : α⦄, p a → (a ∈ s ↔ a ∈ t)
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma filter_inj : s.filter p = t.filter p ↔ ∀ ⦃a⦄, p a → (a ∈ s ↔ a ∈ t) := by
  simp [Finset.ext_iff]
/-
**Finset.filter_inj'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p q : α → Prop} [inst : DecidablePred p] [inst_1 : Decid
ablePred q] {s : Finset α},   Finset.filter p s = Finset.filter q s ↔ ∀ ⦃a : α⦄,
 a ∈ s → (p a ↔ q a)
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma filter_inj' : s.filter p = s.filter q ↔ ∀ ⦃a⦄, a ∈ s → (p a ↔ q a) := by
  simp [Finset.ext_iff]

@[simp]
/-
**Finset.filter_mem_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} [inst : DecidablePred fun x => x ∈ s], s
 ⊆ t → {x ∈ t | x ∈ s} = s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma filter_mem_eq_of_subset [DecidablePred (· ∈ s)] (hst : s ⊆ t) :
    t.filter (· ∈ s) = s := by
  grind

end Filter

end Finset

