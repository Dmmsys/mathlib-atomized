/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finite.Defs
public import Mathlib.Order.Lex

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `Fintype α`:  Typeclass saying that a type is finite. It takes as fields a `Finset` and a proof
  that all terms of type `α` are in it.
* `Finset.univ`: The finset of all elements of a fintype.

See `Data.Fintype.Basic` for elementary results,
`Data.Fintype.Card` for the cardinality of a fintype,
the equivalence with `Fin (Fintype.card α)`, and pigeonhole principles.

## Instances

Instances for `Fintype` for
* `{x // p x}` are in this file as `Fintype.subtype`
* `Option α` are in `Data.Fintype.Option`
* `α × β` are in `Data.Fintype.Prod`
* `α ⊕ β` are in `Data.Fintype.Sum`
* `Σ (a : α), β a` are in `Data.Fintype.Sigma`

These files also contain appropriate `Infinite` instances for these types.

`Infinite` instances for `ℕ`, `ℤ`, `Multiset α`, and `List α` are in `Data.Fintype.Lattice`.
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
/-
**Fintype** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list.
-/
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

/-! ### Preparatory lemmas -/

namespace Finset

/-
**Finset.nodup_map_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nodup_map_iff_injOn {f : α -> β} {s : Finset α} : (Multiset.map f s.val).N
odup ↔ Set.InjOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.nodup_map_iff_inj_on`：nodup_map_iff_inj_on {f : α -> β} {s : Mu
ltiset α} (d : Nodup s) : Nodup (map f s) ↔ forall x in s, forall y in s, f x = 
f y -> x = y
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_map_iff_injOn {f : α → β} {s : Finset α} :
    (Multiset.map f s.val).Nodup ↔ Set.InjOn f s := by
  simp [Multiset.nodup_map_iff_inj_on s.nodup, Set.InjOn]

end Finset

namespace List

variable [DecidableEq α] {a : α} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}

/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq β] : Decidable (Set.InjOn f s) :=
  -- Use custom implementation for better performance.
  decidable_of_iff ((Multiset.map f s.val).Nodup) Finset.nodup_map_iff_injOn
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq β] : Decidable (Set.BijOn f s t') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end List

namespace Finset

variable [Fintype α] {s t : Finset α}

/-- `univ` is the universal finite set of type `Finset α` implied from
  the assumption `Fintype α`. -/
/-
**Finset.univ** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：univ : Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`univ` is the universal finite set of type `Finset α` implied from
  the assumption `Fintype α`.
-/
def univ : Finset α :=
  @Fintype.elems α _

@[simp, grind ←]
/-
**Finset.mem_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_univ (x : α) : x in (univ : Finset α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
-/
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x
/-
**Finset.mem_univ_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_univ_val : forall x, x in (univ : Finset α).1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 := by simp
/-
**Finset.eq_univ_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_univ_iff_forall : s = univ ↔ forall x, x in s
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
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by simp [Finset.ext_iff]
/-
**Finset.eq_univ_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_univ_of_forall : (forall x, x in s) -> s = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
-/
theorem eq_univ_of_forall : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

@[simp, norm_cast]
/-
**Finset.coe_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_univ : ↑(univ : Finset α) = (Set.univ : Set α) := by ext; simp

@[simp, norm_cast]
/-
**Finset.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ := by rw [← coe_univ, coe_inj]

@[simp]
/-
**Finset.subset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_univ (s : Finset α) : s subseteq univ
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a
/-
**Finset.mem_filter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_filter_univ {p : α -> Prop} [DecidablePred p] : forall x, x in univ.fi
lter p ↔ p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_filter_univ {p : α → Prop} [DecidablePred p] : ∀ x, x ∈ univ.filter p ↔ p x := by simp

end Finset

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder Parser.Term PrettyPrinter.Delaborator SubExpr

/-- Elaborate set builder notation for `Finset`.

* `{x | p x}` is elaborated as `Finset.filter (fun x ↦ p x) Finset.univ` if the expected type is
  `Finset ?α`.
* `{x : α | p x}` is elaborated as `Finset.filter (fun x : α ↦ p x) Finset.univ` if the expected
  type is `Finset ?α`.
* `{x ∉ s | p x}` is elaborated as `Finset.filter (fun x ↦ p x) sᶜ` if either the expected type is
  `Finset ?α` or the expected type is not `Set ?α` and `s` has expected type `Finset ?α`.
* `{x ≠ a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) {a}ᶜ` if the expected type is
  `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Finset.Basic` for the `Finset` builder notation elaborator partly overriding this one for
  syntax of the form `{x ∈ s | p x}`.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator handling syntax of the
  form `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.
-/
@[term_elab setBuilder]
meta def elabFinsetBuilderSetOf : TermElab
  | `({ $x:ident | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) Finset.univ)) expectedType?
  | `({ $x:ident : $t | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident : $t ↦ $p) Finset.univ)) expectedType?
  | `({ $x:ident ∉ $s:term | $p }), expectedType? => do
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
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) $sᶜ)) expectedType?
  | `({ $x:ident ≠ $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) (singleton $a)ᶜ)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Delaborator for `Finset.filter`. The `pp.funBinderTypes` option controls whether
to show the domain type when the filter is over `Finset.univ`. -/
@[app_delab Finset.filter] meta def delabFinsetFilter : Delab :=
  whenPPOption getPPNotation do
  let #[_, p, _, t] := (← getExpr).getAppArgs | failure
  guard p.isLambda
  let i ← withNaryArg 1 <| withBindingBodyUnusedName (pure ⟨·⟩)
  let p ← withNaryArg 1 <| withBindingBody i.getId delab
  if t.isAppOfArity ``Finset.univ 2 then
    if ← getPPOption getPPFunBinderTypes then
      let ty ← withNaryArg 0 delab
      `({$i:ident : $ty | $p})
    else
      `({$i:ident | $p})
  -- check if `t` is of the form `s₀ᶜ`, in which case we display `x ∉ s₀` instead
  else if t.isAppOfArity ``Compl.compl 3 then
    let #[_, _, s₀] := t.getAppArgs | failure
    -- if `s₀` is a singleton, we can even use the notation `x ≠ a`
    if s₀.isAppOfArity ``Singleton.singleton 4 then
      let t ← withNaryArg 3 <| withNaryArg 2 <| withNaryArg 3 delab
      `({$i:ident ≠ $t | $p})
    else
      let t ← withNaryArg 3 <| withNaryArg 2 delab
      `({$i:ident ∉ $t | $p})
  else
    let t ← withNaryArg 3 delab
    `({$i:ident ∈ $t | $p})

end Mathlib.Meta

open Finset

namespace Fintype

/-
**Fintype.decidablePiFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidablePiFintype {α} {β : α -> Type*} [forall a, DecidableEq (β a)] [Fin
type α] : DecidableEq (forall a, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidablePiFintype {α} {β : α → Type*} [∀ a, DecidableEq (β a)] [Fintype α] :
    DecidableEq (∀ a, β a) := fun f g =>
  decidable_of_iff (∀ a ∈ @univ α _, f a = g a)
    (by simp [funext_iff])
/-
**Fintype.decidableForallFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableForallFintype {p : α -> Prop} [DecidablePred p] [Fintype α] : Dec
idable (forall a, p a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)
/-
**Fintype.decidableExistsFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableExistsFintype {p : α -> Prop} [DecidablePred p] [Fintype α] : Dec
idable (exists a, p a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)
/-
**Fintype.decidableMemRangeFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α -> β) : Decida
blePred (· in Set.range f)
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α → β) :
    DecidablePred (· ∈ Set.range f) := fun _ => Fintype.decidableExistsFintype
/-
**Fintype.decidableSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableSubsingleton [Fintype α] [DecidableEq α] {s : Set α} [DecidablePr
ed (· in s)] : Decidable s.Subsingleton
参数：· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableSubsingleton [Fintype α] [DecidableEq α] {s : Set α} [DecidablePred (· ∈ s)] :
    Decidable s.Subsingleton := decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, a = b) Iff.rfl

section BundledHoms

/-
**Fintype.decidableEqEquivFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff
/-
**Fintype.decidableEqEmbeddingFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪
 β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff

end BundledHoms

/-
**Fintype.nodup_map_univ_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：nodup_map_univ_iff_injective [Fintype α] {f : α -> β} : (Multiset.map f un
iv.val).Nodup ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nodup_map_iff_injOn`：nodup_map_iff_injOn {f : α -> β} {s : Finset
 α} : (Multiset.map f s.val).Nodup ↔ Set.InjOn f s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.injOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.InjOn f
 Set.univ ↔ Function.Injective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nodup_map_univ_iff_injective [Fintype α] {f : α → β} :
    (Multiset.map f univ.val).Nodup ↔ Function.Injective f := by
  rw [nodup_map_iff_injOn, coe_univ, Set.injOn_univ]
/-
**Fintype.decidableInjectiveFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableInjectiveFintype [DecidableEq β] [Fintype α] : DecidablePred (Inj
ective : (α -> β) -> Prop)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.nodup_map_univ_iff_injective`：nodup_map_univ_iff_injective [Fint
ype α] {f : α -> β} : (Multiset.map f univ.val).Nodup ↔ Function.Injective f
-/
instance decidableInjectiveFintype [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α → β) → Prop) :=
  -- Use custom implementation for better performance.
  fun f => decidable_of_iff ((Multiset.map f univ.val).Nodup) nodup_map_univ_iff_injective
/-
**Fintype.decidableSurjectiveFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] : Decid
ablePred (Surjective : (α -> β) -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) :=
  fun x ↦ inferInstanceAs <| Decidable (∀ b, ∃ a, x a = b)
/-
**Fintype.decidableBijectiveFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableBijectiveFintype [DecidableEq β] [Fintype α] [Fintype β] : Decida
blePred (Bijective : (α -> β) -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableBijectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α → β) → Prop) :=
  fun x ↦ inferInstanceAs <| Decidable (Injective x ∧ Surjective x)
/-
**Fintype.decidableRightInverseFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α -> β) (g :
 β -> α) : Decidable (Function.RightInverse f g)
参数：f : α -> β；g : β -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
    Decidable (Function.RightInverse f g) :=
  inferInstanceAs <| Decidable (∀ x, g (f x) = x)
/-
**Fintype.decidableLeftInverseFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α -> β) (g : 
β -> α) : Decidable (Function.LeftInverse f g)
参数：f : α -> β；g : β -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
    Decidable (Function.LeftInverse f g) :=
  inferInstanceAs <| Decidable (∀ x, f (g x) = x)
/-
**Fintype.subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：subsingleton (α : Type*) : Subsingleton (Fintype α)
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance subsingleton (α : Type*) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩
/-
**Fintype.** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) : Lean.Meta.FastSubsingleton (Fintype α) := {}

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
@[instance_reducible]
/-
**Fintype.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：{α : Type u_1} → {p : α → Prop} → (s : Finset α) → (∀ (x : α), x ∈ s ↔ p x
) → Fintype { x // p x }
参数：s : Finset α；∀ (x : α), x ∈ s ↔ p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype.
-/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

/-- Construct a fintype from a finset with the same elements. -/
@[instance_reducible]
/-
**Fintype.ofFinset** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) : Fint
ype p
参数：s : Finset α；H : forall x, x in s ↔ x in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a fintype from a finset with the same elements.
-/
def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H

end Fintype

/-
**Bool.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.fintype : Fintype Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bool.fintype : Fintype Bool :=
  ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩
/-
**Ordering.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ordering.fintype : Fintype Ordering
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Ordering.fintype : Fintype Ordering :=
  ⟨⟨{.lt, .eq, .gt}, by simp⟩, fun x => by cases x <;> simp⟩
/-
**OrderDual.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›
/-
**OrderDual.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ :=
  ‹Finite α›
/-
**Lex.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Lex.fintype (α : Type*) [Fintype α] : Fintype (Lex α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Lex.fintype (α : Type*) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›
