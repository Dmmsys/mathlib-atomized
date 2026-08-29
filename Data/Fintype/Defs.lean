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

* `Fintype α`: Typeclass saying that a type is finite. It takes as fields a `Finset` and a proof
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

/--
Definition of `Fintype` / `Fintype` 的定义

English:
class Fintype
  parameters: (α : Type*)
  axioms and operations (2):
    - elems : Finset α
    - complete : forall x : α, x in elems

中文:
类 有限类型
  参数: (α : 类型)
  公理与运算 (2 个):
    - elems : 有限集 α
    - complete : 对任意 x : α, x in elems
-/
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : forall x : α, x in elems

/-! ### Preparatory lemmas -/

namespace Finset

/--
theorem `nodup_map_iff_injOn` / 定理 `nodup_map_iff_injOn`

English:
theorem nodup_map_iff_injOn
  given: {f : α -> β} {s : Finset α}
  proof: by
  simp [Multiset.nodup_map_iff_inj_on s.nodup, Set.InjOn]

中文:
定理 nodup_map_iff_injOn
  条件: {f : α -> β} {s : 有限集 α}
  证明: by
  simp [Multiset.nodup_map_iff_inj_on s.nodup, Set.InjOn]

Depends on / 依赖: Multiset, Multiset.nodup_map_iff_inj_on, Set.InjOn, nodup_map_iff_inj_on, s.nodup
-/
theorem nodup_map_iff_injOn {f : α -> β} {s : Finset α} :
    (Multiset.map f s.val).Nodup ↔ Set.InjOn f s := by
  simp [Multiset.nodup_map_iff_inj_on s.nodup, Set.InjOn]

end Finset

namespace List

variable [DecidableEq α] {a : α} {f : α -> β} {s : Finset α} {t : Set β} {t' : Finset β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: β] : Decidable (Set.InjOn f s)
  body: -- Use custom implementation for better performance.
  decidable_of_iff ((Multiset.map f s.val).Nodup) Finset.nodup_map_iff_injOn

中文:
实例 [DecidableEq
  签名: β] : 可判定 (集合.单射限制 f s)
  定义体: -- Use custom implementation for better performance.
  decidable_of_iff ((Multiset.map f s.val).Nodup) Finset.nodup_map_iff_injOn
-/
instance [DecidableEq β] : Decidable (Set.InjOn f s) :=
  -- Use custom implementation for better performance.
  decidable_of_iff ((Multiset.map f s.val).Nodup) Finset.nodup_map_iff_injOn

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: β] : Decidable (Set.BijOn f s t')
  body: inferInstanceAs (Decidable (_ ∧ _ ∧ _))

中文:
实例 [DecidableEq
  签名: β] : 可判定 (集合.双射限制 f s t')
  定义体: inferInstanceAs (Decidable (_ ∧ _ ∧ _))

Depends on / 依赖: Decidable
-/
instance [DecidableEq β] : Decidable (Set.BijOn f s t') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end List

namespace Finset

variable [Fintype α] {s t : Finset α}

/--
Definition of `univ` / `univ` 的定义

English:
definition univ
  signature: : Finset α
  body: @Fintype.elems α _

@[simp, grind ←]

中文:
定义 univ
  签名: : 有限集 α
  定义体: @Fintype.elems α _

@[simp, grind ←]

Depends on / 依赖: Fintype, Fintype.elems
-/
def univ : Finset α :=
  @Fintype.elems α _

@[simp, grind ←]
/--
theorem `mem_univ` / 定理 `mem_univ`

English:
theorem mem_univ
  given: (x : α)
  statement: x in (univ : Finset α)
  proof: Fintype.complete x

中文:
定理 mem_univ
  条件: (x : α)
  结论: x in (univ : 有限集 α)
  证明: Fintype.complete x

Depends on / 依赖: Fintype, Fintype.complete, complete
-/
theorem mem_univ (x : α) : x in (univ : Finset α) :=
  Fintype.complete x

/--
theorem `mem_univ_val` / 定理 `mem_univ_val`

English:
theorem mem_univ_val
  statement: forall x, x in (univ : Finset α).1
  proof: by simp

中文:
定理 mem_univ_val
  结论: 对任意 x, x in (univ : 有限集 α).1
  证明: by simp
-/
theorem mem_univ_val : forall x, x in (univ : Finset α).1 := by simp

/--
theorem `eq_univ_iff_forall` / 定理 `eq_univ_iff_forall`

English:
theorem eq_univ_iff_forall
  statement: s = univ ↔ forall x, x in s
  proof: by simp [Finset.ext_iff]

中文:
定理 eq_univ_iff_对任意
  结论: s = univ ↔ 对任意 x, x in s
  证明: by simp [Finset.ext_iff]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
theorem eq_univ_iff_forall : s = univ ↔ forall x, x in s := by simp [Finset.ext_iff]

/--
theorem `eq_univ_of_forall` / 定理 `eq_univ_of_forall`

English:
theorem eq_univ_of_forall
  statement: (forall x, x in s) -> s = univ
  proof: eq_univ_iff_forall.2

@[simp, norm_cast]

中文:
定理 eq_univ_of_对任意
  结论: (对任意 x, x in s) -> s = univ
  证明: eq_univ_iff_forall.2

@[simp, norm_cast]

Depends on / 依赖: eq_univ_iff_forall
-/
theorem eq_univ_of_forall : (forall x, x in s) -> s = univ :=
  eq_univ_iff_forall.2

@[simp, norm_cast]
/--
theorem `coe_univ` / 定理 `coe_univ`

English:
theorem coe_univ
  statement: ↑(univ : Finset α) = (Set.univ : Set α)
  proof: by ext; simp

@[simp, norm_cast]

中文:
定理 coe_univ
  结论: ↑(univ : 有限集 α) = (集合.univ : 集合 α)
  证明: by ext; simp

@[simp, norm_cast]
-/
theorem coe_univ : ↑(univ : Finset α) = (Set.univ : Set α) := by ext; simp

@[simp, norm_cast]
/--
theorem `coe_eq_univ` / 定理 `coe_eq_univ`

English:
theorem coe_eq_univ
  statement: (s : Set α) = Set.univ ↔ s = univ
  proof: by rw [← coe_univ, coe_inj]

@[simp]

中文:
定理 coe_eq_univ
  结论: (s : 集合 α) = 集合.univ ↔ s = univ
  证明: by rw [← coe_univ, coe_inj]

@[simp]

Depends on / 依赖: coe_inj, coe_univ
-/
theorem coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ := by rw [← coe_univ, coe_inj]

@[simp]
/--
theorem `subset_univ` / 定理 `subset_univ`

English:
theorem subset_univ
  given: (s : Finset α)
  statement: s subseteq univ
  proof: fun a _ => mem_univ a

中文:
定理 subset_univ
  条件: (s : 有限集 α)
  结论: s subseteq univ
  证明: fun a _ => mem_univ a

Depends on / 依赖: mem_univ
-/
theorem subset_univ (s : Finset α) : s subseteq univ := fun a _ => mem_univ a

/--
theorem `mem_filter_univ` / 定理 `mem_filter_univ`

English:
theorem mem_filter_univ
  given: {p : α -> Prop} [DecidablePred p]
  statement: forall x, x in univ.filter p ↔ p x
  proof: by simp

中文:
定理 mem_filter_univ
  条件: {p : α -> 命题} [DecidablePred p]
  结论: 对任意 x, x in univ.filter p ↔ p x
  证明: by simp
-/
theorem mem_filter_univ {p : α -> Prop} [DecidablePred p] : forall x, x in univ.filter p ↔ p x := by simp

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
    elabTerm (← `(Finset.filter (fun $x:ident => $p) Finset.univ)) expectedType?
  | `({ $x:ident : $t | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident : $t => $p) Finset.univ)) expectedType?
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
    elabTerm (← `(Finset.filter (fun $x:ident => $p) $sᶜ)) expectedType?
  | `({ $x:ident != $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident => $p) (singleton $a)ᶜ)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Delaborator for `Finset.filter`. The `pp.funBinderTypes` option controls whether
to show the domain type when the filter is over `Finset.univ`. -/
@[app_delab Finset.filter] meta def delabFinsetFilter : Delab :=
  whenPPOption getPPNotation do
  let #[_, p, _, t] := (← getExpr).getAppArgs | failure
  guard p.isLambda
let i ← withNaryArg 1 withBindingBodyUnusedName (pure ⟨·⟩)
let p ← withNaryArg 1 withBindingBody i.getId delab
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
let t ← withNaryArg 3 withNaryArg 2 withNaryArg 3 delab
      `({$i:ident != $t | $p})
    else
let t ← withNaryArg 3 withNaryArg 2 delab
      `({$i:ident ∉ $t | $p})
  else
    let t ← withNaryArg 3 delab
    `({$i:ident in $t | $p})

end Mathlib.Meta

open Finset

namespace Fintype

/--
Instance `decidablePiFintype` / 实例 `decidablePiFintype`

English:
instance decidablePiFintype
  signature: {α} {β : α -> Type*} [forall a, DecidableEq (β a)] [Fintype α]
  body: fun f g =>
  decidable_of_iff (forall a in @univ α _, f a = g a)
    (by simp [funext_iff])

中文:
实例 decidablePiFintype
  签名: {α} {β : α -> 类型} [对任意 a, DecidableEq (β a)] [有限类型 α]
  定义体: fun f g =>
  decidable_of_iff (forall a in @univ α _, f a = g a)
    (by simp [funext_iff])
-/
instance decidablePiFintype {α} {β : α -> Type*} [forall a, DecidableEq (β a)] [Fintype α] :
    DecidableEq (forall a, β a) := fun f g =>
  decidable_of_iff (forall a in @univ α _, f a = g a)
    (by simp [funext_iff])

/--
Instance `decidableForallFintype` / 实例 `decidableForallFintype`

English:
instance decidableForallFintype
  signature: {p : α -> Prop} [DecidablePred p] [Fintype α]
  body: decidable_of_iff (forall a in @univ α _, p a) (by simp)

中文:
实例 decidableForallFintype
  签名: {p : α -> 命题} [DecidablePred p] [有限类型 α]
  定义体: decidable_of_iff (forall a in @univ α _, p a) (by simp)

Depends on / 依赖: decidable_of_iff
-/
instance decidableForallFintype {p : α -> Prop} [DecidablePred p] [Fintype α] :
    Decidable (forall a, p a) :=
  decidable_of_iff (forall a in @univ α _, p a) (by simp)

/--
Instance `decidableExistsFintype` / 实例 `decidableExistsFintype`

English:
instance decidableExistsFintype
  signature: {p : α -> Prop} [DecidablePred p] [Fintype α]
  body: decidable_of_iff (exists a in @univ α _, p a) (by simp)

中文:
实例 decidableExistsFintype
  签名: {p : α -> 命题} [DecidablePred p] [有限类型 α]
  定义体: decidable_of_iff (exists a in @univ α _, p a) (by simp)

Depends on / 依赖: decidable_of_iff
-/
instance decidableExistsFintype {p : α -> Prop} [DecidablePred p] [Fintype α] :
    Decidable (exists a, p a) :=
  decidable_of_iff (exists a in @univ α _, p a) (by simp)

/--
Instance `decidableMemRangeFintype` / 实例 `decidableMemRangeFintype`

English:
instance decidableMemRangeFintype
  signature: [Fintype α] [DecidableEq β] (f : α -> β)
  body: fun _ => Fintype.decidableExistsFintype

中文:
实例 decidableMemRangeFintype
  签名: [有限类型 α] [DecidableEq β] (f : α -> β)
  定义体: fun _ => Fintype.decidableExistsFintype

Depends on / 依赖: Fintype, Fintype.decidableExistsFintype, decidableExistsFintype
-/
instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α -> β) :
    DecidablePred (· in Set.range f) := fun _ => Fintype.decidableExistsFintype

/--
Instance `decidableSubsingleton` / 实例 `decidableSubsingleton`

English:
instance decidableSubsingleton
  signature: [Fintype α] [DecidableEq α] {s : Set α} [DecidablePred (· in s)]
  body: decidable_of_iff (forall a in s, forall b in s, a = b) Iff.rfl

中文:
实例 decidableSubsingleton
  签名: [有限类型 α] [DecidableEq α] {s : 集合 α} [DecidablePred (· in s)]
  定义体: decidable_of_iff (forall a in s, forall b in s, a = b) Iff.rfl

Depends on / 依赖: Iff.rfl, decidable_of_iff
-/
instance decidableSubsingleton [Fintype α] [DecidableEq α] {s : Set α} [DecidablePred (· in s)] :
    Decidable s.Subsingleton := decidable_of_iff (forall a in s, forall b in s, a = b) Iff.rfl

section BundledHoms

/--
Instance `decidableEqEquivFintype` / 实例 `decidableEqEquivFintype`

English:
instance decidableEqEquivFintype
  signature: [DecidableEq β] [Fintype α]
  body: fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff

中文:
实例 decidableEqEquivFintype
  签名: [DecidableEq β] [有限类型 α]
  定义体: fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff
-/
instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff

/--
Instance `decidableEqEmbeddingFintype` / 实例 `decidableEqEmbeddingFintype`

English:
instance decidableEqEmbeddingFintype
  signature: [DecidableEq β] [Fintype α]
  body: fun a b =>
  decidable_of_iff ((a : α -> β) = b) Function.Embedding.coe_injective.eq_iff

中文:
实例 decidableEqEmbeddingFintype
  签名: [DecidableEq β] [有限类型 α]
  定义体: fun a b =>
  decidable_of_iff ((a : α -> β) = b) Function.Embedding.coe_injective.eq_iff
-/
instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidable_of_iff ((a : α -> β) = b) Function.Embedding.coe_injective.eq_iff

end BundledHoms

/--
theorem `nodup_map_univ_iff_injective` / 定理 `nodup_map_univ_iff_injective`

English:
theorem nodup_map_univ_iff_injective
  given: [Fintype α] {f : α -> β}
  proof: by
  rw [nodup_map_iff_injOn]; rw [coe_univ]; rw [Set.injOn_univ]

中文:
定理 nodup_map_univ_iff_injective
  条件: [有限类型 α] {f : α -> β}
  证明: by
  rw [nodup_map_iff_injOn]; rw [coe_univ]; rw [Set.injOn_univ]

Depends on / 依赖: Set.injOn_univ, coe_univ, injOn_univ, nodup_map_iff_injOn
-/
theorem nodup_map_univ_iff_injective [Fintype α] {f : α -> β} :
    (Multiset.map f univ.val).Nodup ↔ Function.Injective f := by
  rw [nodup_map_iff_injOn]; rw [coe_univ]; rw [Set.injOn_univ]

/--
Instance `decidableInjectiveFintype` / 实例 `decidableInjectiveFintype`

English:
instance decidableInjectiveFintype
  signature: [DecidableEq β] [Fintype α]
  body: -- Use custom implementation for better performance.
  fun f => decidable_of_iff ((Multiset.map f univ.val).Nodup) nodup_map_univ_iff_injective

中文:
实例 decidableInjectiveFintype
  签名: [DecidableEq β] [有限类型 α]
  定义体: -- Use custom implementation for better performance.
  fun f => decidable_of_iff ((Multiset.map f univ.val).Nodup) nodup_map_univ_iff_injective
-/
instance decidableInjectiveFintype [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α -> β) -> Prop) :=
  -- Use custom implementation for better performance.
  fun f => decidable_of_iff ((Multiset.map f univ.val).Nodup) nodup_map_univ_iff_injective

/--
Instance `decidableSurjectiveFintype` / 实例 `decidableSurjectiveFintype`

English:
instance decidableSurjectiveFintype
  signature: [DecidableEq β] [Fintype α] [Fintype β]
  body: fun x => inferInstanceAs Decidable (forall b, exists a, x a = b)

中文:
实例 decidableSurjectiveFintype
  签名: [DecidableEq β] [有限类型 α] [有限类型 β]
  定义体: fun x => inferInstanceAs Decidable (forall b, exists a, x a = b)

Depends on / 依赖: Decidable
-/
instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α -> β) -> Prop) :=
fun x => inferInstanceAs Decidable (forall b, exists a, x a = b)

/--
Instance `decidableBijectiveFintype` / 实例 `decidableBijectiveFintype`

English:
instance decidableBijectiveFintype
  signature: [DecidableEq β] [Fintype α] [Fintype β]
  body: fun x => inferInstanceAs Decidable (Injective x ∧ Surjective x)

中文:
实例 decidableBijectiveFintype
  签名: [DecidableEq β] [有限类型 α] [有限类型 β]
  定义体: fun x => inferInstanceAs Decidable (Injective x ∧ Surjective x)

Depends on / 依赖: Decidable, Injective, Surjective
-/
instance decidableBijectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α -> β) -> Prop) :=
fun x => inferInstanceAs Decidable (Injective x ∧ Surjective x)

/--
Instance `decidableRightInverseFintype` / 实例 `decidableRightInverseFintype`

English:
instance decidableRightInverseFintype
  signature: [DecidableEq α] [Fintype α] (f : α -> β) (g : β -> α)
  body: inferInstanceAs Decidable (forall x, g (f x) = x)

中文:
实例 decidableRightInverseFintype
  签名: [DecidableEq α] [有限类型 α] (f : α -> β) (g : β -> α)
  定义体: inferInstanceAs Decidable (forall x, g (f x) = x)

Depends on / 依赖: Decidable
-/
instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α -> β) (g : β -> α) :
    Decidable (Function.RightInverse f g) :=
inferInstanceAs Decidable (forall x, g (f x) = x)

/--
Instance `decidableLeftInverseFintype` / 实例 `decidableLeftInverseFintype`

English:
instance decidableLeftInverseFintype
  signature: [DecidableEq β] [Fintype β] (f : α -> β) (g : β -> α)
  body: inferInstanceAs Decidable (forall x, f (g x) = x)

中文:
实例 decidableLeftInverseFintype
  签名: [DecidableEq β] [有限类型 β] (f : α -> β) (g : β -> α)
  定义体: inferInstanceAs Decidable (forall x, f (g x) = x)

Depends on / 依赖: Decidable
-/
instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α -> β) (g : β -> α) :
    Decidable (Function.LeftInverse f g) :=
inferInstanceAs Decidable (forall x, f (g x) = x)

/--
Instance `subsingleton` / 实例 `subsingleton`

English:
instance subsingleton
  signature: (α : Type*)
  body: ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩

中文:
实例 subsingleton
  签名: (α : 类型)
  定义体: ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
instance subsingleton (α : Type*) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩

instance (α : Type*) : Lean.Meta.FastSubsingleton (Fintype α) := {}

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
@[instance_reducible]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x)
  body: ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

中文:
定义 subtype
  签名: {p : α -> 命题} (s : 有限集 α) (H : 对任意 x : α, x in s ↔ p x)
  定义体: ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩
-/
protected def subtype {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

/-- Construct a fintype from a finset with the same elements. -/
@[instance_reducible]
/--
Definition of `ofFinset` / `ofFinset` 的定义

English:
definition ofFinset
  signature: {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p)
  body: Fintype.subtype s H

中文:
定义 ofFinset
  签名: {p : 集合 α} (s : 有限集 α) (H : 对任意 x, x in s ↔ x in p)
  定义体: Fintype.subtype s H

Depends on / 依赖: Fintype, Fintype.subtype, subtype
-/
def ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) : Fintype p :=
  Fintype.subtype s H

end Fintype

/--
Instance `Bool.fintype` / 实例 `Bool.fintype`

English:
instance Bool.fintype
  signature: : Fintype Bool
  body: ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩

中文:
实例 布尔值.fintype
  签名: : 有限类型 布尔值
  定义体: ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩
-/
instance Bool.fintype : Fintype Bool :=
  ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩

/--
Instance `Ordering.fintype` / 实例 `Ordering.fintype`

English:
instance Ordering.fintype
  signature: : Fintype Ordering
  body: ⟨⟨{.lt, .eq, .gt}, by simp⟩, fun x => by cases x <;> simp⟩

中文:
实例 Ordering.fintype
  签名: : 有限类型 Ordering
  定义体: ⟨⟨{.lt, .eq, .gt}, by simp⟩, fun x => by cases x <;> simp⟩
-/
instance Ordering.fintype : Fintype Ordering :=
  ⟨⟨{.lt, .eq, .gt}, by simp⟩, fun x => by cases x <;> simp⟩

/--
Instance `OrderDual.fintype` / 实例 `OrderDual.fintype`

English:
instance OrderDual.fintype
  signature: (α : Type*) [Fintype α]
  body: ‹Fintype α›

中文:
实例 OrderDual.fintype
  签名: (α : 类型) [有限类型 α]
  定义体: ‹Fintype α›

Depends on / 依赖: Fintype
-/
instance OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›

/--
Instance `OrderDual.finite` / 实例 `OrderDual.finite`

English:
instance OrderDual.finite
  signature: (α : Type*) [Finite α]
  body: ‹Finite α›

中文:
实例 OrderDual.finite
  签名: (α : 类型) [有限 α]
  定义体: ‹Finite α›

Depends on / 依赖: Finite
-/
instance OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ :=
  ‹Finite α›

/--
Instance `Lex.fintype` / 实例 `Lex.fintype`

English:
instance Lex.fintype
  signature: (α : Type*) [Fintype α]
  body: ‹Fintype α›

中文:
实例 Lex.fintype
  签名: (α : 类型) [有限类型 α]
  定义体: ‹Fintype α›

Depends on / 依赖: Fintype
-/
instance Lex.fintype (α : Type*) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›
