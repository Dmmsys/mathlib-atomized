/-
Copyright (c) 2024 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-!
# Average over a finset

This file defines `Finset.expect`, the average (aka expectation) of a function over a finset.

## Notation

* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 i, f i` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`. This is referred to
  as `expectWith` in lemma names.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

## Implementation notes

This definition is a special case of the general convex combination operator in a convex space.
However:
1. We don't yet have general convex spaces.
2. The uniform weights case is an overwhelmingly useful special case which should have its own API.

When convex spaces are finally defined, we should redefine `Finset.expect` in terms of that convex
combination operator.

## TODO

* Connect `Finset.expect` with the expectation over `s` in the probability theory sense.
* Give a formulation of Jensen's inequality in this language.
-/

@[expose] public section

open Finset Function
open Fintype (card)
open scoped Pointwise

variable {ι κ K M N : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

/-- Average of a function over a finset. If the finset is empty, this is equal to zero. -/
/-
**Finset.expect** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finset.expect [AddCommMonoid M] [Module Rat>=0 M] (s : Finset ι) (f : ι ->
 M) : M
参数：s : Finset ι；f : ι -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Average of a function over a finset. If the finset is empty, this is equal to ze
ro.
-/
def Finset.expect [AddCommMonoid M] [Module ℚ≥0 M] (s : Finset ι) (f : ι → M) : M :=
  (#s : ℚ≥0)⁻¹ • ∑ i ∈ s, f i

namespace BigOperators
open Batteries.ExtendedBinder Lean Meta

/--
* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 i, f i` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

These support destructuring, for example `𝔼 ⟨i, j⟩ ∈ s ×ˢ t, f i j`.

Notation: `"𝔼" bigOpBinders* ("with" term)? "," term` -/
scoped syntax (name := bigexpect) "𝔼 " bigOpBinders ("with " term)? ", " term:67 : term

scoped macro_rules (kind := bigexpect)
  | `(𝔼 $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let i ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.expect (Finset.filter (fun $i ↦ $p) $s) (fun $i ↦ $v))
    | none => `(Finset.expect $s (fun $i ↦ $v))

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr
open Batteries.ExtendedBinder

/-- Delaborator for `Finset.expect`. The `pp.funBinderTypes` option controls whether
to show the domain type when the expect is over `Finset.univ`. -/
@[scoped app_delab Finset.expect] meta def delabFinsetExpect : Delab :=
  whenPPOption getPPNotation <| withOverApp 6 <| do
  let #[_, _, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard <| f.isLambda
  let ppDomain ← getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 0 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    `(𝔼 $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 4 <| delab
    `(𝔼 $(.mk i):ident ∈ $ss, $body)

end BigOperators

open scoped BigOperators

namespace Finset
section AddCommMonoid
variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

/-
**Finset.expect_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_univ [Fintype ι] : 𝔼 i, f i = (∑ i, f i) /Rat Fintype.card ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
lemma expect_univ [Fintype ι] : 𝔼 i, f i = (∑ i, f i) /ℚ Fintype.card ι := by
  rw [expect, card_univ]
/-
**Finset.expect_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] (f : ι → M),   (∅.expect fun i => f i) = 0
参数：f : ι → M；∅.expect fun i => f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_empty (f : ι → M) : 𝔼 i ∈ ∅, f i = 0 := by simp [expect]
/-
**Finset.expect_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] (f : ι → M) (i : ι),   ({i}.expect fun j => f j) = f i
参数：f : ι → M；i : ι；{i}.expect fun j => f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_singleton (f : ι → M) (i : ι) : 𝔼 j ∈ {i}, f j = f i := by simp [expect]
/-
**Finset.expect_const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] (s : Finset ι),   (s.expect fun _i => 0) = 0
参数：s : Finset ι；s.expect fun _i => 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_const_zero (s : Finset ι) : 𝔼 _i ∈ s, (0 : M) = 0 := by simp [expect]

@[congr]
/-
**Finset.expect_congr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_congr {t : Finset ι} (hst : s = t) (h : forall i in t, f i = g i) :
 𝔼 i in s, f i = 𝔼 i in t, g i
参数：hst : s = t；h : forall i in t, f i = g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma expect_congr {t : Finset ι} (hst : s = t) (h : ∀ i ∈ t, f i = g i) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by rw [expect, expect, sum_congr hst h, hst]
/-
**Finset.expectWith_congr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expectWith_congr (hst : s = t) (hpq : forall i in t, p i ↔ q i) (h : foral
l i in t, q i -> f i = g i) : 𝔼 i in s with p i, f i = 𝔼 i in t with q i, g i
参数：hst : s = t；hpq : forall i in t, p i ↔ q i；h : forall i in t, q i -> f i = g 
i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_inj'`：∀ {α : Type u_1} {p q : α → Prop} [inst : DecidableP
red p] [inst_1 : DecidablePred q] {s : Finset α},   Finset.filter p s = Finset.f
ilter q …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma expectWith_congr (hst : s = t) (hpq : ∀ i ∈ t, p i ↔ q i) (h : ∀ i ∈ t, q i → f i = g i) :
    𝔼 i ∈ s with p i, f i = 𝔼 i ∈ t with q i, g i :=
  expect_congr (by rw [hst, filter_inj'.2 hpq]) <| by simpa using h
/-
**Finset.expect_sum_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_sum_comm (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M) : 𝔼 i in s
, ∑ j in t, f i j = ∑ j in t, 𝔼 i in s, f i j
参数：s : Finset ι；t : Finset κ；f : ι -> κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
lemma expect_sum_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, 𝔼 i ∈ s, f i j := by
  simpa only [expect, smul_sum] using sum_comm
/-
**Finset.expect_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_comm (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M) : 𝔼 i in s, 𝔼 
j in t, f i j = 𝔼 j in t, 𝔼 i in s, f i j
参数：s : Finset ι；t : Finset κ；f : ι -> κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.expect_sum_comm`：expect_sum_comm (s : Finset ι) (t : Finset κ) (f
 : ι -> κ -> M) : 𝔼 i in s, ∑ j in t, f i j = ∑ j in t, 𝔼 i in s, f i j
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
lemma expect_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s, 𝔼 j ∈ t, f i j = 𝔼 j ∈ t, 𝔼 i ∈ s, f i j := by
  rw [expect, expect, ← expect_sum_comm, ← expect_sum_comm, expect, expect, smul_comm, sum_comm]
/-
**Finset.expect_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_eq_zero (h : forall i in s, f i = 0) : 𝔼 i in s, f i = 0
参数：h : forall i in s, f i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `Finset.expect_const_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι),   (s.expect fun _i => 
0) = 0
-/
lemma expect_eq_zero (h : ∀ i ∈ s, f i = 0) : 𝔼 i ∈ s, f i = 0 :=
  (expect_congr rfl h).trans s.expect_const_zero
/-
**Finset.exists_ne_zero_of_expect_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_ne_zero_of_expect_ne_zero (h : 𝔼 i in s, f i != 0) : exists i in s,
 f i != 0
参数：h : 𝔼 i in s, f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `Finset.expect_eq_zero`：expect_eq_zero (h : forall i in s, f i = 0) : 𝔼 i
 in s, f i = 0
-/
lemma exists_ne_zero_of_expect_ne_zero (h : 𝔼 i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  contrapose! h; exact expect_eq_zero h
/-
**Finset.expect_add_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_add_distrib (s : Finset ι) (f g : ι -> M) : 𝔼 i in s, (f i + g i) =
 𝔼 i in s, f i + 𝔼 i in s, g i
参数：s : Finset ι；f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_add_distrib (s : Finset ι) (f g : ι → M) :
    𝔼 i ∈ s, (f i + g i) = 𝔼 i ∈ s, f i + 𝔼 i ∈ s, g i := by
  simp [expect, sum_add_distrib]
/-
**Finset.expect_add_expect_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι -> M) : 𝔼 i in s, (f₁ i + f₂ i) + 
𝔼 i in s, (g₁ i + g₂ i) = 𝔼 i in s, (f₁ i + g₁ i) + 𝔼 i in s, (f₂ i + g₂ i)
参数：f₁ f₂ g₁ g₂ : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_add_distrib`：expect_add_distrib (s : Finset ι) (f g : ι ->
 M) : 𝔼 i in s, (f i + g i) = 𝔼 i in s, f i + 𝔼 i in s, g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι → M) :
    𝔼 i ∈ s, (f₁ i + f₂ i) + 𝔼 i ∈ s, (g₁ i + g₂ i) =
      𝔼 i ∈ s, (f₁ i + g₁ i) + 𝔼 i ∈ s, (f₂ i + g₂ i) := by
  simp_rw [expect_add_distrib, add_add_add_comm]
/-
**Finset.expect_eq_single_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_eq_single_of_mem (i : ι) (hi : i in s) (h : forall j in s, j != i -
> f j = 0) : 𝔼 i in s, f i = f i /Rat #s
参数：i : ι；hi : i in s；h : forall j in s, j != i -> f j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
-/
lemma expect_eq_single_of_mem (i : ι) (hi : i ∈ s) (h : ∀ j ∈ s, j ≠ i → f j = 0) :
    𝔼 i ∈ s, f i = f i /ℚ #s := by rw [expect, sum_eq_single_of_mem _ hi h]
/-
**Finset.expect_ite_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_ite_zero (s : Finset ι) (p : ι -> Prop) [DecidablePred p] (h : fora
ll i in s, forall j in s, p i -> p j -> i = j) (a : M) : 𝔼 i in s, ite (p i) a 0
 = ite (exists i in s, p i) (a /Rat #s) 0
参数：s : Finset ι；p : ι -> Prop；h : forall i in s, forall j in s, p i -> p j -> i 
= j；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p],   (∀ i ∈ s, ∀ j 
∈ s, p i …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma expect_ite_zero (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : M) :
    𝔼 i ∈ s, ite (p i) a 0 = ite (∃ i ∈ s, p i) (a /ℚ #s) 0 := by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

section DecidableEq
variable [DecidableEq ι]

/-
**Finset.expect_ite_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_ite_mem (s t : Finset ι) (f : ι -> M) : 𝔼 i in s, (if i in t then f
 i else 0) = (#(s inter t) / #s : Rat>=0) • 𝔼 i in s inter t, f i
参数：s t : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.Nonempty.card_ne_zero`：∀ {α : Type u_1} {s : Finset α}, s.Nonempt
y → s.card ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma expect_ite_mem (s t : Finset ι) (f : ι → M) :
    𝔼 i ∈ s, (if i ∈ t then f i else 0) = (#(s ∩ t) / #s : ℚ≥0) • 𝔼 i ∈ s ∩ t, f i := by
  obtain hst | hst := (s ∩ t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]
/-
**Finset.expect_dite_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι] (i : ι) (f : (j : ι) → i
 = j → M),   (s.expect fun j => if h : i = j then f j h else 0) = if i ∈ s then 
(↑s.card)⁻¹ • f i ⋯ else 0
参数：i : ι；f : (j : ι) → i = j → M；s.expect fun j => if h : i = j then f j h else 
0；↑s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_dite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → a = x → M)
, (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    𝔼 j ∈ s, (if h : i = j then f j h else 0) = if i ∈ s then f i rfl /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]
/-
**Finset.expect_dite_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι] (i : ι) (f : (j : ι) → j
 = i → M),   (s.expect fun j => if h : j = i then f j h else 0) = if i ∈ s then 
(↑s.card)⁻¹ • f i ⋯ else 0
参数：i : ι；f : (j : ι) → j = i → M；s.expect fun j => if h : j = i then f j h else 
0；↑s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → M) :
    𝔼 j ∈ s, (if h : j = i then f j h else 0) = if i ∈ s then f i rfl /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]
/-
**Finset.expect_ite_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι] (i : ι) (f : ι → M),   (
s.expect fun j => if i = j then f j else 0) = if i ∈ s then (↑s.card)⁻¹ • f i el
se 0
参数：i : ι；f : ι → M；s.expect fun j => if i = j then f j else 0；↑s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] lemma expect_ite_eq (i : ι) (f : ι → M) :
    𝔼 j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]
/-
**Finset.expect_ite_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι] (i : ι) (f : ι → M),   (
s.expect fun j => if j = i then f j else 0) = if i ∈ s then (↑s.card)⁻¹ • f i el
se 0
参数：i : ι；f : ι → M；s.expect fun j => if j = i then f j else 0；↑s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] lemma expect_ite_eq' (i : ι) (f : ι → M) :
    𝔼 j ∈ s, (if j = i then f j else 0) = if i ∈ s then f i /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]

end DecidableEq

section bij
variable {t : Finset κ} {g : κ → M}

/-- Reorder an average.

The difference with `Finset.expect_bij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.expect_nbij` is that the bijection is allowed to use membership of the
domain of the average, rather than being a non-dependent function. -/
/-
**Finset.expect_bij** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_bij (i : forall a in s, κ) (hi : forall a ha, i a ha in t) (h : for
all a ha, f a = g (i a ha)) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -
> a₁ = a₂) (i_surj : forall b in t, exists a ha, i a ha = b) : 𝔼 i in s, f i = 𝔼
 i in t, g i
参数：i : forall a in s, κ；hi : forall a ha, i a ha in t；h : forall a ha, f a = g (
i a ha)；i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂；i_surj : fo
rall b in t, exists a ha, i a ha = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reorder an average.

The difference with `Finset.expect_bij'` is that the bijection is specified as a
 surjective
injection, rather than by an inverse function.

The difference with `Finset.expect_nbij` is that the bijection is allowed to use
 membership of the
domain of the average, rather than being a non-dependent function.
-/
lemma expect_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_bij i hi i_inj i_surj, sum_bij i hi i_inj i_surj h]

/-- Reorder an average.

The difference with `Finset.expect_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.expect_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the averages, rather than being non-dependent functions. -/
/-
**Finset.expect_bij'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_bij' (i : forall a in s, κ) (j : forall a in t, ι) (hi : forall a h
a, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : forall a ha, j (i a 
ha) (hi a ha) = a) (right_inv : forall a ha, i (j a ha) (hj a ha) = a) (h : fora
ll a ha, f a = g (i a ha)) : 𝔼 i in s, f i = 𝔼 i in t, g i
参数：i : forall a in s, κ；j : forall a in t, ι；hi : forall a ha, i a ha in t；hj : 
forall a ha, j a ha in s；left_inv : forall a ha, j (i a ha) (hi a ha) = a；right_
inv : forall a ha, i (j a ha) (hj a ha) = a；h : forall a ha, f a = g (i a ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.card_bij'`：card_bij' (i : forall a in s, β) (j : forall a in t, α
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_bij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a
 : ι)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reorder an average.

The difference with `Finset.expect_bij` is that the bijection is specified with 
an inverse, rather
than as a surjective injection.

The difference with `Finset.expect_nbij'` is that the bijection and its inverse 
are allowed to use
membership of the domains of the averages, rather than being non-dependent funct
ions.
-/
lemma expect_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_bij' i j hi hj left_inv right_inv, sum_bij' i j hi hj left_inv right_inv h]

/-- Reorder an average.

The difference with `Finset.expect_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.expect_bij` is that the bijection is a non-dependent function, rather
than being allowed to use membership of the domain of the average. -/
/-
**Finset.expect_nbij** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_nbij (i : ι -> κ) (hi : forall a in s, i a in t) (h : forall a in s
, f a = g (i a)) (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t)
 : 𝔼 i in s, f i = 𝔼 i in t, g i
参数：i : ι -> κ；hi : forall a in s, i a in t；h : forall a in s, f a = g (i a)；i_in
j : (s : Set ι).InjOn i；i_surj : (s : Set ι).SurjOn i t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.card_nbij`：card_nbij (i : α -> β) (hi : Set.MapsTo i s t) (i_inj 
: (s : Set α).InjOn i) (i_surj : (s : Set α).SurjOn i t) : #s = #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reorder an average.

The difference with `Finset.expect_nbij'` is that the bijection is specified as 
a surjective
injection, rather than by an inverse function.

The difference with `Finset.expect_bij` is that the bijection is a non-dependent
 function, rather
than being allowed to use membership of the domain of the average.
-/
lemma expect_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_nbij i hi i_inj i_surj, sum_nbij i hi i_inj i_surj h]

/-- Reorder an average.

The difference with `Finset.expect_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.expect_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the averages.

The difference with `Finset.expect_equiv` is that bijectivity is only required to hold on the
domains of the averages, rather than on the entire types. -/
/-
**Finset.expect_nbij'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a in s, i a in t) (hj 
: forall a in t, j a in s) (left_inv : forall a in s, j (i a) = a) (right_inv : 
forall a in t, i (j a) = a) (h : forall a in s, f a = g (i a)) : 𝔼 i in s, f i =
 𝔼 i in t, g i
参数：i : ι -> κ；j : κ -> ι；hi : forall a in s, i a in t；hj : forall a in t, j a in
 s；left_inv : forall a in s, j (i a) = a；right_inv : forall a in t, i (j a) = a；
h : forall a in s, f a = g (i a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.card_nbij'`：card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo
 i s t) (hj : Set.MapsTo j t s) (left_inv : Set.LeftInvOn j i s) (right_inv : Se
t.Right…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reorder an average.

The difference with `Finset.expect_nbij` is that the bijection is specified with
 an inverse, rather
than as a surjective injection.

The difference with `Finset.expect_bij'` is that the bijection and its inverse a
re non-dependent
functions, rather than being allowed to use membership of the domains of the ave
rages.

The difference with `Finset.expect_equiv` is that bijectivity is only required t
o hold on the
domains of the averages, rather than on the entire types.
-/
lemma expect_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_nbij' i j hi hj left_inv right_inv,
    sum_nbij' i j hi hj left_inv right_inv h]

/-- `Finset.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments. -/
/-
**Finset.expect_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i in t) (hfg : forall
 i in s, f i = g (e i)) : 𝔼 i in s, f i = 𝔼 i in t, g i
参数：e : ι ≃ κ；hst : forall i, i in s ↔ e i in t；hfg : forall i in s, f i = g (e i
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Finset.expect_equiv` is a specialization of `Finset.expect_bij` that automatica
lly fills in
most arguments.
-/
lemma expect_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by simp_rw [expect, card_equiv e hst, sum_equiv e hst hfg]

/-- Expectation over a product set equals the expectation of the fiberwise expectations.

For rewriting in the reverse direction, use `Finset.expect_product'`. -/
/-
**Finset.expect_product** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_product (s : Finset ι) (t : Finset κ) (f : ι × κ -> M) : 𝔼 x in s ×
ˢ t, f x = 𝔼 i in s, 𝔼 j in t, f (i, j)
参数：s : Finset ι；t : Finset κ；f : ι × κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expectation over a product set equals the expectation of the fiberwise expectati
ons.

For rewriting in the reverse direction, use `Finset.expect_product'`.
-/
lemma expect_product (s : Finset ι) (t : Finset κ) (f : ι × κ → M) :
    𝔼 x ∈ s ×ˢ t, f x = 𝔼 i ∈ s, 𝔼 j ∈ t, f (i, j) := by
  simp only [expect, card_product, sum_product, smul_sum, mul_inv, mul_smul, Nat.cast_mul]

/-- Expectation over a product set equals the expectation of the fiberwise expectations.

For rewriting in the reverse direction, use `Finset.expect_product`. -/
/-
**Finset.expect_product'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_product' (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M) : 𝔼 i in s
 ×ˢ t, f i.1 i.2 = 𝔼 i in s, 𝔼 j in t, f i j
参数：s : Finset ι；t : Finset κ；f : ι -> κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_product'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [ins
t : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ → α → β),   ∑ x ∈ s ×ˢ
 t, f x.1…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expectation over a product set equals the expectation of the fiberwise expectati
ons.

For rewriting in the reverse direction, use `Finset.expect_product`.
-/
lemma expect_product' (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s ×ˢ t, f i.1 i.2 = 𝔼 i ∈ s, 𝔼 j ∈ t, f i j := by
  simp only [expect, card_product, sum_product', smul_sum, mul_inv, mul_smul, Nat.cast_mul]

@[simp]
/-
**Finset.expect_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_image [DecidableEq ι] {m : κ -> ι} (hm : (t : Set κ).InjOn m) : 𝔼 i
 in t.image m, f i = 𝔼 i in t, f (m i)
参数：hm : (t : Set κ).InjOn m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_image [DecidableEq ι] {m : κ → ι} (hm : (t : Set κ).InjOn m) :
    𝔼 i ∈ t.image m, f i = 𝔼 i ∈ t, f (m i) := by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

end bij

/-
**Finset.expect_inv_index** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] [inst_2 : DecidableEq ι]   [inst_3 : InvolutiveInv ι] (s : Finset 
ι) (f : ι → M), (s⁻¹.expect fun i => f i) = s.expect fun i => f i⁻¹
参数：s : Finset ι；f : ι → M；s⁻¹.expect fun i => f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.expect_image`：expect_image [DecidableEq ι] {m : κ -> ι} (hm : (t 
: Set κ).InjOn m) : 𝔼 i in t.image m, f i = 𝔼 i in t, f (m i)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
-/
@[simp] lemma expect_inv_index [DecidableEq ι] [InvolutiveInv ι] (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ s⁻¹, f i = 𝔼 i ∈ s, f i⁻¹ := expect_image inv_injective.injOn
/-
**Finset.expect_neg_index** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] [inst_2 : DecidableEq ι]   [inst_3 : InvolutiveNeg ι] (s : Finset 
ι) (f : ι → M), ((-s).expect fun i => f i) = s.expect fun i => f (-i)
参数：s : Finset ι；f : ι → M；(-s).expect fun i => f i；-i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.expect_image`：expect_image [DecidableEq ι] {m : κ -> ι} (hm : (t 
: Set κ).InjOn m) : 𝔼 i in t.image m, f i = 𝔼 i in t, f (m i)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
@[simp] lemma expect_neg_index [DecidableEq ι] [InvolutiveNeg ι] (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ -s, f i = 𝔼 i ∈ s, f (-i) := expect_image neg_injective.injOn

set_option backward.isDefEq.respectTransparency false in
/-
**Finset._root_.map_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.map_expect {F : Type*} [FunLike F M N] [LinearMapClass F ℚ≥0 M N]
    (g : F) (f : ι → M) (s : Finset ι) :
    g (𝔼 i ∈ s, f i) = 𝔼 i ∈ s, g (f i) := by simp only [expect, map_smul, map_sum]

@[simp]
/-
**Finset.card_smul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_smul_expect (s : Finset ι) (f : ι -> M) : #s • 𝔼 i in s, f i = ∑ i in
 s, f i
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_empty`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] (f : ι → M),   (∅.expect fun i => f i) = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.Nonempty.card_ne_zero`：∀ {α : Type u_1} {s : Finset α}, s.Nonempt
y → s.card ≠ 0
-/
lemma card_smul_expect (s : Finset ι) (f : ι → M) : #s • 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, ← Nat.cast_smul_eq_nsmul ℚ≥0, smul_inv_smul₀]
    exact mod_cast hs.card_ne_zero
/-
**Finset._root_.Fintype.card_smul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Fintype.card_smul_expect [Fintype ι] (f : ι → M) :
    Fintype.card ι • 𝔼 i, f i = ∑ i, f i := Finset.card_smul_expect _ _
/-
**Finset.expect_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : _root_.
Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (s.expect fun _i => a) =
 a
参数：a : M；s.expect fun _i => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.Nonempty.card_ne_zero`：∀ {α : Type u_1} {s : Finset α}, s.Nonempt
y → s.card ≠ 0
-/
@[simp] lemma expect_const (hs : s.Nonempty) (a : M) : 𝔼 _i ∈ s, a = a := by
  rw [expect, sum_const, ← Nat.cast_smul_eq_nsmul ℚ≥0, inv_smul_smul₀]
  exact mod_cast hs.card_ne_zero
/-
**Finset.smul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_expect {G : Type*} [DistribSMul G M] [SMulCommClass G Rat>=0 M] (a : 
G) (s : Finset ι) (f : ι -> M) : a • 𝔼 i in s, f i = 𝔼 i in s, a • f i
参数：a : G；s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_expect {G : Type*} [DistribSMul G M] [SMulCommClass G ℚ≥0 M] (a : G)
    (s : Finset ι) (f : ι → M) : a • 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a • f i := by
  simp only [expect, smul_sum, smul_comm]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M] [Module ℚ≥0 M]

/-
**Finset.expect_sub_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_sub_distrib (s : Finset ι) (f g : ι -> M) : 𝔼 i in s, (f i - g i) =
 𝔼 i in s, f i - 𝔼 i in s, g i
参数：s : Finset ι；f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_sub_distrib (s : Finset ι) (f g : ι → M) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  simp only [expect, sum_sub_distrib, smul_sub]

@[simp]
/-
**Finset.expect_neg_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_neg_distrib (s : Finset ι) (f : ι -> M) : 𝔼 i in s, -f i = -𝔼 i in 
s, f i
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_neg_distrib (s : Finset ι) (f : ι → M) : 𝔼 i ∈ s, -f i = -𝔼 i ∈ s, f i := by
  simp [expect]

end AddCommGroup

section Semiring
variable [Semiring M] [Module ℚ≥0 M]

/-
**Finset.card_mul_expect** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : Semiring M] [inst_1 : _root_.Modul
e ℚ≥0 M] (s : Finset ι) (f : ι → M),   (↑s.card * s.expect fun i => f i) = ∑ i ∈
 s, f i
参数：s : Finset ι；f : ι → M；↑s.card * s.expect fun i => f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `Finset.card_smul_expect`：card_smul_expect (s : Finset ι) (f : ι -> M) : 
#s • 𝔼 i in s, f i = ∑ i in s, f i
-/
@[simp] lemma card_mul_expect (s : Finset ι) (f : ι → M) :
    #s * 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by rw [← nsmul_eq_mul, card_smul_expect]
/-
**Finset._root_.Fintype.card_mul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Fintype.card_mul_expect [Fintype ι] (f : ι → M) :
    Fintype.card ι * 𝔼 i, f i = ∑ i, f i := Finset.card_mul_expect _ _
/-
**Finset.expect_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_mul [IsScalarTower Rat>=0 M M] (s : Finset ι) (f : ι -> M) (a : M) 
: (𝔼 i in s, f i) * a = 𝔼 i in s, f i * a
参数：s : Finset ι；f : ι -> M；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
-/
lemma expect_mul [IsScalarTower ℚ≥0 M M] (s : Finset ι) (f : ι → M) (a : M) :
    (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by rw [expect, expect, smul_mul_assoc, sum_mul]
/-
**Finset.mul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_expect [SMulCommClass Rat>=0 M M] (s : Finset ι) (f : ι -> M) (a : M) 
: a * 𝔼 i in s, f i = 𝔼 i in s, a * f i
参数：s : Finset ι；f : ι -> M；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
-/
lemma mul_expect [SMulCommClass ℚ≥0 M M] (s : Finset ι) (f : ι → M) (a : M) :
    a * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a * f i := by rw [expect, expect, mul_smul_comm, mul_sum]
/-
**Finset.expect_mul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_mul_expect [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M] (s
 : Finset ι) (t : Finset κ) (f : ι -> M) (g : κ -> M) : (𝔼 i in s, f i) * 𝔼 j in
 t, g j = 𝔼 i in s, 𝔼 j in t, f i * g j
参数：s : Finset ι；t : Finset κ；f : ι -> M；g : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_mul`：expect_mul [IsScalarTower Rat>=0 M M] (s : Finset ι) 
(f : ι -> M) (a : M) : (𝔼 i in s, f i) * a = 𝔼 i in s, f i * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用引理 `Finset.mul_expect`：mul_expect [SMulCommClass Rat>=0 M M] (s : Finset ι) 
(f : ι -> M) (a : M) : a * 𝔼 i in s, f i = 𝔼 i in s, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (s : Finset ι)
    (t : Finset κ) (f : ι → M) (g : κ → M) :
    (𝔼 i ∈ s, f i) * 𝔼 j ∈ t, g j = 𝔼 i ∈ s, 𝔼 j ∈ t, f i * g j := by
  simp_rw [expect_mul, mul_expect]

end Semiring

section CommSemiring
variable [CommSemiring M] [Module ℚ≥0 M] [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M]

/-
**Finset.expect_pow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_pow (s : Finset ι) (f : ι -> M) (n : Nat) : (𝔼 i in s, f i) ^ n = 𝔼
 p in Fintype.piFinset fun _ : Fin n => s, ∏ i, f (p i)
参数：s : Finset ι；f : ι -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用引理 `Finset.sum_pow'`：sum_pow' (s : Finset κ) (f : κ -> R) (n : Nat) : (∑ a i
n s, f a) ^ n = ∑ p in piFinset fun _i : Fin n => s, ∏ i, f (p i)
· 使用引理 `Fintype.card_piFinset_const`：card_piFinset_const {α : Type*} (s : Finset
 α) (n : Nat) : #(piFinset fun _ : Fin n => s) = #s ^ n
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
-/
lemma expect_pow (s : Finset ι) (f : ι → M) (n : ℕ) :
    (𝔼 i ∈ s, f i) ^ n = 𝔼 p ∈ Fintype.piFinset fun _ : Fin n ↦ s, ∏ i, f (p i) := by
  rw [expect, smul_pow, sum_pow', expect, Fintype.card_piFinset_const, inv_pow, Nat.cast_pow]

end CommSemiring

section Semifield
variable [Semifield K] [CharZero K]

/-
**Finset.expect_indicator_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {K : Type u_3} [inst : Semifield K] [inst_1 : CharZero K]
 [inst_2 : Fintype ι] (s : Finset ι),   (Finset.univ.expect fun i => (↑s).indica
tor 1 i) = ↑s.dens
参数：s : Finset ι；Finset.univ.expect fun i => (↑s).indicator 1 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_indicator_eq_sum_inter`：∀ {ι : Type u_1} {β : Type u_4} [inst
 : AddCommMonoid β] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → β),   ∑ i
 ∈ s, (↑t).indicator f …
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_inv`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p : ℚ≥0), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `NNRat.cast_mul`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p * q) = ↑p * ↑q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_indicator_one [Fintype ι] (s : Finset ι) :
    𝔼 i : ι, (Set.indicator s 1 i : K) = s.dens := by
  classical simp [expect, sum_indicator_eq_sum_inter, dens, div_eq_inv_mul, NNRat.smul_def]
/-
**Finset.expect_boole_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_boole_mul [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι -> K) (i 
: ι) : 𝔼 j, ite (i = j) (Fintype.card ι : K) 0 * f j = f i
参数：f : ι -> K；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_univ`：expect_univ [Fintype ι] : 𝔼 i, f i = (∑ i, f i) /Rat
 Fintype.card ι
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma expect_boole_mul [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → K) (i : ι) :
    𝔼 j, ite (i = j) (Fintype.card ι : K) 0 * f j = f i := by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [← @NNRat.cast_natCast K, ← NNRat.smul_def, inv_smul_smul₀]
  simp [Fintype.card_ne_zero]
/-
**Finset.expect_boole_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι -> K) (i
 : ι) : 𝔼 j, ite (j = i) (Fintype.card ι : K) 0 * f j = f i
参数：f : ι -> K；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.expect_boole_mul`：expect_boole_mul [Fintype ι] [Nonempty ι] [Deci
dableEq ι] (f : ι -> K) (i : ι) : 𝔼 j, ite (i = j) (Fintype.card ι : K) 0 * f j 
= f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → K) (i : ι) :
    𝔼 j, ite (j = i) (Fintype.card ι : K) 0 * f j = f i := by
  simp_rw [@eq_comm _ _ i, expect_boole_mul]
/-
**Finset.expect_eq_sum_div_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_eq_sum_div_card (s : Finset ι) (f : ι -> K) : 𝔼 i in s, f i = (∑ i 
in s, f i) / #s
参数：s : Finset ι；f : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect.eq_1`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι) (f : ι → M),   s.expect f = (
↑s.card)…
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `NNRat.cast_inv`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p : ℚ≥0), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
-/
lemma expect_eq_sum_div_card (s : Finset ι) (f : ι → K) :
    𝔼 i ∈ s, f i = (∑ i ∈ s, f i) / #s := by
  rw [expect, NNRat.smul_def, div_eq_inv_mul, NNRat.cast_inv, NNRat.cast_natCast]
/-
**Finset._root_.Fintype.expect_eq_sum_div_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Fintype.expect_eq_sum_div_card [Fintype ι] (f : ι → K) :
    𝔼 i, f i = (∑ i, f i) / Fintype.card ι := Finset.expect_eq_sum_div_card _ _
/-
**Finset.expect_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_div (s : Finset ι) (f : ι -> K) (a : K) : (𝔼 i in s, f i) / a = 𝔼 i
 in s, f i / a
参数：s : Finset ι；f : ι -> K；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.expect_mul`：expect_mul [IsScalarTower Rat>=0 M M] (s : Finset ι) 
(f : ι -> M) (a : M) : (𝔼 i in s, f i) * a = 𝔼 i in s, f i * a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_div (s : Finset ι) (f : ι → K) (a : K) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, expect_mul]

end Semifield

/-
**Finset.expect_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_6} {π : α → Type u_7} [inst : (a : α) → CommS
emiring (π a)]   [inst_1 : (a : α) → _root_.Module ℚ≥0 (π a)] (s : Finset ι) (f 
: ι → (a : α) → π a) (a : α),   s.expect (fun i => f i) a = s.expect fun i => f 
i a
参数：a : α；π a；a : α；π a；s : Finset ι；f : ι → (a : α) → π a；a : α；fun i => f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_apply {α : Type*} {π : α → Type*} [∀ a, CommSemiring (π a)]
    [∀ a, Module ℚ≥0 (π a)] (s : Finset ι) (f : ι → ∀ a, π a) (a : α) :
    (𝔼 i ∈ s, f i) a = 𝔼 i ∈ s, f i a := by simp [expect]

end Finset

namespace algebraMap
variable [Semifield M] [CharZero M] [Semifield N] [CharZero N] [Algebra M N]

@[simp, norm_cast]
/-
**algebraMap.coe_expect** 是 Mathlib 中的一个引理，位于命名空间 `algebraMap`。
形式化陈述：coe_expect (s : Finset ι) (f : ι -> M) : 𝔼 i in s, f i = 𝔼 i in s, (f i : 
N)
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
lemma coe_expect (s : Finset ι) (f : ι → M) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : N) :=
  map_expect (algebraMap _ _) _ _

end algebraMap

namespace Fintype
variable [Fintype ι] [Fintype κ]

section AddCommMonoid
variable [AddCommMonoid M] [Module ℚ≥0 M]

/-- `Fintype.expect_bijective` is a variant of `Finset.expect_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.expect_comp` for a version without `h`. -/
/-
**Fintype.expect_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_bijective (e : ι -> κ) (he : Bijective e) (f : ι -> M) (g : κ -> M)
 (h : forall i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i
参数：e : ι -> κ；he : Bijective e；f : ι -> M；g : κ -> M；h : forall i, f i = g (e i)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.expect_nbij`：expect_nbij (i : ι -> κ) (hi : forall a in s, i a in
 t) (h : forall a in s, f a = g (i a)) (i_inj : (s : Set ι).InjOn i) (i_surj : (
s : Set …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f

--- 原说明 ---
`Fintype.expect_bijective` is a variant of `Finset.expect_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.expect_comp` for a version without `h`.
-/
lemma expect_bijective (e : ι → κ) (he : Bijective e) (f : ι → M) (g : κ → M)
    (h : ∀ i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i :=
  expect_nbij e (fun _ _ ↦ mem_univ _) (fun i _ ↦ h i) he.injective.injOn <| by
    simpa using he.surjective

/-- `Fintype.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments.

See `Equiv.expect_comp` for a version without `h`. -/
/-
**Fintype.expect_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : forall i, f i = g 
(e i)) : 𝔼 i, f i = 𝔼 i, g i
参数：e : ι ≃ κ；f : ι -> M；g : κ -> M；h : forall i, f i = g (e i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.expect_bijective`：expect_bijective (e : ι -> κ) (he : Bijective 
e) (f : ι -> M) (g : κ -> M) (h : forall i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
`Fintype.expect_equiv` is a specialization of `Finset.expect_bij` that automatic
ally fills in
most arguments.

See `Equiv.expect_comp` for a version without `h`.
-/
lemma expect_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ i, f i = g (e i)) :
    𝔼 i, f i = 𝔼 i, g i := expect_bijective _ e.bijective f g h
/-
**Fintype.expect_const** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_const [Nonempty ι] (a : M) : 𝔼 _i : ι, a = a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
-/
lemma expect_const [Nonempty ι] (a : M) : 𝔼 _i : ι, a = a := Finset.expect_const univ_nonempty _
/-
**Fintype.expect_ite_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_ite_zero (p : ι -> Prop) [DecidablePred p] (h : forall i j, p i -> 
p j -> i = j) (a : M) : 𝔼 i, ite (p i) a 0 = ite (exists i, p i) (a /Rat Fintype
.card ι) 0
参数：p : ι -> Prop；h : forall i j, p i -> p j -> i = j；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_ite_zero`：expect_ite_zero (s : Finset ι) (p : ι -> Prop) [
DecidablePred p] (h : forall i in s, forall j in s, p i -> p j -> i = j) (a : M)
 : 𝔼 i in s,…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_ite_zero (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : M) :
    𝔼 i, ite (p i) a 0 = ite (∃ i, p i) (a /ℚ Fintype.card ι) 0 := by
  simp [univ.expect_ite_zero p (by simpa using h)]

variable [DecidableEq ι]
/-
**Fintype.expect_ite_mem** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [inst_1 : AddCommMonoid
 M] [inst_2 : _root_.Module ℚ≥0 M]   [inst_3 : DecidableEq ι] (s : Finset ι) (f 
: ι → M),   (Finset.univ.expect fun i => if i ∈ s then f i else 0) = s.dens • s.
expect fun i => f i
参数：s : Finset ι；f : ι → M；Finset.univ.expect fun i => if i ∈ s then f i else 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_ite_mem`：expect_ite_mem (s t : Finset ι) (f : ι -> M) : 𝔼 
i in s, (if i in t then f i else 0) = (#(s inter t) / #s : Rat>=0) • 𝔼 i in s in
ter t, f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_ite_mem (s : Finset ι) (f : ι → M) :
    𝔼 i, (if i ∈ s then f i else 0) = s.dens • 𝔼 i ∈ s, f i := by
  simp [Finset.expect_ite_mem, dens]
/-
**Fintype.expect_dite_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_dite_eq (i : ι) (f : forall j, i = j -> M) : 𝔼 j, (if h : i = j the
n f j h else 0) = f i rfl /Rat card ι
参数：i : ι；f : forall j, i = j -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_dite_eq`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMo
noid M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι]
 (i : ι) (f…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    𝔼 j, (if h : i = j then f j h else 0) = f i rfl /ℚ card ι := by simp
/-
**Fintype.expect_dite_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_dite_eq' (i : ι) (f : forall j, j = i -> M) : 𝔼 j, (if h : j = i th
en f j h else 0) = f i rfl /Rat card ι
参数：i : ι；f : forall j, j = i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_dite_eq'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommM
onoid M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι
] (i : ι) (f…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → M) :
    𝔼 j, (if h : j = i then f j h else 0) = f i rfl /ℚ card ι := by simp
/-
**Fintype.expect_ite_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_ite_eq (i : ι) (f : ι -> M) : 𝔼 j, (if i = j then f j else 0) = f i
 /Rat card ι
参数：i : ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_ite_eq`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι] 
(i : ι) (f…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_ite_eq (i : ι) (f : ι → M) :
    𝔼 j, (if i = j then f j else 0) = f i /ℚ card ι := by simp
/-
**Fintype.expect_ite_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_ite_eq' (i : ι) (f : ι -> M) : 𝔼 j, (if j = i then f j else 0) = f 
i /Rat card ι
参数：i : ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_ite_eq'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMo
noid M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι}   [inst_2 : DecidableEq ι]
 (i : ι) (f…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_ite_eq' (i : ι) (f : ι → M) :
    𝔼 j, (if j = i then f j else 0) = f i /ℚ card ι := by simp

end AddCommMonoid

section Semiring
variable [Semiring M] [Module ℚ≥0 M]

/-
**Fintype.expect_one** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_one [Nonempty ι] : 𝔼 _i : ι, (1 : M) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.expect_const`：expect_const [Nonempty ι] (a : M) : 𝔼 _i : ι, a = 
a
-/
lemma expect_one [Nonempty ι] : 𝔼 _i : ι, (1 : M) = 1 := expect_const _
/-
**Fintype.expect_mul_expect** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_mul_expect [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M] (f
 : ι -> M) (g : κ -> M) : (𝔼 i, f i) * 𝔼 j, g j = 𝔼 i, 𝔼 j, f i * g j
参数：f : ι -> M；g : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.expect_mul_expect`：expect_mul_expect [IsScalarTower Rat>=0 M M] [
SMulCommClass Rat>=0 M M] (s : Finset ι) (t : Finset κ) (f : ι -> M) (g : κ -> M
) : (𝔼 i in s,…
-/
lemma expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (f : ι → M)
    (g : κ → M) : (𝔼 i, f i) * 𝔼 j, g j = 𝔼 i, 𝔼 j, f i * g j :=
  Finset.expect_mul_expect ..

end Semiring
end Fintype

