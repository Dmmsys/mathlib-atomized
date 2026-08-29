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

local notation a " /Rat " q => (q : Rat>=0)⁻¹ • a

/--
Definition of `Finset.expect` / `Finset.expect` 的定义

English:
definition Finset.expect
  signature: [AddCommMonoid M] [Module Rat>=0 M] (s : Finset ι) (f : ι -> M)
  body: (#s : Rat>=0)⁻¹ • ∑ i in s, f i

中文:
定义 有限集.expect
  签名: [加法交换幺半群 M] [模 有理数>=0 M] (s : 有限集 ι) (f : ι -> M)
  定义体: (#s : Rat>=0)⁻¹ • ∑ i in s, f i
-/
def Finset.expect [AddCommMonoid M] [Module Rat>=0 M] (s : Finset ι) (f : ι -> M) : M :=
  (#s : Rat>=0)⁻¹ • ∑ i in s, f i

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
    | some p => `(Finset.expect (Finset.filter (fun $i => $p) $s) (fun $i => $v))
    | none => `(Finset.expect $s (fun $i => $v))

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr
open Batteries.ExtendedBinder

/-- Delaborator for `Finset.expect`. The `pp.funBinderTypes` option controls whether
to show the domain type when the expect is over `Finset.univ`. -/
@[scoped app_delab Finset.expect] meta def delabFinsetExpect : Delab :=
whenPPOption getPPNotation withOverApp 6 do
  let #[_, _, _, _, s, f] := (← getExpr).getAppArgs | failure
guard f.isLambda
  let ppDomain ← getPPOption getPPFunBinderTypes
let (i, body) ← withAppArg withBindingBodyUnusedName fun i => do
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
let ss ← withNaryArg 4 delab
    `(𝔼 $(.mk i):ident in $ss, $body)

end BigOperators

open scoped BigOperators

namespace Finset
section AddCommMonoid
variable [AddCommMonoid M] [Module Rat>=0 M] [AddCommMonoid N] [Module Rat>=0 N] {s t : Finset ι}
  {f g : ι -> M} {p q : ι -> Prop} [DecidablePred p] [DecidablePred q]

/--
lemma `expect_univ` / 引理 `expect_univ`

English:
lemma expect_univ
  given: [Fintype ι]
  statement: 𝔼 i, f i = (∑ i, f i) /Rat Fintype.card ι
  proof: by
  rw [expect]; rw [card_univ]

中文:
引理 expect_univ
  条件: [有限类型 ι]
  结论: 𝔼 i, f i = (∑ i, f i) /有理数 有限类型.card ι
  证明: by
  rw [expect]; rw [card_univ]

Depends on / 依赖: card_univ, expect
-/
lemma expect_univ [Fintype ι] : 𝔼 i, f i = (∑ i, f i) /Rat Fintype.card ι := by
  rw [expect]; rw [card_univ]

/--
lemma `expect_empty` / 引理 `expect_empty`

English:
lemma expect_empty
  given: (f : ι -> M)
  statement: 𝔼 i in ∅, f i = 0
  proof: by simp [expect]

中文:
引理 expect_empty
  条件: (f : ι -> M)
  结论: 𝔼 i in ∅, f i = 0
  证明: by simp [expect]
-/
@[simp] lemma expect_empty (f : ι -> M) : 𝔼 i in ∅, f i = 0 := by simp [expect]

/--
lemma `expect_singleton` / 引理 `expect_singleton`

English:
lemma expect_singleton
  given: (f : ι -> M) (i : ι)
  statement: 𝔼 j in {i}, f j = f i
  proof: by simp [expect]

中文:
引理 expect_singleton
  条件: (f : ι -> M) (i : ι)
  结论: 𝔼 j in {i}, f j = f i
  证明: by simp [expect]
-/
@[simp] lemma expect_singleton (f : ι -> M) (i : ι) : 𝔼 j in {i}, f j = f i := by simp [expect]

/--
lemma `expect_const_zero` / 引理 `expect_const_zero`

English:
lemma expect_const_zero
  given: (s : Finset ι)
  statement: 𝔼 _i in s, (0 : M) = 0
  proof: by simp [expect]

@[congr]

中文:
引理 expect_const_zero
  条件: (s : 有限集 ι)
  结论: 𝔼 _i in s, (0 : M) = 0
  证明: by simp [expect]

@[congr]
-/
@[simp] lemma expect_const_zero (s : Finset ι) : 𝔼 _i in s, (0 : M) = 0 := by simp [expect]

@[congr]
/--
lemma `expect_congr` / 引理 `expect_congr`

English:
lemma expect_congr
  given: {t : Finset ι} (hst : s = t) (h : forall i in t, f i = g i)
  proof: by rw [expect, expect, sum_congr hst h, hst]

中文:
引理 expect_congr
  条件: {t : 有限集 ι} (hst : s = t) (h : 对任意 i in t, f i = g i)
  证明: by rw [expect, expect, sum_congr hst h, hst]

Depends on / 依赖: expect, sum_congr
-/
lemma expect_congr {t : Finset ι} (hst : s = t) (h : forall i in t, f i = g i) :
    𝔼 i in s, f i = 𝔼 i in t, g i := by rw [expect, expect, sum_congr hst h, hst]

/--
lemma `expectWith_congr` / 引理 `expectWith_congr`

English:
lemma expectWith_congr
  given: (hst : s = t) (hpq : forall i in t, p i ↔ q i) (h : forall i in t, q i -> f i = g i)
  proof: expect_congr (by rw [hst, filter_inj'.2 hpq]) by simpa using h

中文:
引理 expectWith_congr
  条件: (hst : s = t) (hpq : 对任意 i in t, p i ↔ q i) (h : 对任意 i in t, q i -> f i = g i)
  证明: expect_congr (by rw [hst, filter_inj'.2 hpq]) by simpa using h

Depends on / 依赖: expect_congr, filter_inj
-/
lemma expectWith_congr (hst : s = t) (hpq : forall i in t, p i ↔ q i) (h : forall i in t, q i -> f i = g i) :
    𝔼 i in s with p i, f i = 𝔼 i in t with q i, g i :=
expect_congr (by rw [hst, filter_inj'.2 hpq]) by simpa using h

/--
lemma `expect_sum_comm` / 引理 `expect_sum_comm`

English:
lemma expect_sum_comm
  given: (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M)
  proof: by
  simpa only [expect, smul_sum] using sum_comm

中文:
引理 expect_sum_comm
  条件: (s : 有限集 ι) (t : 有限集 κ) (f : ι -> κ -> M)
  证明: by
  simpa only [expect, smul_sum] using sum_comm

Depends on / 依赖: expect, smul_sum, sum_comm
-/
lemma expect_sum_comm (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M) :
    𝔼 i in s, ∑ j in t, f i j = ∑ j in t, 𝔼 i in s, f i j := by
  simpa only [expect, smul_sum] using sum_comm

/--
lemma `expect_comm` / 引理 `expect_comm`

English:
lemma expect_comm
  given: (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M)
  proof: by
  rw [expect]; rw [expect]; rw [← expect_sum_comm]; rw [← expect_sum_comm]; rw [expect]; rw [expect]; rw [smul_comm]; rw [sum_comm]

中文:
引理 expect_comm
  条件: (s : 有限集 ι) (t : 有限集 κ) (f : ι -> κ -> M)
  证明: by
  rw [expect]; rw [expect]; rw [← expect_sum_comm]; rw [← expect_sum_comm]; rw [expect]; rw [expect]; rw [smul_comm]; rw [sum_comm]

Depends on / 依赖: expect, expect_sum_comm, smul_comm, sum_comm
-/
lemma expect_comm (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M) :
    𝔼 i in s, 𝔼 j in t, f i j = 𝔼 j in t, 𝔼 i in s, f i j := by
  rw [expect]; rw [expect]; rw [← expect_sum_comm]; rw [← expect_sum_comm]; rw [expect]; rw [expect]; rw [smul_comm]; rw [sum_comm]

/--
lemma `expect_eq_zero` / 引理 `expect_eq_zero`

English:
lemma expect_eq_zero
  given: (h : forall i in s, f i = 0)
  statement: 𝔼 i in s, f i = 0
  proof: (expect_congr rfl h).trans s.expect_const_zero

中文:
引理 expect_eq_zero
  条件: (h : 对任意 i in s, f i = 0)
  结论: 𝔼 i in s, f i = 0
  证明: (expect_congr rfl h).trans s.expect_const_zero

Depends on / 依赖: expect_congr, expect_const_zero, s.expect_const_zero
-/
lemma expect_eq_zero (h : forall i in s, f i = 0) : 𝔼 i in s, f i = 0 :=
  (expect_congr rfl h).trans s.expect_const_zero

/--
lemma `exists_ne_zero_of_expect_ne_zero` / 引理 `exists_ne_zero_of_expect_ne_zero`

English:
lemma exists_ne_zero_of_expect_ne_zero
  given: (h : 𝔼 i in s, f i != 0)
  statement: exists i in s, f i != 0
  proof: by
  contrapose! h; exact expect_eq_zero h

中文:
引理 存在_ne_zero_of_expect_ne_zero
  条件: (h : 𝔼 i in s, f i != 0)
  结论: 存在 i in s, f i != 0
  证明: by
  contrapose! h; exact expect_eq_zero h

Depends on / 依赖: contrapose, expect_eq_zero
-/
lemma exists_ne_zero_of_expect_ne_zero (h : 𝔼 i in s, f i != 0) : exists i in s, f i != 0 := by
  contrapose! h; exact expect_eq_zero h

/--
lemma `expect_add_distrib` / 引理 `expect_add_distrib`

English:
lemma expect_add_distrib
  given: (s : Finset ι) (f g : ι -> M)
  proof: by
  simp [expect, sum_add_distrib]

中文:
引理 expect_add_distrib
  条件: (s : 有限集 ι) (f g : ι -> M)
  证明: by
  simp [expect, sum_add_distrib]

Depends on / 依赖: expect, sum_add_distrib
-/
lemma expect_add_distrib (s : Finset ι) (f g : ι -> M) :
    𝔼 i in s, (f i + g i) = 𝔼 i in s, f i + 𝔼 i in s, g i := by
  simp [expect, sum_add_distrib]

/--
lemma `expect_add_expect_comm` / 引理 `expect_add_expect_comm`

English:
lemma expect_add_expect_comm
  given: (f₁ f₂ g₁ g₂ : ι -> M)
  proof: by
  simp_rw [expect_add_distrib, add_add_add_comm]

中文:
引理 expect_add_expect_comm
  条件: (f₁ f₂ g₁ g₂ : ι -> M)
  证明: by
  simp_rw [expect_add_distrib, add_add_add_comm]

Depends on / 依赖: add_add_add_comm, expect_add_distrib, simp_rw
-/
lemma expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι -> M) :
    𝔼 i in s, (f₁ i + f₂ i) + 𝔼 i in s, (g₁ i + g₂ i) =
      𝔼 i in s, (f₁ i + g₁ i) + 𝔼 i in s, (f₂ i + g₂ i) := by
  simp_rw [expect_add_distrib, add_add_add_comm]

/--
lemma `expect_eq_single_of_mem` / 引理 `expect_eq_single_of_mem`

English:
lemma expect_eq_single_of_mem
  given: (i : ι) (hi : i in s) (h : forall j in s, j != i -> f j = 0)
  proof: by rw [expect, sum_eq_single_of_mem _ hi h]

中文:
引理 expect_eq_single_of_mem
  条件: (i : ι) (hi : i in s) (h : 对任意 j in s, j != i -> f j = 0)
  证明: by rw [expect, sum_eq_single_of_mem _ hi h]

Depends on / 依赖: expect, sum_eq_single_of_mem
-/
lemma expect_eq_single_of_mem (i : ι) (hi : i in s) (h : forall j in s, j != i -> f j = 0) :
    𝔼 i in s, f i = f i /Rat #s := by rw [expect, sum_eq_single_of_mem _ hi h]

/--
lemma `expect_ite_zero` / 引理 `expect_ite_zero`

English:
lemma expect_ite_zero
  statement: (s : Finset ι) (p : ι -> Prop) [DecidablePred p]
  proof: by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

中文:
引理 expect_ite_zero
  结论: (s : 有限集 ι) (p : ι -> 命题) [DecidablePred p]
  证明: by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

Depends on / 依赖: expect, split_ifs, sum_ite_zero
-/
lemma expect_ite_zero (s : Finset ι) (p : ι -> Prop) [DecidablePred p]
    (h : forall i in s, forall j in s, p i -> p j -> i = j) (a : M) :
    𝔼 i in s, ite (p i) a 0 = ite (exists i in s, p i) (a /Rat #s) 0 := by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

section DecidableEq
variable [DecidableEq ι]

/--
lemma `expect_ite_mem` / 引理 `expect_ite_mem`

English:
lemma expect_ite_mem
  given: (s t : Finset ι) (f : ι -> M)
  proof: by
  obtain hst | hst := (s inter t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]

中文:
引理 expect_ite_mem
  条件: (s t : 有限集 ι) (f : ι -> M)
  证明: by
  obtain hst | hst := (s inter t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]

Depends on / 依赖: card_ne_zero, eq_empty_or_nonempty, expect, hst.card_ne_zero, inv_mul_eq_div, smul_smul
-/
lemma expect_ite_mem (s t : Finset ι) (f : ι -> M) :
    𝔼 i in s, (if i in t then f i else 0) = (#(s inter t) / #s : Rat>=0) • 𝔼 i in s inter t, f i := by
  obtain hst | hst := (s inter t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]

/--
lemma `expect_dite_eq` / 引理 `expect_dite_eq`

English:
lemma expect_dite_eq
  given: (i : ι) (f : forall j, i = j -> M)
  proof: by
  split_ifs <;> simp [expect, *]

中文:
引理 expect_dite_eq
  条件: (i : ι) (f : 对任意 j, i = j -> M)
  证明: by
  split_ifs <;> simp [expect, *]
-/
@[simp] lemma expect_dite_eq (i : ι) (f : forall j, i = j -> M) :
    𝔼 j in s, (if h : i = j then f j h else 0) = if i in s then f i rfl /Rat #s else 0 := by
  split_ifs <;> simp [expect, *]

/--
lemma `expect_dite_eq'` / 引理 `expect_dite_eq'`

English:
lemma expect_dite_eq'
  given: (i : ι) (f : forall j, j = i -> M)
  proof: by
  split_ifs <;> simp [expect, *]

中文:
引理 expect_dite_eq'
  条件: (i : ι) (f : 对任意 j, j = i -> M)
  证明: by
  split_ifs <;> simp [expect, *]
-/
@[simp] lemma expect_dite_eq' (i : ι) (f : forall j, j = i -> M) :
    𝔼 j in s, (if h : j = i then f j h else 0) = if i in s then f i rfl /Rat #s else 0 := by
  split_ifs <;> simp [expect, *]

/--
lemma `expect_ite_eq` / 引理 `expect_ite_eq`

English:
lemma expect_ite_eq
  given: (i : ι) (f : ι -> M)
  proof: by
  split_ifs <;> simp [expect, *]

中文:
引理 expect_ite_eq
  条件: (i : ι) (f : ι -> M)
  证明: by
  split_ifs <;> simp [expect, *]
-/
@[simp] lemma expect_ite_eq (i : ι) (f : ι -> M) :
    𝔼 j in s, (if i = j then f j else 0) = if i in s then f i /Rat #s else 0 := by
  split_ifs <;> simp [expect, *]

/--
lemma `expect_ite_eq'` / 引理 `expect_ite_eq'`

English:
lemma expect_ite_eq'
  given: (i : ι) (f : ι -> M)
  proof: by
  split_ifs <;> simp [expect, *]

中文:
引理 expect_ite_eq'
  条件: (i : ι) (f : ι -> M)
  证明: by
  split_ifs <;> simp [expect, *]
-/
@[simp] lemma expect_ite_eq' (i : ι) (f : ι -> M) :
    𝔼 j in s, (if j = i then f j else 0) = if i in s then f i /Rat #s else 0 := by
  split_ifs <;> simp [expect, *]

end DecidableEq

section bij
variable {t : Finset κ} {g : κ -> M}

/--
lemma `expect_bij` / 引理 `expect_bij`

English:
lemma expect_bij
  statement: (i : forall a in s, κ) (hi : forall a ha, i a ha in t) (h : forall a ha, f a = g (i a ha))
  proof: by
  simp_rw [expect, card_bij i hi i_inj i_surj, sum_bij i hi i_inj i_surj h]

中文:
引理 expect_bij
  结论: (i : 对任意 a in s, κ) (hi : 对任意 a ha, i a ha in t) (h : 对任意 a ha, f a = g (i a ha))
  证明: by
  simp_rw [expect, card_bij i hi i_inj i_surj, sum_bij i hi i_inj i_surj h]

Depends on / 依赖: card_bij, expect, i_inj, i_surj, simp_rw, sum_bij
-/
lemma expect_bij (i : forall a in s, κ) (hi : forall a ha, i a ha in t) (h : forall a ha, f a = g (i a ha))
    (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂)
    (i_surj : forall b in t, exists a ha, i a ha = b) : 𝔼 i in s, f i = 𝔼 i in t, g i := by
  simp_rw [expect, card_bij i hi i_inj i_surj, sum_bij i hi i_inj i_surj h]

/--
lemma `expect_bij'` / 引理 `expect_bij'`

English:
lemma expect_bij'
  statement: (i : forall a in s, κ) (j : forall a in t, ι) (hi : forall a ha, i a ha in t)
  proof: by
  simp_rw [expect, card_bij' i j hi hj left_inv right_inv, sum_bij' i j hi hj left_inv right_inv h]

中文:
引理 expect_bij'
  结论: (i : 对任意 a in s, κ) (j : 对任意 a in t, ι) (hi : 对任意 a ha, i a ha in t)
  证明: by
  simp_rw [expect, card_bij' i j hi hj left_inv right_inv, sum_bij' i j hi hj left_inv right_inv h]

Depends on / 依赖: card_bij, expect, left_inv, right_inv, simp_rw, sum_bij
-/
lemma expect_bij' (i : forall a in s, κ) (j : forall a in t, ι) (hi : forall a ha, i a ha in t)
    (hj : forall a ha, j a ha in s) (left_inv : forall a ha, j (i a ha) (hi a ha) = a)
    (right_inv : forall a ha, i (j a ha) (hj a ha) = a) (h : forall a ha, f a = g (i a ha)) :
    𝔼 i in s, f i = 𝔼 i in t, g i := by
  simp_rw [expect, card_bij' i j hi hj left_inv right_inv, sum_bij' i j hi hj left_inv right_inv h]

/--
lemma `expect_nbij` / 引理 `expect_nbij`

English:
lemma expect_nbij
  statement: (i : ι -> κ) (hi : forall a in s, i a in t) (h : forall a in s, f a = g (i a))
  proof: by
  simp_rw [expect, card_nbij i hi i_inj i_surj, sum_nbij i hi i_inj i_surj h]

中文:
引理 expect_nbij
  结论: (i : ι -> κ) (hi : 对任意 a in s, i a in t) (h : 对任意 a in s, f a = g (i a))
  证明: by
  simp_rw [expect, card_nbij i hi i_inj i_surj, sum_nbij i hi i_inj i_surj h]

Depends on / 依赖: card_nbij, expect, i_inj, i_surj, simp_rw, sum_nbij
-/
lemma expect_nbij (i : ι -> κ) (hi : forall a in s, i a in t) (h : forall a in s, f a = g (i a))
    (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) :
    𝔼 i in s, f i = 𝔼 i in t, g i := by
  simp_rw [expect, card_nbij i hi i_inj i_surj, sum_nbij i hi i_inj i_surj h]

/--
lemma `expect_nbij'` / 引理 `expect_nbij'`

English:
lemma expect_nbij'
  statement: (i : ι -> κ) (j : κ -> ι) (hi : forall a in s, i a in t) (hj : forall a in t, j a in s)
  proof: by
  simp_rw [expect, card_nbij' i j hi hj left_inv right_inv,
    sum_nbij' i j hi hj left_inv right_inv h]

中文:
引理 expect_nbij'
  结论: (i : ι -> κ) (j : κ -> ι) (hi : 对任意 a in s, i a in t) (hj : 对任意 a in t, j a in s)
  证明: by
  simp_rw [expect, card_nbij' i j hi hj left_inv right_inv,
    sum_nbij' i j hi hj left_inv right_inv h]

Depends on / 依赖: card_nbij, expect, left_inv, right_inv, simp_rw, sum_nbij
-/
lemma expect_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a in s, i a in t) (hj : forall a in t, j a in s)
    (left_inv : forall a in s, j (i a) = a) (right_inv : forall a in t, i (j a) = a)
    (h : forall a in s, f a = g (i a)) : 𝔼 i in s, f i = 𝔼 i in t, g i := by
  simp_rw [expect, card_nbij' i j hi hj left_inv right_inv,
    sum_nbij' i j hi hj left_inv right_inv h]

/--
lemma `expect_equiv` / 引理 `expect_equiv`

English:
lemma expect_equiv
  given: (e : ι ≃ κ) (hst : forall i, i in s ↔ e i in t) (hfg : forall i in s, f i = g (e i))
  proof: by simp_rw [expect, card_equiv e hst, sum_equiv e hst hfg]

中文:
引理 expect_equiv
  条件: (e : ι ≃ κ) (hst : 对任意 i, i in s ↔ e i in t) (hfg : 对任意 i in s, f i = g (e i))
  证明: by simp_rw [expect, card_equiv e hst, sum_equiv e hst hfg]

Depends on / 依赖: card_equiv, expect, simp_rw, sum_equiv
-/
lemma expect_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i in t) (hfg : forall i in s, f i = g (e i)) :
    𝔼 i in s, f i = 𝔼 i in t, g i := by simp_rw [expect, card_equiv e hst, sum_equiv e hst hfg]

/--
lemma `expect_product` / 引理 `expect_product`

English:
lemma expect_product
  given: (s : Finset ι) (t : Finset κ) (f : ι × κ -> M)
  proof: by
  simp only [expect, card_product, sum_product, smul_sum, mul_inv, mul_smul, Nat.cast_mul]

中文:
引理 expect_product
  条件: (s : 有限集 ι) (t : 有限集 κ) (f : ι × κ -> M)
  证明: by
  simp only [expect, card_product, sum_product, smul_sum, mul_inv, mul_smul, Nat.cast_mul]

Depends on / 依赖: Nat.cast_mul, card_product, cast_mul, expect, mul_inv, mul_smul, smul_sum, sum_product
-/
lemma expect_product (s : Finset ι) (t : Finset κ) (f : ι × κ -> M) :
    𝔼 x in s ×ˢ t, f x = 𝔼 i in s, 𝔼 j in t, f (i, j) := by
  simp only [expect, card_product, sum_product, smul_sum, mul_inv, mul_smul, Nat.cast_mul]

/--
lemma `expect_product'` / 引理 `expect_product'`

English:
lemma expect_product'
  given: (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M)
  proof: by
  simp only [expect, card_product, sum_product', smul_sum, mul_inv, mul_smul, Nat.cast_mul]

@[simp]

中文:
引理 expect_product'
  条件: (s : 有限集 ι) (t : 有限集 κ) (f : ι -> κ -> M)
  证明: by
  simp only [expect, card_product, sum_product', smul_sum, mul_inv, mul_smul, Nat.cast_mul]

@[simp]

Depends on / 依赖: Nat.cast_mul, card_product, cast_mul, expect, mul_inv, mul_smul, smul_sum, sum_product
-/
lemma expect_product' (s : Finset ι) (t : Finset κ) (f : ι -> κ -> M) :
    𝔼 i in s ×ˢ t, f i.1 i.2 = 𝔼 i in s, 𝔼 j in t, f i j := by
  simp only [expect, card_product, sum_product', smul_sum, mul_inv, mul_smul, Nat.cast_mul]

@[simp]
/--
lemma `expect_image` / 引理 `expect_image`

English:
lemma expect_image
  given: [DecidableEq ι] {m : κ -> ι} (hm : (t : Set κ).InjOn m)
  proof: by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

中文:
引理 expect_image
  条件: [DecidableEq ι] {m : κ -> ι} (hm : (t : 集合 κ).单射限制 m)
  证明: by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

Depends on / 依赖: card_image_of_injOn, expect, simp_rw, sum_image
-/
lemma expect_image [DecidableEq ι] {m : κ -> ι} (hm : (t : Set κ).InjOn m) :
    𝔼 i in t.image m, f i = 𝔼 i in t, f (m i) := by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

end bij

/--
lemma `expect_inv_index` / 引理 `expect_inv_index`

English:
lemma expect_inv_index
  given: [DecidableEq ι] [InvolutiveInv ι] (s : Finset ι) (f : ι -> M)
  proof: expect_image inv_injective.injOn

中文:
引理 expect_inv_index
  条件: [DecidableEq ι] [InvolutiveInv ι] (s : 有限集 ι) (f : ι -> M)
  证明: expect_image inv_injective.injOn
-/
@[simp] lemma expect_inv_index [DecidableEq ι] [InvolutiveInv ι] (s : Finset ι) (f : ι -> M) :
    𝔼 i in s⁻¹, f i = 𝔼 i in s, f i⁻¹ := expect_image inv_injective.injOn

/--
lemma `expect_neg_index` / 引理 `expect_neg_index`

English:
lemma expect_neg_index
  given: [DecidableEq ι] [InvolutiveNeg ι] (s : Finset ι) (f : ι -> M)
  proof: expect_image neg_injective.injOn

中文:
引理 expect_neg_index
  条件: [DecidableEq ι] [InvolutiveNeg ι] (s : 有限集 ι) (f : ι -> M)
  证明: expect_image neg_injective.injOn
-/
@[simp] lemma expect_neg_index [DecidableEq ι] [InvolutiveNeg ι] (s : Finset ι) (f : ι -> M) :
    𝔼 i in -s, f i = 𝔼 i in s, f (-i) := expect_image neg_injective.injOn

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.map_expect` / 引理 `_root_.map_expect`

English:
lemma _root_.map_expect
  statement: {F : Type*} [FunLike F M N] [LinearMapClass F Rat>=0 M N]
  proof: by simp only [expect, map_smul, map_sum]

@[simp]

中文:
引理 _root_.map_expect
  结论: {F : 类型} [函数状 F M N] [线性映射类 F 有理数>=0 M N]
  证明: by simp only [expect, map_smul, map_sum]

@[simp]

Depends on / 依赖: expect, map_smul, map_sum
-/
lemma _root_.map_expect {F : Type*} [FunLike F M N] [LinearMapClass F Rat>=0 M N]
    (g : F) (f : ι -> M) (s : Finset ι) :
    g (𝔼 i in s, f i) = 𝔼 i in s, g (f i) := by simp only [expect, map_smul, map_sum]

@[simp]
/--
lemma `card_smul_expect` / 引理 `card_smul_expect`

English:
lemma card_smul_expect
  given: (s : Finset ι) (f : ι -> M)
  statement: #s • 𝔼 i in s, f i = ∑ i in s, f i
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, ← Nat.cast_smul_eq_nsmul Rat>=0, smul_inv_smul₀]
    exact mod_cast hs.card_ne_zero

中文:
引理 card_smul_expect
  条件: (s : 有限集 ι) (f : ι -> M)
  结论: #s • 𝔼 i in s, f i = ∑ i in s, f i
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, ← Nat.cast_smul_eq_nsmul Rat>=0, smul_inv_smul₀]
    exact mod_cast hs.card_ne_zero

Depends on / 依赖: Nat.cast_smul_eq_nsmul, card_ne_zero, cast_smul_eq_nsmul, eq_empty_or_nonempty, expect, hs.card_ne_zero, mod_cast, s.eq_empty_or_nonempty
-/
lemma card_smul_expect (s : Finset ι) (f : ι -> M) : #s • 𝔼 i in s, f i = ∑ i in s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, ← Nat.cast_smul_eq_nsmul Rat>=0, smul_inv_smul₀]
    exact mod_cast hs.card_ne_zero

/--
lemma `_root_.Fintype.card_smul_expect` / 引理 `_root_.Fintype.card_smul_expect`

English:
lemma _root_.Fintype.card_smul_expect
  given: [Fintype ι] (f : ι -> M)
  proof: Finset.card_smul_expect _ _

中文:
引理 _root_.有限类型.card_smul_expect
  条件: [有限类型 ι] (f : ι -> M)
  证明: Finset.card_smul_expect _ _
-/
@[simp] lemma _root_.Fintype.card_smul_expect [Fintype ι] (f : ι -> M) :
    Fintype.card ι • 𝔼 i, f i = ∑ i, f i := Finset.card_smul_expect _ _

/--
lemma `expect_const` / 引理 `expect_const`

English:
lemma expect_const
  given: (hs : s.Nonempty) (a : M)
  statement: 𝔼 _i in s, a = a
  proof: by
  rw [expect]; rw [sum_const]; rw [← Nat.cast_smul_eq_nsmul Rat>=0]; rw [inv_smul_smul₀]
  exact mod_cast hs.card_ne_zero

中文:
引理 expect_const
  条件: (hs : s.非空) (a : M)
  结论: 𝔼 _i in s, a = a
  证明: by
  rw [expect]; rw [sum_const]; rw [← Nat.cast_smul_eq_nsmul Rat>=0]; rw [inv_smul_smul₀]
  exact mod_cast hs.card_ne_zero
-/
@[simp] lemma expect_const (hs : s.Nonempty) (a : M) : 𝔼 _i in s, a = a := by
  rw [expect]; rw [sum_const]; rw [← Nat.cast_smul_eq_nsmul Rat>=0]; rw [inv_smul_smul₀]
  exact mod_cast hs.card_ne_zero

/--
lemma `smul_expect` / 引理 `smul_expect`

English:
lemma smul_expect
  statement: {G : Type*} [DistribSMul G M] [SMulCommClass G Rat>=0 M] (a : G)
  proof: by
  simp only [expect, smul_sum, smul_comm]

中文:
引理 smul_expect
  结论: {G : 类型} [分配标量乘法 G M] [标量交换类 G 有理数>=0 M] (a : G)
  证明: by
  simp only [expect, smul_sum, smul_comm]

Depends on / 依赖: expect, smul_comm, smul_sum
-/
lemma smul_expect {G : Type*} [DistribSMul G M] [SMulCommClass G Rat>=0 M] (a : G)
    (s : Finset ι) (f : ι -> M) : a • 𝔼 i in s, f i = 𝔼 i in s, a • f i := by
  simp only [expect, smul_sum, smul_comm]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M] [Module Rat>=0 M]

/--
lemma `expect_sub_distrib` / 引理 `expect_sub_distrib`

English:
lemma expect_sub_distrib
  given: (s : Finset ι) (f g : ι -> M)
  proof: by
  simp only [expect, sum_sub_distrib, smul_sub]

@[simp]

中文:
引理 expect_sub_distrib
  条件: (s : 有限集 ι) (f g : ι -> M)
  证明: by
  simp only [expect, sum_sub_distrib, smul_sub]

@[simp]

Depends on / 依赖: expect, smul_sub, sum_sub_distrib
-/
lemma expect_sub_distrib (s : Finset ι) (f g : ι -> M) :
    𝔼 i in s, (f i - g i) = 𝔼 i in s, f i - 𝔼 i in s, g i := by
  simp only [expect, sum_sub_distrib, smul_sub]

@[simp]
/--
lemma `expect_neg_distrib` / 引理 `expect_neg_distrib`

English:
lemma expect_neg_distrib
  given: (s : Finset ι) (f : ι -> M)
  statement: 𝔼 i in s, -f i = -𝔼 i in s, f i
  proof: by
  simp [expect]

中文:
引理 expect_neg_distrib
  条件: (s : 有限集 ι) (f : ι -> M)
  结论: 𝔼 i in s, -f i = -𝔼 i in s, f i
  证明: by
  simp [expect]

Depends on / 依赖: expect
-/
lemma expect_neg_distrib (s : Finset ι) (f : ι -> M) : 𝔼 i in s, -f i = -𝔼 i in s, f i := by
  simp [expect]

end AddCommGroup

section Semiring
variable [Semiring M] [Module Rat>=0 M]

/--
lemma `card_mul_expect` / 引理 `card_mul_expect`

English:
lemma card_mul_expect
  given: (s : Finset ι) (f : ι -> M)
  proof: by rw [← nsmul_eq_mul, card_smul_expect]

中文:
引理 card_mul_expect
  条件: (s : 有限集 ι) (f : ι -> M)
  证明: by rw [← nsmul_eq_mul, card_smul_expect]
-/
@[simp] lemma card_mul_expect (s : Finset ι) (f : ι -> M) :
    #s * 𝔼 i in s, f i = ∑ i in s, f i := by rw [← nsmul_eq_mul, card_smul_expect]

/--
lemma `_root_.Fintype.card_mul_expect` / 引理 `_root_.Fintype.card_mul_expect`

English:
lemma _root_.Fintype.card_mul_expect
  given: [Fintype ι] (f : ι -> M)
  proof: Finset.card_mul_expect _ _

中文:
引理 _root_.有限类型.card_mul_expect
  条件: [有限类型 ι] (f : ι -> M)
  证明: Finset.card_mul_expect _ _
-/
@[simp] lemma _root_.Fintype.card_mul_expect [Fintype ι] (f : ι -> M) :
    Fintype.card ι * 𝔼 i, f i = ∑ i, f i := Finset.card_mul_expect _ _

/--
lemma `expect_mul` / 引理 `expect_mul`

English:
lemma expect_mul
  given: [IsScalarTower Rat>=0 M M] (s : Finset ι) (f : ι -> M) (a : M)
  proof: by rw [expect, expect, smul_mul_assoc, sum_mul]

中文:
引理 expect_mul
  条件: [标量塔 有理数>=0 M M] (s : 有限集 ι) (f : ι -> M) (a : M)
  证明: by rw [expect, expect, smul_mul_assoc, sum_mul]

Depends on / 依赖: expect, smul_mul_assoc, sum_mul
-/
lemma expect_mul [IsScalarTower Rat>=0 M M] (s : Finset ι) (f : ι -> M) (a : M) :
    (𝔼 i in s, f i) * a = 𝔼 i in s, f i * a := by rw [expect, expect, smul_mul_assoc, sum_mul]

/--
lemma `mul_expect` / 引理 `mul_expect`

English:
lemma mul_expect
  given: [SMulCommClass Rat>=0 M M] (s : Finset ι) (f : ι -> M) (a : M)
  proof: by rw [expect, expect, mul_smul_comm, mul_sum]

中文:
引理 mul_expect
  条件: [标量交换类 有理数>=0 M M] (s : 有限集 ι) (f : ι -> M) (a : M)
  证明: by rw [expect, expect, mul_smul_comm, mul_sum]

Depends on / 依赖: expect, mul_smul_comm, mul_sum
-/
lemma mul_expect [SMulCommClass Rat>=0 M M] (s : Finset ι) (f : ι -> M) (a : M) :
    a * 𝔼 i in s, f i = 𝔼 i in s, a * f i := by rw [expect, expect, mul_smul_comm, mul_sum]

/--
lemma `expect_mul_expect` / 引理 `expect_mul_expect`

English:
lemma expect_mul_expect
  statement: [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M] (s : Finset ι)
  proof: by
  simp_rw [expect_mul, mul_expect]

中文:
引理 expect_mul_expect
  结论: [标量塔 有理数>=0 M M] [标量交换类 有理数>=0 M M] (s : 有限集 ι)
  证明: by
  simp_rw [expect_mul, mul_expect]

Depends on / 依赖: expect_mul, mul_expect, simp_rw
-/
lemma expect_mul_expect [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M] (s : Finset ι)
    (t : Finset κ) (f : ι -> M) (g : κ -> M) :
    (𝔼 i in s, f i) * 𝔼 j in t, g j = 𝔼 i in s, 𝔼 j in t, f i * g j := by
  simp_rw [expect_mul, mul_expect]

end Semiring

section CommSemiring
variable [CommSemiring M] [Module Rat>=0 M] [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M]

/--
lemma `expect_pow` / 引理 `expect_pow`

English:
lemma expect_pow
  given: (s : Finset ι) (f : ι -> M) (n : Nat)
  proof: by
  rw [expect]; rw [smul_pow]; rw [sum_pow']; rw [expect]; rw [Fintype.card_piFinset_const]; rw [inv_pow]; rw [Nat.cast_pow]

中文:
引理 expect_pow
  条件: (s : 有限集 ι) (f : ι -> M) (n : 自然数)
  证明: by
  rw [expect]; rw [smul_pow]; rw [sum_pow']; rw [expect]; rw [Fintype.card_piFinset_const]; rw [inv_pow]; rw [Nat.cast_pow]

Depends on / 依赖: Fintype, Fintype.card_piFinset_const, Nat.cast_pow, card_piFinset_const, cast_pow, expect, inv_pow, smul_pow, sum_pow
-/
lemma expect_pow (s : Finset ι) (f : ι -> M) (n : Nat) :
    (𝔼 i in s, f i) ^ n = 𝔼 p in Fintype.piFinset fun _ : Fin n => s, ∏ i, f (p i) := by
  rw [expect]; rw [smul_pow]; rw [sum_pow']; rw [expect]; rw [Fintype.card_piFinset_const]; rw [inv_pow]; rw [Nat.cast_pow]

end CommSemiring

section Semifield
variable [Semifield K] [CharZero K]

/--
lemma `expect_indicator_one` / 引理 `expect_indicator_one`

English:
lemma expect_indicator_one
  given: [Fintype ι] (s : Finset ι)
  proof: by
  classical simp [expect, sum_indicator_eq_sum_inter, dens, div_eq_inv_mul, NNRat.smul_def]

中文:
引理 expect_indicator_one
  条件: [有限类型 ι] (s : 有限集 ι)
  证明: by
  classical simp [expect, sum_indicator_eq_sum_inter, dens, div_eq_inv_mul, NNRat.smul_def]
-/
@[simp] lemma expect_indicator_one [Fintype ι] (s : Finset ι) :
    𝔼 i : ι, (Set.indicator s 1 i : K) = s.dens := by
  classical simp [expect, sum_indicator_eq_sum_inter, dens, div_eq_inv_mul, NNRat.smul_def]

/--
lemma `expect_boole_mul` / 引理 `expect_boole_mul`

English:
lemma expect_boole_mul
  given: [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι -> K) (i : ι)
  proof: by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [← @NNRat.cast_natCast K]; rw [← NNRat.smul_def]; rw [inv_smul_smul₀]
  simp [Fintype.card_ne_zero]

中文:
引理 expect_boole_mul
  条件: [有限类型 ι] [非空 ι] [DecidableEq ι] (f : ι -> K) (i : ι)
  证明: by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [← @NNRat.cast_natCast K]; rw [← NNRat.smul_def]; rw [inv_smul_smul₀]
  simp [Fintype.card_ne_zero]

Depends on / 依赖: Fintype, Fintype.card_ne_zero, NNRat.cast_natCast, NNRat.smul_def, card_ne_zero, cast_natCast, expect_univ, if_pos, ite_mul, mem_univ, simp_rw, smul_def, sum_ite_eq, zero_mul
-/
lemma expect_boole_mul [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι -> K) (i : ι) :
    𝔼 j, ite (i = j) (Fintype.card ι : K) 0 * f j = f i := by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [← @NNRat.cast_natCast K]; rw [← NNRat.smul_def]; rw [inv_smul_smul₀]
  simp [Fintype.card_ne_zero]

/--
lemma `expect_boole_mul'` / 引理 `expect_boole_mul'`

English:
lemma expect_boole_mul'
  given: [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι -> K) (i : ι)
  proof: by
  simp_rw [@eq_comm _ _ i, expect_boole_mul]

中文:
引理 expect_boole_mul'
  条件: [有限类型 ι] [非空 ι] [DecidableEq ι] (f : ι -> K) (i : ι)
  证明: by
  simp_rw [@eq_comm _ _ i, expect_boole_mul]

Depends on / 依赖: eq_comm, expect_boole_mul, simp_rw
-/
lemma expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι -> K) (i : ι) :
    𝔼 j, ite (j = i) (Fintype.card ι : K) 0 * f j = f i := by
  simp_rw [@eq_comm _ _ i, expect_boole_mul]

/--
lemma `expect_eq_sum_div_card` / 引理 `expect_eq_sum_div_card`

English:
lemma expect_eq_sum_div_card
  given: (s : Finset ι) (f : ι -> K)
  proof: by
  rw [expect]; rw [NNRat.smul_def]; rw [div_eq_inv_mul]; rw [NNRat.cast_inv]; rw [NNRat.cast_natCast]

中文:
引理 expect_eq_sum_div_card
  条件: (s : 有限集 ι) (f : ι -> K)
  证明: by
  rw [expect]; rw [NNRat.smul_def]; rw [div_eq_inv_mul]; rw [NNRat.cast_inv]; rw [NNRat.cast_natCast]

Depends on / 依赖: NNRat.cast_inv, NNRat.cast_natCast, NNRat.smul_def, cast_inv, cast_natCast, div_eq_inv_mul, expect, smul_def
-/
lemma expect_eq_sum_div_card (s : Finset ι) (f : ι -> K) :
    𝔼 i in s, f i = (∑ i in s, f i) / #s := by
  rw [expect]; rw [NNRat.smul_def]; rw [div_eq_inv_mul]; rw [NNRat.cast_inv]; rw [NNRat.cast_natCast]

/--
lemma `_root_.Fintype.expect_eq_sum_div_card` / 引理 `_root_.Fintype.expect_eq_sum_div_card`

English:
lemma _root_.Fintype.expect_eq_sum_div_card
  given: [Fintype ι] (f : ι -> K)
  proof: Finset.expect_eq_sum_div_card _ _

中文:
引理 _root_.有限类型.expect_eq_sum_div_card
  条件: [有限类型 ι] (f : ι -> K)
  证明: Finset.expect_eq_sum_div_card _ _

Depends on / 依赖: Finset, Finset.expect_eq_sum_div_card, expect_eq_sum_div_card
-/
lemma _root_.Fintype.expect_eq_sum_div_card [Fintype ι] (f : ι -> K) :
    𝔼 i, f i = (∑ i, f i) / Fintype.card ι := Finset.expect_eq_sum_div_card _ _

/--
lemma `expect_div` / 引理 `expect_div`

English:
lemma expect_div
  given: (s : Finset ι) (f : ι -> K) (a : K)
  statement: (𝔼 i in s, f i) / a = 𝔼 i in s, f i / a
  proof: by
  simp_rw [div_eq_mul_inv, expect_mul]

中文:
引理 expect_div
  条件: (s : 有限集 ι) (f : ι -> K) (a : K)
  结论: (𝔼 i in s, f i) / a = 𝔼 i in s, f i / a
  证明: by
  simp_rw [div_eq_mul_inv, expect_mul]

Depends on / 依赖: div_eq_mul_inv, expect_mul, simp_rw
-/
lemma expect_div (s : Finset ι) (f : ι -> K) (a : K) : (𝔼 i in s, f i) / a = 𝔼 i in s, f i / a := by
  simp_rw [div_eq_mul_inv, expect_mul]

end Semifield

/--
lemma `expect_apply` / 引理 `expect_apply`

English:
lemma expect_apply
  statement: {α : Type*} {π : α -> Type*} [forall a, CommSemiring (π a)]
  proof: by simp [expect]

中文:
引理 expect_apply
  结论: {α : 类型} {π : α -> 类型} [对任意 a, 交换半环 (π a)]
  证明: by simp [expect]
-/
@[simp] lemma expect_apply {α : Type*} {π : α -> Type*} [forall a, CommSemiring (π a)]
    [forall a, Module Rat>=0 (π a)] (s : Finset ι) (f : ι -> forall a, π a) (a : α) :
    (𝔼 i in s, f i) a = 𝔼 i in s, f i a := by simp [expect]

end Finset

namespace algebraMap
variable [Semifield M] [CharZero M] [Semifield N] [CharZero N] [Algebra M N]

@[simp, norm_cast]
/--
lemma `coe_expect` / 引理 `coe_expect`

English:
lemma coe_expect
  given: (s : Finset ι) (f : ι -> M)
  statement: 𝔼 i in s, f i = 𝔼 i in s, (f i : N)
  proof: map_expect (algebraMap _ _) _ _

中文:
引理 coe_expect
  条件: (s : 有限集 ι) (f : ι -> M)
  结论: 𝔼 i in s, f i = 𝔼 i in s, (f i : N)
  证明: map_expect (algebraMap _ _) _ _

Depends on / 依赖: algebraMap, map_expect
-/
lemma coe_expect (s : Finset ι) (f : ι -> M) : 𝔼 i in s, f i = 𝔼 i in s, (f i : N) :=
  map_expect (algebraMap _ _) _ _

end algebraMap

namespace Fintype
variable [Fintype ι] [Fintype κ]

section AddCommMonoid
variable [AddCommMonoid M] [Module Rat>=0 M]

/--
lemma `expect_bijective` / 引理 `expect_bijective`

English:
lemma expect_bijective
  statement: (e : ι -> κ) (he : Bijective e) (f : ι -> M) (g : κ -> M)
  proof: expect_nbij e (fun _ _ => mem_univ _) (fun i _ => h i) he.injective.injOn by
    simpa using he.surjective

中文:
引理 expect_bijective
  结论: (e : ι -> κ) (he : 双射 e) (f : ι -> M) (g : κ -> M)
  证明: expect_nbij e (fun _ _ => mem_univ _) (fun i _ => h i) he.injective.injOn by
    simpa using he.surjective

Depends on / 依赖: expect_nbij, he.injective.injOn, he.surjective, injective, mem_univ, surjective
-/
lemma expect_bijective (e : ι -> κ) (he : Bijective e) (f : ι -> M) (g : κ -> M)
    (h : forall i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i :=
expect_nbij e (fun _ _ => mem_univ _) (fun i _ => h i) he.injective.injOn by
    simpa using he.surjective

/--
lemma `expect_equiv` / 引理 `expect_equiv`

English:
lemma expect_equiv
  given: (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : forall i, f i = g (e i))
  proof: expect_bijective _ e.bijective f g h

中文:
引理 expect_equiv
  条件: (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : 对任意 i, f i = g (e i))
  证明: expect_bijective _ e.bijective f g h

Depends on / 依赖: bijective, e.bijective, expect_bijective
-/
lemma expect_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : forall i, f i = g (e i)) :
    𝔼 i, f i = 𝔼 i, g i := expect_bijective _ e.bijective f g h

/--
lemma `expect_const` / 引理 `expect_const`

English:
lemma expect_const
  given: [Nonempty ι] (a : M)
  statement: 𝔼 _i : ι, a = a
  proof: Finset.expect_const univ_nonempty _

中文:
引理 expect_const
  条件: [非空 ι] (a : M)
  结论: 𝔼 _i : ι, a = a
  证明: Finset.expect_const univ_nonempty _

Depends on / 依赖: Finset, Finset.expect_const, expect_const, univ_nonempty
-/
lemma expect_const [Nonempty ι] (a : M) : 𝔼 _i : ι, a = a := Finset.expect_const univ_nonempty _

/--
lemma `expect_ite_zero` / 引理 `expect_ite_zero`

English:
lemma expect_ite_zero
  given: (p : ι -> Prop) [DecidablePred p] (h : forall i j, p i -> p j -> i = j) (a : M)
  proof: by
  simp [univ.expect_ite_zero p (by simpa using h)]

中文:
引理 expect_ite_zero
  条件: (p : ι -> 命题) [DecidablePred p] (h : 对任意 i j, p i -> p j -> i = j) (a : M)
  证明: by
  simp [univ.expect_ite_zero p (by simpa using h)]

Depends on / 依赖: expect_ite_zero, univ.expect_ite_zero
-/
lemma expect_ite_zero (p : ι -> Prop) [DecidablePred p] (h : forall i j, p i -> p j -> i = j) (a : M) :
    𝔼 i, ite (p i) a 0 = ite (exists i, p i) (a /Rat Fintype.card ι) 0 := by
  simp [univ.expect_ite_zero p (by simpa using h)]

variable [DecidableEq ι]

/--
lemma `expect_ite_mem` / 引理 `expect_ite_mem`

English:
lemma expect_ite_mem
  given: (s : Finset ι) (f : ι -> M)
  proof: by
  simp [Finset.expect_ite_mem, dens]

中文:
引理 expect_ite_mem
  条件: (s : 有限集 ι) (f : ι -> M)
  证明: by
  simp [Finset.expect_ite_mem, dens]
-/
@[simp] lemma expect_ite_mem (s : Finset ι) (f : ι -> M) :
    𝔼 i, (if i in s then f i else 0) = s.dens • 𝔼 i in s, f i := by
  simp [Finset.expect_ite_mem, dens]

/--
lemma `expect_dite_eq` / 引理 `expect_dite_eq`

English:
lemma expect_dite_eq
  given: (i : ι) (f : forall j, i = j -> M)
  proof: by simp

中文:
引理 expect_dite_eq
  条件: (i : ι) (f : 对任意 j, i = j -> M)
  证明: by simp
-/
lemma expect_dite_eq (i : ι) (f : forall j, i = j -> M) :
    𝔼 j, (if h : i = j then f j h else 0) = f i rfl /Rat card ι := by simp

/--
lemma `expect_dite_eq'` / 引理 `expect_dite_eq'`

English:
lemma expect_dite_eq'
  given: (i : ι) (f : forall j, j = i -> M)
  proof: by simp

中文:
引理 expect_dite_eq'
  条件: (i : ι) (f : 对任意 j, j = i -> M)
  证明: by simp
-/
lemma expect_dite_eq' (i : ι) (f : forall j, j = i -> M) :
    𝔼 j, (if h : j = i then f j h else 0) = f i rfl /Rat card ι := by simp

/--
lemma `expect_ite_eq` / 引理 `expect_ite_eq`

English:
lemma expect_ite_eq
  given: (i : ι) (f : ι -> M)
  proof: by simp

中文:
引理 expect_ite_eq
  条件: (i : ι) (f : ι -> M)
  证明: by simp
-/
lemma expect_ite_eq (i : ι) (f : ι -> M) :
    𝔼 j, (if i = j then f j else 0) = f i /Rat card ι := by simp

/--
lemma `expect_ite_eq'` / 引理 `expect_ite_eq'`

English:
lemma expect_ite_eq'
  given: (i : ι) (f : ι -> M)
  proof: by simp

中文:
引理 expect_ite_eq'
  条件: (i : ι) (f : ι -> M)
  证明: by simp
-/
lemma expect_ite_eq' (i : ι) (f : ι -> M) :
    𝔼 j, (if j = i then f j else 0) = f i /Rat card ι := by simp

end AddCommMonoid

section Semiring
variable [Semiring M] [Module Rat>=0 M]

/--
lemma `expect_one` / 引理 `expect_one`

English:
lemma expect_one
  given: [Nonempty ι]
  statement: 𝔼 _i : ι, (1 : M) = 1
  proof: expect_const _

中文:
引理 expect_one
  条件: [非空 ι]
  结论: 𝔼 _i : ι, (1 : M) = 1
  证明: expect_const _

Depends on / 依赖: expect_const
-/
lemma expect_one [Nonempty ι] : 𝔼 _i : ι, (1 : M) = 1 := expect_const _

/--
lemma `expect_mul_expect` / 引理 `expect_mul_expect`

English:
lemma expect_mul_expect
  statement: [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M] (f : ι -> M)
  proof: Finset.expect_mul_expect ..

中文:
引理 expect_mul_expect
  结论: [标量塔 有理数>=0 M M] [标量交换类 有理数>=0 M M] (f : ι -> M)
  证明: Finset.expect_mul_expect ..

Depends on / 依赖: Finset, Finset.expect_mul_expect, expect_mul_expect
-/
lemma expect_mul_expect [IsScalarTower Rat>=0 M M] [SMulCommClass Rat>=0 M M] (f : ι -> M)
    (g : κ -> M) : (𝔼 i, f i) * 𝔼 j, g j = 𝔼 i, 𝔼 j, f i * g j :=
  Finset.expect_mul_expect ..

end Semiring
end Fintype
