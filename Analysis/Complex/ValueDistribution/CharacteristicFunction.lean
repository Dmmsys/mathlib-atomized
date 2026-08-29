/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
# The Characteristic Function of Value Distribution Theory

This file defines the "characteristic function" attached to a meromorphic function defined on the
complex plane. Also known as "Nevanlinna Height", this is one of the three main functions used in
Value Distribution Theory.

The characteristic function plays a role analogous to the height function in number theory: both
measure the "complexity" of objects. For rational functions, the characteristic function grows like
the degree times the logarithm, much like the logarithmic height in number theory reflects the
degree of an algebraic number.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Characterize rational functions in terms of the growth rate of their characteristic function, as
  discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].
-/

@[expose] public section

open Filter Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {f g : Complex -> E} {a : WithTop E}

variable (f a) in
/--
Definition of `characteristic` / `characteristic` 的定义

English:
definition characteristic
  signature: : Real -> Real
  body: proximity f a + logCounting f a

中文:
定义 characteristic
  签名: : 实数 -> 实数
  定义体: proximity f a + logCounting f a

Depends on / 依赖: logCounting, proximity
-/
noncomputable def characteristic : Real -> Real := proximity f a + logCounting f a

/-!
## Elementary Properties
-/

/--
theorem `characteristic_congr_codiscrete` / 定理 `characteristic_congr_codiscrete`

English:
theorem characteristic_congr_codiscrete
  given: {r : Real} (hfg : f =ᶠ[codiscrete Complex] g) (hr : r != 0)
  proof: by
  simp [characteristic, proximity_congr_codiscrete hfg hr, logCounting_congr_codiscrete hfg]

中文:
定理 characteristic_congr_codiscrete
  条件: {r : 实数} (hfg : f =ᶠ[codiscrete 复形] g) (hr : r != 0)
  证明: by
  simp [characteristic, proximity_congr_codiscrete hfg hr, logCounting_congr_codiscrete hfg]

Depends on / 依赖: characteristic, logCounting_congr_codiscrete, proximity_congr_codiscrete
-/
theorem characteristic_congr_codiscrete {r : Real} (hfg : f =ᶠ[codiscrete Complex] g) (hr : r != 0) :
    characteristic f a r = characteristic g a r := by
  simp [characteristic, proximity_congr_codiscrete hfg hr, logCounting_congr_codiscrete hfg]

/--
The difference between the characteristic functions for the poles of `f` and `f - const` simplifies
to the difference between the proximity functions.
-/
@[simp]
/--
lemma `characteristic_sub_characteristic_eq_proximity_sub_proximity` / 引理 `characteristic_sub_characteristic_eq_proximity_sub_proximity`

English:
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity
  given: (h : Meromorphic f) (a₀ : E)
  proof: by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

中文:
引理 characteristic_sub_characteristic_eq_proximity_sub_proximity
  条件: (h : 亚纯 f) (a₀ : E)
  证明: by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

Depends on / 依赖: Pi.sub_def, characteristic, logCounting_sub_const, sub_def
-/
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromorphic f) (a₀ : E) :
    characteristic f ⊤ - characteristic (f · - a₀) ⊤ = proximity f ⊤ - proximity (f · - a₀) ⊤ := by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

/--
theorem `characteristic_even` / 定理 `characteristic_even`

English:
theorem characteristic_even
  proof: proximity_even.add logCounting_even

中文:
定理 characteristic_even
  证明: proximity_even.add logCounting_even

Depends on / 依赖: logCounting_even, proximity_even, proximity_even.add
-/
theorem characteristic_even :
    (characteristic f a).Even := proximity_even.add logCounting_even

/--
theorem `characteristic_nonneg` / 定理 `characteristic_nonneg`

English:
theorem characteristic_nonneg
  given: {r : Real} (hr : 1 <= r)
  proof: add_nonneg (proximity_nonneg r) (logCounting_nonneg hr)

中文:
定理 characteristic_nonneg
  条件: {r : 实数} (hr : 1 <= r)
  证明: add_nonneg (proximity_nonneg r) (logCounting_nonneg hr)

Depends on / 依赖: add_nonneg, logCounting_nonneg, proximity_nonneg
-/
theorem characteristic_nonneg {r : Real} (hr : 1 <= r) :
    0 <= characteristic f a r :=
  add_nonneg (proximity_nonneg r) (logCounting_nonneg hr)

/--
theorem `characteristic_eventually_nonneg` / 定理 `characteristic_eventually_nonneg`

English:
theorem characteristic_eventually_nonneg
  proof: by
  filter_upwards [Filter.eventually_ge_atTop 1] using fun _ hr => by simp [characteristic_nonneg hr]

中文:
定理 characteristic_eventually_nonneg
  证明: by
  filter_upwards [Filter.eventually_ge_atTop 1] using fun _ hr => by simp [characteristic_nonneg hr]

Depends on / 依赖: Filter, Filter.eventually_ge_atTop, characteristic_nonneg, eventually_ge_atTop, filter_upwards
-/
theorem characteristic_eventually_nonneg :
    0 <=ᶠ[Filter.atTop] characteristic f a := by
  filter_upwards [Filter.eventually_ge_atTop 1] using fun _ hr => by simp [characteristic_nonneg hr]

/-!
## Behaviour under Arithmetic Operations
-/

/--
theorem `characteristic_sum_top_le` / 定理 `characteristic_sum_top_le`

English:
theorem characteristic_sum_top_le
  statement: {α : Type*} (s : Finset α) (f : α -> Complex -> E) {r : Real}
  proof: by
  simp only [characteristic, Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ a in s, f a) ⊤ r + logCounting (∑ a in s, f a) ⊤ r
  _ <= ((∑ a in s, proximity (f a) ⊤) r) + log s.card + (∑ a in s, (logCounting (f a) ⊤)) r := by
      gcongr
      · apply proximity_sum_top_le s f hf r
      · ap

中文:
定理 characteristic_sum_top_le
  结论: {α : 类型} (s : 有限集 α) (f : α -> 复形 -> E) {r : 实数}
  证明: by
  simp only [characteristic, Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ a in s, f a) ⊤ r + logCounting (∑ a in s, f a) ⊤ r
  _ <= ((∑ a in s, proximity (f a) ⊤) r) + log s.card + (∑ a in s, (logCounting (f a) ⊤)) r := by
      gcongr
      · apply proximity_sum_top_le s f hf r
      · ap

Depends on / 依赖: Finset, Finset.sum_apply, Pi.add_apply, add_apply, characteristic, logCounting, logCounting_sum_top_le, proximity, proximity_sum_top_le, s.card, sum_apply
-/
theorem characteristic_sum_top_le {α : Type*} (s : Finset α) (f : α -> Complex -> E) {r : Real}
    (hf : forall a in s, Meromorphic (f a)) (hr : 1 <= r) :
    characteristic (∑ a in s, f a) ⊤ r <= (∑ a in s, (characteristic (f a) ⊤)) r + log s.card := by
  simp only [characteristic, Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ a in s, f a) ⊤ r + logCounting (∑ a in s, f a) ⊤ r
  _ <= ((∑ a in s, proximity (f a) ⊤) r) + log s.card + (∑ a in s, (logCounting (f a) ⊤)) r := by
      gcongr
      · apply proximity_sum_top_le s f hf r
      · apply logCounting_sum_top_le s f hf hr
    _ = ((∑ a in s, proximity (f a) ⊤) r) + (∑ a in s, (logCounting (f a) ⊤)) r + log s.card := by
      ring
    _ = ∑ x in s, (proximity (f x) ⊤ r + logCounting (f x) ⊤ r) + log s.card := by
      simp [Finset.sum_add_distrib]

/--
theorem `characteristic_sum_top_eventuallyLE` / 定理 `characteristic_sum_top_eventuallyLE`

English:
theorem characteristic_sum_top_eventuallyLE
  statement: {α : Type*} (s : Finset α) (f : α -> Complex -> E)
  proof: by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_sum_top_le s f hf hr

中文:
定理 characteristic_sum_top_eventuallyLE
  结论: {α : 类型} (s : 有限集 α) (f : α -> 复形 -> E)
  证明: by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_sum_top_le s f hf hr

Depends on / 依赖: Filter, Filter.eventually_ge_atTop, characteristic_sum_top_le, eventually_ge_atTop, filter_upwards
-/
theorem characteristic_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α -> Complex -> E)
    (hf : forall a in s, Meromorphic (f a)) :
    characteristic (∑ a in s, f a) ⊤
      <=ᶠ[Filter.atTop] ∑ a in s, (characteristic (f a) ⊤) + fun _ => log s.card := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_sum_top_le s f hf hr

/--
theorem `characteristic_add_top_le` / 定理 `characteristic_add_top_le`

English:
theorem characteristic_add_top_le
  statement: {f₁ f₂ : Complex -> E} {r : Real} (h₁f₁ : Meromorphic f₁)
  proof: by
  have h_meromorphic : forall a in Finset.univ, Meromorphic (![f₁, f₂] a) := by
    simpa using ⟨h₁f₁, h₁f₂⟩
  simpa using characteristic_sum_top_le Finset.univ ![f₁, f₂] h_meromorphic hr

中文:
定理 characteristic_add_top_le
  结论: {f₁ f₂ : 复形 -> E} {r : 实数} (h₁f₁ : 亚纯 f₁)
  证明: by
  have h_meromorphic : forall a in Finset.univ, Meromorphic (![f₁, f₂] a) := by
    simpa using ⟨h₁f₁, h₁f₂⟩
  simpa using characteristic_sum_top_le Finset.univ ![f₁, f₂] h_meromorphic hr

Depends on / 依赖: Finset, Finset.univ, Meromorphic, characteristic_sum_top_le, h_meromorphic
-/
theorem characteristic_add_top_le {f₁ f₂ : Complex -> E} {r : Real} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 <= r) :
    characteristic (f₁ + f₂) ⊤ r <= characteristic f₁ ⊤ r + characteristic f₂ ⊤ r + log 2 := by
  have h_meromorphic : forall a in Finset.univ, Meromorphic (![f₁, f₂] a) := by
    simpa using ⟨h₁f₁, h₁f₂⟩
  simpa using characteristic_sum_top_le Finset.univ ![f₁, f₂] h_meromorphic hr

/--
theorem `characteristic_add_top_eventuallyLE` / 定理 `characteristic_add_top_eventuallyLE`

English:
theorem characteristic_add_top_eventuallyLE
  statement: {f₁ f₂ : Complex -> E} (h₁f₁ : Meromorphic f₁)
  proof: by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

中文:
定理 characteristic_add_top_eventuallyLE
  结论: {f₁ f₂ : 复形 -> E} (h₁f₁ : 亚纯 f₁)
  证明: by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

Depends on / 依赖: Filter, Filter.eventually_ge_atTop, characteristic_add_top_le, eventually_ge_atTop, filter_upwards
-/
theorem characteristic_add_top_eventuallyLE {f₁ f₂ : Complex -> E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ + f₂) ⊤
      <=ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ + fun _ => log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

/--
theorem `characteristic_mul_zero_le` / 定理 `characteristic_mul_zero_le`

English:
theorem characteristic_mul_zero_le
  statement: {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 <= r)
  proof: by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_zero_le h₁f₁ h₁f₂ r)
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

中文:
定理 characteristic_mul_zero_le
  结论: {f₁ f₂ : 复形 -> 复形} {r : 实数} (hr : 1 <= r)
  证明: by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_zero_le h₁f₁ h₁f₂ r)
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

Depends on / 依赖: Pi.add_apply, add_add_add_comm, add_apply, add_le_add, characteristic, logCounting_mul_zero_le, proximity_mul_zero_le
-/
theorem characteristic_mul_zero_le {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 <= r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    characteristic (f₁ * f₂) 0 r <= (characteristic f₁ 0 + characteristic f₂ 0) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_zero_le h₁f₁ h₁f₂ r)
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
theorem `characteristic_mul_zero_eventuallyLE` / 定理 `characteristic_mul_zero_eventuallyLE`

English:
theorem characteristic_mul_zero_eventuallyLE
  statement: {f₁ f₂ : Complex -> Complex}
  proof: by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

中文:
定理 characteristic_mul_zero_eventuallyLE
  结论: {f₁ f₂ : 复形 -> 复形}
  证明: by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

Depends on / 依赖: Filter, Filter.eventually_ge_atTop, characteristic_mul_zero_le, eventually_ge_atTop, filter_upwards
-/
theorem characteristic_mul_zero_eventuallyLE {f₁ f₂ : Complex -> Complex}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    characteristic (f₁ * f₂) 0 <=ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
theorem `characteristic_mul_top_le` / 定理 `characteristic_mul_top_le`

English:
theorem characteristic_mul_top_le
  statement: {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 <= r)
  proof: by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r)
    (logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

中文:
定理 characteristic_mul_top_le
  结论: {f₁ f₂ : 复形 -> 复形} {r : 实数} (hr : 1 <= r)
  证明: by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r)
    (logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

Depends on / 依赖: Pi.add_apply, add_add_add_comm, add_apply, add_le_add, characteristic, logCounting_mul_top_le, proximity_mul_top_le
-/
theorem characteristic_mul_top_le {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 <= r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    characteristic (f₁ * f₂) ⊤ r <= (characteristic f₁ ⊤ + characteristic f₂ ⊤) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r)
    (logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
theorem `characteristic_mul_top_eventuallyLE` / 定理 `characteristic_mul_top_eventuallyLE`

English:
theorem characteristic_mul_top_eventuallyLE
  statement: {f₁ f₂ : Complex -> Complex}
  proof: by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

中文:
定理 characteristic_mul_top_eventuallyLE
  结论: {f₁ f₂ : 复形 -> 复形}
  证明: by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

Depends on / 依赖: Filter, Filter.eventually_ge_atTop, characteristic_mul_top_le, eventually_ge_atTop, filter_upwards
-/
theorem characteristic_mul_top_eventuallyLE {f₁ f₂ : Complex -> Complex}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) :
    characteristic (f₁ * f₂) ⊤ <=ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr => characteristic_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For natural numbers `n`, the characteristic function for the zeros of `f ^ n` equals `n` times the
characteristic counting function for the zeros of `f`.
-/
@[simp]
/--
theorem `characteristic_pow_zero` / 定理 `characteristic_pow_zero`

English:
theorem characteristic_pow_zero
  given: {f : Complex -> Complex} {n : Nat} (hf : Meromorphic f)
  proof: by
  simp_all [characteristic]

中文:
定理 characteristic_pow_zero
  条件: {f : 复形 -> 复形} {n : 自然数} (hf : 亚纯 f)
  证明: by
  simp_all [characteristic]

Depends on / 依赖: characteristic
-/
theorem characteristic_pow_zero {f : Complex -> Complex} {n : Nat} (hf : Meromorphic f) :
    characteristic (f ^ n) 0 = n • characteristic f 0 := by
  simp_all [characteristic]

/--
For natural numbers `n`, the characteristic function for the poles of `f ^ n` equals `n` times the
characteristic function for the poles of `f`.
-/
@[simp]
/--
theorem `characteristic_pow_top` / 定理 `characteristic_pow_top`

English:
theorem characteristic_pow_top
  given: {f : Complex -> Complex} {n : Nat} (hf : Meromorphic f)
  proof: by
  simp_all [characteristic]

中文:
定理 characteristic_pow_top
  条件: {f : 复形 -> 复形} {n : 自然数} (hf : 亚纯 f)
  证明: by
  simp_all [characteristic]

Depends on / 依赖: characteristic
-/
theorem characteristic_pow_top {f : Complex -> Complex} {n : Nat} (hf : Meromorphic f) :
    characteristic (f ^ n) ⊤ = n • characteristic f ⊤ := by
  simp_all [characteristic]

end ValueDistribution
