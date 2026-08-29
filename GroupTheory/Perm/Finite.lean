/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations on `Fintype`s

This file contains miscellaneous lemmas about `Equiv.Perm` and `Equiv.swap`, building on top
of those in `Mathlib/Logic/Equiv/Basic.lean` and other files in `Mathlib/GroupTheory/Perm/*`.
-/

public section

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} {β : Type v}

-- An example on how to determine the order of an element of a finite group.
-- import Mathlib.Data.Int.Order.Units
-- example : orderOf (-1 : ℤˣ) = 2 :=
-- orderOf_eq_prime (Int.units_sq _) (by decide)

namespace Equiv.Perm

section Conjugation

variable [DecidableEq α] [Fintype α] {σ τ : Perm α}

/--
theorem `isConj_of_support_equiv` / 定理 `isConj_of_support_equiv`

English:
theorem isConj_of_support_equiv
  proof: by
  refine isConj_iff.2 ⟨Equiv.extendSubtype f, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x in σ.support
  · rw [Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_apply_of_mem]
    · exact hf x (Finset.mem_coe.2 hx)
  · rwa [Classical.not_not.1 ((not_congr mem_support).1 (Equiv.extendSubtype_not_mem f _ _)),
      Classical.not_not.1 ((not_congr mem_support).mp hx)]

中文:
定理 isConj_of_support_equiv
  证明: by
  refine isConj_iff.2 ⟨Equiv.extendSubtype f, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x in σ.support
  · rw [Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_apply_of_mem]
    · exact hf x (Finset.mem_coe.2 hx)
  · rwa [Classical.not_not.1 ((not_congr mem_support).1 (Equiv.extendSubtype_not_mem f _ _)),
      Classical.not_not.1 ((not_congr mem_support).mp hx)]

Depends on / 依赖: Classical, Classical.not_not, Equiv.extendSubtype, Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_not_mem, Finset, Finset.mem_coe, Perm.mul_apply, extendSubtype, extendSubtype_apply_of_mem, extendSubtype_not_mem, isConj_iff, mem_coe, mem_support, mul_apply, mul_inv_eq_iff_eq_mul, not_congr, not_not, support
-/
theorem isConj_of_support_equiv
    (f : { x // x in (σ.support : Set α) } ≃ { x // x in (τ.support : Set α) })
    (hf : forall (x : α) (hx : x in (σ.support : Set α)),
      (f ⟨σ x, apply_mem_support.2 hx⟩ : α) = τ ↑(f ⟨x, hx⟩)) :
    IsConj σ τ := by
  refine isConj_iff.2 ⟨Equiv.extendSubtype f, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x in σ.support
  · rw [Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_apply_of_mem]
    · exact hf x (Finset.mem_coe.2 hx)
  · rwa [Classical.not_not.1 ((not_congr mem_support).1 (Equiv.extendSubtype_not_mem f _ _)),
      Classical.not_not.1 ((not_congr mem_support).mp hx)]

end Conjugation

/--
theorem `perm_symm_on_of_perm_on_finset` / 定理 `perm_symm_on_of_perm_on_finset`

English:
theorem perm_symm_on_of_perm_on_finset
  statement: {s : Finset α} {f : Perm α} (h : forall x in s, f x in s) {y : α}
  proof: by
  have h0 : forall y in s, exists (x : _) (hx : x in s), y = (fun i (_ : i in s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i _ => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp heq) rfl.ge
  obtain ⟨y2, hy2, rfl⟩ := h0 y hy
  simpa using hy2

中文:
定理 perm_symm_on_of_perm_on_finset
  结论: {s : 有限集 α} {f : 置换 α} (h : 对任意 x in s, f x in s) {y : α}
  证明: by
  have h0 : forall y in s, exists (x : _) (hx : x in s), y = (fun i (_ : i in s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i _ => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp heq) rfl.ge
  obtain ⟨y2, hy2, rfl⟩ := h0 y hy
  simpa using hy2

Depends on / 依赖: Equiv.apply_eq_iff_eq, Finset, Finset.surj_on_of_inj_on_of_card_le, apply_eq_iff_eq, rfl.ge, surj_on_of_inj_on_of_card_le
-/
theorem perm_symm_on_of_perm_on_finset {s : Finset α} {f : Perm α} (h : forall x in s, f x in s) {y : α}
    (hy : y in s) : f.symm y in s := by
  have h0 : forall y in s, exists (x : _) (hx : x in s), y = (fun i (_ : i in s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i _ => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp heq) rfl.ge
  obtain ⟨y2, hy2, rfl⟩ := h0 y hy
  simpa using hy2

/--
theorem `perm_symm_mapsTo_of_mapsTo` / 定理 `perm_symm_mapsTo_of_mapsTo`

English:
theorem perm_symm_mapsTo_of_mapsTo
  given: (f : Perm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s)
  proof: by
  cases nonempty_fintype s
  exact fun x hx =>
Set.mem_toFinset.mp
      perm_symm_on_of_perm_on_finset
        (fun a ha => Set.mem_toFinset.mpr (h (Set.mem_toFinset.mp ha)))
        (Set.mem_toFinset.mpr hx)

@[simp]

中文:
定理 perm_symm_mapsTo_of_mapsTo
  条件: (f : 置换 α) {s : 集合 α} [有限 s] (h : 集合.映射到 f s s)
  证明: by
  cases nonempty_fintype s
  exact fun x hx =>
Set.mem_toFinset.mp
      perm_symm_on_of_perm_on_finset
        (fun a ha => Set.mem_toFinset.mpr (h (Set.mem_toFinset.mp ha)))
        (Set.mem_toFinset.mpr hx)

@[simp]

Depends on / 依赖: Set.mem_toFinset.mp, Set.mem_toFinset.mpr, mem_toFinset, nonempty_fintype, perm_symm_on_of_perm_on_finset
-/
theorem perm_symm_mapsTo_of_mapsTo (f : Perm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s) :
    Set.MapsTo f.symm s s := by
  cases nonempty_fintype s
  exact fun x hx =>
Set.mem_toFinset.mp
      perm_symm_on_of_perm_on_finset
        (fun a ha => Set.mem_toFinset.mpr (h (Set.mem_toFinset.mp ha)))
        (Set.mem_toFinset.mpr hx)

@[simp]
/--
theorem `perm_symm_mapsTo_iff_mapsTo` / 定理 `perm_symm_mapsTo_iff_mapsTo`

English:
theorem perm_symm_mapsTo_iff_mapsTo
  given: {f : Perm α} {s : Set α} [Finite s]
  proof: ⟨perm_symm_mapsTo_of_mapsTo f⁻¹, perm_symm_mapsTo_of_mapsTo f⟩

中文:
定理 perm_symm_mapsTo_iff_mapsTo
  条件: {f : 置换 α} {s : 集合 α} [有限 s]
  证明: ⟨perm_symm_mapsTo_of_mapsTo f⁻¹, perm_symm_mapsTo_of_mapsTo f⟩

Depends on / 依赖: perm_symm_mapsTo_of_mapsTo
-/
theorem perm_symm_mapsTo_iff_mapsTo {f : Perm α} {s : Set α} [Finite s] :
    Set.MapsTo f.symm s s ↔ Set.MapsTo f s s :=
  ⟨perm_symm_mapsTo_of_mapsTo f⁻¹, perm_symm_mapsTo_of_mapsTo f⟩

/--
theorem `perm_symm_on_of_perm_on_finite` / 定理 `perm_symm_on_of_perm_on_finite`

English:
theorem perm_symm_on_of_perm_on_finite
  statement: {f : Perm α} {p : α -> Prop} [Finite { x // p x }]
  proof: by
  have : Finite { x | p x } := by simpa
  simpa using perm_symm_mapsTo_of_mapsTo (s := {x | p x}) f h hx

中文:
定理 perm_symm_on_of_perm_on_finite
  结论: {f : 置换 α} {p : α -> 命题} [有限 { x // p x }]
  证明: by
  have : Finite { x | p x } := by simpa
  simpa using perm_symm_mapsTo_of_mapsTo (s := {x | p x}) f h hx

Depends on / 依赖: Finite, perm_symm_mapsTo_of_mapsTo
-/
theorem perm_symm_on_of_perm_on_finite {f : Perm α} {p : α -> Prop} [Finite { x // p x }]
    (h : forall x, p x -> p (f x)) {x : α} (hx : p x) : p (f.symm x) := by
  have : Finite { x | p x } := by simpa
  simpa using perm_symm_mapsTo_of_mapsTo (s := {x | p x}) f h hx

/--
Definition of `subtypePermOfFintype` / `subtypePermOfFintype` 的定义

English:
abbreviation subtypePermOfFintype
  signature: (f : Perm α) {p : α -> Prop} [Finite { x // p x }]
  body: f.subtypePerm fun x => ⟨fun h₂ => f.symm_apply_apply x ▸ perm_symm_on_of_perm_on_finite h h₂, h x⟩

@[simp]

中文:
缩写 subtypePermOfFintype
  签名: (f : 置换 α) {p : α -> 命题} [有限 { x // p x }]
  定义体: f.subtypePerm fun x => ⟨fun h₂ => f.symm_apply_apply x ▸ perm_symm_on_of_perm_on_finite h h₂, h x⟩

@[simp]

Depends on / 依赖: f.subtypePerm, f.symm_apply_apply, perm_symm_on_of_perm_on_finite, subtypePerm, symm_apply_apply
-/
abbrev subtypePermOfFintype (f : Perm α) {p : α -> Prop} [Finite { x // p x }]
    (h : forall x, p x -> p (f x)) : Perm { x // p x } :=
  f.subtypePerm fun x => ⟨fun h₂ => f.symm_apply_apply x ▸ perm_symm_on_of_perm_on_finite h h₂, h x⟩

@[simp]
/--
theorem `subtypePermOfFintype_apply` / 定理 `subtypePermOfFintype_apply`

English:
theorem subtypePermOfFintype_apply
  statement: (f : Perm α) {p : α -> Prop} [Finite { x // p x }]
  proof: rfl

中文:
定理 subtypePermOfFintype_apply
  结论: (f : 置换 α) {p : α -> 命题} [有限 { x // p x }]
  证明: rfl
-/
theorem subtypePermOfFintype_apply (f : Perm α) {p : α -> Prop} [Finite { x // p x }]
    (h : forall x, p x -> p (f x)) (x : { x // p x }) : subtypePermOfFintype f h x = ⟨f x, h x x.2⟩ :=
  rfl

/--
theorem `subtypePermOfFintype_one` / 定理 `subtypePermOfFintype_one`

English:
theorem subtypePermOfFintype_one
  statement: (p : α -> Prop) [Finite { x // p x }]
  proof: rfl

中文:
定理 subtypePermOfFintype_one
  结论: (p : α -> 命题) [有限 { x // p x }]
  证明: rfl
-/
theorem subtypePermOfFintype_one (p : α -> Prop) [Finite { x // p x }]
    (h : forall x, p x -> p ((1 : Perm α) x)) : @subtypePermOfFintype α 1 p _ h = 1 :=
  rfl

/--
theorem `perm_mapsTo_inl_iff_mapsTo_inr` / 定理 `perm_mapsTo_inl_iff_mapsTo_inr`

English:
theorem perm_mapsTo_inl_iff_mapsTo_inr
  given: {m n : Type*} [Finite m] [Finite n] (σ : Perm (m oplus n))
  proof: by
  constructor <;>
    ( intro h
      classical
        rw [← perm_symm_mapsTo_iff_mapsTo] at h
        intro x
        rcases hx : σ x with l | r)
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
    grind
  · rintro _; exact ⟨r, rfl⟩
  · rintro _; exact ⟨l, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
    grind

中文:
定理 perm_mapsTo_inl_iff_mapsTo_inr
  条件: {m n : 类型} [有限 m] [有限 n] (σ : 置换 (m oplus n))
  证明: by
  constructor <;>
    ( intro h
      classical
        rw [← perm_symm_mapsTo_iff_mapsTo] at h
        intro x
        rcases hx : σ x with l | r)
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
    grind
  · rintro _; exact ⟨r, rfl⟩
  · rintro _; exact ⟨l, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
    grind

Depends on / 依赖: classical, perm_symm_mapsTo_iff_mapsTo
-/
theorem perm_mapsTo_inl_iff_mapsTo_inr {m n : Type*} [Finite m] [Finite n] (σ : Perm (m oplus n)) :
    Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) ↔
      Set.MapsTo σ (Set.range Sum.inr) (Set.range Sum.inr) := by
  constructor <;>
    ( intro h
      classical
        rw [← perm_symm_mapsTo_iff_mapsTo] at h
        intro x
        rcases hx : σ x with l | r)
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
    grind
  · rintro _; exact ⟨r, rfl⟩
  · rintro _; exact ⟨l, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
    grind

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mem_sumCongrHom_range_of_perm_mapsTo_inl` / 定理 `mem_sumCongrHom_range_of_perm_mapsTo_inl`

English:
theorem mem_sumCongrHom_range_of_perm_mapsTo_inl
  statement: {m n : Type*} [Finite m] [Finite n]
  proof: by
  have h1 : forall x : m oplus n, (exists a : m, Sum.inl a = x) -> exists a : m, Sum.inl a = σ x := by
    rintro _ ⟨a, rfl⟩; exact h ⟨a, rfl⟩
  have h3 : forall x : m oplus n, (exists b : n, Sum.inr b = x) -> exists b : n, Sum.inr b = σ x := by
    rintro _ ⟨b, rfl⟩; exact (perm_mapsTo_inl_iff_mapsTo_inr σ).mp h ⟨b, rfl⟩
  let σ₁' := subtypePermOfFintype σ h1
  let σ₂' := subtypePermOfFintype σ h3
  let σ₁ := permCongr (Equiv.ofInjective _ Sum.inl_injective).symm σ₁'
  let σ₂ := permCongr (Equiv.ofInjective _ Sum.inr_injective).symm σ₂'
  rw [MonoidHom.mem_range]; rw [Prod.exists]
  use σ₁, σ₂
  rw [Perm.sumCongrHom_apply]
  ext (a | b)
  · rw [Equiv.sumCongr_apply, Sum.map_inl, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inl_injective, ofInjective_apply]
    rfl
  · rw [Equiv.sumCongr_apply, Sum.map_inr, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inr_injective, ofInjective_apply]
    rfl

nonrec theorem Disjoint.orderOf {σ τ : Perm α} (hστ : Disjoint σ τ) :
    orderOf (σ * τ) = Nat.lcm (orderOf σ) (orderOf τ) :=
  haveI h : forall n : Nat, (σ * τ) ^ n = 1 ↔ σ ^ n = 1 ∧ τ ^ n = 1 := fun n => by
    rw [hστ.commute.mul_pow]; rw [Disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n)]
  Nat.dvd_antisymm hστ.commute.orderOf_mul_dvd_lcm
    (Nat.lcm_dvd
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).1)
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).2))

中文:
定理 mem_sumCongrHom_range_of_perm_mapsTo_inl
  结论: {m n : 类型} [有限 m] [有限 n]
  证明: by
  have h1 : forall x : m oplus n, (exists a : m, Sum.inl a = x) -> exists a : m, Sum.inl a = σ x := by
    rintro _ ⟨a, rfl⟩; exact h ⟨a, rfl⟩
  have h3 : forall x : m oplus n, (exists b : n, Sum.inr b = x) -> exists b : n, Sum.inr b = σ x := by
    rintro _ ⟨b, rfl⟩; exact (perm_mapsTo_inl_iff_mapsTo_inr σ).mp h ⟨b, rfl⟩
  let σ₁' := subtypePermOfFintype σ h1
  let σ₂' := subtypePermOfFintype σ h3
  let σ₁ := permCongr (Equiv.ofInjective _ Sum.inl_injective).symm σ₁'
  let σ₂ := permCongr (Equiv.ofInjective _ Sum.inr_injective).symm σ₂'
  rw [MonoidHom.mem_range]; rw [Prod.exists]
  use σ₁, σ₂
  rw [Perm.sumCongrHom_apply]
  ext (a | b)
  · rw [Equiv.sumCongr_apply, Sum.map_inl, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inl_injective, ofInjective_apply]
    rfl
  · rw [Equiv.sumCongr_apply, Sum.map_inr, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inr_injective, ofInjective_apply]
    rfl

nonrec theorem Disjoint.orderOf {σ τ : Perm α} (hστ : Disjoint σ τ) :
    orderOf (σ * τ) = Nat.lcm (orderOf σ) (orderOf τ) :=
  haveI h : forall n : Nat, (σ * τ) ^ n = 1 ↔ σ ^ n = 1 ∧ τ ^ n = 1 := fun n => by
    rw [hστ.commute.mul_pow]; rw [Disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n)]
  Nat.dvd_antisymm hστ.commute.orderOf_mul_dvd_lcm
    (Nat.lcm_dvd
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).1)
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).2))

Depends on / 依赖: Equiv.ofInjective, Sum.inl, Sum.inl_injective, Sum.inr, inl_injective, ofInjective, permCongr, perm_mapsTo_inl_iff_mapsTo_inr, subtypePermOfFintype
-/
theorem mem_sumCongrHom_range_of_perm_mapsTo_inl {m n : Type*} [Finite m] [Finite n]
    {σ : Perm (m oplus n)} (h : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl)) :
    σ in (sumCongrHom m n).range := by
  have h1 : forall x : m oplus n, (exists a : m, Sum.inl a = x) -> exists a : m, Sum.inl a = σ x := by
    rintro _ ⟨a, rfl⟩; exact h ⟨a, rfl⟩
  have h3 : forall x : m oplus n, (exists b : n, Sum.inr b = x) -> exists b : n, Sum.inr b = σ x := by
    rintro _ ⟨b, rfl⟩; exact (perm_mapsTo_inl_iff_mapsTo_inr σ).mp h ⟨b, rfl⟩
  let σ₁' := subtypePermOfFintype σ h1
  let σ₂' := subtypePermOfFintype σ h3
  let σ₁ := permCongr (Equiv.ofInjective _ Sum.inl_injective).symm σ₁'
  let σ₂ := permCongr (Equiv.ofInjective _ Sum.inr_injective).symm σ₂'
  rw [MonoidHom.mem_range]; rw [Prod.exists]
  use σ₁, σ₂
  rw [Perm.sumCongrHom_apply]
  ext (a | b)
  · rw [Equiv.sumCongr_apply, Sum.map_inl, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inl_injective, ofInjective_apply]
    rfl
  · rw [Equiv.sumCongr_apply, Sum.map_inr, permCongr_apply, Equiv.symm_symm,
      apply_ofInjective_symm Sum.inr_injective, ofInjective_apply]
    rfl

nonrec theorem Disjoint.orderOf {σ τ : Perm α} (hστ : Disjoint σ τ) :
    orderOf (σ * τ) = Nat.lcm (orderOf σ) (orderOf τ) :=
  haveI h : forall n : Nat, (σ * τ) ^ n = 1 ↔ σ ^ n = 1 ∧ τ ^ n = 1 := fun n => by
    rw [hστ.commute.mul_pow]; rw [Disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n)]
  Nat.dvd_antisymm hστ.commute.orderOf_mul_dvd_lcm
    (Nat.lcm_dvd
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).1)
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).2))

/--
theorem `Disjoint.extendDomain` / 定理 `Disjoint.extendDomain`

English:
theorem Disjoint.extendDomain
  statement: {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)
  proof: by
  intro b
  by_cases pb : p b
  · refine (h (f.symm ⟨b, pb⟩)).imp ?_ ?_ <;>
      · intro h
        rw [extendDomain_apply_subtype _ _ pb]; rw [h]; rw [apply_symm_apply]; rw [Subtype.coe_mk]
  · left
    rw [extendDomain_apply_not_subtype _ _ pb]

中文:
定理 Disjoint.extendDomain
  结论: {p : β -> 命题} [DecidablePred p] (f : α ≃ 子类型 p)
  证明: by
  intro b
  by_cases pb : p b
  · refine (h (f.symm ⟨b, pb⟩)).imp ?_ ?_ <;>
      · intro h
        rw [extendDomain_apply_subtype _ _ pb]; rw [h]; rw [apply_symm_apply]; rw [Subtype.coe_mk]
  · left
    rw [extendDomain_apply_not_subtype _ _ pb]

Depends on / 依赖: Subtype, Subtype.coe_mk, apply_symm_apply, coe_mk, extendDomain_apply_not_subtype, extendDomain_apply_subtype, f.symm
-/
theorem Disjoint.extendDomain {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)
    {σ τ : Perm α} (h : Disjoint σ τ) : Disjoint (σ.extendDomain f) (τ.extendDomain f) := by
  intro b
  by_cases pb : p b
  · refine (h (f.symm ⟨b, pb⟩)).imp ?_ ?_ <;>
      · intro h
        rw [extendDomain_apply_subtype _ _ pb]; rw [h]; rw [apply_symm_apply]; rw [Subtype.coe_mk]
  · left
    rw [extendDomain_apply_not_subtype _ _ pb]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Disjoint.isConj_mul` / 定理 `Disjoint.isConj_mul`

English:
theorem Disjoint.isConj_mul
  statement: [Finite α] {σ τ π ρ : Perm α} (hc1 : IsConj σ π)
  proof: by
  classical
  cases nonempty_fintype α
  obtain ⟨f, rfl⟩ := isConj_iff.1 hc1
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc2
  have hd1' := coe_inj.2 hd1.support_mul
  have hd2' := coe_inj.2 hd2.support_mul
  rw [coe_union] at *
  have hd1'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd1)
  have hd2'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd2)
  refine isConj_of_support_equiv ?_ ?_
· refine ((Equiv.setCongr hd1').trans (Equiv.Set.union hd1'')).trans
      (Equiv.sumCongr (subtypeEquiv f fun a => ?_) <| subtypeEquiv g fun a => ?_).trans
        ((Equiv.setCongr hd2').trans (Equiv.Set.union hd2'')).symm <;>
      simp only [Set.mem_image, toEmbedding_apply, exists_eq_right, support_conj, coe_map,
        apply_eq_iff_eq]
  intro x hx
  simp only [trans_apply, symm_trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply,
    Equiv.sumCongr_apply]
  rw [hd1']; rw [Set.mem_union] at hx
  rcases hx with hxσ | hxτ
  · rw [mem_coe, mem_support] at hxσ
    rw [Set.union_apply_left]; rw [Set.union_apply_left]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inl, comp_apply,
        Set.union_symm_apply_left, Subtype.coe_mk, apply_eq_iff_eq, coe_inv]
      have h := (hd2 (f x)).resolve_left ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [h]; rw [symm_apply_apply]; rw [(hd1 x).resolve_left hxσ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 x).resolve_left hxσ, mem_coe,
        apply_mem_support, mem_support]
  · rw [mem_coe, ← apply_mem_support, mem_support] at hxτ
    rw [Set.union_apply_right]; rw [Set.union_apply_right]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inr, comp_apply,
        Set.union_symm_apply_right, Subtype.coe_mk]
      have h := (hd2 (g (τ x))).resolve_right ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [coe_inv]; rw [coe_inv]; rw [symm_apply_apply]; rw [h]; rw [(hd1 (τ x)).resolve_right hxτ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, ← apply_mem_support, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 (τ x)).resolve_right hxτ,
        mem_coe, mem_support]

中文:
定理 Disjoint.isConj_mul
  结论: [有限 α] {σ τ π ρ : 置换 α} (hc1 : IsConj σ π)
  证明: by
  classical
  cases nonempty_fintype α
  obtain ⟨f, rfl⟩ := isConj_iff.1 hc1
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc2
  have hd1' := coe_inj.2 hd1.support_mul
  have hd2' := coe_inj.2 hd2.support_mul
  rw [coe_union] at *
  have hd1'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd1)
  have hd2'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd2)
  refine isConj_of_support_equiv ?_ ?_
· refine ((Equiv.setCongr hd1').trans (Equiv.Set.union hd1'')).trans
      (Equiv.sumCongr (subtypeEquiv f fun a => ?_) <| subtypeEquiv g fun a => ?_).trans
        ((Equiv.setCongr hd2').trans (Equiv.Set.union hd2'')).symm <;>
      simp only [Set.mem_image, toEmbedding_apply, exists_eq_right, support_conj, coe_map,
        apply_eq_iff_eq]
  intro x hx
  simp only [trans_apply, symm_trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply,
    Equiv.sumCongr_apply]
  rw [hd1']; rw [Set.mem_union] at hx
  rcases hx with hxσ | hxτ
  · rw [mem_coe, mem_support] at hxσ
    rw [Set.union_apply_left]; rw [Set.union_apply_left]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inl, comp_apply,
        Set.union_symm_apply_left, Subtype.coe_mk, apply_eq_iff_eq, coe_inv]
      have h := (hd2 (f x)).resolve_left ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [h]; rw [symm_apply_apply]; rw [(hd1 x).resolve_left hxσ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 x).resolve_left hxσ, mem_coe,
        apply_mem_support, mem_support]
  · rw [mem_coe, ← apply_mem_support, mem_support] at hxτ
    rw [Set.union_apply_right]; rw [Set.union_apply_right]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inr, comp_apply,
        Set.union_symm_apply_right, Subtype.coe_mk]
      have h := (hd2 (g (τ x))).resolve_right ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [coe_inv]; rw [coe_inv]; rw [symm_apply_apply]; rw [h]; rw [(hd1 (τ x)).resolve_right hxτ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, ← apply_mem_support, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 (τ x)).resolve_right hxτ,
        mem_coe, mem_support]

Depends on / 依赖: Equiv.Set.union, Equiv.setCongr, Equiv.sumCongr, classical, coe_inj, coe_union, disjoint_coe, disjoint_iff_disjoint_support, hd1.support_mul, hd2.support_mul, isConj_iff, isConj_of_support_equiv, nonempty_fintype, setCongr, subtypeEquiv, sumCongr, support_mul
-/
theorem Disjoint.isConj_mul [Finite α] {σ τ π ρ : Perm α} (hc1 : IsConj σ π)
    (hc2 : IsConj τ ρ) (hd1 : Disjoint σ τ) (hd2 : Disjoint π ρ) : IsConj (σ * τ) (π * ρ) := by
  classical
  cases nonempty_fintype α
  obtain ⟨f, rfl⟩ := isConj_iff.1 hc1
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc2
  have hd1' := coe_inj.2 hd1.support_mul
  have hd2' := coe_inj.2 hd2.support_mul
  rw [coe_union] at *
  have hd1'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd1)
  have hd2'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd2)
  refine isConj_of_support_equiv ?_ ?_
· refine ((Equiv.setCongr hd1').trans (Equiv.Set.union hd1'')).trans
      (Equiv.sumCongr (subtypeEquiv f fun a => ?_) <| subtypeEquiv g fun a => ?_).trans
        ((Equiv.setCongr hd2').trans (Equiv.Set.union hd2'')).symm <;>
      simp only [Set.mem_image, toEmbedding_apply, exists_eq_right, support_conj, coe_map,
        apply_eq_iff_eq]
  intro x hx
  simp only [trans_apply, symm_trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply,
    Equiv.sumCongr_apply]
  rw [hd1']; rw [Set.mem_union] at hx
  rcases hx with hxσ | hxτ
  · rw [mem_coe, mem_support] at hxσ
    rw [Set.union_apply_left]; rw [Set.union_apply_left]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inl, comp_apply,
        Set.union_symm_apply_left, Subtype.coe_mk, apply_eq_iff_eq, coe_inv]
      have h := (hd2 (f x)).resolve_left ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [h]; rw [symm_apply_apply]; rw [(hd1 x).resolve_left hxσ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 x).resolve_left hxσ, mem_coe,
        apply_mem_support, mem_support]
  · rw [mem_coe, ← apply_mem_support, mem_support] at hxτ
    rw [Set.union_apply_right]; rw [Set.union_apply_right]
    · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inr, comp_apply,
        Set.union_symm_apply_right, Subtype.coe_mk]
      have h := (hd2 (g (τ x))).resolve_right ?_
      · rw [mul_apply, mul_apply, coe_inv] at h
        rw [coe_inv]; rw [coe_inv]; rw [symm_apply_apply]; rw [h]; rw [(hd1 (τ x)).resolve_right hxτ]
      · rwa [mul_apply, mul_apply, coe_inv, symm_apply_apply, apply_eq_iff_eq]
    · rwa [Subtype.coe_mk, mem_coe, ← apply_mem_support, mem_support]
    · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 (τ x)).resolve_right hxτ,
        mem_coe, mem_support]

/--
theorem `apply_mem_fixedPoints_iff_mem_of_mem_centralizer` / 定理 `apply_mem_fixedPoints_iff_mem_of_mem_centralizer`

English:
theorem apply_mem_fixedPoints_iff_mem_of_mem_centralizer
  statement: {g p : Perm α}
  proof: by
  simp only [Subgroup.mem_centralizer_singleton_iff] at hp
  simp only [Function.mem_fixedPoints_iff]
  rw [← mul_apply]; rw [← hp]; rw [mul_apply]; rw [EmbeddingLike.apply_eq_iff_eq]

中文:
定理 apply_mem_fixedPoints_iff_mem_of_mem_centralizer
  结论: {g p : 置换 α}
  证明: by
  simp only [Subgroup.mem_centralizer_singleton_iff] at hp
  simp only [Function.mem_fixedPoints_iff]
  rw [← mul_apply]; rw [← hp]; rw [mul_apply]; rw [EmbeddingLike.apply_eq_iff_eq]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Function, Function.mem_fixedPoints_iff, Subgroup, Subgroup.mem_centralizer_singleton_iff, apply_eq_iff_eq, mem_centralizer_singleton_iff, mem_fixedPoints_iff, mul_apply
-/
theorem apply_mem_fixedPoints_iff_mem_of_mem_centralizer {g p : Perm α}
    (hp : p in Subgroup.centralizer {g}) {x : α} :
    p x in Function.fixedPoints g ↔ x in Function.fixedPoints g := by
  simp only [Subgroup.mem_centralizer_singleton_iff] at hp
  simp only [Function.mem_fixedPoints_iff]
  rw [← mul_apply]; rw [← hp]; rw [mul_apply]; rw [EmbeddingLike.apply_eq_iff_eq]

variable [DecidableEq α]

/--
lemma `disjoint_ofSubtype_of_memFixedPoints_self` / 引理 `disjoint_ofSubtype_of_memFixedPoints_self`

English:
lemma disjoint_ofSubtype_of_memFixedPoints_self
  statement: {g : Perm α}
  proof: by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x in Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

中文:
引理 disjoint_ofSubtype_of_memFixedPoints_self
  结论: {g : 置换 α}
  证明: by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x in Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

Depends on / 依赖: Function, Function.fixedPoints, disjoint_iff_eq_or_eq, fixedPoints, ofSubtype_apply_of_not_mem
-/
lemma disjoint_ofSubtype_of_memFixedPoints_self {g : Perm α}
    (u : Perm (Function.fixedPoints g)) :
    Disjoint (ofSubtype u) g := by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x in Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

section Fintype

variable [Fintype α]

/--
theorem `support_pow_coprime` / 定理 `support_pow_coprime`

English:
theorem support_pow_coprime
  given: {σ : Perm α} {n : Nat} (h : Nat.Coprime n (orderOf σ))
  proof: by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  exact
    le_antisymm (support_pow_le σ n)
      (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m))

中文:
定理 support_pow_coprime
  条件: {σ : 置换 α} {n : 自然数} (h : 自然数.Coprime n (orderOf σ))
  证明: by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  exact
    le_antisymm (support_pow_le σ n)
      (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m))

Depends on / 依赖: congr_arg, exists_pow_eq_self_of_coprime, ge_of_eq, le_antisymm, le_trans, support, support_pow_le
-/
theorem support_pow_coprime {σ : Perm α} {n : Nat} (h : Nat.Coprime n (orderOf σ)) :
    (σ ^ n).support = σ.support := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  exact
    le_antisymm (support_pow_le σ n)
      (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m))

/--
lemma `ofSubtype_support_disjoint` / 引理 `ofSubtype_support_disjoint`

English:
lemma ofSubtype_support_disjoint
  given: {σ : Perm α} (x : Perm (Function.fixedPoints σ))
  proof: by
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  rw [mem_support] at ha hb
  exact ha (ofSubtype_apply_of_not_mem x (mt Function.mem_fixedPoints_iff.mp hb))

中文:
引理 ofSubtype_support_disjoint
  条件: {σ : 置换 α} (x : 置换 (函数.fixedPoints σ))
  证明: by
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  rw [mem_support] at ha hb
  exact ha (ofSubtype_apply_of_not_mem x (mt Function.mem_fixedPoints_iff.mp hb))

Depends on / 依赖: Finset, Finset.disjoint_iff_ne, Function, Function.mem_fixedPoints_iff.mp, disjoint_iff_ne, mem_fixedPoints_iff, mem_support, ofSubtype_apply_of_not_mem
-/
lemma ofSubtype_support_disjoint {σ : Perm α} (x : Perm (Function.fixedPoints σ)) :
    _root_.Disjoint x.ofSubtype.support σ.support := by
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  rw [mem_support] at ha hb
  exact ha (ofSubtype_apply_of_not_mem x (mt Function.mem_fixedPoints_iff.mp hb))

open Subgroup

/--
lemma `disjoint_of_disjoint_support` / 引理 `disjoint_of_disjoint_support`

English:
lemma disjoint_of_disjoint_support
  statement: {H K : Subgroup (Perm α)}
  proof: by
  rw [disjoint_iff_inf_le]
  intro x ⟨hx1, hx2⟩
  specialize h x hx1 x hx2
  rwa [disjoint_self, Finset.bot_eq_empty, support_eq_empty_iff] at h

中文:
引理 disjoint_of_disjoint_support
  结论: {H K : 子群 (置换 α)}
  证明: by
  rw [disjoint_iff_inf_le]
  intro x ⟨hx1, hx2⟩
  specialize h x hx1 x hx2
  rwa [disjoint_self, Finset.bot_eq_empty, support_eq_empty_iff] at h

Depends on / 依赖: Finset, Finset.bot_eq_empty, bot_eq_empty, disjoint_iff_inf_le, disjoint_self, specialize, support_eq_empty_iff
-/
lemma disjoint_of_disjoint_support {H K : Subgroup (Perm α)}
    (h : forall a in H, forall b in K, _root_.Disjoint a.support b.support) :
    _root_.Disjoint H K := by
  rw [disjoint_iff_inf_le]
  intro x ⟨hx1, hx2⟩
  specialize h x hx1 x hx2
  rwa [disjoint_self, Finset.bot_eq_empty, support_eq_empty_iff] at h

/--
lemma `support_closure_subset_union` / 引理 `support_closure_subset_union`

English:
lemma support_closure_subset_union
  given: (S : Set (Perm α))
  proof: by
  apply closure_induction
  · exact fun x hx => Set.subset_iUnion₂_of_subset x hx subset_rfl
  · simp
  · intro a b ha hb hc hd
    refine (Finset.coe_subset.mpr (support_mul_le a b)).trans ?_
    rw [Finset.sup_eq_union]; rw [Finset.coe_union]; rw [Set.union_subset_iff]
    exact ⟨hc, hd⟩
  · simp only [support_inv, imp_self, implies_true]

中文:
引理 support_closure_subset_union
  条件: (S : 集合 (置换 α))
  证明: by
  apply closure_induction
  · exact fun x hx => Set.subset_iUnion₂_of_subset x hx subset_rfl
  · simp
  · intro a b ha hb hc hd
    refine (Finset.coe_subset.mpr (support_mul_le a b)).trans ?_
    rw [Finset.sup_eq_union]; rw [Finset.coe_union]; rw [Set.union_subset_iff]
    exact ⟨hc, hd⟩
  · simp only [support_inv, imp_self, implies_true]

Depends on / 依赖: Finset, Finset.coe_subset.mpr, Finset.coe_union, Finset.sup_eq_union, Set.subset_iUnion, Set.union_subset_iff, closure_induction, coe_subset, coe_union, imp_self, implies_true, subset_rfl, sup_eq_union, support_inv, support_mul_le, union_subset_iff
-/
lemma support_closure_subset_union (S : Set (Perm α)) :
    forall a in closure S, (a.support : Set α) subseteq ⋃ b in S, b.support := by
  apply closure_induction
  · exact fun x hx => Set.subset_iUnion₂_of_subset x hx subset_rfl
  · simp
  · intro a b ha hb hc hd
    refine (Finset.coe_subset.mpr (support_mul_le a b)).trans ?_
    rw [Finset.sup_eq_union]; rw [Finset.coe_union]; rw [Set.union_subset_iff]
    exact ⟨hc, hd⟩
  · simp only [support_inv, imp_self, implies_true]

/--
lemma `disjoint_support_closure_of_disjoint_support` / 引理 `disjoint_support_closure_of_disjoint_support`

English:
lemma disjoint_support_closure_of_disjoint_support
  statement: {S T : Set (Perm α)}
  proof: by
  intro a ha b hb
  have key1 := support_closure_subset_union S a ha
  have key2 := support_closure_subset_union T b hb
  have key := Set.disjoint_of_subset key1 key2
  simp_rw [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Finset.disjoint_coe] at key
  exact key h

中文:
引理 disjoint_support_closure_of_disjoint_support
  结论: {S T : 集合 (置换 α)}
  证明: by
  intro a ha b hb
  have key1 := support_closure_subset_union S a ha
  have key2 := support_closure_subset_union T b hb
  have key := Set.disjoint_of_subset key1 key2
  simp_rw [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Finset.disjoint_coe] at key
  exact key h

Depends on / 依赖: Finset, Finset.disjoint_coe, Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Set.disjoint_of_subset, disjoint_coe, disjoint_iUnion_left, disjoint_iUnion_right, disjoint_of_subset, simp_rw, support_closure_subset_union
-/
lemma disjoint_support_closure_of_disjoint_support {S T : Set (Perm α)}
    (h : forall a in S, forall b in T, _root_.Disjoint a.support b.support) :
    forall a in closure S, forall b in closure T, _root_.Disjoint a.support b.support := by
  intro a ha b hb
  have key1 := support_closure_subset_union S a ha
  have key2 := support_closure_subset_union T b hb
  have key := Set.disjoint_of_subset key1 key2
  simp_rw [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Finset.disjoint_coe] at key
  exact key h

/--
lemma `disjoint_closure_of_disjoint_support` / 引理 `disjoint_closure_of_disjoint_support`

English:
lemma disjoint_closure_of_disjoint_support
  statement: {S T : Set (Perm α)}
  proof: by
  apply disjoint_of_disjoint_support
  apply disjoint_support_closure_of_disjoint_support
  exact h

中文:
引理 disjoint_closure_of_disjoint_support
  结论: {S T : 集合 (置换 α)}
  证明: by
  apply disjoint_of_disjoint_support
  apply disjoint_support_closure_of_disjoint_support
  exact h

Depends on / 依赖: disjoint_of_disjoint_support, disjoint_support_closure_of_disjoint_support
-/
lemma disjoint_closure_of_disjoint_support {S T : Set (Perm α)}
    (h : forall a in S, forall b in T, _root_.Disjoint a.support b.support) :
    _root_.Disjoint (closure S) (closure T) := by
  apply disjoint_of_disjoint_support
  apply disjoint_support_closure_of_disjoint_support
  exact h

/--
theorem `mem_range_ofSubtype_iff` / 定理 `mem_range_ofSubtype_iff`

English:
theorem mem_range_ofSubtype_iff
  given: {p : α -> Prop} [DecidablePred p] {g : Perm α}
  proof: by
  constructor
  · rintro ⟨k, rfl⟩ x
    simp only [Finset.mem_coe, mem_support_ofSubtype, Set.mem_ofPred_eq]
    exact fun ⟨hx, _⟩ => hx
  · intro hg
    refine ⟨g.subtypePerm fun x => ?_, ofSubtype_subtypePerm _ fun x hx => hg (mem_support.mpr hx)⟩
    by_cases hx : g x = x
    · rw [hx]
    · refine iff_of_true (hg ?_) (hg ?_) <;> simpa

中文:
定理 mem_range_ofSubtype_iff
  条件: {p : α -> 命题} [DecidablePred p] {g : 置换 α}
  证明: by
  constructor
  · rintro ⟨k, rfl⟩ x
    simp only [Finset.mem_coe, mem_support_ofSubtype, Set.mem_ofPred_eq]
    exact fun ⟨hx, _⟩ => hx
  · intro hg
    refine ⟨g.subtypePerm fun x => ?_, ofSubtype_subtypePerm _ fun x hx => hg (mem_support.mpr hx)⟩
    by_cases hx : g x = x
    · rw [hx]
    · refine iff_of_true (hg ?_) (hg ?_) <;> simpa

Depends on / 依赖: Finset, Finset.mem_coe, Set.mem_ofPred_eq, g.subtypePerm, iff_of_true, mem_coe, mem_ofPred_eq, mem_support, mem_support.mpr, mem_support_ofSubtype, ofSubtype_subtypePerm, subtypePerm
-/
theorem mem_range_ofSubtype_iff {p : α -> Prop} [DecidablePred p] {g : Perm α} :
    g in (ofSubtype : Perm (Subtype p) ->* Perm α).range ↔ (g.support : Set α) subseteq Set.ofPred p := by
  constructor
  · rintro ⟨k, rfl⟩ x
    simp only [Finset.mem_coe, mem_support_ofSubtype, Set.mem_ofPred_eq]
    exact fun ⟨hx, _⟩ => hx
  · intro hg
    refine ⟨g.subtypePerm fun x => ?_, ofSubtype_subtypePerm _ fun x hx => hg (mem_support.mpr hx)⟩
    by_cases hx : g x = x
    · rw [hx]
    · refine iff_of_true (hg ?_) (hg ?_) <;> simpa

end Fintype

end Equiv.Perm
