/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# GCD and LCM operations on finsets

## Main definitions

- `Finset.gcd` - the greatest common denominator of a `Finset` of elements of a `GCDMonoid`
- `Finset.lcm` - the least common multiple of a `Finset` of elements of a `GCDMonoid`

## Implementation notes

Many of the proofs use the lemmas `gcd_def` and `lcm_def`, which relate `Finset.gcd`
and `Finset.lcm` to `Multiset.gcd` and `Multiset.lcm`.

TODO: simplify with a tactic and `Data.Finset.Lattice`

## Tags

finset, gcd
-/

@[expose] public section

variable {ι α β γ : Type*}

namespace Finset

open Multiset

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### lcm -/


section lcm

/--
Definition of `lcm` / `lcm` 的定义

English:
definition lcm
  signature: (s : Finset β) (f : β -> α)
  body: s.fold GCDMonoid.lcm 1 f

中文:
定义 lcm
  签名: (s : Finset β) (f : β -> α)
  定义体: s.fold GCDMonoid.lcm 1 f

Depends on / 依赖: GCDMonoid, GCDMonoid.lcm, s.fold
-/
def lcm (s : Finset β) (f : β -> α) : α :=
  s.fold GCDMonoid.lcm 1 f

variable {s s₁ s₂ : Finset β} {f : β -> α}

/--
theorem `lcm_def` / 定理 `lcm_def`

English:
theorem lcm_def
  statement: s.lcm f = (s.1.map f).lcm
  proof: rfl

@[simp]

中文:
定理 lcm_def
  结论: s.lcm f = (s.1.map f).lcm
  证明: rfl

@[simp]
-/
theorem lcm_def : s.lcm f = (s.1.map f).lcm :=
  rfl

@[simp]
/--
theorem `lcm_empty` / 定理 `lcm_empty`

English:
theorem lcm_empty
  statement: (∅ : Finset β).lcm f = 1
  proof: rfl

@[simp]

中文:
定理 lcm_empty
  结论: (∅ : Finset β).lcm f = 1
  证明: rfl

@[simp]
-/
theorem lcm_empty : (∅ : Finset β).lcm f = 1 :=
  rfl

@[simp]
/--
theorem `lcm_dvd_iff` / 定理 `lcm_dvd_iff`

English:
theorem lcm_dvd_iff
  given: {a : α}
  statement: s.lcm f ∣ a ↔ forall b in s, f b ∣ a
  proof: by
  apply Iff.trans Multiset.lcm_dvd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

中文:
定理 lcm_dvd_iff
  条件: {a : α}
  结论: s.lcm f ∣ a ↔ 对任意 b in s, f b ∣ a
  证明: by
  apply Iff.trans Multiset.lcm_dvd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

Depends on / 依赖: Iff.trans, Multiset, Multiset.lcm_dvd, Multiset.mem_map, and_imp, exists_imp, lcm_dvd, mem_map
-/
theorem lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ forall b in s, f b ∣ a := by
  apply Iff.trans Multiset.lcm_dvd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

/--
theorem `lcm_dvd` / 定理 `lcm_dvd`

English:
theorem lcm_dvd
  given: {a : α}
  statement: (forall b in s, f b ∣ a) -> s.lcm f ∣ a
  proof: lcm_dvd_iff.2

中文:
定理 lcm_dvd
  条件: {a : α}
  结论: (对任意 b in s, f b ∣ a) -> s.lcm f ∣ a
  证明: lcm_dvd_iff.2

Depends on / 依赖: lcm_dvd_iff
-/
theorem lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ a :=
  lcm_dvd_iff.2

/--
theorem `dvd_lcm` / 定理 `dvd_lcm`

English:
theorem dvd_lcm
  given: {b : β} (hb : b in s)
  statement: f b ∣ s.lcm f
  proof: lcm_dvd_iff.1 dvd_rfl _ hb

@[simp]

中文:
定理 dvd_lcm
  条件: {b : β} (hb : b in s)
  结论: f b ∣ s.lcm f
  证明: lcm_dvd_iff.1 dvd_rfl _ hb

@[simp]

Depends on / 依赖: dvd_rfl, lcm_dvd_iff
-/
theorem dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f :=
  lcm_dvd_iff.1 dvd_rfl _ hb

@[simp]
/--
theorem `lcm_insert` / 定理 `lcm_insert`

English:
theorem lcm_insert
  given: [DecidableEq β] {b : β}
  proof: by
  by_cases h : b in s
  · rw [insert_eq_of_mem h,
      (lcm_eq_right_iff (f b) (s.lcm f) (Multiset.normalize_lcm (s.1.map f))).2 (dvd_lcm h)]
  apply fold_insert h

@[simp]

中文:
定理 lcm_insert
  条件: [DecidableEq β] {b : β}
  证明: by
  by_cases h : b in s
  · rw [insert_eq_of_mem h,
      (lcm_eq_right_iff (f b) (s.lcm f) (Multiset.normalize_lcm (s.1.map f))).2 (dvd_lcm h)]
  apply fold_insert h

@[simp]

Depends on / 依赖: Multiset, Multiset.normalize_lcm, dvd_lcm, fold_insert, insert_eq_of_mem, lcm_eq_right_iff, normalize_lcm, s.lcm
-/
theorem lcm_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f) := by
  by_cases h : b in s
  · rw [insert_eq_of_mem h,
      (lcm_eq_right_iff (f b) (s.lcm f) (Multiset.normalize_lcm (s.1.map f))).2 (dvd_lcm h)]
  apply fold_insert h

@[simp]
/--
theorem `lcm_singleton` / 定理 `lcm_singleton`

English:
theorem lcm_singleton
  given: {b : β}
  statement: ({b} : Finset β).lcm f = normalize (f b)
  proof: Multiset.lcm_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.

中文:
定理 lcm_singleton
  条件: {b : β}
  结论: ({b} : Finset β).lcm f = normalize (f b)
  证明: Multiset.lcm_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.

Depends on / 依赖: Multiset, Multiset.lcm_singleton, lcm_singleton
-/
theorem lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b) :=
  Multiset.lcm_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.
/--
theorem `normalize_lcm` / 定理 `normalize_lcm`

English:
theorem normalize_lcm
  statement: normalize (s.lcm f) = s.lcm f
  proof: by simp [lcm_def]

中文:
定理 normalize_lcm
  结论: normalize (s.lcm f) = s.lcm f
  证明: by simp [lcm_def]

Depends on / 依赖: lcm_def
-/
theorem normalize_lcm : normalize (s.lcm f) = s.lcm f := by simp [lcm_def]

/--
theorem `lcm_union` / 定理 `lcm_union`

English:
theorem lcm_union
  given: [DecidableEq β]
  statement: (s₁ union s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f)
  proof: Finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm])
    fun a s _ ih => by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]

中文:
定理 lcm_union
  条件: [DecidableEq β]
  结论: (s₁ union s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f)
  证明: Finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm])
    fun a s _ ih => by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]

Depends on / 依赖: Finset, Finset.induction_on, empty_union, induction_on, insert_union, lcm_assoc, lcm_empty, lcm_insert, lcm_one_left, normalize_lcm
-/
theorem lcm_union [DecidableEq β] : (s₁ union s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f) :=
  Finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm])
    fun a s _ ih => by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]

/--
theorem `lcm_congr` / 定理 `lcm_congr`

English:
theorem lcm_congr
  given: {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a)
  proof: by
  subst hs
  exact Finset.fold_congr hfg

中文:
定理 lcm_congr
  条件: {f g : β -> α} (hs : s₁ = s₂) (hfg : 对任意 a in s₂, f a = g a)
  证明: by
  subst hs
  exact Finset.fold_congr hfg

Depends on / 依赖: Finset, Finset.fold_congr, fold_congr
-/
theorem lcm_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a) :
    s₁.lcm f = s₂.lcm g := by
  subst hs
  exact Finset.fold_congr hfg

/--
theorem `lcm_mono_fun` / 定理 `lcm_mono_fun`

English:
theorem lcm_mono_fun
  given: {g : β -> α} (h : forall b in s, f b ∣ g b)
  statement: s.lcm f ∣ s.lcm g
  proof: lcm_dvd fun b hb => (h b hb).trans (dvd_lcm hb)

中文:
定理 lcm_mono_fun
  条件: {g : β -> α} (h : 对任意 b in s, f b ∣ g b)
  结论: s.lcm f ∣ s.lcm g
  证明: lcm_dvd fun b hb => (h b hb).trans (dvd_lcm hb)

Depends on / 依赖: dvd_lcm, lcm_dvd
-/
theorem lcm_mono_fun {g : β -> α} (h : forall b in s, f b ∣ g b) : s.lcm f ∣ s.lcm g :=
  lcm_dvd fun b hb => (h b hb).trans (dvd_lcm hb)

/--
theorem `lcm_mono` / 定理 `lcm_mono`

English:
theorem lcm_mono
  given: (h : s₁ subseteq s₂)
  statement: s₁.lcm f ∣ s₂.lcm f
  proof: lcm_dvd fun _ hb => dvd_lcm (h hb)

中文:
定理 lcm_mono
  条件: (h : s₁ subseteq s₂)
  结论: s₁.lcm f ∣ s₂.lcm f
  证明: lcm_dvd fun _ hb => dvd_lcm (h hb)

Depends on / 依赖: dvd_lcm, lcm_dvd
-/
theorem lcm_mono (h : s₁ subseteq s₂) : s₁.lcm f ∣ s₂.lcm f :=
  lcm_dvd fun _ hb => dvd_lcm (h hb)

/--
theorem `lcm_image` / 定理 `lcm_image`

English:
theorem lcm_image
  given: [DecidableEq β] {g : γ -> β} (s : Finset γ)
  proof: by
  classical induction s using Finset.induction <;> simp [*]

中文:
定理 lcm_image
  条件: [DecidableEq β] {g : γ -> β} (s : Finset γ)
  证明: by
  classical induction s using Finset.induction <;> simp [*]

Depends on / 依赖: Finset, Finset.induction, classical
-/
theorem lcm_image [DecidableEq β] {g : γ -> β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]

/--
theorem `lcm_eq_lcm_image` / 定理 `lcm_eq_lcm_image`

English:
theorem lcm_eq_lcm_image
  given: [DecidableEq α]
  statement: s.lcm f = (s.image f).lcm id
  proof: Eq.symm lcm_image _

@[simp]

中文:
定理 lcm_eq_lcm_image
  条件: [DecidableEq α]
  结论: s.lcm f = (s.image f).lcm id
  证明: Eq.symm lcm_image _

@[simp]

Depends on / 依赖: Eq.symm, lcm_image
-/
theorem lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id :=
Eq.symm lcm_image _

@[simp]
/--
theorem `lcm_eq_zero_iff` / 定理 `lcm_eq_zero_iff`

English:
theorem lcm_eq_zero_iff
  given: [Nontrivial α]
  statement: s.lcm f = 0 ↔ exists x in s, f x = 0
  proof: by
  simp only [lcm_def, Multiset.lcm_eq_zero_iff, Multiset.mem_map, mem_val]

中文:
定理 lcm_eq_zero_iff
  条件: [Nontrivial α]
  结论: s.lcm f = 0 ↔ 存在 x in s, f x = 0
  证明: by
  simp only [lcm_def, Multiset.lcm_eq_zero_iff, Multiset.mem_map, mem_val]

Depends on / 依赖: Multiset, Multiset.lcm_eq_zero_iff, Multiset.mem_map, lcm_def, lcm_eq_zero_iff, mem_map, mem_val
-/
theorem lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ exists x in s, f x = 0 := by
  simp only [lcm_def, Multiset.lcm_eq_zero_iff, Multiset.mem_map, mem_val]

/--
theorem `lcm_ne_zero_iff` / 定理 `lcm_ne_zero_iff`

English:
theorem lcm_ne_zero_iff
  given: [Nontrivial α]
  statement: s.lcm f != 0 ↔ forall x in s, f x != 0
  proof: by
  simp [lcm_eq_zero_iff]

中文:
定理 lcm_ne_zero_iff
  条件: [Nontrivial α]
  结论: s.lcm f != 0 ↔ 对任意 x in s, f x != 0
  证明: by
  simp [lcm_eq_zero_iff]

Depends on / 依赖: lcm_eq_zero_iff
-/
theorem lcm_ne_zero_iff [Nontrivial α] : s.lcm f != 0 ↔ forall x in s, f x != 0 := by
  simp [lcm_eq_zero_iff]

end lcm

/-! ### gcd -/


section gcd

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (s : Finset β) (f : β -> α)
  body: s.fold GCDMonoid.gcd 0 f

中文:
定义 gcd
  签名: (s : Finset β) (f : β -> α)
  定义体: s.fold GCDMonoid.gcd 0 f

Depends on / 依赖: GCDMonoid, GCDMonoid.gcd, s.fold
-/
def gcd (s : Finset β) (f : β -> α) : α :=
  s.fold GCDMonoid.gcd 0 f

variable {s s₁ s₂ : Finset β} {f : β -> α}

/--
theorem `gcd_def` / 定理 `gcd_def`

English:
theorem gcd_def
  statement: s.gcd f = (s.1.map f).gcd
  proof: rfl

@[simp]

中文:
定理 gcd_def
  结论: s.gcd f = (s.1.map f).gcd
  证明: rfl

@[simp]
-/
theorem gcd_def : s.gcd f = (s.1.map f).gcd :=
  rfl

@[simp]
/--
theorem `gcd_empty` / 定理 `gcd_empty`

English:
theorem gcd_empty
  statement: (∅ : Finset β).gcd f = 0
  proof: rfl

中文:
定理 gcd_empty
  结论: (∅ : Finset β).gcd f = 0
  证明: rfl
-/
theorem gcd_empty : (∅ : Finset β).gcd f = 0 :=
  rfl

/--
theorem `dvd_gcd_iff` / 定理 `dvd_gcd_iff`

English:
theorem dvd_gcd_iff
  given: {a : α}
  statement: a ∣ s.gcd f ↔ forall b in s, a ∣ f b
  proof: by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

中文:
定理 dvd_gcd_iff
  条件: {a : α}
  结论: a ∣ s.gcd f ↔ 对任意 b in s, a ∣ f b
  证明: by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

Depends on / 依赖: Iff.trans, Multiset, Multiset.dvd_gcd, Multiset.mem_map, and_imp, dvd_gcd, exists_imp, mem_map
-/
theorem dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a ∣ f b := by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

/--
theorem `gcd_dvd` / 定理 `gcd_dvd`

English:
theorem gcd_dvd
  given: {b : β} (hb : b in s)
  statement: s.gcd f ∣ f b
  proof: dvd_gcd_iff.1 dvd_rfl _ hb

中文:
定理 gcd_dvd
  条件: {b : β} (hb : b in s)
  结论: s.gcd f ∣ f b
  证明: dvd_gcd_iff.1 dvd_rfl _ hb

Depends on / 依赖: dvd_gcd_iff, dvd_rfl
-/
theorem gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b :=
  dvd_gcd_iff.1 dvd_rfl _ hb

/--
theorem `dvd_gcd` / 定理 `dvd_gcd`

English:
theorem dvd_gcd
  given: {a : α}
  statement: (forall b in s, a ∣ f b) -> a ∣ s.gcd f
  proof: dvd_gcd_iff.2

中文:
定理 dvd_gcd
  条件: {a : α}
  结论: (对任意 b in s, a ∣ f b) -> a ∣ s.gcd f
  证明: dvd_gcd_iff.2

Depends on / 依赖: dvd_gcd_iff
-/
theorem dvd_gcd {a : α} : (forall b in s, a ∣ f b) -> a ∣ s.gcd f :=
  dvd_gcd_iff.2

/--
theorem `gcd_cons` / 定理 `gcd_cons`

English:
theorem gcd_cons
  given: {b : β} (h : b ∉ s)
  proof: fold_cons h

@[simp]

中文:
定理 gcd_cons
  条件: {b : β} (h : b ∉ s)
  证明: fold_cons h

@[simp]

Depends on / 依赖: fold_cons
-/
theorem gcd_cons {b : β} (h : b ∉ s) :
    (cons b s h : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) :=
  fold_cons h

@[simp]
/--
theorem `gcd_insert` / 定理 `gcd_insert`

English:
theorem gcd_insert
  given: [DecidableEq β] {b : β}
  proof: by
  by_cases h : b in s
  · rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)]
  apply fold_insert h

@[simp]

中文:
定理 gcd_insert
  条件: [DecidableEq β] {b : β}
  证明: by
  by_cases h : b in s
  · rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)]
  apply fold_insert h

@[simp]

Depends on / 依赖: Multiset, Multiset.normalize_gcd, fold_insert, gcd_dvd, gcd_eq_right_iff, insert_eq_of_mem, normalize_gcd, s.gcd
-/
theorem gcd_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) := by
  by_cases h : b in s
  · rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)]
  apply fold_insert h

@[simp]
/--
theorem `gcd_singleton` / 定理 `gcd_singleton`

English:
theorem gcd_singleton
  given: {b : β}
  statement: ({b} : Finset β).gcd f = normalize (f b)
  proof: Multiset.gcd_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.

中文:
定理 gcd_singleton
  条件: {b : β}
  结论: ({b} : Finset β).gcd f = normalize (f b)
  证明: Multiset.gcd_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.

Depends on / 依赖: Multiset, Multiset.gcd_singleton, gcd_singleton
-/
theorem gcd_singleton {b : β} : ({b} : Finset β).gcd f = normalize (f b) :=
  Multiset.gcd_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.
/--
theorem `normalize_gcd` / 定理 `normalize_gcd`

English:
theorem normalize_gcd
  statement: normalize (s.gcd f) = s.gcd f
  proof: by simp [gcd_def]

中文:
定理 normalize_gcd
  结论: normalize (s.gcd f) = s.gcd f
  证明: by simp [gcd_def]

Depends on / 依赖: gcd_def
-/
theorem normalize_gcd : normalize (s.gcd f) = s.gcd f := by simp [gcd_def]

/--
theorem `gcd_union` / 定理 `gcd_union`

English:
theorem gcd_union
  given: [DecidableEq β]
  statement: (s₁ union s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f)
  proof: Finset.induction_on s₁ (by rw [empty_union, gcd_empty, gcd_zero_left, normalize_gcd])
    fun a s _ ih => by rw [insert_union, gcd_insert, gcd_insert, ih, gcd_assoc]

中文:
定理 gcd_union
  条件: [DecidableEq β]
  结论: (s₁ union s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f)
  证明: Finset.induction_on s₁ (by rw [empty_union, gcd_empty, gcd_zero_left, normalize_gcd])
    fun a s _ ih => by rw [insert_union, gcd_insert, gcd_insert, ih, gcd_assoc]

Depends on / 依赖: Finset, Finset.induction_on, empty_union, gcd_assoc, gcd_empty, gcd_insert, gcd_zero_left, induction_on, insert_union, normalize_gcd
-/
theorem gcd_union [DecidableEq β] : (s₁ union s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f) :=
  Finset.induction_on s₁ (by rw [empty_union, gcd_empty, gcd_zero_left, normalize_gcd])
    fun a s _ ih => by rw [insert_union, gcd_insert, gcd_insert, ih, gcd_assoc]

/--
theorem `gcd_congr` / 定理 `gcd_congr`

English:
theorem gcd_congr
  given: {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a)
  proof: by
  subst hs
  exact Finset.fold_congr hfg

中文:
定理 gcd_congr
  条件: {f g : β -> α} (hs : s₁ = s₂) (hfg : 对任意 a in s₂, f a = g a)
  证明: by
  subst hs
  exact Finset.fold_congr hfg

Depends on / 依赖: Finset, Finset.fold_congr, fold_congr
-/
theorem gcd_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  subst hs
  exact Finset.fold_congr hfg

/--
theorem `gcd_mono_fun` / 定理 `gcd_mono_fun`

English:
theorem gcd_mono_fun
  given: {g : β -> α} (h : forall b in s, f b ∣ g b)
  statement: s.gcd f ∣ s.gcd g
  proof: dvd_gcd fun b hb => (gcd_dvd hb).trans (h b hb)

中文:
定理 gcd_mono_fun
  条件: {g : β -> α} (h : 对任意 b in s, f b ∣ g b)
  结论: s.gcd f ∣ s.gcd g
  证明: dvd_gcd fun b hb => (gcd_dvd hb).trans (h b hb)

Depends on / 依赖: dvd_gcd, gcd_dvd
-/
theorem gcd_mono_fun {g : β -> α} (h : forall b in s, f b ∣ g b) : s.gcd f ∣ s.gcd g :=
  dvd_gcd fun b hb => (gcd_dvd hb).trans (h b hb)

/--
theorem `gcd_mono` / 定理 `gcd_mono`

English:
theorem gcd_mono
  given: (h : s₁ subseteq s₂)
  statement: s₂.gcd f ∣ s₁.gcd f
  proof: dvd_gcd fun _ hb => gcd_dvd (h hb)

中文:
定理 gcd_mono
  条件: (h : s₁ subseteq s₂)
  结论: s₂.gcd f ∣ s₁.gcd f
  证明: dvd_gcd fun _ hb => gcd_dvd (h hb)

Depends on / 依赖: dvd_gcd, gcd_dvd
-/
theorem gcd_mono (h : s₁ subseteq s₂) : s₂.gcd f ∣ s₁.gcd f :=
  dvd_gcd fun _ hb => gcd_dvd (h hb)

/--
theorem `gcd_image` / 定理 `gcd_image`

English:
theorem gcd_image
  given: [DecidableEq β] {g : γ -> β} (s : Finset γ)
  proof: by
  classical induction s using Finset.induction <;> simp [*]

中文:
定理 gcd_image
  条件: [DecidableEq β] {g : γ -> β} (s : Finset γ)
  证明: by
  classical induction s using Finset.induction <;> simp [*]

Depends on / 依赖: Finset, Finset.induction, classical
-/
theorem gcd_image [DecidableEq β] {g : γ -> β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]

/--
theorem `gcd_eq_gcd_image` / 定理 `gcd_eq_gcd_image`

English:
theorem gcd_eq_gcd_image
  given: [DecidableEq α]
  statement: s.gcd f = (s.image f).gcd id
  proof: Eq.symm gcd_image _

中文:
定理 gcd_eq_gcd_image
  条件: [DecidableEq α]
  结论: s.gcd f = (s.image f).gcd id
  证明: Eq.symm gcd_image _

Depends on / 依赖: Eq.symm, gcd_image
-/
theorem gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id :=
Eq.symm gcd_image _

/--
theorem `gcd_eq_zero_iff` / 定理 `gcd_eq_zero_iff`

English:
theorem gcd_eq_zero_iff
  statement: s.gcd f = 0 ↔ forall x in s, f x = 0
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s h ih => grind [gcd_cons, _root_.gcd_eq_zero_iff]

中文:
定理 gcd_eq_zero_iff
  结论: s.gcd f = 0 ↔ 对任意 x in s, f x = 0
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s h ih => grind [gcd_cons, _root_.gcd_eq_zero_iff]

Depends on / 依赖: Finset, Finset.cons_induction_on, _root_, _root_.gcd_eq_zero_iff, cons_induction_on, gcd_cons, gcd_eq_zero_iff
-/
theorem gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f x = 0 := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s h ih => grind [gcd_cons, _root_.gcd_eq_zero_iff]

/--
theorem `gcd_ne_zero_iff` / 定理 `gcd_ne_zero_iff`

English:
theorem gcd_ne_zero_iff
  statement: s.gcd f != 0 ↔ exists x in s, f x != 0
  proof: by
  simp [gcd_eq_zero_iff]

中文:
定理 gcd_ne_zero_iff
  结论: s.gcd f != 0 ↔ 存在 x in s, f x != 0
  证明: by
  simp [gcd_eq_zero_iff]

Depends on / 依赖: gcd_eq_zero_iff
-/
theorem gcd_ne_zero_iff : s.gcd f != 0 ↔ exists x in s, f x != 0 := by
  simp [gcd_eq_zero_iff]

/--
theorem `gcd_eq_gcd_filter_ne_zero` / 定理 `gcd_eq_gcd_filter_ne_zero`

English:
theorem gcd_eq_gcd_filter_ne_zero
  given: [DecidablePred fun x : β => f x = 0]
  proof: by
  classical
    trans ({x in s | f x = 0} union {x in s | f x != 0}).gcd f
    · rw [filter_union_filter_not_eq]
    rw [gcd_union]
    refine Eq.trans (?_ : _ = GCDMonoid.gcd (0 : α) ?_) (?_ : GCDMonoid.gcd (0 : α) _ = _)
    · exact gcd {x in s | f x != 0} f
    · refine congr (congr rfl <| s.i

中文:
定理 gcd_eq_gcd_filter_ne_zero
  条件: [DecidablePred fun x : β => f x = 0]
  证明: by
  classical
    trans ({x in s | f x = 0} union {x in s | f x != 0}).gcd f
    · rw [filter_union_filter_not_eq]
    rw [gcd_union]
    refine Eq.trans (?_ : _ = GCDMonoid.gcd (0 : α) ?_) (?_ : GCDMonoid.gcd (0 : α) _ = _)
    · exact gcd {x in s | f x != 0} f
    · refine congr (congr rfl <| s.i

Depends on / 依赖: Eq.trans, GCDMonoid, GCDMonoid.gcd, classical, filter_insert, filter_union_filter_not_eq, gcd_union, gcd_zero_left, induction_on, normalize_gcd, s.induction_on, split_ifs
-/
theorem gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β => f x = 0] :
    s.gcd f = {x in s | f x != 0}.gcd f := by
  classical
    trans ({x in s | f x = 0} union {x in s | f x != 0}).gcd f
    · rw [filter_union_filter_not_eq]
    rw [gcd_union]
    refine Eq.trans (?_ : _ = GCDMonoid.gcd (0 : α) ?_) (?_ : GCDMonoid.gcd (0 : α) _ = _)
    · exact gcd {x in s | f x != 0} f
    · refine congr (congr rfl <| s.induction_on ?_ ?_) (by simp)
      · simp
      · intro a s _ h
        rw [filter_insert]
        split_ifs with h1 <;> simp [h, h1]
    simp only [gcd_zero_left, normalize_gcd]

nonrec theorem gcd_mul_left {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
    {s : Finset β} {f : β -> α} {a : α} :
    (s.gcd fun x => a * f x) = normalize a * s.gcd f := by
  classical
    refine s.induction_on ?_ ?_
    · simp
    · intro b t _ h
      rw [gcd_insert]; rw [gcd_insert]; rw [h]; rw [← gcd_mul_left]
      apply ((normalize_associated a).mul_right _).gcd_eq_right

nonrec theorem gcd_mul_right {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
    {s : Finset β} {f : β -> α} {a : α} :
    (s.gcd fun x => f x * a) = s.gcd f * normalize a := by
  simp_rw [mul_comm]; exact gcd_mul_left

variable (s f) in
nonrec theorem gcd_mul_left' (a : α) : Associated (s.gcd fun x => a * f x) (a * s.gcd f) := by
  classical exact s.induction_on (by simp) fun b s hbs h => by
             simpa using .trans (.gcd .rfl h) (gcd_mul_left' ..)

variable (s f) in
nonrec theorem gcd_mul_right' (a : α) : Associated (s.gcd fun x => f x * a) (s.gcd f * a) := by
  simp_rw [mul_comm]; apply gcd_mul_left'

/--
theorem `extract_gcd'` / 定理 `extract_gcd'`

English:
theorem extract_gcd'
  statement: (f g : β -> α) (hs : exists x, x in s ∧ f x != 0)
  proof: by
  rw [← normalize_gcd]; rw [normalize_eq_one]; rw [← associated_one_iff_isUnit]
  refine .of_mul_left (.symm <| .trans ?_ (gcd_mul_left' ..)) .rfl (a := s.gcd f) ?_
  · simp [← gcd_congr rfl hg]
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs

中文:
定理 extract_gcd'
  结论: (f g : β -> α) (hs : 存在 x, x in s ∧ f x != 0)
  证明: by
  rw [← normalize_gcd]; rw [normalize_eq_one]; rw [← associated_one_iff_isUnit]
  refine .of_mul_left (.symm <| .trans ?_ (gcd_mul_left' ..)) .rfl (a := s.gcd f) ?_
  · simp [← gcd_congr rfl hg]
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs

Depends on / 依赖: associated_one_iff_isUnit, contrapose, gcd_congr, gcd_eq_zero_iff, gcd_mul_left, normalize_eq_one, normalize_gcd, of_mul_left, s.gcd, s.gcd_eq_zero_iff
-/
theorem extract_gcd' (f g : β -> α) (hs : exists x, x in s ∧ f x != 0)
    (hg : forall b in s, f b = s.gcd f * g b) : s.gcd g = 1 := by
  rw [← normalize_gcd]; rw [normalize_eq_one]; rw [← associated_one_iff_isUnit]
  refine .of_mul_left (.symm <| .trans ?_ (gcd_mul_left' ..)) .rfl (a := s.gcd f) ?_
  · simp [← gcd_congr rfl hg]
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs

/--
theorem `extract_gcd` / 定理 `extract_gcd`

English:
theorem extract_gcd
  given: (f : β -> α) (hs : s.Nonempty)
  proof: by
  classical
    by_cases! h : forall x in s, f x = (0 : α)
    · refine ⟨fun _ => 1, fun b hb => by rw [h b hb, gcd_eq_zero_iff.2 h, mul_one], ?_⟩
      rw [gcd_eq_gcd_image]; rw [image_const hs]; rw [gcd_singleton]; rw [id]; rw [normalize_one]
    · choose g' hg using @gcd_dvd _ _ _ _ s f
      

中文:
定理 extract_gcd
  条件: (f : β -> α) (hs : s.Nonempty)
  证明: by
  classical
    by_cases! h : forall x in s, f x = (0 : α)
    · refine ⟨fun _ => 1, fun b hb => by rw [h b hb, gcd_eq_zero_iff.2 h, mul_one], ?_⟩
      rw [gcd_eq_gcd_image]; rw [image_const hs]; rw [gcd_singleton]; rw [id]; rw [normalize_one]
    · choose g' hg using @gcd_dvd _ _ _ _ s f
      

Depends on / 依赖: classical, dif_pos, dite_true, extract_gcd, gcd_dvd, gcd_eq_gcd_image, gcd_eq_zero_iff, gcd_singleton, image_const, mul_one, normalize_one
-/
theorem extract_gcd (f : β -> α) (hs : s.Nonempty) :
    exists g : β -> α, (forall b in s, f b = s.gcd f * g b) ∧ s.gcd g = 1 := by
  classical
    by_cases! h : forall x in s, f x = (0 : α)
    · refine ⟨fun _ => 1, fun b hb => by rw [h b hb, gcd_eq_zero_iff.2 h, mul_one], ?_⟩
      rw [gcd_eq_gcd_image]; rw [image_const hs]; rw [gcd_singleton]; rw [id]; rw [normalize_one]
    · choose g' hg using @gcd_dvd _ _ _ _ s f
      refine ⟨fun b => if hb : b in s then g' hb else 0, fun b hb => ?_,
          extract_gcd' f _ h fun b hb => ?_⟩
      · simp only [hb, hg, dite_true]
      rw [dif_pos hb]; rw [hg hb]

variable [Div α] [MulDivCancelClass α] {f : ι -> α} {s : Finset ι} {i : ι}

/--
lemma `gcd_div_eq_one` / 引理 `gcd_div_eq_one`

English:
lemma gcd_div_eq_one
  given: (his : i in s) (hfi : f i != 0)
  statement: s.gcd (fun j => f j / s.gcd f) = 1
  proof: by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha => ?_).trans hg
  rw [he a ha]; rw [mul_div_cancel_left₀]
exact mt Finset.gcd_eq_zero_iff.1 fun h => hfi h i his

中文:
引理 gcd_div_eq_one
  条件: (his : i in s) (hfi : f i != 0)
  结论: s.gcd (fun j => f j / s.gcd f) = 1
  证明: by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha => ?_).trans hg
  rw [he a ha]; rw [mul_div_cancel_left₀]
exact mt Finset.gcd_eq_zero_iff.1 fun h => hfi h i his

Depends on / 依赖: Finset, Finset.extract_gcd, Finset.gcd_congr, Finset.gcd_eq_zero_iff, extract_gcd, gcd_congr, gcd_eq_zero_iff
-/
lemma gcd_div_eq_one (his : i in s) (hfi : f i != 0) : s.gcd (fun j => f j / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha => ?_).trans hg
  rw [he a ha]; rw [mul_div_cancel_left₀]
exact mt Finset.gcd_eq_zero_iff.1 fun h => hfi h i his

/--
lemma `gcd_div_id_eq_one` / 引理 `gcd_div_id_eq_one`

English:
lemma gcd_div_id_eq_one
  given: {s : Finset α} {a : α} (has : a in s) (ha : a != 0)
  proof: gcd_div_eq_one has ha

中文:
引理 gcd_div_id_eq_one
  条件: {s : Finset α} {a : α} (has : a in s) (ha : a != 0)
  证明: gcd_div_eq_one has ha

Depends on / 依赖: gcd_div_eq_one
-/
lemma gcd_div_id_eq_one {s : Finset α} {a : α} (has : a in s) (ha : a != 0) :
    s.gcd (fun b => b / s.gcd id) = 1 := gcd_div_eq_one has ha

end gcd

end Finset

namespace Finset

section IsDomain

variable [CommRing α] [NormalizedGCDMonoid α]

/--
theorem `gcd_eq_of_dvd_sub` / 定理 `gcd_eq_of_dvd_sub`

English:
theorem gcd_eq_of_dvd_sub
  statement: {s : Finset β} {f g : β -> α} {a : α}
  proof: by
  classical
    revert h
    refine s.induction_on ?_ ?_
    · simp
    intro b s _ hi h
    rw [gcd_insert]; rw [gcd_insert]; rw [gcd_comm (f b)]; rw [← gcd_assoc]; rw [hi fun x hx => h _ (mem_insert_of_mem hx)]; rw [gcd_comm a]; rw [gcd_assoc]; rw [gcd_comm a (GCDMonoid.gcd _ _)]; rw [gcd_comm 

中文:
定理 gcd_eq_of_dvd_sub
  结论: {s : Finset β} {f g : β -> α} {a : α}
  证明: by
  classical
    revert h
    refine s.induction_on ?_ ?_
    · simp
    intro b s _ hi h
    rw [gcd_insert]; rw [gcd_insert]; rw [gcd_comm (f b)]; rw [← gcd_assoc]; rw [hi fun x hx => h _ (mem_insert_of_mem hx)]; rw [gcd_comm a]; rw [gcd_assoc]; rw [gcd_comm a (GCDMonoid.gcd _ _)]; rw [gcd_comm 

Depends on / 依赖: GCDMonoid, GCDMonoid.gcd, classical, congr_arg, gcd_assoc, gcd_comm, gcd_eq_of_dvd_sub_right, gcd_insert, induction_on, mem_insert_of_mem, mem_insert_self, revert, s.induction_on
-/
theorem gcd_eq_of_dvd_sub {s : Finset β} {f g : β -> α} {a : α}
    (h : forall x : β, x in s -> a ∣ f x - g x) :
    GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g) := by
  classical
    revert h
    refine s.induction_on ?_ ?_
    · simp
    intro b s _ hi h
    rw [gcd_insert]; rw [gcd_insert]; rw [gcd_comm (f b)]; rw [← gcd_assoc]; rw [hi fun x hx => h _ (mem_insert_of_mem hx)]; rw [gcd_comm a]; rw [gcd_assoc]; rw [gcd_comm a (GCDMonoid.gcd _ _)]; rw [gcd_comm (g b)]; rw [gcd_assoc _ _ a]; rw [gcd_comm _ a]
    exact congr_arg _ (gcd_eq_of_dvd_sub_right (h _ (mem_insert_self _ _)))

end IsDomain

variable {s : Finset ι}

/-- The gcd of a finset of integers is nonnegative. -/
@[grind .]
/--
theorem `Int.finsetGcd_nonneg` / 定理 `Int.finsetGcd_nonneg`

English:
theorem Int.finsetGcd_nonneg
  given: {f : ι -> Int}
  statement: 0 <= s.gcd f
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [gcd_cons]; rw [← Int.coe_gcd]
    grind

中文:
定理 Int.finsetGcd_nonneg
  条件: {f : ι -> 整数}
  结论: 0 <= s.gcd f
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [gcd_cons]; rw [← Int.coe_gcd]
    grind

Depends on / 依赖: Finset, Finset.cons_induction_on, Int.coe_gcd, coe_gcd, cons_induction_on, gcd_cons
-/
theorem Int.finsetGcd_nonneg {f : ι -> Int} : 0 <= s.gcd f := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [gcd_cons]; rw [← Int.coe_gcd]
    grind

end Finset
