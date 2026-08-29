/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Set.Image

/-!
# Support of a function

In this file we define `Function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `Function.mulSupport f = {x | f x ≠ 1}`.
-/

@[expose] public section

assert_not_exists Monoid CompleteLattice

open Function Set

variable {ι κ M N P : Type*}

namespace Function
variable [One M] [One N] [One P] {f g : ι -> M} {s : Set ι} {x : ι}

/-- `mulSupport` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive /-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/]
/--
Definition of `mulSupport` / `mulSupport` 的定义

English:
definition mulSupport
  signature: (f : ι -> M)
  body: {x | f x != 1}

@[to_additive]

中文:
定义 mulSupport
  签名: (f : ι -> M)
  定义体: {x | f x != 1}

@[to_additive]
-/
def mulSupport (f : ι -> M) : Set ι := {x | f x != 1}

@[to_additive]
/--
lemma `mulSupport_eq_preimage` / 引理 `mulSupport_eq_preimage`

English:
lemma mulSupport_eq_preimage
  given: (f : ι -> M)
  statement: mulSupport f = f ⁻¹' {1}ᶜ
  proof: rfl

@[to_additive]

中文:
引理 mulSupport_eq_preimage
  条件: (f : ι -> M)
  结论: mulSupport f = f ⁻¹' {1}ᶜ
  证明: rfl

@[to_additive]
-/
lemma mulSupport_eq_preimage (f : ι -> M) : mulSupport f = f ⁻¹' {1}ᶜ := rfl

@[to_additive]
/--
lemma `notMem_mulSupport` / 引理 `notMem_mulSupport`

English:
lemma notMem_mulSupport
  statement: x ∉ mulSupport f ↔ f x = 1
  proof: not_not

@[to_additive]

中文:
引理 notMem_mulSupport
  结论: x ∉ mulSupport f ↔ f x = 1
  证明: not_not

@[to_additive]

Depends on / 依赖: not_not
-/
lemma notMem_mulSupport : x ∉ mulSupport f ↔ f x = 1 := not_not

@[to_additive]
/--
lemma `compl_mulSupport` / 引理 `compl_mulSupport`

English:
lemma compl_mulSupport
  statement: (mulSupport f)ᶜ = {x | f x = 1}
  proof: ext fun _ => notMem_mulSupport

@[to_additive (attr := simp)]

中文:
引理 compl_mulSupport
  结论: (mulSupport f)ᶜ = {x | f x = 1}
  证明: ext fun _ => notMem_mulSupport

@[to_additive (attr := simp)]

Depends on / 依赖: notMem_mulSupport
-/
lemma compl_mulSupport : (mulSupport f)ᶜ = {x | f x = 1} := ext fun _ => notMem_mulSupport

@[to_additive (attr := simp)]
/--
lemma `mem_mulSupport` / 引理 `mem_mulSupport`

English:
lemma mem_mulSupport
  statement: x in mulSupport f ↔ f x != 1
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 mem_mulSupport
  结论: x in mulSupport f ↔ f x != 1
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma mem_mulSupport : x in mulSupport f ↔ f x != 1 := .rfl

@[to_additive (attr := simp)]
/--
lemma `mulSupport_subset_iff` / 引理 `mulSupport_subset_iff`

English:
lemma mulSupport_subset_iff
  statement: mulSupport f subseteq s ↔ forall x, f x != 1 -> x in s
  proof: .rfl

@[to_additive]

中文:
引理 mulSupport_subset_iff
  结论: mulSupport f subseteq s ↔ 对任意 x, f x != 1 -> x in s
  证明: .rfl

@[to_additive]
-/
lemma mulSupport_subset_iff : mulSupport f subseteq s ↔ forall x, f x != 1 -> x in s := .rfl

@[to_additive]
/--
lemma `mulSupport_subset_iff'` / 引理 `mulSupport_subset_iff'`

English:
lemma mulSupport_subset_iff'
  statement: mulSupport f subseteq s ↔ forall x ∉ s, f x = 1
  proof: forall_congr' fun _ => not_imp_comm

@[to_additive]

中文:
引理 mulSupport_subset_iff'
  结论: mulSupport f subseteq s ↔ 对任意 x ∉ s, f x = 1
  证明: forall_congr' fun _ => not_imp_comm

@[to_additive]

Depends on / 依赖: forall_congr, not_imp_comm
-/
lemma mulSupport_subset_iff' : mulSupport f subseteq s ↔ forall x ∉ s, f x = 1 :=
  forall_congr' fun _ => not_imp_comm

@[to_additive]
/--
lemma `mulSupport_eq_iff` / 引理 `mulSupport_eq_iff`

English:
lemma mulSupport_eq_iff
  statement: mulSupport f = s ↔ (forall x, x in s -> f x != 1) ∧ forall x, x ∉ s -> f x = 1
  proof: by
  simp +contextual only [Set.ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

@[to_additive]

中文:
引理 mulSupport_eq_iff
  结论: mulSupport f = s ↔ (对任意 x, x in s -> f x != 1) ∧ 对任意 x, x ∉ s -> f x = 1
  证明: by
  simp +contextual only [Set.ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

@[to_additive]

Depends on / 依赖: Set.ext_iff, and_comm, contextual, ext_iff, forall_and, iff_def, mem_mulSupport, ne_eq, not_imp_comm
-/
lemma mulSupport_eq_iff : mulSupport f = s ↔ (forall x, x in s -> f x != 1) ∧ forall x, x ∉ s -> f x = 1 := by
  simp +contextual only [Set.ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

@[to_additive]
/--
lemma `ext_iff_mulSupport` / 引理 `ext_iff_mulSupport`

English:
lemma ext_iff_mulSupport
  statement: f = g ↔ f.mulSupport = g.mulSupport ∧ forall x in f.mulSupport, f x = g x where
  proof: h ▸ ⟨rfl, fun _ _ => rfl⟩
  mpr := fun ⟨h₁, h₂⟩ => funext fun x => by
    if hx : x in f.mulSupport then exact h₂ x hx
    else rw [notMem_mulSupport.1 hx, notMem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]

@[to_additive]

中文:
引理 ext_iff_mulSupport
  结论: f = g ↔ f.mulSupport = g.mulSupport ∧ 对任意 x in f.mulSupport, f x = g x where
  证明: h ▸ ⟨rfl, fun _ _ => rfl⟩
  mpr := fun ⟨h₁, h₂⟩ => funext fun x => by
    if hx : x in f.mulSupport then exact h₂ x hx
    else rw [notMem_mulSupport.1 hx, notMem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]

@[to_additive]
-/
lemma ext_iff_mulSupport : f = g ↔ f.mulSupport = g.mulSupport ∧ forall x in f.mulSupport, f x = g x where
  mp h := h ▸ ⟨rfl, fun _ _ => rfl⟩
  mpr := fun ⟨h₁, h₂⟩ => funext fun x => by
    if hx : x in f.mulSupport then exact h₂ x hx
    else rw [notMem_mulSupport.1 hx, notMem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]

@[to_additive]
/--
lemma `mulSupport_update_of_ne_one` / 引理 `mulSupport_update_of_ne_one`

English:
lemma mulSupport_update_of_ne_one
  given: [DecidableEq ι] (f : ι -> M) (x : ι) {y : M} (hy : y != 1)
  proof: by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]

中文:
引理 mulSupport_update_of_ne_one
  条件: [DecidableEq ι] (f : ι -> M) (x : ι) {y : M} (hy : y != 1)
  证明: by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]

Depends on / 依赖: eq_or_ne
-/
lemma mulSupport_update_of_ne_one [DecidableEq ι] (f : ι -> M) (x : ι) {y : M} (hy : y != 1) :
    mulSupport (update f x y) = insert x (mulSupport f) := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]
/--
lemma `mulSupport_update_one` / 引理 `mulSupport_update_one`

English:
lemma mulSupport_update_one
  given: [DecidableEq ι] (f : ι -> M) (x : ι)
  proof: by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]

中文:
引理 mulSupport_update_one
  条件: [DecidableEq ι] (f : ι -> M) (x : ι)
  证明: by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]

Depends on / 依赖: eq_or_ne
-/
lemma mulSupport_update_one [DecidableEq ι] (f : ι -> M) (x : ι) :
    mulSupport (update f x 1) = mulSupport f \ {x} := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]
/--
lemma `mulSupport_update_eq_ite` / 引理 `mulSupport_update_eq_ite`

English:
lemma mulSupport_update_eq_ite
  given: [DecidableEq ι] [DecidableEq M] (f : ι -> M) (x : ι) (y : M)
  proof: by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [mulSupport_update_one, mulSupport_update_of_ne_one, *]

@[to_additive]

中文:
引理 mulSupport_update_eq_ite
  条件: [DecidableEq ι] [DecidableEq M] (f : ι -> M) (x : ι) (y : M)
  证明: by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [mulSupport_update_one, mulSupport_update_of_ne_one, *]

@[to_additive]

Depends on / 依赖: eq_or_ne, mulSupport_update_of_ne_one, mulSupport_update_one
-/
lemma mulSupport_update_eq_ite [DecidableEq ι] [DecidableEq M] (f : ι -> M) (x : ι) (y : M) :
    mulSupport (update f x y) = if y = 1 then mulSupport f \ {x} else insert x (mulSupport f) := by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [mulSupport_update_one, mulSupport_update_of_ne_one, *]

@[to_additive]
/--
lemma `mulSupport_extend_one_subset` / 引理 `mulSupport_extend_one_subset`

English:
lemma mulSupport_extend_one_subset
  given: {f : ι -> κ} {g : ι -> N}
  proof: mulSupport_subset_iff'.mpr fun x hfg => by
    by_cases hf : exists a, f a = x
    · rw [extend, dif_pos hf, ← notMem_mulSupport]
      rw [← Classical.choose_spec hf] at hfg
      exact fun hg => hfg ⟨_, hg, rfl⟩
    · rw [extend_apply' _ _ _ hf]; rfl

@[to_additive]

中文:
引理 mulSupport_extend_one_subset
  条件: {f : ι -> κ} {g : ι -> N}
  证明: mulSupport_subset_iff'.mpr fun x hfg => by
    by_cases hf : exists a, f a = x
    · rw [extend, dif_pos hf, ← notMem_mulSupport]
      rw [← Classical.choose_spec hf] at hfg
      exact fun hg => hfg ⟨_, hg, rfl⟩
    · rw [extend_apply' _ _ _ hf]; rfl

@[to_additive]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_pos, extend, extend_apply, mulSupport_subset_iff, notMem_mulSupport
-/
lemma mulSupport_extend_one_subset {f : ι -> κ} {g : ι -> N} :
    mulSupport (f.extend g 1) subseteq f '' mulSupport g :=
  mulSupport_subset_iff'.mpr fun x hfg => by
    by_cases hf : exists a, f a = x
    · rw [extend, dif_pos hf, ← notMem_mulSupport]
      rw [← Classical.choose_spec hf] at hfg
      exact fun hg => hfg ⟨_, hg, rfl⟩
    · rw [extend_apply' _ _ _ hf]; rfl

@[to_additive]
/--
lemma `mulSupport_extend_one` / 引理 `mulSupport_extend_one`

English:
lemma mulSupport_extend_one
  given: {f : ι -> κ} {g : ι -> N} (hf : f.Injective)
  proof: mulSupport_extend_one_subset.antisymm by
    rintro _ ⟨x, hx, rfl⟩; rwa [mem_mulSupport, hf.extend_apply]

@[to_additive]

中文:
引理 mulSupport_extend_one
  条件: {f : ι -> κ} {g : ι -> N} (hf : f.单射)
  证明: mulSupport_extend_one_subset.antisymm by
    rintro _ ⟨x, hx, rfl⟩; rwa [mem_mulSupport, hf.extend_apply]

@[to_additive]

Depends on / 依赖: antisymm, extend_apply, hf.extend_apply, mem_mulSupport, mulSupport_extend_one_subset, mulSupport_extend_one_subset.antisymm
-/
lemma mulSupport_extend_one {f : ι -> κ} {g : ι -> N} (hf : f.Injective) :
    mulSupport (f.extend g 1) = f '' mulSupport g :=
mulSupport_extend_one_subset.antisymm by
    rintro _ ⟨x, hx, rfl⟩; rwa [mem_mulSupport, hf.extend_apply]

@[to_additive]
/--
lemma `mulSupport_disjoint_iff` / 引理 `mulSupport_disjoint_iff`

English:
lemma mulSupport_disjoint_iff
  statement: Disjoint (mulSupport f) s ↔ EqOn f 1 s
  proof: by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', notMem_compl_iff, EqOn,
    Pi.one_apply]

@[to_additive]

中文:
引理 mulSupport_disjoint_iff
  结论: Disjoint (mulSupport f) s ↔ EqOn f 1 s
  证明: by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', notMem_compl_iff, EqOn,
    Pi.one_apply]

@[to_additive]

Depends on / 依赖: Pi.one_apply, mulSupport_subset_iff, notMem_compl_iff, one_apply, simp_rw, subset_compl_iff_disjoint_right
-/
lemma mulSupport_disjoint_iff : Disjoint (mulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', notMem_compl_iff, EqOn,
    Pi.one_apply]

@[to_additive]
/--
lemma `disjoint_mulSupport_iff` / 引理 `disjoint_mulSupport_iff`

English:
lemma disjoint_mulSupport_iff
  statement: Disjoint s (mulSupport f) ↔ EqOn f 1 s
  proof: by
  rw [disjoint_comm]; rw [mulSupport_disjoint_iff]

@[to_additive (attr := simp)]

中文:
引理 disjoint_mulSupport_iff
  结论: Disjoint s (mulSupport f) ↔ EqOn f 1 s
  证明: by
  rw [disjoint_comm]; rw [mulSupport_disjoint_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: disjoint_comm, mulSupport_disjoint_iff
-/
lemma disjoint_mulSupport_iff : Disjoint s (mulSupport f) ↔ EqOn f 1 s := by
  rw [disjoint_comm]; rw [mulSupport_disjoint_iff]

@[to_additive (attr := simp)]
/--
lemma `mulSupport_eq_empty_iff` / 引理 `mulSupport_eq_empty_iff`

English:
lemma mulSupport_eq_empty_iff
  statement: mulSupport f = ∅ ↔ f = 1
  proof: by
  rw [← subset_empty_iff]; rw [mulSupport_subset_iff']; rw [funext_iff]
  simp

@[to_additive (attr := simp)]

中文:
引理 mulSupport_eq_empty_iff
  结论: mulSupport f = ∅ ↔ f = 1
  证明: by
  rw [← subset_empty_iff]; rw [mulSupport_subset_iff']; rw [funext_iff]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: funext_iff, mulSupport_subset_iff, subset_empty_iff
-/
lemma mulSupport_eq_empty_iff : mulSupport f = ∅ ↔ f = 1 := by
  rw [← subset_empty_iff]; rw [mulSupport_subset_iff']; rw [funext_iff]
  simp

@[to_additive (attr := simp)]
/--
lemma `mulSupport_nonempty_iff` / 引理 `mulSupport_nonempty_iff`

English:
lemma mulSupport_nonempty_iff
  statement: (mulSupport f).Nonempty ↔ f != 1
  proof: by
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [mulSupport_eq_empty_iff]

@[to_additive]

中文:
引理 mulSupport_nonempty_iff
  结论: (mulSupport f).非空 ↔ f != 1
  证明: by
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [mulSupport_eq_empty_iff]

@[to_additive]

Depends on / 依赖: mulSupport_eq_empty_iff, nonempty_iff_ne_empty
-/
lemma mulSupport_nonempty_iff : (mulSupport f).Nonempty ↔ f != 1 := by
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [mulSupport_eq_empty_iff]

@[to_additive]
/--
theorem `_root_.Subsingleton.mulSupport_eq` / 定理 `_root_.Subsingleton.mulSupport_eq`

English:
theorem _root_.Subsingleton.mulSupport_eq
  given: [Subsingleton M] (f : ι -> M)
  statement: mulSupport f = ∅
  proof: mulSupport_eq_empty_iff.mpr Subsingleton.elim f 1

@[to_additive]

中文:
定理 _root_.子单例.mulSupport_eq
  条件: [子单例 M] (f : ι -> M)
  结论: mulSupport f = ∅
  证明: mulSupport_eq_empty_iff.mpr Subsingleton.elim f 1

@[to_additive]

Depends on / 依赖: Subsingleton, Subsingleton.elim, mulSupport_eq_empty_iff, mulSupport_eq_empty_iff.mpr
-/
theorem _root_.Subsingleton.mulSupport_eq [Subsingleton M] (f : ι -> M) : mulSupport f = ∅ :=
mulSupport_eq_empty_iff.mpr Subsingleton.elim f 1

@[to_additive]
/--
lemma `range_subset_insert_image_mulSupport` / 引理 `range_subset_insert_image_mulSupport`

English:
lemma range_subset_insert_image_mulSupport
  given: (f : ι -> M)
  proof: by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using!
    fun x (hx : x in mulSupport f) => mem_image_of_mem f hx

@[to_additive]

中文:
引理 range_subset_insert_image_mulSupport
  条件: (f : ι -> M)
  证明: by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using!
    fun x (hx : x in mulSupport f) => mem_image_of_mem f hx

@[to_additive]

Depends on / 依赖: mem_image_of_mem, mem_insert_iff, mulSupport, or_iff_not_imp_left, range_subset_iff
-/
lemma range_subset_insert_image_mulSupport (f : ι -> M) :
    range f subseteq insert 1 (f '' mulSupport f) := by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using!
    fun x (hx : x in mulSupport f) => mem_image_of_mem f hx

@[to_additive]
/--
lemma `range_eq_image_or_of_mulSupport_subset` / 引理 `range_eq_image_or_of_mulSupport_subset`

English:
lemma range_eq_image_or_of_mulSupport_subset
  given: {k : Set ι} (h : mulSupport f subseteq k)
  proof: by
  have : range f subseteq insert 1 (f '' k) :=
    (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_mono h))
  grind

@[to_additive (attr := simp)]

中文:
引理 range_eq_image_or_of_mulSupport_subset
  条件: {k : 集合 ι} (h : mulSupport f subseteq k)
  证明: by
  have : range f subseteq insert 1 (f '' k) :=
    (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_mono h))
  grind

@[to_additive (attr := simp)]

Depends on / 依赖: image_mono, insert, insert_subset_insert, range_subset_insert_image_mulSupport, subseteq
-/
lemma range_eq_image_or_of_mulSupport_subset {k : Set ι} (h : mulSupport f subseteq k) :
    range f = f '' k ∨ range f = insert 1 (f '' k) := by
  have : range f subseteq insert 1 (f '' k) :=
    (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_mono h))
  grind

@[to_additive (attr := simp)]
/--
lemma `mulSupport_one` / 引理 `mulSupport_one`

English:
lemma mulSupport_one
  statement: mulSupport (1 : ι -> M) = ∅
  proof: mulSupport_eq_empty_iff.2 rfl

@[to_additive (attr := simp)]

中文:
引理 mulSupport_one
  结论: mulSupport (1 : ι -> M) = ∅
  证明: mulSupport_eq_empty_iff.2 rfl

@[to_additive (attr := simp)]

Depends on / 依赖: mulSupport_eq_empty_iff
-/
lemma mulSupport_one : mulSupport (1 : ι -> M) = ∅ := mulSupport_eq_empty_iff.2 rfl

@[to_additive (attr := simp)]
/--
lemma `mulSupport_fun_one` / 引理 `mulSupport_fun_one`

English:
lemma mulSupport_fun_one
  statement: mulSupport (fun _ => 1 : ι -> M) = ∅
  proof: mulSupport_one

@[to_additive]

中文:
引理 mulSupport_fun_one
  结论: mulSupport (fun _ => 1 : ι -> M) = ∅
  证明: mulSupport_one

@[to_additive]

Depends on / 依赖: mulSupport_one
-/
lemma mulSupport_fun_one : mulSupport (fun _ => 1 : ι -> M) = ∅ := mulSupport_one

@[to_additive]
/--
lemma `mulSupport_const` / 引理 `mulSupport_const`

English:
lemma mulSupport_const
  given: {c : M} (hc : c != 1)
  statement: (mulSupport fun _ : ι => c) = Set.univ
  proof: by
  ext x; simp [hc]

中文:
引理 mulSupport_const
  条件: {c : M} (hc : c != 1)
  结论: (mulSupport fun _ : ι => c) = 集合.univ
  证明: by
  ext x; simp [hc]
-/
lemma mulSupport_const {c : M} (hc : c != 1) : (mulSupport fun _ : ι => c) = Set.univ := by
  ext x; simp [hc]

/-- The multiplicative support of a function that is everywhere non-one is the whole space. -/
@[to_additive /-- The support of a function that is everywhere nonzero is the whole space. -/]
/--
lemma `mulSupport_eq_univ` / 引理 `mulSupport_eq_univ`

English:
lemma mulSupport_eq_univ
  given: (hf : forall x, f x != 1)
  statement: mulSupport f = Set.univ
  proof: Set.eq_univ_of_forall hf

@[to_additive]

中文:
引理 mulSupport_eq_univ
  条件: (hf : 对任意 x, f x != 1)
  结论: mulSupport f = 集合.univ
  证明: Set.eq_univ_of_forall hf

@[to_additive]

Depends on / 依赖: Set.eq_univ_of_forall, eq_univ_of_forall
-/
lemma mulSupport_eq_univ (hf : forall x, f x != 1) : mulSupport f = Set.univ :=
  Set.eq_univ_of_forall hf

@[to_additive]
/--
lemma `mulSupport_binop_subset` / 引理 `mulSupport_binop_subset`

English:
lemma mulSupport_binop_subset
  given: (op : M -> N -> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N)
  proof: fun x hx =>
not_or_of_imp fun hf hg => hx by simp only [hf, hg, op1]

@[to_additive]

中文:
引理 mulSupport_binop_subset
  条件: (op : M -> N -> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N)
  证明: fun x hx =>
not_or_of_imp fun hf hg => hx by simp only [hf, hg, op1]

@[to_additive]
-/
lemma mulSupport_binop_subset (op : M -> N -> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) :
    mulSupport (fun x => op (f x) (g x)) subseteq mulSupport f union mulSupport g := fun x hx =>
not_or_of_imp fun hf hg => hx by simp only [hf, hg, op1]

@[to_additive]
/--
lemma `mulSupport_comp_subset` / 引理 `mulSupport_comp_subset`

English:
lemma mulSupport_comp_subset
  given: {g : M -> N} (hg : g 1 = 1) (f : ι -> M)
  proof: fun x => mt fun h => by simp only [(· ∘ ·), *]

@[to_additive]

中文:
引理 mulSupport_comp_subset
  条件: {g : M -> N} (hg : g 1 = 1) (f : ι -> M)
  证明: fun x => mt fun h => by simp only [(· ∘ ·), *]

@[to_additive]
-/
lemma mulSupport_comp_subset {g : M -> N} (hg : g 1 = 1) (f : ι -> M) :
    mulSupport (g ∘ f) subseteq mulSupport f := fun x => mt fun h => by simp only [(· ∘ ·), *]

@[to_additive]
/--
lemma `mulSupport_subset_comp` / 引理 `mulSupport_subset_comp`

English:
lemma mulSupport_subset_comp
  given: {g : M -> N} (hg : forall {x}, g x = 1 -> x = 1) (f : ι -> M)
  proof: fun _ => mt hg

@[to_additive]

中文:
引理 mulSupport_subset_comp
  条件: {g : M -> N} (hg : 对任意 {x}, g x = 1 -> x = 1) (f : ι -> M)
  证明: fun _ => mt hg

@[to_additive]
-/
lemma mulSupport_subset_comp {g : M -> N} (hg : forall {x}, g x = 1 -> x = 1) (f : ι -> M) :
    mulSupport f subseteq mulSupport (g ∘ f) := fun _ => mt hg

@[to_additive]
/--
lemma `mulSupport_comp_eq` / 引理 `mulSupport_comp_eq`

English:
lemma mulSupport_comp_eq
  given: (g : M -> N) (hg : forall {x}, g x = 1 ↔ x = 1) (f : ι -> M)
  proof: Set.ext fun _ => not_congr hg

@[to_additive]

中文:
引理 mulSupport_comp_eq
  条件: (g : M -> N) (hg : 对任意 {x}, g x = 1 ↔ x = 1) (f : ι -> M)
  证明: Set.ext fun _ => not_congr hg

@[to_additive]

Depends on / 依赖: Set.ext, not_congr
-/
lemma mulSupport_comp_eq (g : M -> N) (hg : forall {x}, g x = 1 ↔ x = 1) (f : ι -> M) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun _ => not_congr hg

@[to_additive]
/--
lemma `mulSupport_comp_eq_of_range_subset` / 引理 `mulSupport_comp_eq_of_range_subset`

English:
lemma mulSupport_comp_eq_of_range_subset
  statement: {g : M -> N} {f : ι -> M}
  proof: Set.ext fun x => not_congr by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]

中文:
引理 mulSupport_comp_eq_of_range_subset
  结论: {g : M -> N} {f : ι -> M}
  证明: Set.ext fun x => not_congr by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]

Depends on / 依赖: Function, Function.comp, Set.ext, mem_range_self, not_congr
-/
lemma mulSupport_comp_eq_of_range_subset {g : M -> N} {f : ι -> M}
    (hg : forall {x}, x in range f -> (g x = 1 ↔ x = 1)) :
    mulSupport (g ∘ f) = mulSupport f :=
Set.ext fun x => not_congr by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]
/--
lemma `mulSupport_comp_eq_preimage` / 引理 `mulSupport_comp_eq_preimage`

English:
lemma mulSupport_comp_eq_preimage
  given: (g : κ -> M) (f : ι -> κ)
  proof: rfl

@[to_additive support_prodMk]

中文:
引理 mulSupport_comp_eq_preimage
  条件: (g : κ -> M) (f : ι -> κ)
  证明: rfl

@[to_additive support_prodMk]
-/
lemma mulSupport_comp_eq_preimage (g : κ -> M) (f : ι -> κ) :
    mulSupport (g ∘ f) = f ⁻¹' mulSupport g := rfl

@[to_additive support_prodMk]
/--
lemma `mulSupport_prodMk` / 引理 `mulSupport_prodMk`

English:
lemma mulSupport_prodMk
  given: (f : ι -> M) (g : ι -> N)
  proof: Set.ext fun x => by
    simp only [mulSupport, not_and_or, mem_union, mem_ofPred_eq, Prod.mk_eq_one, Ne]

@[to_additive support_prodMk']

中文:
引理 mulSupport_prodMk
  条件: (f : ι -> M) (g : ι -> N)
  证明: Set.ext fun x => by
    simp only [mulSupport, not_and_or, mem_union, mem_ofPred_eq, Prod.mk_eq_one, Ne]

@[to_additive support_prodMk']

Depends on / 依赖: Prod.mk_eq_one, Set.ext, mem_ofPred_eq, mem_union, mk_eq_one, mulSupport, not_and_or
-/
lemma mulSupport_prodMk (f : ι -> M) (g : ι -> N) :
    mulSupport (fun x => (f x, g x)) = mulSupport f union mulSupport g :=
  Set.ext fun x => by
    simp only [mulSupport, not_and_or, mem_union, mem_ofPred_eq, Prod.mk_eq_one, Ne]

@[to_additive support_prodMk']
/--
lemma `mulSupport_prodMk'` / 引理 `mulSupport_prodMk'`

English:
lemma mulSupport_prodMk'
  given: (f : ι -> M × N)
  proof: by
  simp only [← mulSupport_prodMk]

@[to_additive]

中文:
引理 mulSupport_prodMk'
  条件: (f : ι -> M × N)
  证明: by
  simp only [← mulSupport_prodMk]

@[to_additive]

Depends on / 依赖: mulSupport_prodMk
-/
lemma mulSupport_prodMk' (f : ι -> M × N) :
    mulSupport f = (mulSupport fun x => (f x).1) union mulSupport fun x => (f x).2 := by
  simp only [← mulSupport_prodMk]

@[to_additive]
/--
lemma `mulSupport_along_fiber_subset` / 引理 `mulSupport_along_fiber_subset`

English:
lemma mulSupport_along_fiber_subset
  given: (f : ι × κ -> M) (i : ι)
  proof: fun j hj => ⟨(i, j), by simpa using hj⟩

@[to_additive]

中文:
引理 mulSupport_along_fiber_subset
  条件: (f : ι × κ -> M) (i : ι)
  证明: fun j hj => ⟨(i, j), by simpa using hj⟩

@[to_additive]
-/
lemma mulSupport_along_fiber_subset (f : ι × κ -> M) (i : ι) :
    (mulSupport fun j => f (i, j)) subseteq (mulSupport f).image Prod.snd :=
  fun j hj => ⟨(i, j), by simpa using hj⟩

@[to_additive]
/--
lemma `mulSupport_curry` / 引理 `mulSupport_curry`

English:
lemma mulSupport_curry
  given: (f : ι × κ -> M)
  statement: (mulSupport f.curry) = (mulSupport f).image Prod.fst
  proof: by
  simp [mulSupport, funext_iff, image]

@[to_additive]

中文:
引理 mulSupport_curry
  条件: (f : ι × κ -> M)
  结论: (mulSupport f.curry) = (mulSupport f).像 积类型.fst
  证明: by
  simp [mulSupport, funext_iff, image]

@[to_additive]

Depends on / 依赖: funext_iff, mulSupport
-/
lemma mulSupport_curry (f : ι × κ -> M) : (mulSupport f.curry) = (mulSupport f).image Prod.fst := by
  simp [mulSupport, funext_iff, image]

@[to_additive]
/--
lemma `mulSupport_fun_curry` / 引理 `mulSupport_fun_curry`

English:
lemma mulSupport_fun_curry
  given: (f : ι × κ -> M)
  proof: mulSupport_curry f

中文:
引理 mulSupport_fun_curry
  条件: (f : ι × κ -> M)
  证明: mulSupport_curry f

Depends on / 依赖: mulSupport_curry
-/
lemma mulSupport_fun_curry (f : ι × κ -> M) :
    mulSupport (fun i j => f (i, j)) = (mulSupport f).image Prod.fst := mulSupport_curry f

end Function

namespace Set
variable [One M] {f : ι -> M} {s : Set κ} {g : κ -> ι}

@[to_additive]
/--
lemma `image_inter_mulSupport_eq` / 引理 `image_inter_mulSupport_eq`

English:
lemma image_inter_mulSupport_eq
  statement: g '' s inter mulSupport f = g '' (s inter mulSupport (f ∘ g))
  proof: by
  rw [mulSupport_comp_eq_preimage f g]; rw [image_inter_preimage]

中文:
引理 image_inter_mulSupport_eq
  结论: g '' s inter mulSupport f = g '' (s inter mulSupport (f ∘ g))
  证明: by
  rw [mulSupport_comp_eq_preimage f g]; rw [image_inter_preimage]

Depends on / 依赖: image_inter_preimage, mulSupport_comp_eq_preimage
-/
lemma image_inter_mulSupport_eq : g '' s inter mulSupport f = g '' (s inter mulSupport (f ∘ g)) := by
  rw [mulSupport_comp_eq_preimage f g]; rw [image_inter_preimage]

end Set

namespace Pi
variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

@[to_additive]
/--
lemma `mulSupport_mulSingle_subset` / 引理 `mulSupport_mulSingle_subset`

English:
lemma mulSupport_mulSingle_subset
  statement: mulSupport (mulSingle i a) subseteq {i}
  proof: fun _ hx =>
by_contra fun hx' => hx mulSingle_eq_of_ne hx' _

@[to_additive]

中文:
引理 mulSupport_mulSingle_subset
  结论: mulSupport (mulSingle i a) subseteq {i}
  证明: fun _ hx =>
by_contra fun hx' => hx mulSingle_eq_of_ne hx' _

@[to_additive]
-/
lemma mulSupport_mulSingle_subset : mulSupport (mulSingle i a) subseteq {i} := fun _ hx =>
by_contra fun hx' => hx mulSingle_eq_of_ne hx' _

@[to_additive]
/--
lemma `mulSupport_mulSingle_one` / 引理 `mulSupport_mulSingle_one`

English:
lemma mulSupport_mulSingle_one
  statement: mulSupport (mulSingle i (1 : M)) = ∅
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 mulSupport_mulSingle_one
  结论: mulSupport (mulSingle i (1 : M)) = ∅
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma mulSupport_mulSingle_one : mulSupport (mulSingle i (1 : M)) = ∅ := by simp

@[to_additive (attr := simp)]
/--
lemma `mulSupport_mulSingle_of_ne` / 引理 `mulSupport_mulSingle_of_ne`

English:
lemma mulSupport_mulSingle_of_ne
  given: (h : a != 1)
  statement: mulSupport (mulSingle i a) = {i}
  proof: mulSupport_mulSingle_subset.antisymm fun x hx => by rwa [mem_mulSupport, hx, mulSingle_eq_same]

@[to_additive]

中文:
引理 mulSupport_mulSingle_of_ne
  条件: (h : a != 1)
  结论: mulSupport (mulSingle i a) = {i}
  证明: mulSupport_mulSingle_subset.antisymm fun x hx => by rwa [mem_mulSupport, hx, mulSingle_eq_same]

@[to_additive]

Depends on / 依赖: antisymm, mem_mulSupport, mulSingle_eq_same, mulSupport_mulSingle_subset, mulSupport_mulSingle_subset.antisymm
-/
lemma mulSupport_mulSingle_of_ne (h : a != 1) : mulSupport (mulSingle i a) = {i} :=
  mulSupport_mulSingle_subset.antisymm fun x hx => by rwa [mem_mulSupport, hx, mulSingle_eq_same]

@[to_additive]
/--
lemma `mulSupport_mulSingle` / 引理 `mulSupport_mulSingle`

English:
lemma mulSupport_mulSingle
  given: [DecidableEq M]
  proof: by split_ifs with h <;> simp [h]

@[to_additive]

中文:
引理 mulSupport_mulSingle
  条件: [DecidableEq M]
  证明: by split_ifs with h <;> simp [h]

@[to_additive]

Depends on / 依赖: split_ifs
-/
lemma mulSupport_mulSingle [DecidableEq M] :
    mulSupport (mulSingle i a) = if a = 1 then ∅ else {i} := by split_ifs with h <;> simp [h]

@[to_additive]
/--
lemma `subsingleton_mulSupport_mulSingle` / 引理 `subsingleton_mulSupport_mulSingle`

English:
lemma subsingleton_mulSupport_mulSingle
  statement: (mulSupport (mulSingle i a)).Subsingleton
  proof: by
  classical
  rw [mulSupport_mulSingle]
  split_ifs with h <;> simp

@[to_additive]

中文:
引理 subsingleton_mulSupport_mulSingle
  结论: (mulSupport (mulSingle i a)).子单例
  证明: by
  classical
  rw [mulSupport_mulSingle]
  split_ifs with h <;> simp

@[to_additive]

Depends on / 依赖: classical, mulSupport_mulSingle, split_ifs
-/
lemma subsingleton_mulSupport_mulSingle : (mulSupport (mulSingle i a)).Subsingleton := by
  classical
  rw [mulSupport_mulSingle]
  split_ifs with h <;> simp

@[to_additive]
/--
lemma `mulSupport_mulSingle_disjoint` / 引理 `mulSupport_mulSingle_disjoint`

English:
lemma mulSupport_mulSingle_disjoint
  given: (ha : a != 1) (hb : b != 1)
  proof: by
  rw [mulSupport_mulSingle_of_ne ha]; rw [mulSupport_mulSingle_of_ne hb]; rw [disjoint_singleton]

中文:
引理 mulSupport_mulSingle_disjoint
  条件: (ha : a != 1) (hb : b != 1)
  证明: by
  rw [mulSupport_mulSingle_of_ne ha]; rw [mulSupport_mulSingle_of_ne hb]; rw [disjoint_singleton]

Depends on / 依赖: disjoint_singleton, mulSupport_mulSingle_of_ne
-/
lemma mulSupport_mulSingle_disjoint (ha : a != 1) (hb : b != 1) :
    Disjoint (mulSupport (mulSingle i a)) (mulSupport (mulSingle j b)) ↔ i != j := by
  rw [mulSupport_mulSingle_of_ne ha]; rw [mulSupport_mulSingle_of_ne hb]; rw [disjoint_singleton]

end Pi
