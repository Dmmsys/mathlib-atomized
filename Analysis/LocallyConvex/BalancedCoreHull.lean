/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balancedCore`: The largest balanced subset of a set `s`.
* `balancedHull`: The smallest balanced superset of a set `s`.

## Main statements

* `balancedCore_eq_iInter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `‖r‖ ≤ 1`. We show that `balancedHull` has the
defining properties of a hull in `Balanced.balancedHull_subset_of_subset` and `subset_balancedHull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balancedCore_eq_iInter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/

@[expose] public section


open Set Pointwise Topology Filter

variable {𝕜 E ι : Type*}

section balancedHull

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable (𝕜) [SMul 𝕜 E] {s t : Set E} {x : E}

/--
Definition of `balancedCore` / `balancedCore` 的定义

English:
definition balancedCore
  signature: (s : Set E)
  body: ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t subseteq s }

中文:
定义 balancedCore
  签名: (s : 集合 E)
  定义体: ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t subseteq s }

Depends on / 依赖: Balanced, subseteq
-/
def balancedCore (s : Set E) :=
  ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t subseteq s }

/--
Definition of `balancedCoreAux` / `balancedCoreAux` 的定义

English:
definition balancedCoreAux
  signature: (s : Set E)
  body: ⋂ (r : 𝕜) (_ : 1 <= ‖r‖), r • s

中文:
定义 balancedCoreAux
  签名: (s : 集合 E)
  定义体: ⋂ (r : 𝕜) (_ : 1 <= ‖r‖), r • s
-/
def balancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (_ : 1 <= ‖r‖), r • s

/--
Definition of `balancedHull` / `balancedHull` 的定义

English:
definition balancedHull
  signature: (s : Set E)
  body: ⋃ (r : 𝕜) (_ : ‖r‖ <= 1), r • s

中文:
定义 balancedHull
  签名: (s : 集合 E)
  定义体: ⋃ (r : 𝕜) (_ : ‖r‖ <= 1), r • s
-/
def balancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (_ : ‖r‖ <= 1), r • s

variable {𝕜}

/--
theorem `balancedCore_subset` / 定理 `balancedCore_subset`

English:
theorem balancedCore_subset
  given: (s : Set E)
  statement: balancedCore 𝕜 s subseteq s
  proof: sUnion_subset fun _ ht => ht.2

中文:
定理 balancedCore_subset
  条件: (s : 集合 E)
  结论: balancedCore 𝕜 s subseteq s
  证明: sUnion_subset fun _ ht => ht.2

Depends on / 依赖: sUnion_subset
-/
theorem balancedCore_subset (s : Set E) : balancedCore 𝕜 s subseteq s :=
  sUnion_subset fun _ ht => ht.2

/--
theorem `balancedCore_empty` / 定理 `balancedCore_empty`

English:
theorem balancedCore_empty
  statement: balancedCore 𝕜 (∅ : Set E) = ∅
  proof: eq_empty_of_subset_empty (balancedCore_subset _)

中文:
定理 balancedCore_empty
  结论: balancedCore 𝕜 (∅ : 集合 E) = ∅
  证明: eq_empty_of_subset_empty (balancedCore_subset _)

Depends on / 依赖: balancedCore_subset, eq_empty_of_subset_empty
-/
theorem balancedCore_empty : balancedCore 𝕜 (∅ : Set E) = ∅ :=
  eq_empty_of_subset_empty (balancedCore_subset _)

/--
theorem `mem_balancedCore_iff` / 定理 `mem_balancedCore_iff`

English:
theorem mem_balancedCore_iff
  statement: x in balancedCore 𝕜 s ↔ exists t, Balanced 𝕜 t ∧ t subseteq s ∧ x in t
  proof: by
  simp_rw [balancedCore, mem_sUnion, mem_ofPred_eq, and_assoc]

中文:
定理 mem_balancedCore_iff
  结论: x in balancedCore 𝕜 s ↔ 存在 t, Balanced 𝕜 t ∧ t subseteq s ∧ x in t
  证明: by
  simp_rw [balancedCore, mem_sUnion, mem_ofPred_eq, and_assoc]

Depends on / 依赖: and_assoc, balancedCore, mem_ofPred_eq, mem_sUnion, simp_rw
-/
theorem mem_balancedCore_iff : x in balancedCore 𝕜 s ↔ exists t, Balanced 𝕜 t ∧ t subseteq s ∧ x in t := by
  simp_rw [balancedCore, mem_sUnion, mem_ofPred_eq, and_assoc]

/--
theorem `smul_balancedCore_subset` / 定理 `smul_balancedCore_subset`

English:
theorem smul_balancedCore_subset
  given: (s : Set E) {a : 𝕜} (ha : ‖a‖ <= 1)
  proof: by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balancedCore_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩

中文:
定理 smul_balancedCore_subset
  条件: (s : 集合 E) {a : 𝕜} (ha : ‖a‖ <= 1)
  证明: by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balancedCore_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩

Depends on / 依赖: mem_balancedCore_iff, smul_mem_smul_set
-/
theorem smul_balancedCore_subset (s : Set E) {a : 𝕜} (ha : ‖a‖ <= 1) :
    a • balancedCore 𝕜 s subseteq balancedCore 𝕜 s := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balancedCore_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩

/--
theorem `balancedCore_balanced` / 定理 `balancedCore_balanced`

English:
theorem balancedCore_balanced
  given: (s : Set E)
  statement: Balanced 𝕜 (balancedCore 𝕜 s)
  proof: fun _ =>
  smul_balancedCore_subset s

中文:
定理 balancedCore_balanced
  条件: (s : 集合 E)
  结论: Balanced 𝕜 (balancedCore 𝕜 s)
  证明: fun _ =>
  smul_balancedCore_subset s
-/
theorem balancedCore_balanced (s : Set E) : Balanced 𝕜 (balancedCore 𝕜 s) := fun _ =>
  smul_balancedCore_subset s

/--
theorem `Balanced.subset_balancedCore_of_subset` / 定理 `Balanced.subset_balancedCore_of_subset`

English:
theorem Balanced.subset_balancedCore_of_subset
  given: (hs : Balanced 𝕜 s) (h : s subseteq t)
  proof: subset_sUnion_of_mem ⟨hs, h⟩

中文:
定理 Balanced.subset_balancedCore_of_subset
  条件: (hs : Balanced 𝕜 s) (h : s subseteq t)
  证明: subset_sUnion_of_mem ⟨hs, h⟩

Depends on / 依赖: subset_sUnion_of_mem
-/
theorem Balanced.subset_balancedCore_of_subset (hs : Balanced 𝕜 s) (h : s subseteq t) :
    s subseteq balancedCore 𝕜 t :=
  subset_sUnion_of_mem ⟨hs, h⟩

/--
lemma `Balanced.balancedCore_eq` / 引理 `Balanced.balancedCore_eq`

English:
lemma Balanced.balancedCore_eq
  given: (h : Balanced 𝕜 s)
  statement: balancedCore 𝕜 s = s
  proof: le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset subset_rfl)

中文:
引理 Balanced.balancedCore_eq
  条件: (h : Balanced 𝕜 s)
  结论: balancedCore 𝕜 s = s
  证明: le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset subset_rfl)

Depends on / 依赖: balancedCore_subset, h.subset_balancedCore_of_subset, le_antisymm, subset_balancedCore_of_subset, subset_rfl
-/
lemma Balanced.balancedCore_eq (h : Balanced 𝕜 s) : balancedCore 𝕜 s = s :=
  le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset subset_rfl)

/--
theorem `mem_balancedCoreAux_iff` / 定理 `mem_balancedCoreAux_iff`

English:
theorem mem_balancedCoreAux_iff
  statement: x in balancedCoreAux 𝕜 s ↔ forall r : 𝕜, 1 <= ‖r‖ -> x in r • s
  proof: mem_iInter₂

中文:
定理 mem_balancedCoreAux_iff
  结论: x in balancedCoreAux 𝕜 s ↔ 对任意 r : 𝕜, 1 <= ‖r‖ -> x in r • s
  证明: mem_iInter₂
-/
theorem mem_balancedCoreAux_iff : x in balancedCoreAux 𝕜 s ↔ forall r : 𝕜, 1 <= ‖r‖ -> x in r • s :=
  mem_iInter₂

/--
theorem `mem_balancedHull_iff` / 定理 `mem_balancedHull_iff`

English:
theorem mem_balancedHull_iff
  statement: x in balancedHull 𝕜 s ↔ exists r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
  proof: by
  simp [balancedHull]

中文:
定理 mem_balancedHull_iff
  结论: x in balancedHull 𝕜 s ↔ 存在 r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
  证明: by
  simp [balancedHull]

Depends on / 依赖: balancedHull
-/
theorem mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exists r : 𝕜, ‖r‖ <= 1 ∧ x in r • s := by
  simp [balancedHull]

/--
theorem `Balanced.balancedHull_subset_of_subset` / 定理 `Balanced.balancedHull_subset_of_subset`

English:
theorem Balanced.balancedHull_subset_of_subset
  given: (ht : Balanced 𝕜 t) (h : s subseteq t)
  proof: by
  intro x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)

@[mono, gcongr]

中文:
定理 Balanced.balancedHull_subset_of_subset
  条件: (ht : Balanced 𝕜 t) (h : s subseteq t)
  证明: by
  intro x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)

@[mono, gcongr]

Depends on / 依赖: ht.smul_mem, mem_balancedHull_iff, smul_mem
-/
theorem Balanced.balancedHull_subset_of_subset (ht : Balanced 𝕜 t) (h : s subseteq t) :
    balancedHull 𝕜 s subseteq t := by
  intro x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)

@[mono, gcongr]
/--
theorem `balancedHull_mono` / 定理 `balancedHull_mono`

English:
theorem balancedHull_mono
  given: (hst : s subseteq t)
  statement: balancedHull 𝕜 s subseteq balancedHull 𝕜 t
  proof: by
  intro x hx
  rw [mem_balancedHull_iff] at *
  obtain ⟨r, hr₁, hr₂⟩ := hx
  use r
  exact ⟨hr₁, smul_set_mono hst hr₂⟩

中文:
定理 balancedHull_mono
  条件: (hst : s subseteq t)
  结论: balancedHull 𝕜 s subseteq balancedHull 𝕜 t
  证明: by
  intro x hx
  rw [mem_balancedHull_iff] at *
  obtain ⟨r, hr₁, hr₂⟩ := hx
  use r
  exact ⟨hr₁, smul_set_mono hst hr₂⟩

Depends on / 依赖: mem_balancedHull_iff, smul_set_mono
-/
theorem balancedHull_mono (hst : s subseteq t) : balancedHull 𝕜 s subseteq balancedHull 𝕜 t := by
  intro x hx
  rw [mem_balancedHull_iff] at *
  obtain ⟨r, hr₁, hr₂⟩ := hx
  use r
  exact ⟨hr₁, smul_set_mono hst hr₂⟩

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s : Set E}

/--
theorem `balancedCore_zero_mem` / 定理 `balancedCore_zero_mem`

English:
theorem balancedCore_zero_mem
  given: (hs : (0 : E) in s)
  statement: (0 : E) in balancedCore 𝕜 s
  proof: mem_balancedCore_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, Set.zero_mem_zero⟩

中文:
定理 balancedCore_zero_mem
  条件: (hs : (0 : E) in s)
  结论: (0 : E) in balancedCore 𝕜 s
  证明: mem_balancedCore_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, Set.zero_mem_zero⟩

Depends on / 依赖: Set.zero_mem_zero, balanced_zero, mem_balancedCore_iff, zero_mem_zero, zero_subset
-/
theorem balancedCore_zero_mem (hs : (0 : E) in s) : (0 : E) in balancedCore 𝕜 s :=
  mem_balancedCore_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, Set.zero_mem_zero⟩

/--
theorem `balancedCore_nonempty_iff` / 定理 `balancedCore_nonempty_iff`

English:
theorem balancedCore_nonempty_iff
  statement: (balancedCore 𝕜 s).Nonempty ↔ (0 : E) in s
  proof: ⟨fun h => zero_subset.1 (zero_smul_set h).superset.trans
(balancedCore_balanced s (0 : 𝕜) <| norm_zero.trans_le zero_le_one).trans
      balancedCore_subset _,
    fun h => ⟨0, balancedCore_zero_mem h⟩⟩

中文:
定理 balancedCore_nonempty_iff
  结论: (balancedCore 𝕜 s).非空 ↔ (0 : E) in s
  证明: ⟨fun h => zero_subset.1 (zero_smul_set h).superset.trans
(balancedCore_balanced s (0 : 𝕜) <| norm_zero.trans_le zero_le_one).trans
      balancedCore_subset _,
    fun h => ⟨0, balancedCore_zero_mem h⟩⟩

Depends on / 依赖: balancedCore_balanced, balancedCore_subset, balancedCore_zero_mem, norm_zero, norm_zero.trans_le, superset, superset.trans, trans_le, zero_le_one, zero_smul_set, zero_subset
-/
theorem balancedCore_nonempty_iff : (balancedCore 𝕜 s).Nonempty ↔ (0 : E) in s :=
⟨fun h => zero_subset.1 (zero_smul_set h).superset.trans
(balancedCore_balanced s (0 : 𝕜) <| norm_zero.trans_le zero_le_one).trans
      balancedCore_subset _,
    fun h => ⟨0, balancedCore_zero_mem h⟩⟩

/--
lemma `Balanced.zero_mem` / 引理 `Balanced.zero_mem`

English:
lemma Balanced.zero_mem
  given: (hs : Balanced 𝕜 s) (hs_nonempty : s.Nonempty)
  statement: (0 : E) in s
  proof: by
  rw [← hs.balancedCore_eq] at hs_nonempty
  exact balancedCore_nonempty_iff.mp hs_nonempty

中文:
引理 Balanced.zero_mem
  条件: (hs : Balanced 𝕜 s) (hs_nonempty : s.非空)
  结论: (0 : E) in s
  证明: by
  rw [← hs.balancedCore_eq] at hs_nonempty
  exact balancedCore_nonempty_iff.mp hs_nonempty

Depends on / 依赖: balancedCore_eq, balancedCore_nonempty_iff, balancedCore_nonempty_iff.mp, hs.balancedCore_eq, hs_nonempty
-/
lemma Balanced.zero_mem (hs : Balanced 𝕜 s) (hs_nonempty : s.Nonempty) : (0 : E) in s := by
  rw [← hs.balancedCore_eq] at hs_nonempty
  exact balancedCore_nonempty_iff.mp hs_nonempty

variable (𝕜) in
/--
theorem `subset_balancedHull` / 定理 `subset_balancedHull`

English:
theorem subset_balancedHull
  given: [NormOneClass 𝕜] {s : Set E}
  statement: s subseteq balancedHull 𝕜 s
  proof: fun _ hx =>
  mem_balancedHull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩

中文:
定理 subset_balancedHull
  条件: [NormOne类 𝕜] {s : 集合 E}
  结论: s subseteq balancedHull 𝕜 s
  证明: fun _ hx =>
  mem_balancedHull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩
-/
theorem subset_balancedHull [NormOneClass 𝕜] {s : Set E} : s subseteq balancedHull 𝕜 s := fun _ hx =>
  mem_balancedHull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩

/--
theorem `balancedHull.balanced` / 定理 `balancedHull.balanced`

English:
theorem balancedHull.balanced
  given: (s : Set E)
  statement: Balanced 𝕜 (balancedHull 𝕜 s)
  proof: by
  intro a ha
  simp_rw [balancedHull, smul_set_iUnion₂, subset_def, mem_iUnion₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩

中文:
定理 balancedHull.balanced
  条件: (s : 集合 E)
  结论: Balanced 𝕜 (balancedHull 𝕜 s)
  证明: by
  intro a ha
  simp_rw [balancedHull, smul_set_iUnion₂, subset_def, mem_iUnion₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩

Depends on / 依赖: balancedHull, norm_mul_le, norm_nonneg, simp_rw, smul_assoc, subset_def
-/
theorem balancedHull.balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s) := by
  intro a ha
  simp_rw [balancedHull, smul_set_iUnion₂, subset_def, mem_iUnion₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩

open Balanced in
/--
theorem `balancedHull_add_subset` / 定理 `balancedHull_add_subset`

English:
theorem balancedHull_add_subset
  given: [NormOneClass 𝕜] {t : Set E}
  proof: balancedHull_subset_of_subset (add (balancedHull.balanced _) (balancedHull.balanced _))
    (add_subset_add (subset_balancedHull _) (subset_balancedHull _))

中文:
定理 balancedHull_add_subset
  条件: [NormOne类 𝕜] {t : 集合 E}
  证明: balancedHull_subset_of_subset (add (balancedHull.balanced _) (balancedHull.balanced _))
    (add_subset_add (subset_balancedHull _) (subset_balancedHull _))

Depends on / 依赖: add_subset_add, balanced, balancedHull, balancedHull.balanced, balancedHull_subset_of_subset, subset_balancedHull
-/
theorem balancedHull_add_subset [NormOneClass 𝕜] {t : Set E} :
    balancedHull 𝕜 (s + t) subseteq balancedHull 𝕜 s + balancedHull 𝕜 t :=
  balancedHull_subset_of_subset (add (balancedHull.balanced _) (balancedHull.balanced _))
    (add_subset_add (subset_balancedHull _) (subset_balancedHull _))

end Module

end SeminormedRing

section NormedField

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

@[simp]
/--
theorem `balancedCoreAux_empty` / 定理 `balancedCoreAux_empty`

English:
theorem balancedCoreAux_empty
  statement: balancedCoreAux 𝕜 (∅ : Set E) = ∅
  proof: by
  simp_rw [balancedCoreAux, iInter₂_eq_empty_iff, smul_set_empty]
  exact fun _ => ⟨1, norm_one.ge, notMem_empty _⟩

中文:
定理 balancedCoreAux_empty
  结论: balancedCoreAux 𝕜 (∅ : 集合 E) = ∅
  证明: by
  simp_rw [balancedCoreAux, iInter₂_eq_empty_iff, smul_set_empty]
  exact fun _ => ⟨1, norm_one.ge, notMem_empty _⟩

Depends on / 依赖: balancedCoreAux, norm_one, norm_one.ge, notMem_empty, simp_rw, smul_set_empty
-/
theorem balancedCoreAux_empty : balancedCoreAux 𝕜 (∅ : Set E) = ∅ := by
  simp_rw [balancedCoreAux, iInter₂_eq_empty_iff, smul_set_empty]
  exact fun _ => ⟨1, norm_one.ge, notMem_empty _⟩

/--
theorem `balancedCoreAux_subset` / 定理 `balancedCoreAux_subset`

English:
theorem balancedCoreAux_subset
  given: (s : Set E)
  statement: balancedCoreAux 𝕜 s subseteq s
  proof: fun x hx => by
  simpa only [one_smul] using mem_balancedCoreAux_iff.1 hx 1 norm_one.ge

中文:
定理 balancedCoreAux_subset
  条件: (s : 集合 E)
  结论: balancedCoreAux 𝕜 s subseteq s
  证明: fun x hx => by
  simpa only [one_smul] using mem_balancedCoreAux_iff.1 hx 1 norm_one.ge

Depends on / 依赖: mem_balancedCoreAux_iff, norm_one, norm_one.ge, one_smul
-/
theorem balancedCoreAux_subset (s : Set E) : balancedCoreAux 𝕜 s subseteq s := fun x hx => by
  simpa only [one_smul] using mem_balancedCoreAux_iff.1 hx 1 norm_one.ge

/--
theorem `balancedCoreAux_balanced` / 定理 `balancedCoreAux_balanced`

English:
theorem balancedCoreAux_balanced
  given: (h0 : (0 : E) in balancedCoreAux 𝕜 s)
  proof: by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_balancedCoreAux_iff] at hy ⊢
  intro r hr
  have h'' : 1 <= ‖a⁻¹ • r‖ := by
    rw [norm_smul]; rw [norm_inv]
    exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ (norm_pos_iff.mpr h)).2 ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

中文:
定理 balancedCoreAux_balanced
  条件: (h0 : (0 : E) in balancedCoreAux 𝕜 s)
  证明: by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_balancedCoreAux_iff] at hy ⊢
  intro r hr
  have h'' : 1 <= ‖a⁻¹ • r‖ := by
    rw [norm_smul]; rw [norm_inv]
    exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ (norm_pos_iff.mpr h)).2 ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

Depends on / 依赖: eq_or_ne, mem_balancedCoreAux_iff, norm_inv, norm_pos_iff, norm_pos_iff.mpr, norm_smul, one_le_mul_of_one_le_of_one_le, simp_rw, smul_assoc, zero_smul
-/
theorem balancedCoreAux_balanced (h0 : (0 : E) in balancedCoreAux 𝕜 s) :
    Balanced 𝕜 (balancedCoreAux 𝕜 s) := by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_balancedCoreAux_iff] at hy ⊢
  intro r hr
  have h'' : 1 <= ‖a⁻¹ • r‖ := by
    rw [norm_smul]; rw [norm_inv]
    exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ (norm_pos_iff.mpr h)).2 ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

/--
theorem `balancedCoreAux_maximal` / 定理 `balancedCoreAux_maximal`

English:
theorem balancedCoreAux_maximal
  given: (h : t subseteq s) (ht : Balanced 𝕜 t)
  statement: t subseteq balancedCoreAux 𝕜 s
  proof: by
  refine fun x hx => mem_balancedCoreAux_iff.2 fun r hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine h (ht.smul_mem ?_ hx)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hr

中文:
定理 balancedCoreAux_maximal
  条件: (h : t subseteq s) (ht : Balanced 𝕜 t)
  结论: t subseteq balancedCoreAux 𝕜 s
  证明: by
  refine fun x hx => mem_balancedCoreAux_iff.2 fun r hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine h (ht.smul_mem ?_ hx)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hr

Depends on / 依赖: ht.smul_mem, mem_balancedCoreAux_iff, norm_inv, norm_pos_iff, norm_pos_iff.mp, smul_mem, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem balancedCoreAux_maximal (h : t subseteq s) (ht : Balanced 𝕜 t) : t subseteq balancedCoreAux 𝕜 s := by
  refine fun x hx => mem_balancedCoreAux_iff.2 fun r hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine h (ht.smul_mem ?_ hx)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hr

/--
theorem `balancedCore_subset_balancedCoreAux` / 定理 `balancedCore_subset_balancedCoreAux`

English:
theorem balancedCore_subset_balancedCoreAux
  statement: balancedCore 𝕜 s subseteq balancedCoreAux 𝕜 s
  proof: balancedCoreAux_maximal (balancedCore_subset s) (balancedCore_balanced s)

中文:
定理 balancedCore_subset_balancedCoreAux
  结论: balancedCore 𝕜 s subseteq balancedCoreAux 𝕜 s
  证明: balancedCoreAux_maximal (balancedCore_subset s) (balancedCore_balanced s)

Depends on / 依赖: balancedCoreAux_maximal, balancedCore_balanced, balancedCore_subset
-/
theorem balancedCore_subset_balancedCoreAux : balancedCore 𝕜 s subseteq balancedCoreAux 𝕜 s :=
  balancedCoreAux_maximal (balancedCore_subset s) (balancedCore_balanced s)

/--
theorem `balancedCore_eq_iInter` / 定理 `balancedCore_eq_iInter`

English:
theorem balancedCore_eq_iInter
  given: (hs : (0 : E) in s)
  proof: by
  refine balancedCore_subset_balancedCoreAux.antisymm ?_
  refine (balancedCoreAux_balanced ?_).subset_balancedCore_of_subset (balancedCoreAux_subset s)
  exact balancedCore_subset_balancedCoreAux (balancedCore_zero_mem hs)

中文:
定理 balancedCore_eq_i整数er
  条件: (hs : (0 : E) in s)
  证明: by
  refine balancedCore_subset_balancedCoreAux.antisymm ?_
  refine (balancedCoreAux_balanced ?_).subset_balancedCore_of_subset (balancedCoreAux_subset s)
  exact balancedCore_subset_balancedCoreAux (balancedCore_zero_mem hs)

Depends on / 依赖: antisymm, balancedCoreAux_balanced, balancedCoreAux_subset, balancedCore_subset_balancedCoreAux, balancedCore_subset_balancedCoreAux.antisymm, balancedCore_zero_mem, subset_balancedCore_of_subset
-/
theorem balancedCore_eq_iInter (hs : (0 : E) in s) :
    balancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 <= ‖r‖), r • s := by
  refine balancedCore_subset_balancedCoreAux.antisymm ?_
  refine (balancedCoreAux_balanced ?_).subset_balancedCore_of_subset (balancedCoreAux_subset s)
  exact balancedCore_subset_balancedCoreAux (balancedCore_zero_mem hs)

/--
theorem `subset_balancedCore` / 定理 `subset_balancedCore`

English:
theorem subset_balancedCore
  given: (ht : (0 : E) in t) (hst : forall a : 𝕜, ‖a‖ <= 1 -> a • s subseteq t)
  proof: by
  rw [balancedCore_eq_iInter ht]
  refine subset_iInter₂ fun a ha => ?_
  rw [subset_smul_set_iff₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha)]
  apply hst
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ ha

中文:
定理 subset_balancedCore
  条件: (ht : (0 : E) in t) (hst : 对任意 a : 𝕜, ‖a‖ <= 1 -> a • s subseteq t)
  证明: by
  rw [balancedCore_eq_iInter ht]
  refine subset_iInter₂ fun a ha => ?_
  rw [subset_smul_set_iff₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha)]
  apply hst
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ ha

Depends on / 依赖: balancedCore_eq_iInter, norm_inv, norm_pos_iff, norm_pos_iff.mp, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem subset_balancedCore (ht : (0 : E) in t) (hst : forall a : 𝕜, ‖a‖ <= 1 -> a • s subseteq t) :
    s subseteq balancedCore 𝕜 t := by
  rw [balancedCore_eq_iInter ht]
  refine subset_iInter₂ fun a ha => ?_
  rw [subset_smul_set_iff₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha)]
  apply hst
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ ha

end NormedField

end balancedHull

/-! ### Topological properties -/


section Topology

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousSMul 𝕜 E] {U : Set E}

/--
theorem `IsClosed.balancedCore` / 定理 `IsClosed.balancedCore`

English:
theorem IsClosed.balancedCore
  given: (hU : IsClosed U)
  statement: IsClosed (balancedCore 𝕜 U)
  proof: by
  by_cases h : (0 : E) in U
  · rw [balancedCore_eq_iInter h]
    refine isClosed_iInter fun a => ?_
    refine isClosed_iInter fun ha => ?_
    have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [norm_pos_iff] at ha'
    exact isClosedMap_smul_of_ne_zero ha' U hU
  · have : balancedCore 𝕜 U = ∅ := by
      contrapose! h
      exact balancedCore_nonempty_iff.mp h
    rw [this]
    exact isClosed_empty

omit [ContinuousSMul 𝕜 E] in

中文:
定理 是闭集.balancedCore
  条件: (hU : 是闭集 U)
  结论: 是闭集 (balancedCore 𝕜 U)
  证明: by
  by_cases h : (0 : E) in U
  · rw [balancedCore_eq_iInter h]
    refine isClosed_iInter fun a => ?_
    refine isClosed_iInter fun ha => ?_
    have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [norm_pos_iff] at ha'
    exact isClosedMap_smul_of_ne_zero ha' U hU
  · have : balancedCore 𝕜 U = ∅ := by
      contrapose! h
      exact balancedCore_nonempty_iff.mp h
    rw [this]
    exact isClosed_empty

omit [ContinuousSMul 𝕜 E] in
-/
protected theorem IsClosed.balancedCore (hU : IsClosed U) : IsClosed (balancedCore 𝕜 U) := by
  by_cases h : (0 : E) in U
  · rw [balancedCore_eq_iInter h]
    refine isClosed_iInter fun a => ?_
    refine isClosed_iInter fun ha => ?_
    have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [norm_pos_iff] at ha'
    exact isClosedMap_smul_of_ne_zero ha' U hU
  · have : balancedCore 𝕜 U = ∅ := by
      contrapose! h
      exact balancedCore_nonempty_iff.mp h
    rw [this]
    exact isClosed_empty

omit [ContinuousSMul 𝕜 E] in
/--
theorem `IsOpen.balancedHull` / 定理 `IsOpen.balancedHull`

English:
theorem IsOpen.balancedHull
  statement: [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : IsOpen s)
  proof: by
  have : (⋃ r : 𝕜, ⋃ (_ : ‖r‖ <= 1), r • s) = (⋃ r : 𝕜, ⋃ (_ : ‖r‖ <= 1 ∧ r != 0), r • s) := by
    refine subset_antisymm (Set.iUnion₂_mono' fun r hr => ?_) (Set.iUnion₂_mono' (by grind))
    obtain rfl | hr_ne := eq_or_ne r 0
    · exact ⟨1, by simp, by simpa [Set.zero_smul_set ⟨0, hzero⟩]⟩
    · use r
  rw [balancedHull]; rw [this]
  exact isOpen_biUnion (fun r hr => hs.smul₀ hr.2)

中文:
定理 是开集.balancedHull
  结论: [连续常数标量乘法 𝕜 E] {s : 集合 E} (hs : 是开集 s)
  证明: by
  have : (⋃ r : 𝕜, ⋃ (_ : ‖r‖ <= 1), r • s) = (⋃ r : 𝕜, ⋃ (_ : ‖r‖ <= 1 ∧ r != 0), r • s) := by
    refine subset_antisymm (Set.iUnion₂_mono' fun r hr => ?_) (Set.iUnion₂_mono' (by grind))
    obtain rfl | hr_ne := eq_or_ne r 0
    · exact ⟨1, by simp, by simpa [Set.zero_smul_set ⟨0, hzero⟩]⟩
    · use r
  rw [balancedHull]; rw [this]
  exact isOpen_biUnion (fun r hr => hs.smul₀ hr.2)
-/
protected theorem IsOpen.balancedHull [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : IsOpen s)
    (hzero : 0 in s) : IsOpen (balancedHull 𝕜 s) := by
  have : (⋃ r : 𝕜, ⋃ (_ : ‖r‖ <= 1), r • s) = (⋃ r : 𝕜, ⋃ (_ : ‖r‖ <= 1 ∧ r != 0), r • s) := by
    refine subset_antisymm (Set.iUnion₂_mono' fun r hr => ?_) (Set.iUnion₂_mono' (by grind))
    obtain rfl | hr_ne := eq_or_ne r 0
    · exact ⟨1, by simp, by simpa [Set.zero_smul_set ⟨0, hzero⟩]⟩
    · use r
  rw [balancedHull]; rw [this]
  exact isOpen_biUnion (fun r hr => hs.smul₀ hr.2)

-- We don't have a `NontriviallyNormedDivisionRing`, so we use a `NeBot` assumption instead
variable [NeBot (𝓝[!=] (0 : 𝕜))]

/--
theorem `balancedCore_mem_nhds_zero` / 定理 `balancedCore_mem_nhds_zero`

English:
theorem balancedCore_mem_nhds_zero
  given: (hU : U in 𝓝 (0 : E))
  statement: balancedCore 𝕜 U in 𝓝 (0 : E)
  proof: by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : exists (r : Real) (V : Set E),
      0 < r ∧ V in 𝓝 (0 : E) ∧ forall (c : 𝕜) (y : E), ‖c‖ < r -> y in V -> c • y in U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using!
      h.basis_left (NormedAddGroup.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  obtain ⟨y, hyr, hy₀⟩ : exists y : 𝕜, ‖y‖ < r ∧ y != 0 :=
Filter.nonempty_of_mem
      (nhdsWithin_hasBasis NormedAddGroup.nhds_zero_basis_norm_lt {0}ᶜ).mem_of_mem hr
  have : y • V in 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balancedCore 𝕜 U`
  refine Filter.mem_of_superset this (subset_balancedCore (mem_of_mem_nhds hU) fun a ha => ?_)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine hrVU _ _ ?_ hz
  rw [norm_mul]; rw [← one_mul r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

中文:
定理 balancedCore_mem_nhds_zero
  条件: (hU : U in 𝓝 (0 : E))
  结论: balancedCore 𝕜 U in 𝓝 (0 : E)
  证明: by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : exists (r : Real) (V : Set E),
      0 < r ∧ V in 𝓝 (0 : E) ∧ forall (c : 𝕜) (y : E), ‖c‖ < r -> y in V -> c • y in U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using!
      h.basis_left (NormedAddGroup.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  obtain ⟨y, hyr, hy₀⟩ : exists y : 𝕜, ‖y‖ < r ∧ y != 0 :=
Filter.nonempty_of_mem
      (nhdsWithin_hasBasis NormedAddGroup.nhds_zero_basis_norm_lt {0}ᶜ).mem_of_mem hr
  have : y • V in 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balancedCore 𝕜 U`
  refine Filter.mem_of_superset this (subset_balancedCore (mem_of_mem_nhds hU) fun a ha => ?_)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine hrVU _ _ ?_ hz
  rw [norm_mul]; rw [← one_mul r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos
-/
theorem balancedCore_mem_nhds_zero (hU : U in 𝓝 (0 : E)) : balancedCore 𝕜 U in 𝓝 (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : exists (r : Real) (V : Set E),
      0 < r ∧ V in 𝓝 (0 : E) ∧ forall (c : 𝕜) (y : E), ‖c‖ < r -> y in V -> c • y in U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using!
      h.basis_left (NormedAddGroup.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  obtain ⟨y, hyr, hy₀⟩ : exists y : 𝕜, ‖y‖ < r ∧ y != 0 :=
Filter.nonempty_of_mem
      (nhdsWithin_hasBasis NormedAddGroup.nhds_zero_basis_norm_lt {0}ᶜ).mem_of_mem hr
  have : y • V in 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balancedCore 𝕜 U`
  refine Filter.mem_of_superset this (subset_balancedCore (mem_of_mem_nhds hU) fun a ha => ?_)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine hrVU _ _ ?_ hz
  rw [norm_mul]; rw [← one_mul r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

variable (𝕜 E)

/--
theorem `nhds_basis_balanced` / 定理 `nhds_basis_balanced`

English:
theorem nhds_basis_balanced
  proof: Filter.hasBasis_self.mpr fun s hs =>
    ⟨balancedCore 𝕜 s, balancedCore_mem_nhds_zero hs, balancedCore_balanced s,
      balancedCore_subset s⟩

中文:
定理 nhds_basis_balanced
  证明: Filter.hasBasis_self.mpr fun s hs =>
    ⟨balancedCore 𝕜 s, balancedCore_mem_nhds_zero hs, balancedCore_balanced s,
      balancedCore_subset s⟩

Depends on / 依赖: Filter, Filter.hasBasis_self.mpr, balancedCore, balancedCore_balanced, balancedCore_mem_nhds_zero, balancedCore_subset, hasBasis_self
-/
theorem nhds_basis_balanced :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id :=
  Filter.hasBasis_self.mpr fun s hs =>
    ⟨balancedCore 𝕜 s, balancedCore_mem_nhds_zero hs, balancedCore_balanced s,
      balancedCore_subset s⟩

/--
theorem `nhds_basis_closed_balanced` / 定理 `nhds_basis_closed_balanced`

English:
theorem nhds_basis_closed_balanced
  given: [RegularSpace E]
  proof: by
  refine
    (closed_nhds_basis 0).to_hasBasis (fun s hs => ?_) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine ⟨balancedCore 𝕜 s, ⟨balancedCore_mem_nhds_zero hs.1, ?_⟩, balancedCore_subset s⟩
  exact ⟨hs.2.balancedCore, balancedCore_balanced s⟩

中文:
定理 nhds_basis_closed_balanced
  条件: [正则空间 E]
  证明: by
  refine
    (closed_nhds_basis 0).to_hasBasis (fun s hs => ?_) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine ⟨balancedCore 𝕜 s, ⟨balancedCore_mem_nhds_zero hs.1, ?_⟩, balancedCore_subset s⟩
  exact ⟨hs.2.balancedCore, balancedCore_balanced s⟩

Depends on / 依赖: balancedCore, balancedCore_balanced, balancedCore_mem_nhds_zero, balancedCore_subset, closed_nhds_basis, rfl.subset, subset, to_hasBasis
-/
theorem nhds_basis_closed_balanced [RegularSpace E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s in 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id := by
  refine
    (closed_nhds_basis 0).to_hasBasis (fun s hs => ?_) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine ⟨balancedCore 𝕜 s, ⟨balancedCore_mem_nhds_zero hs.1, ?_⟩, balancedCore_subset s⟩
  exact ⟨hs.2.balancedCore, balancedCore_balanced s⟩

end Topology
