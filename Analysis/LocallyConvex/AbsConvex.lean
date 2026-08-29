/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Absolutely convex sets

A set `s` in a commutative monoid `E` is called absolutely convex or disked if it is convex and
balanced. The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `absConvexHull`: the absolutely convex hull of a set `s` is the smallest absolutely convex set
  containing `s`;
* `closedAbsConvexHull`: the closed absolutely convex hull of a set `s` is the smallest absolutely
  convex set containing `s`;

## Main statements

* `absConvexHull_eq_convexHull_balancedHull`: when the locally convex space is a module, the
  absolutely convex hull of a set `s` equals the convex hull of the balanced hull of `s`;
* `convexHull_union_neg_eq_absConvexHull`: the convex hull of `s ∪ -s` is the absolutely convex hull
  of `s`;
* `closedAbsConvexHull_closure_eq_closedAbsConvexHull` : the closed absolutely convex hull of the
  closure of `s` equals the closed absolutely convex hull of `s`;

## Tags

disks, convex, balanced
-/

@[expose] public section

open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E : Type*}

section AbsolutelyConvex

variable (𝕜) [SeminormedRing 𝕜] [SMul 𝕜 E] [AddCommMonoid E] [PartialOrder 𝕜]

/--
Definition of `AbsConvex` / `AbsConvex` 的定义

English:
definition AbsConvex
  signature: (s : Set E)
  body: Balanced 𝕜 s ∧ Convex 𝕜 s

中文:
定义 AbsConvex
  签名: (s : Set E)
  定义体: Balanced 𝕜 s ∧ Convex 𝕜 s

Depends on / 依赖: Balanced, Convex
-/
def AbsConvex (s : Set E) : Prop := Balanced 𝕜 s ∧ Convex 𝕜 s

variable {𝕜}

/--
theorem `AbsConvex.empty` / 定理 `AbsConvex.empty`

English:
theorem AbsConvex.empty
  statement: AbsConvex 𝕜 (∅ : Set E)
  proof: ⟨balanced_empty, convex_empty⟩

中文:
定理 AbsConvex.empty
  结论: AbsConvex 𝕜 (∅ : Set E)
  证明: ⟨balanced_empty, convex_empty⟩

Depends on / 依赖: balanced_empty, convex_empty
-/
theorem AbsConvex.empty : AbsConvex 𝕜 (∅ : Set E) := ⟨balanced_empty, convex_empty⟩

/--
theorem `AbsConvex.univ` / 定理 `AbsConvex.univ`

English:
theorem AbsConvex.univ
  statement: AbsConvex 𝕜 (univ : Set E)
  proof: ⟨balanced_univ, convex_univ⟩

中文:
定理 AbsConvex.univ
  结论: AbsConvex 𝕜 (univ : Set E)
  证明: ⟨balanced_univ, convex_univ⟩

Depends on / 依赖: balanced_univ, convex_univ
-/
theorem AbsConvex.univ : AbsConvex 𝕜 (univ : Set E) := ⟨balanced_univ, convex_univ⟩

/--
theorem `AbsConvex.inter` / 定理 `AbsConvex.inter`

English:
theorem AbsConvex.inter
  given: {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t)
  proof: ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

中文:
定理 AbsConvex.inter
  条件: {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t)
  证明: ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
-/
theorem AbsConvex.inter {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t) :
    AbsConvex 𝕜 (s inter t) := ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

/--
theorem `AbsConvex.sInter` / 定理 `AbsConvex.sInter`

English:
theorem AbsConvex.sInter
  given: {S : Set (Set E)} (h : forall s in S, AbsConvex 𝕜 s)
  statement: AbsConvex 𝕜 (⋂₀ S)
  proof: ⟨.sInter fun s hs => (h s hs).1, convex_sInter fun s hs => (h s hs).2⟩

中文:
定理 AbsConvex.sInter
  条件: {S : Set (Set E)} (h : 对任意 s in S, AbsConvex 𝕜 s)
  结论: AbsConvex 𝕜 (⋂₀ S)
  证明: ⟨.sInter fun s hs => (h s hs).1, convex_sInter fun s hs => (h s hs).2⟩

Depends on / 依赖: convex_sInter, sInter
-/
theorem AbsConvex.sInter {S : Set (Set E)} (h : forall s in S, AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S) :=
  ⟨.sInter fun s hs => (h s hs).1, convex_sInter fun s hs => (h s hs).2⟩

/--
theorem `AbsConvex.iInter` / 定理 `AbsConvex.iInter`

English:
theorem AbsConvex.iInter
  given: {ι : Sort*} {s : ι -> Set E} (h : forall i, AbsConvex 𝕜 (s i))
  proof: sInter_range s ▸ AbsConvex.sInter forall_mem_range.2 h

中文:
定理 AbsConvex.iInter
  条件: {ι : Sort*} {s : ι -> Set E} (h : 对任意 i, AbsConvex 𝕜 (s i))
  证明: sInter_range s ▸ AbsConvex.sInter forall_mem_range.2 h

Depends on / 依赖: AbsConvex, AbsConvex.sInter, forall_mem_range, sInter, sInter_range
-/
theorem AbsConvex.iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, AbsConvex 𝕜 (s i)) :
    AbsConvex 𝕜 (⋂ i, s i) :=
sInter_range s ▸ AbsConvex.sInter forall_mem_range.2 h

/--
theorem `AbsConvex.iInter₂` / 定理 `AbsConvex.iInter₂`

English:
theorem AbsConvex.iInter₂
  statement: {ι : Sort*} {κ : ι -> Sort*} {f : forall i, κ i -> Set E}
  proof: AbsConvex.iInter fun _ => (AbsConvex.iInter fun _ => h _ _)

中文:
定理 AbsConvex.iInter₂
  结论: {ι : Sort*} {κ : ι -> Sort*} {f : 对任意 i, κ i -> Set E}
  证明: AbsConvex.iInter fun _ => (AbsConvex.iInter fun _ => h _ _)

Depends on / 依赖: AbsConvex, AbsConvex.iInter, iInter
-/
theorem AbsConvex.iInter₂ {ι : Sort*} {κ : ι -> Sort*} {f : forall i, κ i -> Set E}
    (h : forall i j, AbsConvex 𝕜 (f i j)) : AbsConvex 𝕜 (⋂ (i) (j), f i j) :=
  AbsConvex.iInter fun _ => (AbsConvex.iInter fun _ => h _ _)

variable (𝕜)

/-- The absolute convex hull of a set `s` is the minimal absolute convex set that includes `s`. -/
@[simps! isClosed]
/--
Definition of `absConvexHull` / `absConvexHull` 的定义

English:
definition absConvexHull
  signature: : ClosureOperator (Set E)
  body: .ofCompletePred (AbsConvex 𝕜) fun _ => .sInter

中文:
定义 absConvexHull
  签名: : ClosureOperator (Set E)
  定义体: .ofCompletePred (AbsConvex 𝕜) fun _ => .sInter

Depends on / 依赖: AbsConvex, ofCompletePred, sInter
-/
def absConvexHull : ClosureOperator (Set E) :=
  .ofCompletePred (AbsConvex 𝕜) fun _ => .sInter

variable {𝕜} {s : Set E}

/--
theorem `subset_absConvexHull` / 定理 `subset_absConvexHull`

English:
theorem subset_absConvexHull
  statement: s subseteq absConvexHull 𝕜 s
  proof: (absConvexHull 𝕜).le_closure s

中文:
定理 subset_absConvexHull
  结论: s subseteq absConvexHull 𝕜 s
  证明: (absConvexHull 𝕜).le_closure s

Depends on / 依赖: absConvexHull, le_closure
-/
theorem subset_absConvexHull : s subseteq absConvexHull 𝕜 s :=
  (absConvexHull 𝕜).le_closure s

/--
theorem `absConvex_absConvexHull` / 定理 `absConvex_absConvexHull`

English:
theorem absConvex_absConvexHull
  statement: AbsConvex 𝕜 (absConvexHull 𝕜 s)
  proof: (absConvexHull 𝕜).isClosed_closure s

中文:
定理 absConvex_absConvexHull
  结论: AbsConvex 𝕜 (absConvexHull 𝕜 s)
  证明: (absConvexHull 𝕜).isClosed_closure s

Depends on / 依赖: absConvexHull, isClosed_closure
-/
theorem absConvex_absConvexHull : AbsConvex 𝕜 (absConvexHull 𝕜 s) :=
  (absConvexHull 𝕜).isClosed_closure s

/--
theorem `balanced_absConvexHull` / 定理 `balanced_absConvexHull`

English:
theorem balanced_absConvexHull
  statement: Balanced 𝕜 (absConvexHull 𝕜 s)
  proof: absConvex_absConvexHull.1

中文:
定理 balanced_absConvexHull
  结论: Balanced 𝕜 (absConvexHull 𝕜 s)
  证明: absConvex_absConvexHull.1

Depends on / 依赖: absConvex_absConvexHull
-/
theorem balanced_absConvexHull : Balanced 𝕜 (absConvexHull 𝕜 s) :=
  absConvex_absConvexHull.1

/--
theorem `convex_absConvexHull` / 定理 `convex_absConvexHull`

English:
theorem convex_absConvexHull
  statement: Convex 𝕜 (absConvexHull 𝕜 s)
  proof: absConvex_absConvexHull.2

中文:
定理 convex_absConvexHull
  结论: Convex 𝕜 (absConvexHull 𝕜 s)
  证明: absConvex_absConvexHull.2

Depends on / 依赖: absConvex_absConvexHull
-/
theorem convex_absConvexHull : Convex 𝕜 (absConvexHull 𝕜 s) :=
  absConvex_absConvexHull.2

set_option backward.isDefEq.respectTransparency false in
variable (𝕜 s) in
/--
theorem `absConvexHull_eq_iInter` / 定理 `absConvexHull_eq_iInter`

English:
theorem absConvexHull_eq_iInter
  proof: by
  simp [absConvexHull, iInter_subtype, iInter_and]

中文:
定理 absConvexHull_eq_iInter
  证明: by
  simp [absConvexHull, iInter_subtype, iInter_and]

Depends on / 依赖: absConvexHull, iInter_and, iInter_subtype
-/
theorem absConvexHull_eq_iInter :
    absConvexHull 𝕜 s = ⋂ (t : Set E) (_ : s subseteq t) (_ : AbsConvex 𝕜 t), t := by
  simp [absConvexHull, iInter_subtype, iInter_and]

variable {t : Set E} {x : E}

/--
theorem `mem_absConvexHull_iff` / 定理 `mem_absConvexHull_iff`

English:
theorem mem_absConvexHull_iff
  statement: x in absConvexHull 𝕜 s ↔ forall t, s subseteq t -> AbsConvex 𝕜 t -> x in t
  proof: by
  simp_rw [absConvexHull_eq_iInter, mem_iInter]

中文:
定理 mem_absConvexHull_iff
  结论: x in absConvexHull 𝕜 s ↔ 对任意 t, s subseteq t -> AbsConvex 𝕜 t -> x in t
  证明: by
  simp_rw [absConvexHull_eq_iInter, mem_iInter]

Depends on / 依赖: absConvexHull_eq_iInter, mem_iInter, simp_rw
-/
theorem mem_absConvexHull_iff : x in absConvexHull 𝕜 s ↔ forall t, s subseteq t -> AbsConvex 𝕜 t -> x in t := by
  simp_rw [absConvexHull_eq_iInter, mem_iInter]

/--
theorem `absConvexHull_min` / 定理 `absConvexHull_min`

English:
theorem absConvexHull_min
  statement: s subseteq t -> AbsConvex 𝕜 t -> absConvexHull 𝕜 s subseteq t
  proof: (absConvexHull 𝕜).closure_min

中文:
定理 absConvexHull_min
  结论: s subseteq t -> AbsConvex 𝕜 t -> absConvexHull 𝕜 s subseteq t
  证明: (absConvexHull 𝕜).closure_min

Depends on / 依赖: absConvexHull, closure_min
-/
theorem absConvexHull_min : s subseteq t -> AbsConvex 𝕜 t -> absConvexHull 𝕜 s subseteq t :=
  (absConvexHull 𝕜).closure_min

/--
theorem `AbsConvex.absConvexHull_subset_iff` / 定理 `AbsConvex.absConvexHull_subset_iff`

English:
theorem AbsConvex.absConvexHull_subset_iff
  given: (ht : AbsConvex 𝕜 t)
  statement: absConvexHull 𝕜 s subseteq t ↔ s subseteq t
  proof: (show (absConvexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]

中文:
定理 AbsConvex.absConvexHull_subset_iff
  条件: (ht : AbsConvex 𝕜 t)
  结论: absConvexHull 𝕜 s subseteq t ↔ s subseteq t
  证明: (show (absConvexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]

Depends on / 依赖: IsClosed, absConvexHull, closure_le_iff
-/
theorem AbsConvex.absConvexHull_subset_iff (ht : AbsConvex 𝕜 t) : absConvexHull 𝕜 s subseteq t ↔ s subseteq t :=
  (show (absConvexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
/--
theorem `absConvexHull_mono` / 定理 `absConvexHull_mono`

English:
theorem absConvexHull_mono
  given: (hst : s subseteq t)
  statement: absConvexHull 𝕜 s subseteq absConvexHull 𝕜 t
  proof: (absConvexHull 𝕜).monotone hst

中文:
定理 absConvexHull_mono
  条件: (hst : s subseteq t)
  结论: absConvexHull 𝕜 s subseteq absConvexHull 𝕜 t
  证明: (absConvexHull 𝕜).monotone hst

Depends on / 依赖: absConvexHull, monotone
-/
theorem absConvexHull_mono (hst : s subseteq t) : absConvexHull 𝕜 s subseteq absConvexHull 𝕜 t :=
  (absConvexHull 𝕜).monotone hst

/--
lemma `absConvexHull_eq_self` / 引理 `absConvexHull_eq_self`

English:
lemma absConvexHull_eq_self
  statement: absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s
  proof: (absConvexHull 𝕜).isClosed_iff.symm

alias ⟨_, AbsConvex.absConvexHull_eq⟩ := absConvexHull_eq_self

@[simp]

中文:
引理 absConvexHull_eq_self
  结论: absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s
  证明: (absConvexHull 𝕜).isClosed_iff.symm

alias ⟨_, AbsConvex.absConvexHull_eq⟩ := absConvexHull_eq_self

@[simp]

Depends on / 依赖: absConvexHull, isClosed_iff, isClosed_iff.symm
-/
lemma absConvexHull_eq_self : absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s :=
  (absConvexHull 𝕜).isClosed_iff.symm

alias ⟨_, AbsConvex.absConvexHull_eq⟩ := absConvexHull_eq_self

@[simp]
/--
theorem `absConvexHull_univ` / 定理 `absConvexHull_univ`

English:
theorem absConvexHull_univ
  statement: absConvexHull 𝕜 (univ : Set E) = univ
  proof: ClosureOperator.closure_top (absConvexHull 𝕜)

@[simp]

中文:
定理 absConvexHull_univ
  结论: absConvexHull 𝕜 (univ : Set E) = univ
  证明: ClosureOperator.closure_top (absConvexHull 𝕜)

@[simp]

Depends on / 依赖: ClosureOperator, ClosureOperator.closure_top, absConvexHull, closure_top
-/
theorem absConvexHull_univ : absConvexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (absConvexHull 𝕜)

@[simp]
/--
theorem `absConvexHull_empty` / 定理 `absConvexHull_empty`

English:
theorem absConvexHull_empty
  statement: absConvexHull 𝕜 (∅ : Set E) = ∅
  proof: AbsConvex.empty.absConvexHull_eq

@[simp]

中文:
定理 absConvexHull_empty
  结论: absConvexHull 𝕜 (∅ : Set E) = ∅
  证明: AbsConvex.empty.absConvexHull_eq

@[simp]

Depends on / 依赖: AbsConvex, AbsConvex.empty.absConvexHull_eq, absConvexHull_eq
-/
theorem absConvexHull_empty : absConvexHull 𝕜 (∅ : Set E) = ∅ :=
  AbsConvex.empty.absConvexHull_eq

@[simp]
/--
theorem `absConvexHull_eq_empty` / 定理 `absConvexHull_eq_empty`

English:
theorem absConvexHull_eq_empty
  statement: absConvexHull 𝕜 s = ∅ ↔ s = ∅
  proof: by
  constructor
  · intro h
    rw [← Set.subset_empty_iff]; rw [← h]
    exact subset_absConvexHull
  · rintro rfl
    exact absConvexHull_empty

@[simp]

中文:
定理 absConvexHull_eq_empty
  结论: absConvexHull 𝕜 s = ∅ ↔ s = ∅
  证明: by
  constructor
  · intro h
    rw [← Set.subset_empty_iff]; rw [← h]
    exact subset_absConvexHull
  · rintro rfl
    exact absConvexHull_empty

@[simp]

Depends on / 依赖: Set.subset_empty_iff, absConvexHull_empty, subset_absConvexHull, subset_empty_iff
-/
theorem absConvexHull_eq_empty : absConvexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff]; rw [← h]
    exact subset_absConvexHull
  · rintro rfl
    exact absConvexHull_empty

@[simp]
/--
theorem `absConvexHull_nonempty` / 定理 `absConvexHull_nonempty`

English:
theorem absConvexHull_nonempty
  statement: (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [Ne]
  exact not_congr absConvexHull_eq_empty

protected alias ⟨_, Set.Nonempty.absConvexHull⟩ := absConvexHull_nonempty

中文:
定理 absConvexHull_nonempty
  结论: (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty
  证明: by
  rw [nonempty_iff_ne_empty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [Ne]
  exact not_congr absConvexHull_eq_empty

protected alias ⟨_, Set.Nonempty.absConvexHull⟩ := absConvexHull_nonempty

Depends on / 依赖: absConvexHull_eq_empty, nonempty_iff_ne_empty, not_congr
-/
theorem absConvexHull_nonempty : (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [Ne]
  exact not_congr absConvexHull_eq_empty

protected alias ⟨_, Set.Nonempty.absConvexHull⟩ := absConvexHull_nonempty

variable [TopologicalSpace E]

/--
theorem `absConvex_closed_sInter` / 定理 `absConvex_closed_sInter`

English:
theorem absConvex_closed_sInter
  given: {S : Set (Set E)} (h : forall s in S, AbsConvex 𝕜 s ∧ IsClosed s)
  proof: ⟨AbsConvex.sInter (fun s hs => (h s hs).1), isClosed_sInter fun _ hs => (h _ hs).2⟩

中文:
定理 absConvex_closed_sInter
  条件: {S : Set (Set E)} (h : 对任意 s in S, AbsConvex 𝕜 s ∧ IsClosed s)
  证明: ⟨AbsConvex.sInter (fun s hs => (h s hs).1), isClosed_sInter fun _ hs => (h _ hs).2⟩

Depends on / 依赖: AbsConvex, AbsConvex.sInter, isClosed_sInter, sInter
-/
theorem absConvex_closed_sInter {S : Set (Set E)} (h : forall s in S, AbsConvex 𝕜 s ∧ IsClosed s) :
    AbsConvex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S) :=
  ⟨AbsConvex.sInter (fun s hs => (h s hs).1), isClosed_sInter fun _ hs => (h _ hs).2⟩

variable (𝕜) in
/-- The absolutely convex closed hull of a set `s` is the minimal absolutely convex closed set that
includes `s`. -/
@[simps! isClosed]
/--
Definition of `closedAbsConvexHull` / `closedAbsConvexHull` 的定义

English:
definition closedAbsConvexHull
  signature: : ClosureOperator (Set E)
  body: .ofCompletePred (fun s => AbsConvex 𝕜 s ∧ IsClosed s) fun _ => absConvex_closed_sInter

中文:
定义 closedAbsConvexHull
  签名: : ClosureOperator (Set E)
  定义体: .ofCompletePred (fun s => AbsConvex 𝕜 s ∧ IsClosed s) fun _ => absConvex_closed_sInter

Depends on / 依赖: AbsConvex, IsClosed, absConvex_closed_sInter, ofCompletePred
-/
def closedAbsConvexHull : ClosureOperator (Set E) :=
  .ofCompletePred (fun s => AbsConvex 𝕜 s ∧ IsClosed s) fun _ => absConvex_closed_sInter

/--
theorem `absConvex_convexClosedHull` / 定理 `absConvex_convexClosedHull`

English:
theorem absConvex_convexClosedHull
  given: {s : Set E}
  proof: ((closedAbsConvexHull 𝕜).isClosed_closure s).1

中文:
定理 absConvex_convexClosedHull
  条件: {s : Set E}
  证明: ((closedAbsConvexHull 𝕜).isClosed_closure s).1

Depends on / 依赖: closedAbsConvexHull, isClosed_closure
-/
theorem absConvex_convexClosedHull {s : Set E} :
    AbsConvex 𝕜 (closedAbsConvexHull 𝕜 s) := ((closedAbsConvexHull 𝕜).isClosed_closure s).1

/--
theorem `isClosed_closedAbsConvexHull` / 定理 `isClosed_closedAbsConvexHull`

English:
theorem isClosed_closedAbsConvexHull
  given: {s : Set E}
  proof: ((closedAbsConvexHull 𝕜).isClosed_closure s).2

中文:
定理 isClosed_closedAbsConvexHull
  条件: {s : Set E}
  证明: ((closedAbsConvexHull 𝕜).isClosed_closure s).2

Depends on / 依赖: closedAbsConvexHull, isClosed_closure
-/
theorem isClosed_closedAbsConvexHull {s : Set E} :
    IsClosed (closedAbsConvexHull 𝕜 s) := ((closedAbsConvexHull 𝕜).isClosed_closure s).2

/--
theorem `subset_closedAbsConvexHull` / 定理 `subset_closedAbsConvexHull`

English:
theorem subset_closedAbsConvexHull
  given: {s : Set E}
  statement: s subseteq closedAbsConvexHull 𝕜 s
  proof: (closedAbsConvexHull 𝕜).le_closure s

中文:
定理 subset_closedAbsConvexHull
  条件: {s : Set E}
  结论: s subseteq closedAbsConvexHull 𝕜 s
  证明: (closedAbsConvexHull 𝕜).le_closure s

Depends on / 依赖: closedAbsConvexHull, le_closure
-/
theorem subset_closedAbsConvexHull {s : Set E} : s subseteq closedAbsConvexHull 𝕜 s :=
  (closedAbsConvexHull 𝕜).le_closure s

/--
theorem `closure_subset_closedAbsConvexHull` / 定理 `closure_subset_closedAbsConvexHull`

English:
theorem closure_subset_closedAbsConvexHull
  given: {s : Set E}
  statement: closure s subseteq closedAbsConvexHull 𝕜 s
  proof: closure_minimal subset_closedAbsConvexHull isClosed_closedAbsConvexHull

中文:
定理 closure_subset_closedAbsConvexHull
  条件: {s : Set E}
  结论: closure s subseteq closedAbsConvexHull 𝕜 s
  证明: closure_minimal subset_closedAbsConvexHull isClosed_closedAbsConvexHull

Depends on / 依赖: closure_minimal, isClosed_closedAbsConvexHull, subset_closedAbsConvexHull
-/
theorem closure_subset_closedAbsConvexHull {s : Set E} : closure s subseteq closedAbsConvexHull 𝕜 s :=
  closure_minimal subset_closedAbsConvexHull isClosed_closedAbsConvexHull

/--
theorem `closedAbsConvexHull_min` / 定理 `closedAbsConvexHull_min`

English:
theorem closedAbsConvexHull_min
  statement: {s t : Set E} (hst : s subseteq t) (h_conv : AbsConvex 𝕜 t)
  proof: (closedAbsConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

中文:
定理 closedAbsConvexHull_min
  结论: {s t : Set E} (hst : s subseteq t) (h_conv : AbsConvex 𝕜 t)
  证明: (closedAbsConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

Depends on / 依赖: closedAbsConvexHull, closure_min, h_closed, h_conv
-/
theorem closedAbsConvexHull_min {s t : Set E} (hst : s subseteq t) (h_conv : AbsConvex 𝕜 t)
    (h_closed : IsClosed t) : closedAbsConvexHull 𝕜 s subseteq t :=
  (closedAbsConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

/--
theorem `absConvexHull_subset_closedAbsConvexHull` / 定理 `absConvexHull_subset_closedAbsConvexHull`

English:
theorem absConvexHull_subset_closedAbsConvexHull
  given: {s : Set E}
  proof: absConvexHull_min subset_closedAbsConvexHull absConvex_convexClosedHull

@[simp]

中文:
定理 absConvexHull_subset_closedAbsConvexHull
  条件: {s : Set E}
  证明: absConvexHull_min subset_closedAbsConvexHull absConvex_convexClosedHull

@[simp]

Depends on / 依赖: absConvexHull_min, absConvex_convexClosedHull, subset_closedAbsConvexHull
-/
theorem absConvexHull_subset_closedAbsConvexHull {s : Set E} :
    (absConvexHull 𝕜) s subseteq (closedAbsConvexHull 𝕜) s :=
  absConvexHull_min subset_closedAbsConvexHull absConvex_convexClosedHull

@[simp]
/--
theorem `closedAbsConvexHull_closure_eq_closedAbsConvexHull` / 定理 `closedAbsConvexHull_closure_eq_closedAbsConvexHull`

English:
theorem closedAbsConvexHull_closure_eq_closedAbsConvexHull
  given: {s : Set E}
  proof: subset_antisymm (by simpa using ((closedAbsConvexHull 𝕜).monotone
      (closure_subset_closedAbsConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedAbsConvexHull 𝕜).monotone subset_closure)

中文:
定理 closedAbsConvexHull_closure_eq_closedAbsConvexHull
  条件: {s : Set E}
  证明: subset_antisymm (by simpa using ((closedAbsConvexHull 𝕜).monotone
      (closure_subset_closedAbsConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedAbsConvexHull 𝕜).monotone subset_closure)

Depends on / 依赖: closedAbsConvexHull, closure_subset_closedAbsConvexHull, monotone, subset_antisymm, subset_closure
-/
theorem closedAbsConvexHull_closure_eq_closedAbsConvexHull {s : Set E} :
    closedAbsConvexHull 𝕜 (closure s) = closedAbsConvexHull 𝕜 s :=
  subset_antisymm (by simpa using ((closedAbsConvexHull 𝕜).monotone
      (closure_subset_closedAbsConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedAbsConvexHull 𝕜).monotone subset_closure)

end AbsolutelyConvex

section NormedField

variable [NormedField 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/--
theorem `AbsConvex.closure` / 定理 `AbsConvex.closure`

English:
theorem AbsConvex.closure
  given: {s : Set E} (hs : AbsConvex 𝕜 s)
  statement: AbsConvex 𝕜 (closure s)
  proof: ⟨Balanced.closure hs.1, Convex.closure hs.2⟩

中文:
定理 AbsConvex.closure
  条件: {s : Set E} (hs : AbsConvex 𝕜 s)
  结论: AbsConvex 𝕜 (closure s)
  证明: ⟨Balanced.closure hs.1, Convex.closure hs.2⟩

Depends on / 依赖: Balanced, Balanced.closure, Convex, Convex.closure, closure
-/
theorem AbsConvex.closure {s : Set E} (hs : AbsConvex 𝕜 s) : AbsConvex 𝕜 (closure s) :=
  ⟨Balanced.closure hs.1, Convex.closure hs.2⟩

/--
theorem `closedAbsConvexHull_eq_closure_absConvexHull` / 定理 `closedAbsConvexHull_eq_closure_absConvexHull`

English:
theorem closedAbsConvexHull_eq_closure_absConvexHull
  given: {s : Set E}
  proof: subset_antisymm
  (closedAbsConvexHull_min (subset_trans (subset_absConvexHull) subset_closure)
    (AbsConvex.closure absConvex_absConvexHull) isClosed_closure)
  (closure_minimal absConvexHull_subset_closedAbsConvexHull isClosed_closedAbsConvexHull)

中文:
定理 closedAbsConvexHull_eq_closure_absConvexHull
  条件: {s : Set E}
  证明: subset_antisymm
  (closedAbsConvexHull_min (subset_trans (subset_absConvexHull) subset_closure)
    (AbsConvex.closure absConvex_absConvexHull) isClosed_closure)
  (closure_minimal absConvexHull_subset_closedAbsConvexHull isClosed_closedAbsConvexHull)

Depends on / 依赖: subset_antisymm
-/
theorem closedAbsConvexHull_eq_closure_absConvexHull {s : Set E} :
    closedAbsConvexHull 𝕜 s = closure (absConvexHull 𝕜 s) := subset_antisymm
  (closedAbsConvexHull_min (subset_trans (subset_absConvexHull) subset_closure)
    (AbsConvex.closure absConvex_absConvexHull) isClosed_closure)
  (closure_minimal absConvexHull_subset_closedAbsConvexHull isClosed_closedAbsConvexHull)

end NormedField

section

variable (𝕜) [NontriviallyNormedField 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/--
theorem `absConvexHull_add_subset` / 定理 `absConvexHull_add_subset`

English:
theorem absConvexHull_add_subset
  given: {s t : Set E}
  proof: absConvexHull_min (add_subset_add subset_absConvexHull subset_absConvexHull)
    ⟨Balanced.add balanced_absConvexHull balanced_absConvexHull,
      Convex.add convex_absConvexHull convex_absConvexHull⟩

中文:
定理 absConvexHull_add_subset
  条件: {s t : Set E}
  证明: absConvexHull_min (add_subset_add subset_absConvexHull subset_absConvexHull)
    ⟨Balanced.add balanced_absConvexHull balanced_absConvexHull,
      Convex.add convex_absConvexHull convex_absConvexHull⟩

Depends on / 依赖: Balanced, Balanced.add, Convex, Convex.add, absConvexHull_min, add_subset_add, balanced_absConvexHull, convex_absConvexHull, subset_absConvexHull
-/
theorem absConvexHull_add_subset {s t : Set E} :
    absConvexHull 𝕜 (s + t) subseteq absConvexHull 𝕜 s + absConvexHull 𝕜 t :=
  absConvexHull_min (add_subset_add subset_absConvexHull subset_absConvexHull)
    ⟨Balanced.add balanced_absConvexHull balanced_absConvexHull,
      Convex.add convex_absConvexHull convex_absConvexHull⟩

/--
theorem `absConvexHull_eq_convexHull_balancedHull` / 定理 `absConvexHull_eq_convexHull_balancedHull`

English:
theorem absConvexHull_eq_convexHull_balancedHull
  given: {s : Set E}
  proof: le_antisymm
  (absConvexHull_min
    ((subset_convexHull 𝕜 s).trans (convexHull_mono (subset_balancedHull 𝕜)))
      ⟨Balanced.convexHull (balancedHull.balanced s), convex_convexHull ..⟩)
  (convexHull_min (balanced_absConvexHull.balancedHull_subset_of_subset subset_absConvexHull)
      convex_absCo

中文:
定理 absConvexHull_eq_convexHull_balancedHull
  条件: {s : Set E}
  证明: le_antisymm
  (absConvexHull_min
    ((subset_convexHull 𝕜 s).trans (convexHull_mono (subset_balancedHull 𝕜)))
      ⟨Balanced.convexHull (balancedHull.balanced s), convex_convexHull ..⟩)
  (convexHull_min (balanced_absConvexHull.balancedHull_subset_of_subset subset_absConvexHull)
      convex_absCo

Depends on / 依赖: le_antisymm
-/
theorem absConvexHull_eq_convexHull_balancedHull {s : Set E} :
    absConvexHull 𝕜 s = convexHull 𝕜 (balancedHull 𝕜 s) := le_antisymm
  (absConvexHull_min
    ((subset_convexHull 𝕜 s).trans (convexHull_mono (subset_balancedHull 𝕜)))
      ⟨Balanced.convexHull (balancedHull.balanced s), convex_convexHull ..⟩)
  (convexHull_min (balanced_absConvexHull.balancedHull_subset_of_subset subset_absConvexHull)
      convex_absConvexHull)

/--
theorem `balancedHull_convexHull_subset_absConvexHull` / 定理 `balancedHull_convexHull_subset_absConvexHull`

English:
theorem balancedHull_convexHull_subset_absConvexHull
  given: {s : Set E}
  proof: balanced_absConvexHull.balancedHull_subset_of_subset
    (convexHull_min subset_absConvexHull convex_absConvexHull)

@[deprecated balancedHull_convexHull_subset_absConvexHull (since := "2026-05-23")]
alias balancedHull_convexHull_subseteq_absConvexHull := balancedHull_convexHull_subset_absConvexHull

中文:
定理 balancedHull_convexHull_subset_absConvexHull
  条件: {s : Set E}
  证明: balanced_absConvexHull.balancedHull_subset_of_subset
    (convexHull_min subset_absConvexHull convex_absConvexHull)

@[deprecated balancedHull_convexHull_subset_absConvexHull (since := "2026-05-23")]
alias balancedHull_convexHull_subseteq_absConvexHull := balancedHull_convexHull_subset_absConvexHull

Depends on / 依赖: balancedHull_subset_of_subset, balanced_absConvexHull, balanced_absConvexHull.balancedHull_subset_of_subset, convexHull_min, convex_absConvexHull, subset_absConvexHull
-/
theorem balancedHull_convexHull_subset_absConvexHull {s : Set E} :
    balancedHull 𝕜 (convexHull 𝕜 s) subseteq absConvexHull 𝕜 s :=
  balanced_absConvexHull.balancedHull_subset_of_subset
    (convexHull_min subset_absConvexHull convex_absConvexHull)

@[deprecated balancedHull_convexHull_subset_absConvexHull (since := "2026-05-23")]
alias balancedHull_convexHull_subseteq_absConvexHull := balancedHull_convexHull_subset_absConvexHull

variable [ZeroLEOneClass 𝕜] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] [IsTopologicalAddGroup E]

/--
theorem `IsOpen.absConvexHull` / 定理 `IsOpen.absConvexHull`

English:
theorem IsOpen.absConvexHull
  given: {s : Set E} (hs : IsOpen s) (hzero : 0 in s)
  proof: by
  rw [absConvexHull_eq_convexHull_balancedHull]
.convexHull exact hs.balancedHull hzero

中文:
定理 IsOpen.absConvexHull
  条件: {s : Set E} (hs : IsOpen s) (hzero : 0 in s)
  证明: by
  rw [absConvexHull_eq_convexHull_balancedHull]
.convexHull exact hs.balancedHull hzero

Depends on / 依赖: absConvexHull_eq_convexHull_balancedHull, balancedHull, convexHull, hs.balancedHull
-/
theorem IsOpen.absConvexHull {s : Set E} (hs : IsOpen s) (hzero : 0 in s) :
    IsOpen (absConvexHull 𝕜 s) := by
  rw [absConvexHull_eq_convexHull_balancedHull]
.convexHull exact hs.balancedHull hzero

end

section NontriviallyNormedField

variable (𝕜 E)
variable [NontriviallyNormedField 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [LocallyConvexSpace 𝕜 E] [ContinuousSMul 𝕜 E]

/--
theorem `nhds_hasBasis_absConvex` / 定理 `nhds_hasBasis_absConvex`

English:
theorem nhds_hasBasis_absConvex
  proof: by
  refine
    (LocallyConvexSpace.convex_basis_zero 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine ⟨convexHull 𝕜 (balancedCore 𝕜 s), ?_, convexHull_min (balancedCore_subset s) hs.2⟩
  refine ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (su

中文:
定理 nhds_hasBasis_absConvex
  证明: by
  refine
    (LocallyConvexSpace.convex_basis_zero 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine ⟨convexHull 𝕜 (balancedCore 𝕜 s), ?_, convexHull_min (balancedCore_subset s) hs.2⟩
  refine ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (su

Depends on / 依赖: Filter, Filter.mem_of_superset, LocallyConvexSpace, LocallyConvexSpace.convex_basis_zero, balancedCore, balancedCore_balanced, balancedCore_mem_nhds_zero, balancedCore_subset, convexHull, convexHull_min, convex_basis_zero, convex_convexHull, mem_of_superset, rfl.subset, subset, subset_convexHull, to_hasBasis
-/
theorem nhds_hasBasis_absConvex :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s in 𝓝 (0 : E) ∧ AbsConvex 𝕜 s) id := by
  refine
    (LocallyConvexSpace.convex_basis_zero 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine ⟨convexHull 𝕜 (balancedCore 𝕜 s), ?_, convexHull_min (balancedCore_subset s) hs.2⟩
  refine ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (subset_convexHull 𝕜 _), ?_⟩
  refine ⟨(balancedCore_balanced s).convexHull, ?_⟩
  exact convex_convexHull 𝕜 (balancedCore 𝕜 s)

variable [IsTopologicalAddGroup E] [ZeroLEOneClass 𝕜]

/--
theorem `nhds_hasBasis_absConvex_open` / 定理 `nhds_hasBasis_absConvex_open`

English:
theorem nhds_hasBasis_absConvex_open
  proof: by
  refine (nhds_hasBasis_absConvex 𝕜 E).to_hasBasis ?_ ?_
  · intro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine ⟨interior s, ?_, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_con

中文:
定理 nhds_hasBasis_absConvex_open
  证明: by
  refine (nhds_hasBasis_absConvex 𝕜 E).to_hasBasis ?_ ?_
  · intro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine ⟨interior s, ?_, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_con

Depends on / 依赖: hs_balanced, hs_balanced.interior, hs_convex, hs_convex.interior, hs_nhds, hs_open, hs_open.mem_nhds, hs_zero, interior, interior_subset, isOpen_interior, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mpr, mem_nhds, nhds_hasBasis_absConvex, rfl.subset, subset, to_hasBasis
-/
theorem nhds_hasBasis_absConvex_open :
    (𝓝 (0 : E)).HasBasis (fun s => (0 : E) in s ∧ IsOpen s ∧ AbsConvex 𝕜 s) id := by
  refine (nhds_hasBasis_absConvex 𝕜 E).to_hasBasis ?_ ?_
  · intro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine ⟨interior s, ?_, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩
  intro s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩

/--
theorem `nhds_hasBasis_absConvex_closed` / 定理 `nhds_hasBasis_absConvex_closed`

English:
theorem nhds_hasBasis_absConvex_closed
  proof: by
  refine (nhds_basis_opens 0).to_hasBasis ?_
    fun s ⟨hs_nhds, _, _⟩ => ⟨interior s,
      by simp [interior_subset, mem_interior_iff_mem_nhds.mpr hs_nhds]⟩
  intro s ⟨hs_zero, hs_open⟩
  obtain ⟨W, hW_open, hW_zero, hW_add⟩ :=
    exists_open_nhds_zero_add_subset (hs_open.mem_nhds hs_zero)
  o

中文:
定理 nhds_hasBasis_absConvex_closed
  证明: by
  refine (nhds_basis_opens 0).to_hasBasis ?_
    fun s ⟨hs_nhds, _, _⟩ => ⟨interior s,
      by simp [interior_subset, mem_interior_iff_mem_nhds.mpr hs_nhds]⟩
  intro s ⟨hs_zero, hs_open⟩
  obtain ⟨W, hW_open, hW_zero, hW_add⟩ :=
    exists_open_nhds_zero_add_subset (hs_open.mem_nhds hs_zero)
  o

Depends on / 依赖: Filter, Filter.mem_of_superset, closure, exists_open_nhds_zero_add_subset, hV_abs, hV_open, hV_open.mem_nhds, hV_zero, hW_add, hW_open, hW_open.mem_nhds, hW_zero, hs_nhds, hs_open, hs_open.mem_nhds, hs_zero, interior, interior_subset, isClosed_closure, mem_iff
-/
theorem nhds_hasBasis_absConvex_closed :
    (𝓝 (0 : E)).HasBasis (fun s => s in 𝓝 (0 : E) ∧ IsClosed s ∧ AbsConvex 𝕜 s) id := by
  refine (nhds_basis_opens 0).to_hasBasis ?_
    fun s ⟨hs_nhds, _, _⟩ => ⟨interior s,
      by simp [interior_subset, mem_interior_iff_mem_nhds.mpr hs_nhds]⟩
  intro s ⟨hs_zero, hs_open⟩
  obtain ⟨W, hW_open, hW_zero, hW_add⟩ :=
    exists_open_nhds_zero_add_subset (hs_open.mem_nhds hs_zero)
  obtain ⟨V, ⟨hV_zero, hV_open, hV_abs⟩, hVW⟩ :=
    (nhds_hasBasis_absConvex_open 𝕜 E).mem_iff.mp (hW_open.mem_nhds hW_zero)
  exact ⟨closure V,
    ⟨Filter.mem_of_superset (hV_open.mem_nhds hV_zero) subset_closure, isClosed_closure,
     hV_abs.closure⟩,
    (closure_subset_add_self_of_mem_nhds_zero (hV_open.mem_nhds hV_zero)).trans
      ((add_subset_add hVW hVW).trans hW_add)⟩

/--
theorem `exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset` / 定理 `exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset`

English:
theorem exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset
  given: [FirstCountableTopology E]
  proof: by
  obtain ⟨u, hu_basis, -⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero E
  have hu_zero (n : Nat) : 0 in interior (u n) :=
    mem_interior_iff_mem_nhds.mpr (hu_basis.mem_of_mem trivial)
  let v (n : Nat) := absConvexHull 𝕜 (interior (u n))
  have hv_open (n : Nat) : IsOpen (v n) := i

中文:
定理 exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset
  条件: [FirstCountableTopology E]
  证明: by
  obtain ⟨u, hu_basis, -⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero E
  have hu_zero (n : Nat) : 0 in interior (u n) :=
    mem_interior_iff_mem_nhds.mpr (hu_basis.mem_of_mem trivial)
  let v (n : Nat) := absConvexHull 𝕜 (interior (u n))
  have hv_open (n : Nat) : IsOpen (v n) := i

Depends on / 依赖: HasAntitoneBasis, IsOpen, IsTopologicalAddGroup, IsTopologicalAddGroup.exists_antitone_basis_nhds_zero, absConvexHull, exists_antitone_basis_nhds_zero, hu_basis, hu_basis.mem_of_mem, hu_basis.to_hasBasi, hu_zero, hv_basis, hv_nhds, hv_open, interior, isOpen_interior, isOpen_interior.absConvexHull, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mpr, mem_nhds, mem_of_mem
-/
theorem exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset [FirstCountableTopology E] :
    exists x : Nat -> Set E, (𝓝 (0 : E)).HasAntitoneBasis x ∧
      forall n, IsOpen (x n) ∧ AbsConvex 𝕜 (x n) ∧ x (n + 1) + x (n + 1) subseteq x n ∧
        closure (x (n + 1)) subseteq x n := by
  obtain ⟨u, hu_basis, -⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero E
  have hu_zero (n : Nat) : 0 in interior (u n) :=
    mem_interior_iff_mem_nhds.mpr (hu_basis.mem_of_mem trivial)
  let v (n : Nat) := absConvexHull 𝕜 (interior (u n))
  have hv_open (n : Nat) : IsOpen (v n) := isOpen_interior.absConvexHull 𝕜 (hu_zero n)
  have hv_nhds (n : Nat) : v n in 𝓝 0 := (hv_open n).mem_nhds (subset_absConvexHull (hu_zero n))
  have hv_basis : (𝓝 0).HasAntitoneBasis v := by
    refine ⟨hu_basis.to_hasBasis ?_ ?_,
      fun _ _ hij => absConvexHull_mono (interior_mono (hu_basis.antitone hij))⟩
    · intro n _
      obtain ⟨W, ⟨hW_nhds, hW_abs⟩, hWn⟩ :=
        (nhds_hasBasis_absConvex 𝕜 E).mem_iff.mp (hu_basis.mem_of_mem trivial)
      obtain ⟨m, hm⟩ := hu_basis.mem_iff.mp hW_nhds
      exact ⟨m, trivial, (absConvexHull_min (interior_subset.trans hm) hW_abs).trans hWn⟩
    · intro n _
      obtain ⟨m, hm⟩ := hu_basis.mem_iff.mp (isOpen_interior.mem_nhds (hu_zero n))
      exact ⟨m, trivial, hm.trans subset_absConvexHull⟩
  obtain ⟨φ, -, hφ_add, hφ_basis⟩ := hv_basis.subbasis_with_rel
    (r := fun i j => v j + v j subseteq v i) fun m => by
      obtain ⟨W, hW_open, hW_zero, hW_add⟩ := exists_open_nhds_zero_add_subset (hv_nhds m)
      obtain ⟨N, hN⟩ := hv_basis.mem_iff.mp (hW_open.mem_nhds hW_zero)
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      exact (add_subset_add ((hv_basis.antitone hM).trans hN)
        ((hv_basis.antitone hM).trans hN)).trans hW_add
  exact ⟨v ∘ φ, hφ_basis, fun n => ⟨hv_open (φ n), absConvex_absConvexHull, hφ_add (by simp),
    (closure_subset_add_self_of_mem_nhds_zero (hv_nhds (φ (n + 1)))).trans
        (hφ_add n.lt_succ_self)⟩⟩

end NontriviallyNormedField

section

variable [AddCommGroup E] [Module Real E]

/--
lemma `balancedHull_subset_convexHull_union_neg` / 引理 `balancedHull_subset_convexHull_union_neg`

English:
lemma balancedHull_subset_convexHull_union_neg
  given: {s : Set E}
  proof: by
  intro a ha
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 ha
  apply segment_subset_convexHull (mem_union_left (-s) hy) (mem_union_right _ (neg_mem_neg.mpr hy))
  have : 0 <= 1 + r := neg_le_iff_add_nonneg'.mp (neg_le_of_abs_le hr)
  have : 0 <= 1 - r := sub_nonneg.2 (le_of_abs_le hr)
 

中文:
引理 balancedHull_subset_convexHull_union_neg
  条件: {s : Set E}
  证明: by
  intro a ha
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 ha
  apply segment_subset_convexHull (mem_union_left (-s) hy) (mem_union_right _ (neg_mem_neg.mpr hy))
  have : 0 <= 1 + r := neg_le_iff_add_nonneg'.mp (neg_le_of_abs_le hr)
  have : 0 <= 1 - r := sub_nonneg.2 (le_of_abs_le hr)
 

Depends on / 依赖: le_of_abs_le, mem_balancedHull_iff, mem_union_left, mem_union_right, neg_le_iff_add_nonneg, neg_le_of_abs_le, neg_mem_neg, neg_mem_neg.mpr, ring_nf, segment_subset_convexHull, smul_neg, sub_eq_add_neg, sub_nonneg, sub_smul
-/
lemma balancedHull_subset_convexHull_union_neg {s : Set E} :
    balancedHull Real s subseteq convexHull Real (s union -s) := by
  intro a ha
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 ha
  apply segment_subset_convexHull (mem_union_left (-s) hy) (mem_union_right _ (neg_mem_neg.mpr hy))
  have : 0 <= 1 + r := neg_le_iff_add_nonneg'.mp (neg_le_of_abs_le hr)
  have : 0 <= 1 - r := sub_nonneg.2 (le_of_abs_le hr)
  refine ⟨(1 + r)/2, (1 - r)/2, by positivity, by positivity, by ring, ?_⟩
  rw [smul_neg]; rw [← sub_eq_add_neg]; rw [← sub_smul]
  ring_nf

@[simp]
/--
theorem `convexHull_union_neg_eq_absConvexHull` / 定理 `convexHull_union_neg_eq_absConvexHull`

English:
theorem convexHull_union_neg_eq_absConvexHull
  given: {s : Set E}
  proof: by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact le_antisymm (convexHull_mono (union_subset (subset_balancedHull Real)
    (fun _ _ => by rw [mem_balancedHull_iff]; use -1; simp_all)))
    (by
      rw [← Convex.convexHull_eq (convex_convexHull Real (s union -s))]
      exact convexHull_mo

中文:
定理 convexHull_union_neg_eq_absConvexHull
  条件: {s : Set E}
  证明: by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact le_antisymm (convexHull_mono (union_subset (subset_balancedHull Real)
    (fun _ _ => by rw [mem_balancedHull_iff]; use -1; simp_all)))
    (by
      rw [← Convex.convexHull_eq (convex_convexHull Real (s union -s))]
      exact convexHull_mo

Depends on / 依赖: Convex, Convex.convexHull_eq, absConvexHull_eq_convexHull_balancedHull, balancedHull_subset_convexHull_union_neg, convexHull_eq, convexHull_mono, convex_convexHull, le_antisymm, mem_balancedHull_iff, subset_balancedHull, union_subset
-/
theorem convexHull_union_neg_eq_absConvexHull {s : Set E} :
    convexHull Real (s union -s) = absConvexHull Real s := by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact le_antisymm (convexHull_mono (union_subset (subset_balancedHull Real)
    (fun _ _ => by rw [mem_balancedHull_iff]; use -1; simp_all)))
    (by
      rw [← Convex.convexHull_eq (convex_convexHull Real (s union -s))]
      exact convexHull_mono balancedHull_subset_convexHull_union_neg)

variable (𝕜) {s : Set E}
variable [NontriviallyNormedField 𝕜] [PartialOrder 𝕜] [Module 𝕜 E] [SMulCommClass Real 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [lcs : LocallyConvexSpace Real E] [ContinuousSMul Real E]

@[simp]
/--
lemma `totallyBounded_absConvexHull` / 引理 `totallyBounded_absConvexHull`

English:
lemma totallyBounded_absConvexHull
  statement: TotallyBounded (absConvexHull Real s) ↔ TotallyBounded s
  proof: by
  simp [← convexHull_union_neg_eq_absConvexHull]

protected alias ⟨_, TotallyBounded.absConvexHull⟩ := totallyBounded_absConvexHull

中文:
引理 totallyBounded_absConvexHull
  结论: TotallyBounded (absConvexHull 实数 s) ↔ TotallyBounded s
  证明: by
  simp [← convexHull_union_neg_eq_absConvexHull]

protected alias ⟨_, TotallyBounded.absConvexHull⟩ := totallyBounded_absConvexHull

Depends on / 依赖: convexHull_union_neg_eq_absConvexHull
-/
lemma totallyBounded_absConvexHull : TotallyBounded (absConvexHull Real s) ↔ TotallyBounded s := by
  simp [← convexHull_union_neg_eq_absConvexHull]

protected alias ⟨_, TotallyBounded.absConvexHull⟩ := totallyBounded_absConvexHull

end

/--
lemma `zero_mem_absConvexHull` / 引理 `zero_mem_absConvexHull`

English:
lemma zero_mem_absConvexHull
  statement: {s : Set E} [SeminormedRing 𝕜] [PartialOrder 𝕜] [AddCommGroup E]
  proof: balanced_absConvexHull.zero_mem (Nonempty.mono subset_absConvexHull Set.Nonempty.of_subtype)

中文:
引理 zero_mem_absConvexHull
  结论: {s : Set E} [SeminormedRing 𝕜] [PartialOrder 𝕜] [AddCommGroup E]
  证明: balanced_absConvexHull.zero_mem (Nonempty.mono subset_absConvexHull Set.Nonempty.of_subtype)

Depends on / 依赖: Nonempty, Nonempty.mono, Set.Nonempty.of_subtype, balanced_absConvexHull, balanced_absConvexHull.zero_mem, of_subtype, subset_absConvexHull, zero_mem
-/
lemma zero_mem_absConvexHull {s : Set E} [SeminormedRing 𝕜] [PartialOrder 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Nonempty s] : 0 in absConvexHull 𝕜 s :=
  balanced_absConvexHull.zero_mem (Nonempty.mono subset_absConvexHull Set.Nonempty.of_subtype)

/--
theorem `isCompact_closedAbsConvexHull_of_totallyBounded` / 定理 `isCompact_closedAbsConvexHull_of_totallyBounded`

English:
theorem isCompact_closedAbsConvexHull_of_totallyBounded
  statement: {E : Type*} [AddCommGroup E] [Module Real E]
  proof: by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := Real) ht.absConvexHull

中文:
定理 isCompact_closedAbsConvexHull_of_totallyBounded
  结论: {E : 类型} [AddCommGroup E] [Module 实数 E]
  证明: by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := Real) ht.absConvexHull

Depends on / 依赖: absConvexHull, closedAbsConvexHull_eq_closure_absConvexHull, ht.absConvexHull, isCompact_closure_of_totallyBounded_quasiComplete
-/
theorem isCompact_closedAbsConvexHull_of_totallyBounded {E : Type*} [AddCommGroup E] [Module Real E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul Real E] [LocallyConvexSpace Real E]
    [QuasiCompleteSpace Real E] {s : Set E} (ht : TotallyBounded s) :
    IsCompact (closedAbsConvexHull Real s) := by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := Real) ht.absConvexHull
