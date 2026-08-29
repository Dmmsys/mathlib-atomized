/-
Copyright (c) 2021 Yury Kudryashov, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Separated
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Metric separation

This file defines a few notions of separations of sets in a metric space.


The first notion (`Metric.IsSeparated`) is quantitative and describes a single set: a set `s` is
`ε`-separated if the distance between any two distinct elements is strictly greater than `ε`

The second notion (`Metric.AreSeparated`) is qualitative and about two sets: Two sets `s` and `t`
are separated if the distance between `x ∈ s` and `y ∈ t` is bounded from below by a positive
constant.
-/

@[expose] public section

open EMetric Set
open scoped NNReal ENNReal

noncomputable section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
variable {s t : Set X} {ε δ : Real>=0∞} {x : X} {y : Y}

/-!
### Metric-separated sets

In this section we define the predicate `Metric.IsSeparated` for `ε`-separated sets.
-/

/--
Definition of `IsSeparated` / `IsSeparated` 的定义

English:
definition IsSeparated
  signature: (ε : Real>=0∞) (s : Set X)
  body: s.Pairwise (ε < edist · ·)

中文:
定义 是分离
  签名: (ε : 实数>=0∞) (s : 集合 X)
  定义体: s.Pairwise (ε < edist · ·)

Depends on / 依赖: Pairwise, s.Pairwise
-/
def IsSeparated (ε : Real>=0∞) (s : Set X) : Prop := s.Pairwise (ε < edist · ·)

/--
lemma `isSeparated_iff_setRelIsSeparated` / 引理 `isSeparated_iff_setRelIsSeparated`

English:
lemma isSeparated_iff_setRelIsSeparated
  proof: by
  simp [IsSeparated, SetRel.IsSeparated]

@[grind .]

中文:
引理 isSeparated_iff_setRelIsSeparated
  证明: by
  simp [IsSeparated, SetRel.IsSeparated]

@[grind .]

Depends on / 依赖: IsSeparated, SetRel, SetRel.IsSeparated
-/
lemma isSeparated_iff_setRelIsSeparated :
    IsSeparated ε s ↔ SetRel.IsSeparated {(x, y) | edist x y <= ε} s := by
  simp [IsSeparated, SetRel.IsSeparated]

@[grind .]
/--
lemma `IsSeparated.empty` / 引理 `IsSeparated.empty`

English:
lemma IsSeparated.empty
  statement: IsSeparated ε (∅ : Set X)
  proof: pairwise_empty _

中文:
引理 是分离.empty
  结论: 是分离 ε (∅ : 集合 X)
  证明: pairwise_empty _
-/
protected lemma IsSeparated.empty : IsSeparated ε (∅ : Set X) := pairwise_empty _
/--
lemma `IsSeparated.singleton` / 引理 `IsSeparated.singleton`

English:
lemma IsSeparated.singleton
  statement: IsSeparated ε {x}
  proof: pairwise_singleton ..

中文:
引理 是分离.singleton
  结论: 是分离 ε {x}
  证明: pairwise_singleton ..
-/
protected lemma IsSeparated.singleton : IsSeparated ε {x} := pairwise_singleton ..

/--
lemma `IsSeparated.of_subsingleton` / 引理 `IsSeparated.of_subsingleton`

English:
lemma IsSeparated.of_subsingleton
  given: (hs : s.Subsingleton)
  statement: IsSeparated ε s
  proof: hs.pairwise _

alias _root_.Set.Subsingleton.isSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.anti (hεδ : ε <= δ) (hs : IsSeparated δ s) : IsSeparated ε s :=
  hs.mono' fun _ _ => hεδ.trans_lt

中文:
引理 是分离.of_subsingleton
  条件: (hs : s.子单例)
  结论: 是分离 ε s
  证明: hs.pairwise _

alias _root_.Set.Subsingleton.isSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.anti (hεδ : ε <= δ) (hs : IsSeparated δ s) : IsSeparated ε s :=
  hs.mono' fun _ _ => hεδ.trans_lt
-/
@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated ε s := hs.pairwise _

alias _root_.Set.Subsingleton.isSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.anti (hεδ : ε <= δ) (hs : IsSeparated δ s) : IsSeparated ε s :=
  hs.mono' fun _ _ => hεδ.trans_lt

/--
lemma `IsSeparated.subset` / 引理 `IsSeparated.subset`

English:
lemma IsSeparated.subset
  given: (hst : s subseteq t) (hs : IsSeparated ε t)
  statement: IsSeparated ε s
  proof: hs.mono hst

中文:
引理 是分离.subset
  条件: (hst : s subseteq t) (hs : 是分离 ε t)
  结论: 是分离 ε s
  证明: hs.mono hst

Depends on / 依赖: hs.mono
-/
lemma IsSeparated.subset (hst : s subseteq t) (hs : IsSeparated ε t) : IsSeparated ε s := hs.mono hst

/--
lemma `isSeparated_insert` / 引理 `isSeparated_insert`

English:
lemma isSeparated_insert
  proof: have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm

中文:
引理 isSeparated_insert
  证明: have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm

Depends on / 依赖: Std.Symm, edist_comm, pairwise_insert_of_symm, symm_def
-/
lemma isSeparated_insert :
    IsSeparated ε (insert x s) ↔ IsSeparated ε s ∧ forall y in s, x != y -> ε < edist x y :=
  have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm

/--
lemma `isSeparated_insert_of_notMem` / 引理 `isSeparated_insert_of_notMem`

English:
lemma isSeparated_insert_of_notMem
  given: (hx : x ∉ s)
  proof: have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm_of_notMem hx

中文:
引理 isSeparated_insert_of_notMem
  条件: (hx : x ∉ s)
  证明: have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm_of_notMem hx

Depends on / 依赖: Std.Symm, edist_comm, pairwise_insert_of_symm_of_notMem, symm_def
-/
lemma isSeparated_insert_of_notMem (hx : x ∉ s) :
    IsSeparated ε (insert x s) ↔ IsSeparated ε s ∧ forall y in s, ε < edist x y :=
  have : Std.Symm (α := X) (ε < edist · ·) := by simp [symm_def, edist_comm]
  pairwise_insert_of_symm_of_notMem hx

/--
lemma `IsSeparated.insert` / 引理 `IsSeparated.insert`

English:
lemma IsSeparated.insert
  given: (hs : IsSeparated ε s) (h : forall y in s, x != y -> ε < edist x y)
  proof: isSeparated_insert.2 ⟨hs, h⟩

@[simp]

中文:
引理 是分离.insert
  条件: (hs : 是分离 ε s) (h : 对任意 y in s, x != y -> ε < edist x y)
  证明: isSeparated_insert.2 ⟨hs, h⟩

@[simp]
-/
protected lemma IsSeparated.insert (hs : IsSeparated ε s) (h : forall y in s, x != y -> ε < edist x y) :
    IsSeparated ε (insert x s) := isSeparated_insert.2 ⟨hs, h⟩

@[simp]
/--
lemma `isSeparated_zero` / 引理 `isSeparated_zero`

English:
lemma isSeparated_zero
  given: {X : Type*} [EMetricSpace X] (s : Set X)
  statement: IsSeparated 0 s
  proof: by
  simp [IsSeparated, Set.Pairwise]

中文:
引理 isSeparated_zero
  条件: {X : 类型} [广义度量空间 X] (s : 集合 X)
  结论: 是分离 0 s
  证明: by
  simp [IsSeparated, Set.Pairwise]

Depends on / 依赖: IsSeparated, Pairwise, Set.Pairwise
-/
lemma isSeparated_zero {X : Type*} [EMetricSpace X] (s : Set X) : IsSeparated 0 s := by
  simp [IsSeparated, Set.Pairwise]

/--
lemma `IsSeparated.image_antilipschitz` / 引理 `IsSeparated.image_antilipschitz`

English:
lemma IsSeparated.image_antilipschitz
  statement: {ε K₁ : Real>=0} {f : X -> Y}
  proof: by
  rintro x' ⟨x, hx, rfl⟩ y' ⟨y, hy, rfl⟩ hne
  have hmul : (↑ε : Real>=0∞) < edist (f x) (f y) * ↑K₁ :=
    lt_of_lt_of_le (hs hx hy (by grind)) (by rw [mul_comm]; exact hf x y)
  exact ENNReal.coe_div hK₁.ne' ▸ ENNReal.div_lt_of_lt_mul hmul

中文:
引理 是分离.image_antilipschitz
  结论: {ε K₁ : 实数>=0} {f : X -> Y}
  证明: by
  rintro x' ⟨x, hx, rfl⟩ y' ⟨y, hy, rfl⟩ hne
  have hmul : (↑ε : Real>=0∞) < edist (f x) (f y) * ↑K₁ :=
    lt_of_lt_of_le (hs hx hy (by grind)) (by rw [mul_comm]; exact hf x y)
  exact ENNReal.coe_div hK₁.ne' ▸ ENNReal.div_lt_of_lt_mul hmul

Depends on / 依赖: ENNReal, ENNReal.coe_div, ENNReal.div_lt_of_lt_mul, coe_div, div_lt_of_lt_mul, lt_of_lt_of_le, mul_comm
-/
lemma IsSeparated.image_antilipschitz {ε K₁ : Real>=0} {f : X -> Y}
    (hs : IsSeparated ε s) (hf : AntilipschitzWith K₁ f) (hK₁ : 0 < K₁) :
    IsSeparated ↑(ε / K₁) (f '' s) := by
  rintro x' ⟨x, hx, rfl⟩ y' ⟨y, hy, rfl⟩ hne
  have hmul : (↑ε : Real>=0∞) < edist (f x) (f y) * ↑K₁ :=
    lt_of_lt_of_le (hs hx hy (by grind)) (by rw [mul_comm]; exact hf x y)
  exact ENNReal.coe_div hK₁.ne' ▸ ENNReal.div_lt_of_lt_mul hmul

/-!
### Metric separated pairs of sets

In this section we define the predicate `Metric.AreSeparated`. We say that two sets in an
(extended) metric space are *metric separated* if the (extended) distance between `x ∈ s` and
`y ∈ t` is bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/

/--
Definition of `AreSeparated` / `AreSeparated` 的定义

English:
definition AreSeparated
  signature: (s t : Set X)
  body: exists r, r != 0 ∧ forall x in s, forall y in t, r <= edist x y

中文:
定义 AreSeparated
  签名: (s t : 集合 X)
  定义体: exists r, r != 0 ∧ forall x in s, forall y in t, r <= edist x y
-/
def AreSeparated (s t : Set X) := exists r, r != 0 ∧ forall x in s, forall y in t, r <= edist x y

namespace AreSeparated

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : AreSeparated s t)
  statement: AreSeparated t s
  proof: let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩

中文:
定理 symm
  条件: (h : AreSeparated s t)
  结论: AreSeparated t s
  证明: let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩

Depends on / 依赖: edist_comm
-/
theorem symm (h : AreSeparated s t) : AreSeparated t s :=
  let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  statement: AreSeparated s t ↔ AreSeparated t s
  proof: ⟨symm, symm⟩

@[simp]

中文:
定理 comm
  结论: AreSeparated s t ↔ AreSeparated t s
  证明: ⟨symm, symm⟩

@[simp]
-/
theorem comm : AreSeparated s t ↔ AreSeparated t s := ⟨symm, symm⟩

@[simp]
/--
theorem `empty_left` / 定理 `empty_left`

English:
theorem empty_left
  given: (s : Set X)
  statement: AreSeparated ∅ s
  proof: ⟨1, one_ne_zero, fun _x => False.elim⟩

@[simp]

中文:
定理 empty_left
  条件: (s : 集合 X)
  结论: AreSeparated ∅ s
  证明: ⟨1, one_ne_zero, fun _x => False.elim⟩

@[simp]

Depends on / 依赖: False.elim, one_ne_zero
-/
theorem empty_left (s : Set X) : AreSeparated ∅ s :=
  ⟨1, one_ne_zero, fun _x => False.elim⟩

@[simp]
/--
theorem `empty_right` / 定理 `empty_right`

English:
theorem empty_right
  given: (s : Set X)
  statement: AreSeparated s ∅
  proof: (empty_left s).symm

中文:
定理 empty_right
  条件: (s : 集合 X)
  结论: AreSeparated s ∅
  证明: (empty_left s).symm

Depends on / 依赖: empty_left
-/
theorem empty_right (s : Set X) : AreSeparated s ∅ :=
  (empty_left s).symm

/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  given: (h : AreSeparated s t)
  statement: Disjoint s t
  proof: let ⟨r, r0, hr⟩ := h
Set.disjoint_left.mpr fun x hx1 hx2 => r0 by simpa using hr x hx1 x hx2

中文:
定理 disjoint
  条件: (h : AreSeparated s t)
  结论: Disjoint s t
  证明: let ⟨r, r0, hr⟩ := h
Set.disjoint_left.mpr fun x hx1 hx2 => r0 by simpa using hr x hx1 x hx2
-/
protected theorem disjoint (h : AreSeparated s t) : Disjoint s t :=
  let ⟨r, r0, hr⟩ := h
Set.disjoint_left.mpr fun x hx1 hx2 => r0 by simpa using hr x hx1 x hx2

/--
theorem `subset_compl_right` / 定理 `subset_compl_right`

English:
theorem subset_compl_right
  given: (h : AreSeparated s t)
  statement: s subseteq tᶜ
  proof: fun _ hs ht =>
  h.disjoint.le_bot ⟨hs, ht⟩

@[gcongr, mono]

中文:
定理 subset_compl_right
  条件: (h : AreSeparated s t)
  结论: s subseteq tᶜ
  证明: fun _ hs ht =>
  h.disjoint.le_bot ⟨hs, ht⟩

@[gcongr, mono]
-/
theorem subset_compl_right (h : AreSeparated s t) : s subseteq tᶜ := fun _ hs ht =>
  h.disjoint.le_bot ⟨hs, ht⟩

@[gcongr, mono]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {s' t'} (hs : s subseteq s') (ht : t subseteq t')
  proof: fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩

中文:
定理 mono
  条件: {s' t'} (hs : s subseteq s') (ht : t subseteq t')
  证明: fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩
-/
theorem mono {s' t'} (hs : s subseteq s') (ht : t subseteq t') :
    AreSeparated s' t' -> AreSeparated s t := fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩

/--
theorem `mono_left` / 定理 `mono_left`

English:
theorem mono_left
  given: {s'} (h' : AreSeparated s' t) (hs : s subseteq s')
  statement: AreSeparated s t
  proof: h'.mono hs Subset.rfl

中文:
定理 mono_left
  条件: {s'} (h' : AreSeparated s' t) (hs : s subseteq s')
  结论: AreSeparated s t
  证明: h'.mono hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl
-/
theorem mono_left {s'} (h' : AreSeparated s' t) (hs : s subseteq s') : AreSeparated s t :=
  h'.mono hs Subset.rfl

/--
theorem `mono_right` / 定理 `mono_right`

English:
theorem mono_right
  given: {t'} (h' : AreSeparated s t') (ht : t subseteq t')
  statement: AreSeparated s t
  proof: h'.mono Subset.rfl ht

中文:
定理 mono_right
  条件: {t'} (h' : AreSeparated s t') (ht : t subseteq t')
  结论: AreSeparated s t
  证明: h'.mono Subset.rfl ht

Depends on / 依赖: Subset, Subset.rfl
-/
theorem mono_right {t'} (h' : AreSeparated s t') (ht : t subseteq t') : AreSeparated s t :=
  h'.mono Subset.rfl ht

/--
theorem `union_left` / 定理 `union_left`

English:
theorem union_left
  given: {s'} (h : AreSeparated s t) (h' : AreSeparated s' t)
  proof: by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine ⟨min r r', ?_, fun x hx y hy => hx.elim ?_ ?_⟩
  · rw [← pos_iff_ne_zero] at r0 r0' ⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)

@[simp]

中文:
定理 union_left
  条件: {s'} (h : AreSeparated s t) (h' : AreSeparated s' t)
  证明: by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine ⟨min r r', ?_, fun x hx y hy => hx.elim ?_ ?_⟩
  · rw [← pos_iff_ne_zero] at r0 r0' ⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)

@[simp]

Depends on / 依赖: hx.elim, lt_min, min_le_left, min_le_right, pos_iff_ne_zero
-/
theorem union_left {s'} (h : AreSeparated s t) (h' : AreSeparated s' t) :
    AreSeparated (s union s') t := by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine ⟨min r r', ?_, fun x hx y hy => hx.elim ?_ ?_⟩
  · rw [← pos_iff_ne_zero] at r0 r0' ⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)

@[simp]
/--
theorem `union_left_iff` / 定理 `union_left_iff`

English:
theorem union_left_iff
  given: {s'}
  proof: ⟨fun h => ⟨h.mono_left subset_union_left, h.mono_left subset_union_right⟩, fun h =>
    h.1.union_left h.2⟩

中文:
定理 union_left_iff
  条件: {s'}
  证明: ⟨fun h => ⟨h.mono_left subset_union_left, h.mono_left subset_union_right⟩, fun h =>
    h.1.union_left h.2⟩

Depends on / 依赖: h.mono_left, mono_left, subset_union_left, subset_union_right, union_left
-/
theorem union_left_iff {s'} :
    AreSeparated (s union s') t ↔ AreSeparated s t ∧ AreSeparated s' t :=
  ⟨fun h => ⟨h.mono_left subset_union_left, h.mono_left subset_union_right⟩, fun h =>
    h.1.union_left h.2⟩

/--
theorem `union_right` / 定理 `union_right`

English:
theorem union_right
  given: {t'} (h : AreSeparated s t) (h' : AreSeparated s t')
  proof: (h.symm.union_left h'.symm).symm

@[simp]

中文:
定理 union_right
  条件: {t'} (h : AreSeparated s t) (h' : AreSeparated s t')
  证明: (h.symm.union_left h'.symm).symm

@[simp]

Depends on / 依赖: h.symm.union_left, union_left
-/
theorem union_right {t'} (h : AreSeparated s t) (h' : AreSeparated s t') :
    AreSeparated s (t union t') :=
  (h.symm.union_left h'.symm).symm

@[simp]
/--
theorem `union_right_iff` / 定理 `union_right_iff`

English:
theorem union_right_iff
  given: {t'}
  proof: comm.trans union_left_iff.trans and_congr comm comm

中文:
定理 union_right_iff
  条件: {t'}
  证明: comm.trans union_left_iff.trans and_congr comm comm

Depends on / 依赖: and_congr, comm.trans, union_left_iff, union_left_iff.trans
-/
theorem union_right_iff {t'} :
    AreSeparated s (t union t') ↔ AreSeparated s t ∧ AreSeparated s t' :=
comm.trans union_left_iff.trans and_congr comm comm

/--
theorem `finite_iUnion_left_iff` / 定理 `finite_iUnion_left_iff`

English:
theorem finite_iUnion_left_iff
  statement: {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set X}
  proof: by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hI => rw [biUnion_insert, forall_mem_insert, union_left_iff, hI]

alias ⟨_, finite_iUnion_left⟩ := finite_iUnion_left_iff

中文:
定理 finite_iUnion_left_iff
  结论: {ι : 类型} {I : 集合 ι} (hI : I.有限) {s : ι -> 集合 X}
  证明: by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hI => rw [biUnion_insert, forall_mem_insert, union_left_iff, hI]

alias ⟨_, finite_iUnion_left⟩ := finite_iUnion_left_iff

Depends on / 依赖: Finite, Set.Finite.induction_on, biUnion_insert, forall_mem_insert, induction_on, insert, union_left_iff
-/
theorem finite_iUnion_left_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set X}
    {t : Set X} : AreSeparated (⋃ i in I, s i) t ↔ forall i in I, AreSeparated (s i) t := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hI => rw [biUnion_insert, forall_mem_insert, union_left_iff, hI]

alias ⟨_, finite_iUnion_left⟩ := finite_iUnion_left_iff

/--
theorem `finite_iUnion_right_iff` / 定理 `finite_iUnion_right_iff`

English:
theorem finite_iUnion_right_iff
  statement: {ι : Type*} {I : Set ι} (hI : I.Finite) {s : Set X}
  proof: by
  simpa only [@comm _ _ s] using finite_iUnion_left_iff hI

@[simp]

中文:
定理 finite_iUnion_right_iff
  结论: {ι : 类型} {I : 集合 ι} (hI : I.有限) {s : 集合 X}
  证明: by
  simpa only [@comm _ _ s] using finite_iUnion_left_iff hI

@[simp]

Depends on / 依赖: finite_iUnion_left_iff
-/
theorem finite_iUnion_right_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : Set X}
    {t : ι -> Set X} : AreSeparated s (⋃ i in I, t i) ↔ forall i in I, AreSeparated s (t i) := by
  simpa only [@comm _ _ s] using finite_iUnion_left_iff hI

@[simp]
/--
theorem `finset_iUnion_left_iff` / 定理 `finset_iUnion_left_iff`

English:
theorem finset_iUnion_left_iff
  given: {ι : Type*} {I : Finset ι} {s : ι -> Set X} {t : Set X}
  proof: finite_iUnion_left_iff I.finite_toSet

alias ⟨_, finset_iUnion_left⟩ := finset_iUnion_left_iff

@[simp]

中文:
定理 finset_iUnion_left_iff
  条件: {ι : 类型} {I : 有限集 ι} {s : ι -> 集合 X} {t : 集合 X}
  证明: finite_iUnion_left_iff I.finite_toSet

alias ⟨_, finset_iUnion_left⟩ := finset_iUnion_left_iff

@[simp]

Depends on / 依赖: I.finite_toSet, finite_iUnion_left_iff, finite_toSet
-/
theorem finset_iUnion_left_iff {ι : Type*} {I : Finset ι} {s : ι -> Set X} {t : Set X} :
    AreSeparated (⋃ i in I, s i) t ↔ forall i in I, AreSeparated (s i) t :=
  finite_iUnion_left_iff I.finite_toSet

alias ⟨_, finset_iUnion_left⟩ := finset_iUnion_left_iff

@[simp]
/--
theorem `finset_iUnion_right_iff` / 定理 `finset_iUnion_right_iff`

English:
theorem finset_iUnion_right_iff
  given: {ι : Type*} {I : Finset ι} {s : Set X} {t : ι -> Set X}
  proof: finite_iUnion_right_iff I.finite_toSet

alias ⟨_, finset_iUnion_right⟩ := finset_iUnion_right_iff

中文:
定理 finset_iUnion_right_iff
  条件: {ι : 类型} {I : 有限集 ι} {s : 集合 X} {t : ι -> 集合 X}
  证明: finite_iUnion_right_iff I.finite_toSet

alias ⟨_, finset_iUnion_right⟩ := finset_iUnion_right_iff

Depends on / 依赖: I.finite_toSet, finite_iUnion_right_iff, finite_toSet
-/
theorem finset_iUnion_right_iff {ι : Type*} {I : Finset ι} {s : Set X} {t : ι -> Set X} :
    AreSeparated s (⋃ i in I, t i) ↔ forall i in I, AreSeparated s (t i) :=
  finite_iUnion_right_iff I.finite_toSet

alias ⟨_, finset_iUnion_right⟩ := finset_iUnion_right_iff

end Metric.AreSeparated
