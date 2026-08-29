/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Decomposing walks

## Main definitions
- `takeUntil`: The path obtained by taking edges of an existing path until a given vertex.
- `dropUntil`: The path obtained by dropping edges of an existing path until a given vertex.
- `rotate`: Rotate a loop walk such that it is centered at the given vertex.
-/

@[expose] public section

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {v w u : V}

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/--
Definition of `takeUntil` / `takeUntil` 的定义

English:
definition takeUntil
  signature: {v w : V}

中文:
定义 takeUntil
  签名: {v w : V}
-/
def takeUntil {v w : V} : forall (p : G.Walk v w) (u : V), u in p.support -> G.Walk v u
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then
      hx ▸ Walk.nil
    else
      cons r (takeUntil p u <| by
        cases h
        · exact (hx rfl).elim
        · assumption)

/--
theorem `takeUntil_nil` / 定理 `takeUntil_nil`

English:
theorem takeUntil_nil
  given: {u : V} {h}
  statement: takeUntil (nil : G.Walk u u) u h = nil
  proof: rfl

中文:
定理 takeUntil_nil
  条件: {u : V} {h}
  结论: takeUntil (nil : G.途径 u u) u h = nil
  证明: rfl
-/
@[simp] theorem takeUntil_nil {u : V} {h} : takeUntil (nil : G.Walk u u) u h = nil := rfl

/--
lemma `takeUntil_cons` / 引理 `takeUntil_cons`

English:
lemma takeUntil_cons
  statement: {v' : V} {p : G.Walk v' v} (hwp : w in p.support) (h : u != w)
  proof: by
  simp [Walk.takeUntil, h]

@[simp]

中文:
引理 takeUntil_cons
  结论: {v' : V} {p : G.途径 v' v} (hwp : w in p.support) (h : u != w)
  证明: by
  simp [Walk.takeUntil, h]

@[simp]

Depends on / 依赖: Walk.takeUntil, takeUntil
-/
lemma takeUntil_cons {v' : V} {p : G.Walk v' v} (hwp : w in p.support) (h : u != w)
    (hadj : G.Adj u v') :
    (p.cons hadj).takeUntil w (List.mem_of_mem_tail hwp) = (p.takeUntil w hwp).cons hadj := by
  simp [Walk.takeUntil, h]

@[simp]
/--
lemma `takeUntil_first` / 引理 `takeUntil_first`

English:
lemma takeUntil_first
  given: (p : G.Walk u v)
  proof: by cases p <;> simp [Walk.takeUntil]

@[simp]

中文:
引理 takeUntil_first
  条件: (p : G.途径 u v)
  证明: by cases p <;> simp [Walk.takeUntil]

@[simp]

Depends on / 依赖: Walk.takeUntil, takeUntil
-/
lemma takeUntil_first (p : G.Walk u v) :
    p.takeUntil u p.start_mem_support = .nil := by cases p <;> simp [Walk.takeUntil]

@[simp]
/--
lemma `nil_takeUntil` / 引理 `nil_takeUntil`

English:
lemma nil_takeUntil
  given: (p : G.Walk u v) (hwp : w in p.support)
  proof: ⟨Nil.eq, (by cases ·; simp)⟩

中文:
引理 nil_takeUntil
  条件: (p : G.途径 u v) (hwp : w in p.support)
  证明: ⟨Nil.eq, (by cases ·; simp)⟩

Depends on / 依赖: Nil.eq
-/
lemma nil_takeUntil (p : G.Walk u v) (hwp : w in p.support) :
    (p.takeUntil w hwp).Nil ↔ u = w := ⟨Nil.eq, (by cases ·; simp)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `takeUntil_eq_take` / 引理 `takeUntil_eq_take`

English:
lemma takeUntil_eq_take
  given: (p : G.Walk u v) (h : w in p.support)
  proof: by
  apply ext_support
  induction p with
  | nil =>
    simp only [takeUntil, eq_mpr_eq_cast, support_nil, getVert_nil, take, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | cons hadj p ih =>
    grind [takeUntil, support, copy_rfl_rfl, support_take]

中文:
引理 takeUntil_eq_take
  条件: (p : G.途径 u v) (h : w in p.support)
  证明: by
  apply ext_support
  induction p with
  | nil =>
    simp only [takeUntil, eq_mpr_eq_cast, support_nil, getVert_nil, take, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | cons hadj p ih =>
    grind [takeUntil, support, copy_rfl_rfl, support_take]

Depends on / 依赖: copy_rfl_rfl, eq_mpr_eq_cast, ext_support, getVert_nil, mem_support_nil_iff, support, support_copy, support_nil, support_take, takeUntil
-/
lemma takeUntil_eq_take (p : G.Walk u v) (h : w in p.support) :
    p.takeUntil w h = (p.take <| p.support.idxOf w).copy rfl (p.getVert_support_idxOf h) := by
  apply ext_support
  induction p with
  | nil =>
    simp only [takeUntil, eq_mpr_eq_cast, support_nil, getVert_nil, take, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | cons hadj p ih =>
    grind [takeUntil, support, copy_rfl_rfl, support_take]

/--
lemma `length_takeUntil` / 引理 `length_takeUntil`

English:
lemma length_takeUntil
  given: (p : G.Walk u v) (h : w in p.support)
  proof: by
  simp [takeUntil_eq_take, Nat.le_iff_lt_add_one, ← length_support, List.idxOf_lt_length_of_mem h]

中文:
引理 length_takeUntil
  条件: (p : G.途径 u v) (h : w in p.support)
  证明: by
  simp [takeUntil_eq_take, Nat.le_iff_lt_add_one, ← length_support, List.idxOf_lt_length_of_mem h]

Depends on / 依赖: List.idxOf_lt_length_of_mem, Nat.le_iff_lt_add_one, idxOf_lt_length_of_mem, le_iff_lt_add_one, length_support, takeUntil_eq_take
-/
lemma length_takeUntil (p : G.Walk u v) (h : w in p.support) :
    (p.takeUntil w h).length = p.support.idxOf w := by
  simp [takeUntil_eq_take, Nat.le_iff_lt_add_one, ← length_support, List.idxOf_lt_length_of_mem h]

/--
Definition of `dropUntil` / `dropUntil` 的定义

English:
definition dropUntil
  signature: {v w : V}

中文:
定义 dropUntil
  签名: {v w : V}
-/
def dropUntil {v w : V} : forall (p : G.Walk v w) (u : V), u in p.support -> G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
else dropUntil p u by
      cases h
      · exact (hx rfl).elim
      · assumption

/-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `SimpleGraph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
@[simp]
/--
theorem `take_spec` / 定理 `take_spec`

English:
theorem take_spec
  given: {u v w : V} (p : G.Walk v w) (h : u in p.support)
  proof: by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]

@[simp]

中文:
定理 take_spec
  条件: {u v w : V} (p : G.途径 v w) (h : u in p.support)
  证明: by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]

@[simp]

Depends on / 依赖: mem_support_nil_iff, split_ifs
-/
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]

@[simp]
/--
lemma `dropUntil_first` / 引理 `dropUntil_first`

English:
lemma dropUntil_first
  given: (p : G.Walk u v) (h : u in p.support)
  statement: p.dropUntil u h = p
  proof: by
  unfold dropUntil
  split <;> simp

中文:
引理 dropUntil_first
  条件: (p : G.途径 u v) (h : u in p.support)
  结论: p.dropUntil u h = p
  证明: by
  unfold dropUntil
  split <;> simp

Depends on / 依赖: dropUntil
-/
lemma dropUntil_first (p : G.Walk u v) (h : u in p.support) : p.dropUntil u h = p := by
  unfold dropUntil
  split <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `dropUntil_eq_drop` / 引理 `dropUntil_eq_drop`

English:
lemma dropUntil_eq_drop
  given: (p : G.Walk u v) (h : w in p.support)
  proof: by
  apply ext_support
  induction p with
  | nil =>
    simp only [dropUntil, eq_mpr_eq_cast, support_nil, getVert_nil, drop, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | @cons a _ _ _ p ih =>
    by_cases! h' : w = a
    · subst h'
      simp [dropUntil_first]
    · rw [drop_cons

中文:
引理 dropUntil_eq_drop
  条件: (p : G.途径 u v) (h : w in p.support)
  证明: by
  apply ext_support
  induction p with
  | nil =>
    simp only [dropUntil, eq_mpr_eq_cast, support_nil, getVert_nil, drop, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | @cons a _ _ _ p ih =>
    by_cases! h' : w = a
    · subst h'
      simp [dropUntil_first]
    · rw [drop_cons

Depends on / 依赖: dropUntil, dropUntil_first, drop_cons_eq, eq_mpr_eq_cast, ext_support, getVert_nil, mem_support_nil_iff, support_copy, support_nil
-/
lemma dropUntil_eq_drop (p : G.Walk u v) (h : w in p.support) :
    p.dropUntil w h = (p.drop <| p.support.idxOf w).copy (p.getVert_support_idxOf h) rfl := by
  apply ext_support
  induction p with
  | nil =>
    simp only [dropUntil, eq_mpr_eq_cast, support_nil, getVert_nil, drop, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | @cons a _ _ _ p ih =>
    by_cases! h' : w = a
    · subst h'
      simp [dropUntil_first]
    · rw [drop_cons_eq _ _ _ (by grind), support_copy, dropUntil]
      grind

/--
lemma `length_dropUntil` / 引理 `length_dropUntil`

English:
lemma length_dropUntil
  given: (p : G.Walk u v) (h : w in p.support)
  proof: by
  simp [dropUntil_eq_drop]

中文:
引理 length_dropUntil
  条件: (p : G.途径 u v) (h : w in p.support)
  证明: by
  simp [dropUntil_eq_drop]

Depends on / 依赖: dropUntil_eq_drop
-/
lemma length_dropUntil (p : G.Walk u v) (h : w in p.support) :
    (p.dropUntil w h).length = p.length - p.support.idxOf w := by
  simp [dropUntil_eq_drop]

/--
theorem `isSubwalk_takeUntil` / 定理 `isSubwalk_takeUntil`

English:
theorem isSubwalk_takeUntil
  given: (p : G.Walk u v) (h : w in p.support)
  statement: (p.takeUntil w h).IsSubwalk p
  proof: ⟨nil, p.dropUntil w h, by simp⟩

中文:
定理 isSubwalk_takeUntil
  条件: (p : G.途径 u v) (h : w in p.support)
  结论: (p.takeUntil w h).IsSubwalk p
  证明: ⟨nil, p.dropUntil w h, by simp⟩

Depends on / 依赖: dropUntil, p.dropUntil
-/
theorem isSubwalk_takeUntil (p : G.Walk u v) (h : w in p.support) : (p.takeUntil w h).IsSubwalk p :=
  ⟨nil, p.dropUntil w h, by simp⟩

/--
theorem `isSubwalk_dropUntil` / 定理 `isSubwalk_dropUntil`

English:
theorem isSubwalk_dropUntil
  given: (p : G.Walk u v) (h : w in p.support)
  statement: (p.dropUntil w h).IsSubwalk p
  proof: ⟨p.takeUntil w h, nil, by simp⟩

中文:
定理 isSubwalk_dropUntil
  条件: (p : G.途径 u v) (h : w in p.support)
  结论: (p.dropUntil w h).IsSubwalk p
  证明: ⟨p.takeUntil w h, nil, by simp⟩

Depends on / 依赖: p.takeUntil, takeUntil
-/
theorem isSubwalk_dropUntil (p : G.Walk u v) (h : w in p.support) : (p.dropUntil w h).IsSubwalk p :=
  ⟨p.takeUntil w h, nil, by simp⟩

/--
theorem `mem_support_iff_exists_append` / 定理 `mem_support_iff_exists_append`

English:
theorem mem_support_iff_exists_append
  statement: {V : Type u} {G : SimpleGraph V} {u v w : V}
  proof: by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

@[simp]

中文:
定理 mem_support_iff_存在_append
  结论: {V : 类型u} {G : 简单图 V} {u v w : V}
  证明: by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

@[simp]

Depends on / 依赖: classical, end_mem_support, mem_support_append_iff, or_self_iff, p.take_spec, start_mem_support, take_spec
-/
theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w in p.support ↔ exists (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

@[simp]
/--
theorem `count_support_takeUntil_eq_one` / 定理 `count_support_takeUntil_eq_one`

English:
theorem count_support_takeUntil_eq_one
  given: {u v w : V} (p : G.Walk v w) (h : u in p.support)
  proof: by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp
  · cases h
    · simp
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]

中文:
定理 count_support_takeUntil_eq_one
  条件: {u v w : V} (p : G.途径 v w) (h : u in p.support)
  证明: by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp
  · cases h
    · simp
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]

Depends on / 依赖: List.count_cons, count_cons, eq_comm, mem_support_nil_iff, split_ifs
-/
theorem count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp
  · cases h
    · simp
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]

/--
theorem `count_edges_takeUntil_le_one` / 定理 `count_edges_takeUntil_le_one`

English:
theorem count_edges_takeUntil_le_one
  given: {u v w : V} (p : G.Walk v w) (h : u in p.support) (x : V)
  proof: by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp
  | cons ha p' ih =>
    cases h
    · simp
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · simp only [beq_iff_

中文:
定理 count_edges_takeUntil_le_one
  条件: {u v w : V} (p : G.途径 v w) (h : u in p.support) (x : V)
  证明: by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp
  | cons ha p' ih =>
    cases h
    · simp
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · simp only [beq_iff_

Depends on / 依赖: List.count_cons, Sym2.eq, Sym2.rel_iff, beq_iff_eq, count_cons, edges_cons, mem_support_nil_iff, rel_iff, split_ifs
-/
theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u in p.support) (x : V) :
    (p.takeUntil u h).edges.count s(u, x) <= 1 := by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp
  | cons ha p' ih =>
    cases h
    · simp
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · simp only [beq_iff_eq, Sym2.eq, Sym2.rel_iff'] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih

@[simp]
/--
theorem `takeUntil_copy` / 定理 `takeUntil_copy`

English:
theorem takeUntil_copy
  statement: {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 takeUntil_copy
  结论: {u v w v' w'} (p : G.途径 v w) (hv : v = v') (hw : w = w')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u in (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl

@[simp]
/--
theorem `dropUntil_copy` / 定理 `dropUntil_copy`

English:
theorem dropUntil_copy
  statement: {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
  proof: by
  subst_vars
  rfl

中文:
定理 dropUntil_copy
  结论: {u v w v' w'} (p : G.途径 v w) (hv : v = v') (hw : w = w')
  证明: by
  subst_vars
  rfl
-/
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u in (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
  subst_vars
  rfl

/--
theorem `support_takeUntil_prefix_support` / 定理 `support_takeUntil_prefix_support`

English:
theorem support_takeUntil_prefix_support
  given: (p : G.Walk v w) (h : u in p.support)
  proof: by
  grw [takeUntil_eq_take, support_copy, support_take, List.take_prefix]

中文:
定理 support_takeUntil_prefix_support
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: by
  grw [takeUntil_eq_take, support_copy, support_take, List.take_prefix]

Depends on / 依赖: List.take_prefix, support_copy, support_take, takeUntil_eq_take, take_prefix
-/
theorem support_takeUntil_prefix_support (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).support <+: p.support := by
  grw [takeUntil_eq_take, support_copy, support_take, List.take_prefix]

/--
theorem `support_takeUntil_subset_support` / 定理 `support_takeUntil_subset_support`

English:
theorem support_takeUntil_subset_support
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .subset p.support_takeUntil_prefix_support h

@[deprecated (since := "2026-05-25")]
alias support_takeUntil_subset := support_takeUntil_subset_support

中文:
定理 support_takeUntil_subset_support
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .subset p.support_takeUntil_prefix_support h

@[deprecated (since := "2026-05-25")]
alias support_takeUntil_subset := support_takeUntil_subset_support

Depends on / 依赖: p.support_takeUntil_prefix_support, subset, support_takeUntil_prefix_support
-/
theorem support_takeUntil_subset_support (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).support subseteq p.support :=
.subset p.support_takeUntil_prefix_support h

@[deprecated (since := "2026-05-25")]
alias support_takeUntil_subset := support_takeUntil_subset_support

/--
theorem `support_dropUntil_suffix_support` / 定理 `support_dropUntil_suffix_support`

English:
theorem support_dropUntil_suffix_support
  given: (p : G.Walk v w) (h : u in p.support)
  proof: by
  grw [dropUntil_eq_drop, support_copy, drop_support_eq_support_drop_min, List.drop_suffix]

中文:
定理 support_dropUntil_suffix_support
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: by
  grw [dropUntil_eq_drop, support_copy, drop_support_eq_support_drop_min, List.drop_suffix]

Depends on / 依赖: List.drop_suffix, dropUntil_eq_drop, drop_suffix, drop_support_eq_support_drop_min, support_copy
-/
theorem support_dropUntil_suffix_support (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).support <:+ p.support := by
  grw [dropUntil_eq_drop, support_copy, drop_support_eq_support_drop_min, List.drop_suffix]

/--
theorem `support_dropUntil_subset_support` / 定理 `support_dropUntil_subset_support`

English:
theorem support_dropUntil_subset_support
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .subset p.support_dropUntil_suffix_support h

@[deprecated (since := "2026-05-25")]
alias support_dropUntil_subset := support_dropUntil_subset_support

中文:
定理 support_dropUntil_subset_support
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .subset p.support_dropUntil_suffix_support h

@[deprecated (since := "2026-05-25")]
alias support_dropUntil_subset := support_dropUntil_subset_support

Depends on / 依赖: p.support_dropUntil_suffix_support, subset, support_dropUntil_suffix_support
-/
theorem support_dropUntil_subset_support (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).support subseteq p.support :=
.subset p.support_dropUntil_suffix_support h

@[deprecated (since := "2026-05-25")]
alias support_dropUntil_subset := support_dropUntil_subset_support

/--
theorem `darts_takeUntil_prefix_darts` / 定理 `darts_takeUntil_prefix_darts`

English:
theorem darts_takeUntil_prefix_darts
  given: (p : G.Walk v w) (h : u in p.support)
  proof: by
  grw [takeUntil_eq_take, darts_copy, darts_take, List.take_prefix]

中文:
定理 darts_takeUntil_prefix_darts
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: by
  grw [takeUntil_eq_take, darts_copy, darts_take, List.take_prefix]

Depends on / 依赖: List.take_prefix, darts_copy, darts_take, takeUntil_eq_take, take_prefix
-/
theorem darts_takeUntil_prefix_darts (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).darts <+: p.darts := by
  grw [takeUntil_eq_take, darts_copy, darts_take, List.take_prefix]

/--
theorem `darts_takeUntil_subset_darts` / 定理 `darts_takeUntil_subset_darts`

English:
theorem darts_takeUntil_subset_darts
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .subset p.darts_takeUntil_prefix_darts h

@[deprecated (since := "2026-05-25")] alias darts_takeUntil_subset := darts_takeUntil_subset_darts

中文:
定理 darts_takeUntil_subset_darts
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .subset p.darts_takeUntil_prefix_darts h

@[deprecated (since := "2026-05-25")] alias darts_takeUntil_subset := darts_takeUntil_subset_darts

Depends on / 依赖: darts_takeUntil_prefix_darts, p.darts_takeUntil_prefix_darts, subset
-/
theorem darts_takeUntil_subset_darts (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).darts subseteq p.darts :=
.subset p.darts_takeUntil_prefix_darts h

@[deprecated (since := "2026-05-25")] alias darts_takeUntil_subset := darts_takeUntil_subset_darts

/--
theorem `darts_dropUntil_suffix_darts` / 定理 `darts_dropUntil_suffix_darts`

English:
theorem darts_dropUntil_suffix_darts
  given: (p : G.Walk v w) (h : u in p.support)
  proof: by
  grw [dropUntil_eq_drop, darts_copy, darts_drop, List.drop_suffix]

中文:
定理 darts_dropUntil_suffix_darts
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: by
  grw [dropUntil_eq_drop, darts_copy, darts_drop, List.drop_suffix]

Depends on / 依赖: List.drop_suffix, darts_copy, darts_drop, dropUntil_eq_drop, drop_suffix
-/
theorem darts_dropUntil_suffix_darts (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).darts <:+ p.darts := by
  grw [dropUntil_eq_drop, darts_copy, darts_drop, List.drop_suffix]

/--
theorem `darts_dropUntil_subset_darts` / 定理 `darts_dropUntil_subset_darts`

English:
theorem darts_dropUntil_subset_darts
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .subset p.darts_dropUntil_suffix_darts h

@[deprecated (since := "2026-05-25")] alias darts_dropUntil_subset := darts_dropUntil_subset_darts

中文:
定理 darts_dropUntil_subset_darts
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .subset p.darts_dropUntil_suffix_darts h

@[deprecated (since := "2026-05-25")] alias darts_dropUntil_subset := darts_dropUntil_subset_darts

Depends on / 依赖: darts_dropUntil_suffix_darts, p.darts_dropUntil_suffix_darts, subset
-/
theorem darts_dropUntil_subset_darts (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).darts subseteq p.darts :=
.subset p.darts_dropUntil_suffix_darts h

@[deprecated (since := "2026-05-25")] alias darts_dropUntil_subset := darts_dropUntil_subset_darts

/--
theorem `edges_takeUntil_prefix_edges` / 定理 `edges_takeUntil_prefix_edges`

English:
theorem edges_takeUntil_prefix_edges
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .map _ p.darts_takeUntil_prefix_darts h

中文:
定理 edges_takeUntil_prefix_edges
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .map _ p.darts_takeUntil_prefix_darts h

Depends on / 依赖: darts_takeUntil_prefix_darts, p.darts_takeUntil_prefix_darts
-/
theorem edges_takeUntil_prefix_edges (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).edges <+: p.edges :=
.map _ p.darts_takeUntil_prefix_darts h

/--
theorem `edges_takeUntil_subset_edges` / 定理 `edges_takeUntil_subset_edges`

English:
theorem edges_takeUntil_subset_edges
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .subset p.edges_takeUntil_prefix_edges h

@[deprecated (since := "2026-05-25")] alias edges_takeUntil_subset := edges_takeUntil_subset_edges

中文:
定理 edges_takeUntil_subset_edges
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .subset p.edges_takeUntil_prefix_edges h

@[deprecated (since := "2026-05-25")] alias edges_takeUntil_subset := edges_takeUntil_subset_edges

Depends on / 依赖: edges_takeUntil_prefix_edges, p.edges_takeUntil_prefix_edges, subset
-/
theorem edges_takeUntil_subset_edges (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).edges subseteq p.edges :=
.subset p.edges_takeUntil_prefix_edges h

@[deprecated (since := "2026-05-25")] alias edges_takeUntil_subset := edges_takeUntil_subset_edges

/--
theorem `edges_dropUntil_suffix_edges` / 定理 `edges_dropUntil_suffix_edges`

English:
theorem edges_dropUntil_suffix_edges
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .map _ p.darts_dropUntil_suffix_darts h

中文:
定理 edges_dropUntil_suffix_edges
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .map _ p.darts_dropUntil_suffix_darts h

Depends on / 依赖: darts_dropUntil_suffix_darts, p.darts_dropUntil_suffix_darts
-/
theorem edges_dropUntil_suffix_edges (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).edges <:+ p.edges :=
.map _ p.darts_dropUntil_suffix_darts h

/--
theorem `edges_dropUntil_subset_edges` / 定理 `edges_dropUntil_subset_edges`

English:
theorem edges_dropUntil_subset_edges
  given: (p : G.Walk v w) (h : u in p.support)
  proof: .subset p.edges_dropUntil_suffix_edges h

@[deprecated (since := "2026-05-25")] alias edges_dropUntil_subset := edges_dropUntil_subset_edges

中文:
定理 edges_dropUntil_subset_edges
  条件: (p : G.途径 v w) (h : u in p.support)
  证明: .subset p.edges_dropUntil_suffix_edges h

@[deprecated (since := "2026-05-25")] alias edges_dropUntil_subset := edges_dropUntil_subset_edges

Depends on / 依赖: edges_dropUntil_suffix_edges, p.edges_dropUntil_suffix_edges, subset
-/
theorem edges_dropUntil_subset_edges (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).edges subseteq p.edges :=
.subset p.edges_dropUntil_suffix_edges h

@[deprecated (since := "2026-05-25")] alias edges_dropUntil_subset := edges_dropUntil_subset_edges

/--
theorem `length_takeUntil_le_length` / 定理 `length_takeUntil_le_length`

English:
theorem length_takeUntil_le_length
  given: {u v w : V} (p : G.Walk v w) (h : u in p.support)
  proof: by
.length_le simpa using p.darts_takeUntil_prefix_darts h

@[deprecated (since := "2026-05-25")] alias length_takeUntil_le := length_takeUntil_le_length

中文:
定理 length_takeUntil_le_length
  条件: {u v w : V} (p : G.途径 v w) (h : u in p.support)
  证明: by
.length_le simpa using p.darts_takeUntil_prefix_darts h

@[deprecated (since := "2026-05-25")] alias length_takeUntil_le := length_takeUntil_le_length

Depends on / 依赖: darts_takeUntil_prefix_darts, length_le, p.darts_takeUntil_prefix_darts
-/
theorem length_takeUntil_le_length {u v w : V} (p : G.Walk v w) (h : u in p.support) :
    (p.takeUntil u h).length <= p.length := by
.length_le simpa using p.darts_takeUntil_prefix_darts h

@[deprecated (since := "2026-05-25")] alias length_takeUntil_le := length_takeUntil_le_length

/--
theorem `length_dropUntil_le_length` / 定理 `length_dropUntil_le_length`

English:
theorem length_dropUntil_le_length
  given: {u v w : V} (p : G.Walk v w) (h : u in p.support)
  proof: by
.length_le simpa using p.darts_dropUntil_suffix_darts h

@[deprecated (since := "2026-05-25")] alias length_dropUntil_le := length_dropUntil_le_length

中文:
定理 length_dropUntil_le_length
  条件: {u v w : V} (p : G.途径 v w) (h : u in p.support)
  证明: by
.length_le simpa using p.darts_dropUntil_suffix_darts h

@[deprecated (since := "2026-05-25")] alias length_dropUntil_le := length_dropUntil_le_length

Depends on / 依赖: darts_dropUntil_suffix_darts, length_le, p.darts_dropUntil_suffix_darts
-/
theorem length_dropUntil_le_length {u v w : V} (p : G.Walk v w) (h : u in p.support) :
    (p.dropUntil u h).length <= p.length := by
.length_le simpa using p.darts_dropUntil_suffix_darts h

@[deprecated (since := "2026-05-25")] alias length_dropUntil_le := length_dropUntil_le_length

/--
lemma `takeUntil_append_of_mem_left` / 引理 `takeUntil_append_of_mem_left`

English:
lemma takeUntil_append_of_mem_left
  given: {x : V} (p : G.Walk u v) (q : G.Walk v w) (hx : x in p.support)
  proof: by
  induction p with
  | nil => rw [mem_support_nil_iff] at hx; subst_vars; simp
  | cons => grind [cons_append, takeUntil]

中文:
引理 takeUntil_append_of_mem_left
  条件: {x : V} (p : G.途径 u v) (q : G.途径 v w) (hx : x in p.support)
  证明: by
  induction p with
  | nil => rw [mem_support_nil_iff] at hx; subst_vars; simp
  | cons => grind [cons_append, takeUntil]

Depends on / 依赖: cons_append, mem_support_nil_iff, takeUntil
-/
lemma takeUntil_append_of_mem_left {x : V} (p : G.Walk u v) (q : G.Walk v w) (hx : x in p.support) :
    (p.append q).takeUntil x (support_subset_support_append_left _ _ hx) = p.takeUntil _ hx := by
  induction p with
  | nil => rw [mem_support_nil_iff] at hx; subst_vars; simp
  | cons => grind [cons_append, takeUntil]

/--
lemma `getVert_takeUntil` / 引理 `getVert_takeUntil`

English:
lemma getVert_takeUntil
  statement: {u v : V} {n : Nat} {p : G.Walk u v} (hw : w in p.support)
  proof: by
  conv_rhs => rw [← take_spec p hw, getVert_append]
  cases hn.lt_or_eq <;> simp_all

中文:
引理 getVert_takeUntil
  结论: {u v : V} {n : 自然数} {p : G.途径 u v} (hw : w in p.support)
  证明: by
  conv_rhs => rw [← take_spec p hw, getVert_append]
  cases hn.lt_or_eq <;> simp_all

Depends on / 依赖: conv_rhs, getVert_append, hn.lt_or_eq, lt_or_eq, take_spec
-/
lemma getVert_takeUntil {u v : V} {n : Nat} {p : G.Walk u v} (hw : w in p.support)
    (hn : n <= (p.takeUntil w hw).length) : (p.takeUntil w hw).getVert n = p.getVert n := by
  conv_rhs => rw [← take_spec p hw, getVert_append]
  cases hn.lt_or_eq <;> simp_all

/--
lemma `snd_takeUntil` / 引理 `snd_takeUntil`

English:
lemma snd_takeUntil
  given: (hsu : w != u) (p : G.Walk u v) (h : w in p.support)
  proof: by
  apply p.getVert_takeUntil h
  contrapose hsu
  symm
  simpa [length_eq_zero_iff] using hsu

中文:
引理 snd_takeUntil
  条件: (hsu : w != u) (p : G.途径 u v) (h : w in p.support)
  证明: by
  apply p.getVert_takeUntil h
  contrapose hsu
  symm
  simpa [length_eq_zero_iff] using hsu

Depends on / 依赖: contrapose, getVert_takeUntil, length_eq_zero_iff, p.getVert_takeUntil
-/
lemma snd_takeUntil (hsu : w != u) (p : G.Walk u v) (h : w in p.support) :
    (p.takeUntil w h).snd = p.snd := by
  apply p.getVert_takeUntil h
  contrapose hsu
  symm
  simpa [length_eq_zero_iff] using hsu

/--
lemma `getVert_length_takeUntil` / 引理 `getVert_length_takeUntil`

English:
lemma getVert_length_takeUntil
  given: {p : G.Walk v w} (h : u in p.support)
  proof: by
  have := congr_arg₂ (y := (p.takeUntil _ h).length) getVert (p.take_spec h) rfl
  grind [getVert_append, getVert_zero]

中文:
引理 getVert_length_takeUntil
  条件: {p : G.途径 v w} (h : u in p.support)
  证明: by
  have := congr_arg₂ (y := (p.takeUntil _ h).length) getVert (p.take_spec h) rfl
  grind [getVert_append, getVert_zero]

Depends on / 依赖: getVert, getVert_append, getVert_zero, length, p.takeUntil, p.take_spec, takeUntil, take_spec
-/
lemma getVert_length_takeUntil {p : G.Walk v w} (h : u in p.support) :
    p.getVert (p.takeUntil _ h).length = u := by
  have := congr_arg₂ (y := (p.takeUntil _ h).length) getVert (p.take_spec h) rfl
  grind [getVert_append, getVert_zero]

/--
lemma `getVert_lt_length_takeUntil_ne` / 引理 `getVert_lt_length_takeUntil_ne`

English:
lemma getVert_lt_length_takeUntil_ne
  statement: {n : Nat} {p : G.Walk v w} (h : u in p.support)
  proof: by
  rintro rfl
  have h₁ : n < (p.takeUntil _ h).support.dropLast.length := by simpa
  have : p.getVert n in (p.takeUntil _ h).support.dropLast := by
    simp_rw [p.getVert_takeUntil h hn.le ▸ getVert_eq_support_getElem _ hn.le,
      ← List.getElem_dropLast h₁, List.getElem_mem h₁]
  have := dropL

中文:
引理 getVert_lt_length_takeUntil_ne
  结论: {n : 自然数} {p : G.途径 v w} (h : u in p.support)
  证明: by
  rintro rfl
  have h₁ : n < (p.takeUntil _ h).support.dropLast.length := by simpa
  have : p.getVert n in (p.takeUntil _ h).support.dropLast := by
    simp_rw [p.getVert_takeUntil h hn.le ▸ getVert_eq_support_getElem _ hn.le,
      ← List.getElem_dropLast h₁, List.getElem_mem h₁]
  have := dropL

Depends on / 依赖: List.getElem_dropLast, List.getElem_mem, List.not_mem_of_count_eq_zero, count_support_takeUntil_eq_one, dropLast, dropLast_support_concat, getElem_dropLast, getElem_mem, getVert, getVert_eq_support_getElem, getVert_takeUntil, hn.le, length, not_mem_of_count_eq_zero, p.count_support_takeUntil_eq_one, p.getVert, p.getVert_takeUntil, p.takeUntil, simp_rw, support
-/
lemma getVert_lt_length_takeUntil_ne {n : Nat} {p : G.Walk v w} (h : u in p.support)
    (hn : n < (p.takeUntil _ h).length) : p.getVert n != u := by
  rintro rfl
  have h₁ : n < (p.takeUntil _ h).support.dropLast.length := by simpa
  have : p.getVert n in (p.takeUntil _ h).support.dropLast := by
    simp_rw [p.getVert_takeUntil h hn.le ▸ getVert_eq_support_getElem _ hn.le,
      ← List.getElem_dropLast h₁, List.getElem_mem h₁]
  have := dropLast_support_concat _ ▸ p.count_support_takeUntil_eq_one h
  grind [List.not_mem_of_count_eq_zero]

/--
theorem `getVert_le_length_takeUntil_eq_iff` / 定理 `getVert_le_length_takeUntil_eq_iff`

English:
theorem getVert_le_length_takeUntil_eq_iff
  statement: {n : Nat} {p : G.Walk v w} (h : u in p.support)
  proof: by
  grind [getVert_length_takeUntil, getVert_lt_length_takeUntil_ne]

中文:
定理 getVert_le_length_takeUntil_eq_iff
  结论: {n : 自然数} {p : G.途径 v w} (h : u in p.support)
  证明: by
  grind [getVert_length_takeUntil, getVert_lt_length_takeUntil_ne]

Depends on / 依赖: getVert_length_takeUntil, getVert_lt_length_takeUntil_ne
-/
theorem getVert_le_length_takeUntil_eq_iff {n : Nat} {p : G.Walk v w} (h : u in p.support)
    (hn : n <= (p.takeUntil _ h).length) : p.getVert n = u ↔ n = (p.takeUntil _ h).length := by
  grind [getVert_length_takeUntil, getVert_lt_length_takeUntil_ne]

/--
lemma `length_takeUntil_lt_length` / 引理 `length_takeUntil_lt_length`

English:
lemma length_takeUntil_lt_length
  given: {u v w : V} {p : G.Walk v w} (h : u in p.support) (huw : u != w)
  proof: by
  rw [(p.length_takeUntil_le_length h).lt_iff_ne]
  exact fun hl => huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

@[deprecated (since := "2026-05-25")] alias length_takeUntil_lt := length_takeUntil_lt_length

中文:
引理 length_takeUntil_lt_length
  条件: {u v w : V} {p : G.途径 v w} (h : u in p.support) (huw : u != w)
  证明: by
  rw [(p.length_takeUntil_le_length h).lt_iff_ne]
  exact fun hl => huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

@[deprecated (since := "2026-05-25")] alias length_takeUntil_lt := length_takeUntil_lt_length

Depends on / 依赖: getVert, getVert_takeUntil, length, length_takeUntil_le_length, lt_iff_ne, p.getVert, p.length, p.length_takeUntil_le_length, p.takeUntil, takeUntil
-/
lemma length_takeUntil_lt_length {u v w : V} {p : G.Walk v w} (h : u in p.support) (huw : u != w) :
    (p.takeUntil u h).length < p.length := by
  rw [(p.length_takeUntil_le_length h).lt_iff_ne]
  exact fun hl => huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

@[deprecated (since := "2026-05-25")] alias length_takeUntil_lt := length_takeUntil_lt_length

/--
lemma `length_dropUntil_lt_length` / 引理 `length_dropUntil_lt_length`

English:
lemma length_dropUntil_lt_length
  given: {u v w : V} {p : G.Walk v w} (h : u in p.support) (huv : u != v)
  proof: by
  grind [length_dropUntil, cons_tail_support]

中文:
引理 length_dropUntil_lt_length
  条件: {u v w : V} {p : G.途径 v w} (h : u in p.support) (huv : u != v)
  证明: by
  grind [length_dropUntil, cons_tail_support]

Depends on / 依赖: cons_tail_support, length_dropUntil
-/
lemma length_dropUntil_lt_length {u v w : V} {p : G.Walk v w} (h : u in p.support) (huv : u != v) :
    (p.dropUntil u h).length < p.length := by
  grind [length_dropUntil, cons_tail_support]

/--
lemma `takeUntil_takeUntil` / 引理 `takeUntil_takeUntil`

English:
lemma takeUntil_takeUntil
  statement: {w x : V} (p : G.Walk u v) (hw : w in p.support)
  proof: by
  simp_rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx, take_spec]

中文:
引理 takeUntil_takeUntil
  结论: {w x : V} (p : G.途径 u v) (hw : w in p.support)
  证明: by
  simp_rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx, take_spec]

Depends on / 依赖: dropUntil, p.dropUntil, simp_rw, takeUntil_append_of_mem_left, take_spec
-/
lemma takeUntil_takeUntil {w x : V} (p : G.Walk u v) (hw : w in p.support)
    (hx : x in (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx =
      p.takeUntil x (p.support_takeUntil_subset_support hw hx) := by
  simp_rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx, take_spec]

/--
lemma `notMem_support_takeUntil_support_takeUntil_subset` / 引理 `notMem_support_takeUntil_support_takeUntil_subset`

English:
lemma notMem_support_takeUntil_support_takeUntil_subset
  statement: {p : G.Walk u v} {x : V} (h : x != w)
  proof: by
  rw [← takeUntil_takeUntil p hw hx]
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt_length _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w 

中文:
引理 notMem_support_takeUntil_support_takeUntil_subset
  结论: {p : G.途径 u v} {x : V} (h : x != w)
  证明: by
  rw [← takeUntil_takeUntil p hw hx]
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt_length _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w 

Depends on / 依赖: h.symm, length, length_takeUntil_lt_length, p.takeUntil, takeUntil, takeUntil_takeUntil
-/
lemma notMem_support_takeUntil_support_takeUntil_subset {p : G.Walk u v} {x : V} (h : x != w)
    (hw : w in p.support) (hx : x in (p.takeUntil w hw).support) :
    w ∉ (p.takeUntil x (p.support_takeUntil_subset_support hw hx)).support := by
  rw [← takeUntil_takeUntil p hw hx]
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt_length _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w hw).length := by
    exact length_takeUntil_lt_length _ h
  simp only [takeUntil_takeUntil] at h1 h2
  lia

/--
Definition of `rotate` / `rotate` 的定义

English:
definition rotate
  signature: (c : G.Walk v v) (u : V) (h : u in c.support)
  body: (c.dropUntil u h).append (c.takeUntil u h)

@[simp]

中文:
定义 rotate
  签名: (c : G.途径 v v) (u : V) (h : u in c.support)
  定义体: (c.dropUntil u h).append (c.takeUntil u h)

@[simp]

Depends on / 依赖: append, c.dropUntil, c.takeUntil, dropUntil, takeUntil
-/
def rotate (c : G.Walk v v) (u : V) (h : u in c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
/--
theorem `support_rotate` / 定理 `support_rotate`

English:
theorem support_rotate
  given: (c : G.Walk v v) (u : V) (h)
  proof: by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append]; rw [take_spec]

@[simp]

中文:
定理 support_rotate
  条件: (c : G.途径 v v) (u : V) (h)
  证明: by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append]; rw [take_spec]

@[simp]

Depends on / 依赖: IsRotated, List.IsRotated.trans, List.isRotated_append, isRotated_append, rotate, tail_support_append, take_spec
-/
theorem support_rotate (c : G.Walk v v) (u : V) (h) :
    (c.rotate u h).support.tail ~r c.support.tail := by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append]; rw [take_spec]

@[simp]
/--
theorem `mem_support_rotate_iff` / 定理 `mem_support_rotate_iff`

English:
theorem mem_support_rotate_iff
  given: (c : G.Walk v v) (u : V) (h)
  proof: by
  grind [rotate, take_spec, mem_support_append_iff]

中文:
定理 mem_support_rotate_iff
  条件: (c : G.途径 v v) (u : V) (h)
  证明: by
  grind [rotate, take_spec, mem_support_append_iff]

Depends on / 依赖: mem_support_append_iff, rotate, take_spec
-/
theorem mem_support_rotate_iff (c : G.Walk v v) (u : V) (h) :
    w in (c.rotate u h).support ↔ w in c.support := by
  grind [rotate, take_spec, mem_support_append_iff]

/--
theorem `rotate_darts` / 定理 `rotate_darts`

English:
theorem rotate_darts
  given: (c : G.Walk v v) (u : V) (h)
  statement: (c.rotate u h).darts ~r c.darts
  proof: by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append]; rw [take_spec]

中文:
定理 rotate_darts
  条件: (c : G.途径 v v) (u : V) (h)
  结论: (c.rotate u h).darts ~r c.darts
  证明: by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append]; rw [take_spec]

Depends on / 依赖: IsRotated, List.IsRotated.trans, List.isRotated_append, darts_append, isRotated_append, rotate, take_spec
-/
theorem rotate_darts (c : G.Walk v v) (u : V) (h) : (c.rotate u h).darts ~r c.darts := by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append]; rw [take_spec]

/--
theorem `rotate_edges` / 定理 `rotate_edges`

English:
theorem rotate_edges
  given: (c : G.Walk v v) (u : V) (h)
  statement: (c.rotate u h).edges ~r c.edges
  proof: (rotate_darts c u h).map _

中文:
定理 rotate_edges
  条件: (c : G.途径 v v) (u : V) (h)
  结论: (c.rotate u h).edges ~r c.edges
  证明: (rotate_darts c u h).map _

Depends on / 依赖: rotate_darts
-/
theorem rotate_edges (c : G.Walk v v) (u : V) (h) : (c.rotate u h).edges ~r c.edges :=
  (rotate_darts c u h).map _

/--
lemma `length_rotate` / 引理 `length_rotate`

English:
lemma length_rotate
  given: (c : G.Walk v v) (u : V) (h)
  statement: (c.rotate u h).length = c.length
  proof: by
  simpa using (rotate_edges c u h).perm.length_eq

@[simp]

中文:
引理 length_rotate
  条件: (c : G.途径 v v) (u : V) (h)
  结论: (c.rotate u h).length = c.length
  证明: by
  simpa using (rotate_edges c u h).perm.length_eq

@[simp]
-/
@[simp] lemma length_rotate (c : G.Walk v v) (u : V) (h) : (c.rotate u h).length = c.length := by
  simpa using (rotate_edges c u h).perm.length_eq

@[simp]
/--
theorem `nil_rotate` / 定理 `nil_rotate`

English:
theorem nil_rotate
  given: {c : G.Walk v v} (h)
  statement: (c.rotate u h).Nil ↔ c.Nil
  proof: by
  simp [← length_eq_zero_iff]

@[deprecated nil_rotate (since := "2026-05-11")]

中文:
定理 nil_rotate
  条件: {c : G.途径 v v} (h)
  结论: (c.rotate u h).Nil ↔ c.Nil
  证明: by
  simp [← length_eq_zero_iff]

@[deprecated nil_rotate (since := "2026-05-11")]

Depends on / 依赖: length_eq_zero_iff
-/
theorem nil_rotate {c : G.Walk v v} (h) : (c.rotate u h).Nil ↔ c.Nil := by
  simp [← length_eq_zero_iff]

@[deprecated nil_rotate (since := "2026-05-11")]
/--
lemma `rotate_eq_nil` / 引理 `rotate_eq_nil`

English:
lemma rotate_eq_nil
  given: {c : G.Walk v v} (h)
  statement: c.rotate u h = nil ↔ c = nil
  proof: by simp

中文:
引理 rotate_eq_nil
  条件: {c : G.途径 v v} (h)
  结论: c.rotate u h = nil ↔ c = nil
  证明: by simp
-/
lemma rotate_eq_nil {c : G.Walk v v} (h) : c.rotate u h = nil ↔ c = nil := by simp

end WalkDecomp

/--
theorem `mem_support_iff_exists_getVert` / 定理 `mem_support_iff_exists_getVert`

English:
theorem mem_support_iff_exists_getVert
  given: {u v w : V} {p : G.Walk v w}
  proof: by
  classical
  exact Iff.intro
    (fun h => ⟨_, p.getVert_length_takeUntil h, p.length_takeUntil_le_length h⟩)
    (fun ⟨_, h, _⟩ => h ▸ getVert_mem_support _ _)

中文:
定理 mem_support_iff_存在_getVert
  条件: {u v w : V} {p : G.途径 v w}
  证明: by
  classical
  exact Iff.intro
    (fun h => ⟨_, p.getVert_length_takeUntil h, p.length_takeUntil_le_length h⟩)
    (fun ⟨_, h, _⟩ => h ▸ getVert_mem_support _ _)

Depends on / 依赖: Iff.intro, classical, getVert_length_takeUntil, getVert_mem_support, length_takeUntil_le_length, p.getVert_length_takeUntil, p.length_takeUntil_le_length
-/
theorem mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} :
    u in p.support ↔ exists n, p.getVert n = u ∧ n <= p.length := by
  classical
  exact Iff.intro
    (fun h => ⟨_, p.getVert_length_takeUntil h, p.length_takeUntil_le_length h⟩)
    (fun ⟨_, h, _⟩ => h ▸ getVert_mem_support _ _)

end SimpleGraph.Walk
