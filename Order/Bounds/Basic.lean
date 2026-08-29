/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.BoundedOrder.Monotone
public import Mathlib.Order.Interval.Set.Basic

/-!
# Upper / lower bounds

In this file we prove various lemmas about upper/lower bounds of a set:
monotonicity, behaviour under `∪`, `∩`, `insert`,
and provide formulas for `∅`, `univ`, and intervals.
-/

@[expose] public section

open Function Set

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section

variable [Preorder α] {s t u : Set α} {a b : α}

@[to_dual]
/--
theorem `mem_upperBounds` / 定理 `mem_upperBounds`

English:
theorem mem_upperBounds
  statement: a in upperBounds s ↔ forall x in s, x <= a
  proof: Iff.rfl

@[to_dual]

中文:
定理 mem_upperBounds
  结论: a in upperBounds s ↔ 对任意 x in s, x <= a
  证明: Iff.rfl

@[to_dual]

Depends on / 依赖: Iff.rfl
-/
theorem mem_upperBounds : a in upperBounds s ↔ forall x in s, x <= a :=
  Iff.rfl

@[to_dual]
/--
lemma `mem_upperBounds_iff_subset_Iic` / 引理 `mem_upperBounds_iff_subset_Iic`

English:
lemma mem_upperBounds_iff_subset_Iic
  statement: a in upperBounds s ↔ s subseteq Iic a
  proof: Iff.rfl

@[to_dual]

中文:
引理 mem_upperBounds_iff_subset_Iic
  结论: a in upperBounds s ↔ s subseteq Iic a
  证明: Iff.rfl

@[to_dual]

Depends on / 依赖: Iff.rfl
-/
lemma mem_upperBounds_iff_subset_Iic : a in upperBounds s ↔ s subseteq Iic a := Iff.rfl

@[to_dual]
/--
theorem `bddAbove_def` / 定理 `bddAbove_def`

English:
theorem bddAbove_def
  statement: BddAbove s ↔ exists x, forall y in s, y <= x
  proof: Iff.rfl

@[to_dual]

中文:
定理 bddAbove_def
  结论: BddAbove s ↔ 存在 x, 对任意 y in s, y <= x
  证明: Iff.rfl

@[to_dual]

Depends on / 依赖: Iff.rfl
-/
theorem bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= x :=
  Iff.rfl

@[to_dual]
/--
theorem `top_mem_upperBounds` / 定理 `top_mem_upperBounds`

English:
theorem top_mem_upperBounds
  given: [OrderTop α] (s : Set α)
  statement: ⊤ in upperBounds s
  proof: fun _ _ => le_top

@[to_dual (attr := simp)]

中文:
定理 top_mem_upperBounds
  条件: [OrderTop α] (s : Set α)
  结论: ⊤ in upperBounds s
  证明: fun _ _ => le_top

@[to_dual (attr := simp)]

Depends on / 依赖: le_top
-/
theorem top_mem_upperBounds [OrderTop α] (s : Set α) : ⊤ in upperBounds s := fun _ _ => le_top

@[to_dual (attr := simp)]
/--
theorem `isLeast_bot_iff` / 定理 `isLeast_bot_iff`

English:
theorem isLeast_bot_iff
  given: [OrderBot α]
  statement: IsLeast s ⊥ ↔ ⊥ in s
  proof: and_iff_left bot_mem_lowerBounds _

中文:
定理 isLeast_bot_iff
  条件: [OrderBot α]
  结论: IsLeast s ⊥ ↔ ⊥ in s
  证明: and_iff_left bot_mem_lowerBounds _

Depends on / 依赖: and_iff_left, bot_mem_lowerBounds
-/
theorem isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ in s :=
and_iff_left bot_mem_lowerBounds _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bddAbove_iff`. -/
@[to_dual
/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bddBelow_iff`. -/]
/--
theorem `not_bddAbove_iff'` / 定理 `not_bddAbove_iff'`

English:
theorem not_bddAbove_iff'
  statement: ¬BddAbove s ↔ forall x, exists y in s, ¬y <= x
  proof: by
  simp [BddAbove, upperBounds, Set.Nonempty]

中文:
定理 not_bddAbove_iff'
  结论: ¬BddAbove s ↔ 对任意 x, 存在 y in s, ¬y <= x
  证明: by
  simp [BddAbove, upperBounds, Set.Nonempty]

Depends on / 依赖: BddAbove, Nonempty, Set.Nonempty, upperBounds
-/
theorem not_bddAbove_iff' : ¬BddAbove s ↔ forall x, exists y in s, ¬y <= x := by
  simp [BddAbove, upperBounds, Set.Nonempty]

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bddAbove_iff'`. -/
@[to_dual
/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bddBelow_iff'`. -/]
/--
theorem `not_bddAbove_iff` / 定理 `not_bddAbove_iff`

English:
theorem not_bddAbove_iff
  given: {α : Type*} [LinearOrder α] {s : Set α}
  proof: by
  simp only [not_bddAbove_iff', not_le]

@[to_dual (attr := simp)]

中文:
定理 not_bddAbove_iff
  条件: {α : 类型} [LinearOrder α] {s : Set α}
  证明: by
  simp only [not_bddAbove_iff', not_le]

@[to_dual (attr := simp)]

Depends on / 依赖: not_bddAbove_iff, not_le
-/
theorem not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddAbove s ↔ forall x, exists y in s, x < y := by
  simp only [not_bddAbove_iff', not_le]

@[to_dual (attr := simp)]
/--
lemma `bddAbove_preimage_ofDual` / 引理 `bddAbove_preimage_ofDual`

English:
lemma bddAbove_preimage_ofDual
  given: {s : Set α}
  statement: BddAbove (ofDual ⁻¹' s) ↔ BddBelow s
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
引理 bddAbove_preimage_ofDual
  条件: {s : Set α}
  结论: BddAbove (ofDual ⁻¹' s) ↔ BddBelow s
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
lemma bddAbove_preimage_ofDual {s : Set α} : BddAbove (ofDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[to_dual (attr := simp)]
/--
lemma `bddAbove_preimage_toDual` / 引理 `bddAbove_preimage_toDual`

English:
lemma bddAbove_preimage_toDual
  given: {s : Set αᵒᵈ}
  statement: BddAbove (toDual ⁻¹' s) ↔ BddBelow s
  proof: Iff.rfl

@[to_dual]

中文:
引理 bddAbove_preimage_toDual
  条件: {s : Set αᵒᵈ}
  结论: BddAbove (toDual ⁻¹' s) ↔ BddBelow s
  证明: Iff.rfl

@[to_dual]

Depends on / 依赖: Iff.rfl
-/
lemma bddAbove_preimage_toDual {s : Set αᵒᵈ} : BddAbove (toDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[to_dual]
/--
theorem `BddAbove.dual` / 定理 `BddAbove.dual`

English:
theorem BddAbove.dual
  given: (h : BddAbove s)
  statement: BddBelow (ofDual ⁻¹' s)
  proof: h

@[to_dual]

中文:
定理 BddAbove.dual
  条件: (h : BddAbove s)
  结论: BddBelow (ofDual ⁻¹' s)
  证明: h

@[to_dual]
-/
theorem BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s) :=
  h

@[to_dual]
/--
theorem `IsLeast.dual` / 定理 `IsLeast.dual`

English:
theorem IsLeast.dual
  given: (h : IsLeast s a)
  statement: IsGreatest (ofDual ⁻¹' s) (toDual a)
  proof: h

@[to_dual]

中文:
定理 IsLeast.dual
  条件: (h : IsLeast s a)
  结论: IsGreatest (ofDual ⁻¹' s) (toDual a)
  证明: h

@[to_dual]
-/
theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (ofDual ⁻¹' s) (toDual a) :=
  h

@[to_dual]
/--
theorem `IsLUB.dual` / 定理 `IsLUB.dual`

English:
theorem IsLUB.dual
  given: (h : IsLUB s a)
  statement: IsGLB (ofDual ⁻¹' s) (toDual a)
  proof: h

中文:
定理 IsLUB.dual
  条件: (h : IsLUB s a)
  结论: IsGLB (ofDual ⁻¹' s) (toDual a)
  证明: h
-/
theorem IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a) :=
  h

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
@[to_dual
/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/]
/--
Definition of `IsLeast.orderBot` / `IsLeast.orderBot` 的定义

English:
abbreviation IsLeast.orderBot
  signature: (h : IsLeast s a)
  body: ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

@[to_dual]

中文:
缩写 IsLeast.orderBot
  签名: (h : IsLeast s a)
  定义体: ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

@[to_dual]
-/
abbrev IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

@[to_dual]
/--
theorem `isLUB_congr` / 定理 `isLUB_congr`

English:
theorem isLUB_congr
  given: (h : upperBounds s = upperBounds t)
  statement: IsLUB s a ↔ IsLUB t a
  proof: by
  rw [IsLUB]; rw [IsLUB]; rw [h]

@[to_dual (attr := simp)]

中文:
定理 isLUB_congr
  条件: (h : upperBounds s = upperBounds t)
  结论: IsLUB s a ↔ IsLUB t a
  证明: by
  rw [IsLUB]; rw [IsLUB]; rw [h]

@[to_dual (attr := simp)]
-/
theorem isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a ↔ IsLUB t a := by
  rw [IsLUB]; rw [IsLUB]; rw [h]

@[to_dual (attr := simp)]
/--
lemma `IsCofinalFor.of_subset` / 引理 `IsCofinalFor.of_subset`

English:
lemma IsCofinalFor.of_subset
  given: (hst : s subseteq t)
  statement: IsCofinalFor s t
  proof: fun a ha => ⟨a, hst ha, le_rfl⟩

@[to_dual]
alias LE.le.isCofinalFor := IsCofinalFor.of_subset

@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCofinalFor := LE.le.isCofinalFor
@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCoinitialFor := LE.le.isCoinitialFor

@[depre

中文:
引理 IsCofinalFor.of_subset
  条件: (hst : s subseteq t)
  结论: IsCofinalFor s t
  证明: fun a ha => ⟨a, hst ha, le_rfl⟩

@[to_dual]
alias LE.le.isCofinalFor := IsCofinalFor.of_subset

@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCofinalFor := LE.le.isCofinalFor
@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCoinitialFor := LE.le.isCoinitialFor

@[depre

Depends on / 依赖: le_rfl
-/
lemma IsCofinalFor.of_subset (hst : s subseteq t) : IsCofinalFor s t :=
  fun a ha => ⟨a, hst ha, le_rfl⟩

@[to_dual]
alias LE.le.isCofinalFor := IsCofinalFor.of_subset

@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCofinalFor := LE.le.isCofinalFor
@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCoinitialFor := LE.le.isCoinitialFor

@[deprecated LE.le.isCofinalFor (since := "2026-01-08")]
alias HasSubset.Subset.iscofinalfor := IsCofinalFor.of_subset
@[deprecated LE.le.isCoinitialFor (since := "2026-01-08")]
alias HasSubset.Subset.iscoinitialfor := IsCoinitialFor.of_subset

@[to_dual (attr := refl)]
/--
lemma `IsCofinalFor.rfl` / 引理 `IsCofinalFor.rfl`

English:
lemma IsCofinalFor.rfl
  statement: IsCofinalFor s s
  proof: .of_subset .rfl

@[to_dual]

中文:
引理 IsCofinalFor.rfl
  结论: IsCofinalFor s s
  证明: .of_subset .rfl

@[to_dual]
-/
protected lemma IsCofinalFor.rfl : IsCofinalFor s s := .of_subset .rfl

@[to_dual]
/--
lemma `IsCofinalFor.trans` / 引理 `IsCofinalFor.trans`

English:
lemma IsCofinalFor.trans
  given: (hst : IsCofinalFor s t) (htu : IsCofinalFor t u)
  proof: fun _a ha => let ⟨_b, hb, hab⟩ := hst ha; let ⟨c, hc, hbc⟩ := htu hb; ⟨c, hc, hab.trans hbc⟩

@[to_dual]

中文:
引理 IsCofinalFor.trans
  条件: (hst : IsCofinalFor s t) (htu : IsCofinalFor t u)
  证明: fun _a ha => let ⟨_b, hb, hab⟩ := hst ha; let ⟨c, hc, hbc⟩ := htu hb; ⟨c, hc, hab.trans hbc⟩

@[to_dual]
-/
protected lemma IsCofinalFor.trans (hst : IsCofinalFor s t) (htu : IsCofinalFor t u) :
    IsCofinalFor s u :=
  fun _a ha => let ⟨_b, hb, hab⟩ := hst ha; let ⟨c, hc, hbc⟩ := htu hb; ⟨c, hc, hab.trans hbc⟩

@[to_dual]
/--
lemma `IsCofinalFor.mono_left` / 引理 `IsCofinalFor.mono_left`

English:
lemma IsCofinalFor.mono_left
  given: (hst : s subseteq t) (htu : IsCofinalFor t u)
  proof: hst.isCofinalFor.trans htu

@[to_dual]

中文:
引理 IsCofinalFor.mono_left
  条件: (hst : s subseteq t) (htu : IsCofinalFor t u)
  证明: hst.isCofinalFor.trans htu

@[to_dual]
-/
protected lemma IsCofinalFor.mono_left (hst : s subseteq t) (htu : IsCofinalFor t u) :
    IsCofinalFor s u := hst.isCofinalFor.trans htu

@[to_dual]
/--
lemma `IsCofinalFor.mono_right` / 引理 `IsCofinalFor.mono_right`

English:
lemma IsCofinalFor.mono_right
  given: (htu : t subseteq u) (hst : IsCofinalFor s t)
  proof: hst.trans htu.isCofinalFor

中文:
引理 IsCofinalFor.mono_right
  条件: (htu : t subseteq u) (hst : IsCofinalFor s t)
  证明: hst.trans htu.isCofinalFor
-/
protected lemma IsCofinalFor.mono_right (htu : t subseteq u) (hst : IsCofinalFor s t) :
    IsCofinalFor s u := hst.trans htu.isCofinalFor

/--
lemma `DirectedOn.isCofinalFor_fst_image_prod_snd_image` / 引理 `DirectedOn.isCofinalFor_fst_image_prod_snd_image`

English:
lemma DirectedOn.isCofinalFor_fst_image_prod_snd_image
  statement: {β : Type*} [Preorder β] {s : Set (α × β)}
  proof: by
  rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  exact ⟨z, hz, hxz.1, hyz.2⟩

@[to_dual]

中文:
引理 DirectedOn.isCofinalFor_fst_image_prod_snd_image
  结论: {β : 类型} [Preorder β] {s : Set (α × β)}
  证明: by
  rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  exact ⟨z, hz, hxz.1, hyz.2⟩

@[to_dual]
-/
lemma DirectedOn.isCofinalFor_fst_image_prod_snd_image {β : Type*} [Preorder β] {s : Set (α × β)}
    (hs : DirectedOn (· <= ·) s) : IsCofinalFor ((Prod.fst '' s) ×ˢ (Prod.snd '' s)) s := by
  rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  exact ⟨z, hz, hxz.1, hyz.2⟩

@[to_dual]
/--
lemma `IsCofinalFor.nonempty` / 引理 `IsCofinalFor.nonempty`

English:
lemma IsCofinalFor.nonempty
  given: (h : IsCofinalFor s t) (hs : s.Nonempty)
  statement: t.Nonempty
  proof: let ⟨_, ha⟩ := hs; let ⟨b, hb, _⟩ := h ha; ⟨b, hb⟩

中文:
引理 IsCofinalFor.nonempty
  条件: (h : IsCofinalFor s t) (hs : s.Nonempty)
  结论: t.Nonempty
  证明: let ⟨_, ha⟩ := hs; let ⟨b, hb, _⟩ := h ha; ⟨b, hb⟩
-/
lemma IsCofinalFor.nonempty (h : IsCofinalFor s t) (hs : s.Nonempty) : t.Nonempty :=
  let ⟨_, ha⟩ := hs; let ⟨b, hb, _⟩ := h ha; ⟨b, hb⟩

/--
theorem `IsCofinalFor.union_left` / 定理 `IsCofinalFor.union_left`

English:
theorem IsCofinalFor.union_left
  given: (hc : IsCofinalFor s t)
  statement: IsCofinalFor (s union t) t
  proof: by
  rintro a (has | hat)
  · exact hc has
  · exact ⟨a, hat, le_rfl⟩

中文:
定理 IsCofinalFor.union_left
  条件: (hc : IsCofinalFor s t)
  结论: IsCofinalFor (s union t) t
  证明: by
  rintro a (has | hat)
  · exact hc has
  · exact ⟨a, hat, le_rfl⟩

Depends on / 依赖: le_rfl
-/
theorem IsCofinalFor.union_left (hc : IsCofinalFor s t) : IsCofinalFor (s union t) t := by
  rintro a (has | hat)
  · exact hc has
  · exact ⟨a, hat, le_rfl⟩

/--
theorem `IsCofinalFor.union_right` / 定理 `IsCofinalFor.union_right`

English:
theorem IsCofinalFor.union_right
  given: (hc : IsCofinalFor s t)
  statement: IsCofinalFor (t union s) t
  proof: by
  rw [union_comm]
  exact hc.union_left

中文:
定理 IsCofinalFor.union_right
  条件: (hc : IsCofinalFor s t)
  结论: IsCofinalFor (t union s) t
  证明: by
  rw [union_comm]
  exact hc.union_left

Depends on / 依赖: hc.union_left, union_comm, union_left
-/
theorem IsCofinalFor.union_right (hc : IsCofinalFor s t) : IsCofinalFor (t union s) t := by
  rw [union_comm]
  exact hc.union_left

/--
theorem `DirectedOn.of_isCofinalFor` / 定理 `DirectedOn.of_isCofinalFor`

English:
theorem DirectedOn.of_isCofinalFor
  statement: (hd : DirectedOn (· <= ·) t)
  proof: by
  intro x hx y hy
  obtain ⟨z, hz, hxz, hyz⟩ := hd x (hst hx) y (hst hy)
  obtain ⟨w, hw, hzw⟩ := hc hz
  exact ⟨w, hw, hxz.trans hzw, hyz.trans hzw⟩

中文:
定理 DirectedOn.of_isCofinalFor
  结论: (hd : DirectedOn (· <= ·) t)
  证明: by
  intro x hx y hy
  obtain ⟨z, hz, hxz, hyz⟩ := hd x (hst hx) y (hst hy)
  obtain ⟨w, hw, hzw⟩ := hc hz
  exact ⟨w, hw, hxz.trans hzw, hyz.trans hzw⟩

Depends on / 依赖: hxz.trans, hyz.trans
-/
theorem DirectedOn.of_isCofinalFor (hd : DirectedOn (· <= ·) t)
    (hst : s subseteq t) (hc : IsCofinalFor t s) : DirectedOn (· <= ·) s := by
  intro x hx y hy
  obtain ⟨z, hz, hxz, hyz⟩ := hd x (hst hx) y (hst hy)
  obtain ⟨w, hw, hzw⟩ := hc hz
  exact ⟨w, hw, hxz.trans hzw, hyz.trans hzw⟩

/--
theorem `isCofinalFor_or_isCofinalFor_of_directedOn_union` / 定理 `isCofinalFor_or_isCofinalFor_of_directedOn_union`

English:
theorem isCofinalFor_or_isCofinalFor_of_directedOn_union
  given: (h : DirectedOn (· <= ·) (s union t))
  proof: by
  rw [or_iff_not_imp_left]
  intro hts x hx
  simp only [IsCofinalFor, not_forall, not_exists, not_and] at hts
  obtain ⟨y, hy, hys⟩ := hts
  obtain ⟨z, (hzs | hzt), hxz, hyz⟩ := h x (.inl hx) y (.inr hy)
  · cases hys z hzs hyz
  · exact ⟨z, hzt, hxz⟩

中文:
定理 isCofinalFor_or_isCofinalFor_of_directedOn_union
  条件: (h : DirectedOn (· <= ·) (s union t))
  证明: by
  rw [or_iff_not_imp_left]
  intro hts x hx
  simp only [IsCofinalFor, not_forall, not_exists, not_and] at hts
  obtain ⟨y, hy, hys⟩ := hts
  obtain ⟨z, (hzs | hzt), hxz, hyz⟩ := h x (.inl hx) y (.inr hy)
  · cases hys z hzs hyz
  · exact ⟨z, hzt, hxz⟩

Depends on / 依赖: IsCofinalFor, not_and, not_exists, not_forall, or_iff_not_imp_left
-/
theorem isCofinalFor_or_isCofinalFor_of_directedOn_union (h : DirectedOn (· <= ·) (s union t)) :
    IsCofinalFor t s ∨ IsCofinalFor s t := by
  rw [or_iff_not_imp_left]
  intro hts x hx
  simp only [IsCofinalFor, not_forall, not_exists, not_and] at hts
  obtain ⟨y, hy, hys⟩ := hts
  obtain ⟨z, (hzs | hzt), hxz, hyz⟩ := h x (.inl hx) y (.inr hy)
  · cases hys z hzs hyz
  · exact ⟨z, hzt, hxz⟩

/--
theorem `directedOn_union_iff` / 定理 `directedOn_union_iff`

English:
theorem directedOn_union_iff
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isCofinalFor_or_isCofinalFor_of_directedOn_union h with hts | hst
    · exact .inl ⟨DirectedOn.of_isCofinalFor h subset_union_left hts.union_right, hts⟩
    · exact .inr ⟨DirectedOn.of_isCofinalFor h subset_union_right hst.union_left, hst⟩
  · rintro (⟨hs, ht

中文:
定理 directedOn_union_iff
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isCofinalFor_or_isCofinalFor_of_directedOn_union h with hts | hst
    · exact .inl ⟨DirectedOn.of_isCofinalFor h subset_union_left hts.union_right, hts⟩
    · exact .inr ⟨DirectedOn.of_isCofinalFor h subset_union_right hst.union_left, hst⟩
  · rintro (⟨hs, ht

Depends on / 依赖: DirectedOn, DirectedOn.of_isCofinalFor, hst.union_left, hts.union_right, isCofinalFor_or_isCofinalFor_of_directedOn_union, of_isCofinalFor, subset_union_left, subset_union_right, union_left, union_right
-/
theorem directedOn_union_iff :
    DirectedOn (· <= ·) (s union t) ↔
      DirectedOn (· <= ·) s ∧ IsCofinalFor t s ∨ DirectedOn (· <= ·) t ∧ IsCofinalFor s t := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases isCofinalFor_or_isCofinalFor_of_directedOn_union h with hts | hst
    · exact .inl ⟨DirectedOn.of_isCofinalFor h subset_union_left hts.union_right, hts⟩
    · exact .inr ⟨DirectedOn.of_isCofinalFor h subset_union_right hst.union_left, hst⟩
  · rintro (⟨hs, hts⟩ | ⟨ht, hst⟩) x hx y hy
    · obtain ⟨x', hx', hxx'⟩ := hts.union_right hx
      obtain ⟨y', hy', hyy'⟩ := hts.union_right hy
      obtain ⟨z, hz, hx'z, hy'z⟩ := hs x' hx' y' hy'
      exact ⟨z, .inl hz, hxx'.trans hx'z, hyy'.trans hy'z⟩
    · obtain ⟨x', hx', hxx'⟩ := hst.union_left hx
      obtain ⟨y', hy', hyy'⟩ := hst.union_left hy
      obtain ⟨z, hz, hx'z, hy'z⟩ := ht x' hx' y' hy'
      exact ⟨z, .inr hz, hxx'.trans hx'z, hyy'.trans hy'z⟩

/--
theorem `directedOn_or_directedOn_of_union` / 定理 `directedOn_or_directedOn_of_union`

English:
theorem directedOn_or_directedOn_of_union
  given: (h : DirectedOn (· <= ·) (s union t))
  proof: by
  rw [directedOn_union_iff] at h
  tauto

中文:
定理 directedOn_or_directedOn_of_union
  条件: (h : DirectedOn (· <= ·) (s union t))
  证明: by
  rw [directedOn_union_iff] at h
  tauto

Depends on / 依赖: directedOn_union_iff
-/
theorem directedOn_or_directedOn_of_union (h : DirectedOn (· <= ·) (s union t)) :
    DirectedOn (· <= ·) s ∨ DirectedOn (· <= ·) t := by
  rw [directedOn_union_iff] at h
  tauto

/--
theorem `directedOn_or_directedOn_of_union'` / 定理 `directedOn_or_directedOn_of_union'`

English:
theorem directedOn_or_directedOn_of_union'
  proof: by
  obtain h | h := directedOn_or_directedOn_of_union h
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · aesop
    · exact .inl ⟨h, hs⟩
  · obtain rfl | ht := t.eq_empty_or_nonempty
    · aesop
    · exact .inr ⟨h, ht⟩

中文:
定理 directedOn_or_directedOn_of_union'
  证明: by
  obtain h | h := directedOn_or_directedOn_of_union h
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · aesop
    · exact .inl ⟨h, hs⟩
  · obtain rfl | ht := t.eq_empty_or_nonempty
    · aesop
    · exact .inr ⟨h, ht⟩

Depends on / 依赖: directedOn_or_directedOn_of_union, eq_empty_or_nonempty, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty
-/
theorem directedOn_or_directedOn_of_union'
    (hn : (s union t).Nonempty) (h : DirectedOn (· <= ·) (s union t)) :
    DirectedOn (· <= ·) s ∧ s.Nonempty ∨ DirectedOn (· <= ·) t ∧ t.Nonempty := by
  obtain h | h := directedOn_or_directedOn_of_union h
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · aesop
    · exact .inl ⟨h, hs⟩
  · obtain rfl | ht := t.eq_empty_or_nonempty
    · aesop
    · exact .inr ⟨h, ht⟩

/-!
### Monotonicity
-/


@[to_dual]
/--
theorem `upperBounds_mono_set` / 定理 `upperBounds_mono_set`

English:
theorem upperBounds_mono_set
  given: ⦃s t
  statement: Set α⦄ (hst : s subseteq t) : upperBounds t subseteq upperBounds s
  proof: fun _ hb _ h => hb hst h

@[to_dual (attr := gcongr)]

中文:
定理 upperBounds_mono_set
  条件: ⦃s t
  结论: Set α⦄ (hst : s subseteq t) : upperBounds t subseteq upperBounds s
  证明: fun _ hb _ h => hb hst h

@[to_dual (attr := gcongr)]
-/
theorem upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subseteq t) : upperBounds t subseteq upperBounds s :=
fun _ hb _ h => hb hst h

@[to_dual (attr := gcongr)]
/--
lemma `upperBounds_mono_of_isCofinalFor` / 引理 `upperBounds_mono_of_isCofinalFor`

English:
lemma upperBounds_mono_of_isCofinalFor
  given: (hst : IsCofinalFor s t)
  statement: upperBounds t subseteq upperBounds s
  proof: fun _a ha _b hb => let ⟨_c, hc, hbc⟩ := hst hb; hbc.trans (ha hc)

@[to_dual]

中文:
引理 upperBounds_mono_of_isCofinalFor
  条件: (hst : IsCofinalFor s t)
  结论: upperBounds t subseteq upperBounds s
  证明: fun _a ha _b hb => let ⟨_c, hc, hbc⟩ := hst hb; hbc.trans (ha hc)

@[to_dual]

Depends on / 依赖: hbc.trans
-/
lemma upperBounds_mono_of_isCofinalFor (hst : IsCofinalFor s t) : upperBounds t subseteq upperBounds s :=
  fun _a ha _b hb => let ⟨_c, hc, hbc⟩ := hst hb; hbc.trans (ha hc)

@[to_dual]
/--
theorem `upperBounds_mono_mem` / 定理 `upperBounds_mono_mem`

English:
theorem upperBounds_mono_mem
  given: ⦃a b⦄ (hab : a <= b)
  statement: a in upperBounds s -> b in upperBounds s
  proof: fun ha _ h => le_trans (ha h) hab

@[to_dual]

中文:
定理 upperBounds_mono_mem
  条件: ⦃a b⦄ (hab : a <= b)
  结论: a in upperBounds s -> b in upperBounds s
  证明: fun ha _ h => le_trans (ha h) hab

@[to_dual]

Depends on / 依赖: le_trans
-/
theorem upperBounds_mono_mem ⦃a b⦄ (hab : a <= b) : a in upperBounds s -> b in upperBounds s :=
  fun ha _ h => le_trans (ha h) hab

@[to_dual]
/--
theorem `upperBounds_mono` / 定理 `upperBounds_mono`

English:
theorem upperBounds_mono
  given: ⦃s t
  statement: Set α⦄ (hst : s subseteq t) ⦃a b⦄ (hab : a <= b) :
  proof: fun ha =>
upperBounds_mono_set hst upperBounds_mono_mem hab ha

中文:
定理 upperBounds_mono
  条件: ⦃s t
  结论: Set α⦄ (hst : s subseteq t) ⦃a b⦄ (hab : a <= b) :
  证明: fun ha =>
upperBounds_mono_set hst upperBounds_mono_mem hab ha
-/
theorem upperBounds_mono ⦃s t : Set α⦄ (hst : s subseteq t) ⦃a b⦄ (hab : a <= b) :
    a in upperBounds t -> b in upperBounds s := fun ha =>
upperBounds_mono_set hst upperBounds_mono_mem hab ha

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
@[to_dual (attr := gcongr) /-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/]
/--
theorem `BddAbove.mono` / 定理 `BddAbove.mono`

English:
theorem BddAbove.mono
  given: ⦃s t
  statement: Set α⦄ (h : s subseteq t) : BddAbove t -> BddAbove s
  proof: Nonempty.mono upperBounds_mono_set h

中文:
定理 BddAbove.mono
  条件: ⦃s t
  结论: Set α⦄ (h : s subseteq t) : BddAbove t -> BddAbove s
  证明: Nonempty.mono upperBounds_mono_set h

Depends on / 依赖: Nonempty, Nonempty.mono, upperBounds_mono_set
-/
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove t -> BddAbove s :=
Nonempty.mono upperBounds_mono_set h

/-- If the range of a function `g` is bounded above, then `g ∘ f` is bounded above for all functions
`f`. -/
@[to_dual /-- If the range of a function `g` is bounded below, then `g ∘ f` is bounded below for all
functions `f`. -/]
/--
theorem `BddAbove.range_comp_right` / 定理 `BddAbove.range_comp_right`

English:
theorem BddAbove.range_comp_right
  statement: (f : γ -> β) {g : β -> α}
  proof: hg.mono (range_comp_subset_range f g)

中文:
定理 BddAbove.range_comp_right
  结论: (f : γ -> β) {g : β -> α}
  证明: hg.mono (range_comp_subset_range f g)

Depends on / 依赖: hg.mono, range_comp_subset_range
-/
theorem BddAbove.range_comp_right (f : γ -> β) {g : β -> α}
    (hg : BddAbove (Set.range g)) : BddAbove (Set.range (g ∘ f)) :=
  hg.mono (range_comp_subset_range f g)

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
@[to_dual /-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower
bound for any set `t`, `s ⊆ t ⊆ p`. -/]
/--
theorem `IsLUB.of_subset_of_superset` / 定理 `IsLUB.of_subset_of_superset`

English:
theorem IsLUB.of_subset_of_superset
  statement: {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s subseteq t)
  proof: ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩

中文:
定理 IsLUB.of_subset_of_superset
  结论: {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s subseteq t)
  证明: ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩

Depends on / 依赖: lowerBounds_mono_set, upperBounds_mono_set
-/
theorem IsLUB.of_subset_of_superset {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s subseteq t)
    (htp : t subseteq p) : IsLUB t a :=
  ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩

/-- The least upper bound of a set is also the least upper bound of any cofinal subset. -/
@[to_dual /-- The greatest lower bound of a set is also the greatest lower bound of any
coinitial subset. -/]
/--
theorem `IsLUB.of_isCofinalFor` / 定理 `IsLUB.of_isCofinalFor`

English:
theorem IsLUB.of_isCofinalFor
  statement: {s t : Set α} (hs : IsLUB s a) (hts : t subseteq s)
  proof: ⟨upperBounds_mono_set hts hs.1, fun _b hb => hs.2 (upperBounds_mono_of_isCofinalFor hst hb)⟩

@[to_dual]

中文:
定理 IsLUB.of_isCofinalFor
  结论: {s t : Set α} (hs : IsLUB s a) (hts : t subseteq s)
  证明: ⟨upperBounds_mono_set hts hs.1, fun _b hb => hs.2 (upperBounds_mono_of_isCofinalFor hst hb)⟩

@[to_dual]

Depends on / 依赖: upperBounds_mono_of_isCofinalFor, upperBounds_mono_set
-/
theorem IsLUB.of_isCofinalFor {s t : Set α} (hs : IsLUB s a) (hts : t subseteq s)
    (hst : IsCofinalFor s t) : IsLUB t a :=
  ⟨upperBounds_mono_set hts hs.1, fun _b hb => hs.2 (upperBounds_mono_of_isCofinalFor hst hb)⟩

@[to_dual]
/--
theorem `IsLeast.mono` / 定理 `IsLeast.mono`

English:
theorem IsLeast.mono
  given: (ha : IsLeast s a) (hb : IsLeast t b) (hst : s subseteq t)
  statement: b <= a
  proof: hb.2 (hst ha.1)

@[to_dual]

中文:
定理 IsLeast.mono
  条件: (ha : IsLeast s a) (hb : IsLeast t b) (hst : s subseteq t)
  结论: b <= a
  证明: hb.2 (hst ha.1)

@[to_dual]
-/
theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s subseteq t) : b <= a :=
  hb.2 (hst ha.1)

@[to_dual]
/--
theorem `IsLUB.mono` / 定理 `IsLUB.mono`

English:
theorem IsLUB.mono
  given: (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subseteq t)
  statement: a <= b
  proof: IsLeast.mono hb ha upperBounds_mono_set hst

@[to_dual]

中文:
定理 IsLUB.mono
  条件: (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subseteq t)
  结论: a <= b
  证明: IsLeast.mono hb ha upperBounds_mono_set hst

@[to_dual]

Depends on / 依赖: IsLeast, IsLeast.mono, upperBounds_mono_set
-/
theorem IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subseteq t) : a <= b :=
IsLeast.mono hb ha upperBounds_mono_set hst

@[to_dual]
/--
theorem `subset_lowerBounds_upperBounds` / 定理 `subset_lowerBounds_upperBounds`

English:
theorem subset_lowerBounds_upperBounds
  given: (s : Set α)
  statement: s subseteq lowerBounds (upperBounds s)
  proof: fun _ hx _ hy => hy hx

@[to_dual]

中文:
定理 subset_lowerBounds_upperBounds
  条件: (s : Set α)
  结论: s subseteq lowerBounds (upperBounds s)
  证明: fun _ hx _ hy => hy hx

@[to_dual]
-/
theorem subset_lowerBounds_upperBounds (s : Set α) : s subseteq lowerBounds (upperBounds s) :=
  fun _ hx _ hy => hy hx

@[to_dual]
/--
theorem `Set.Nonempty.bddAbove_lowerBounds` / 定理 `Set.Nonempty.bddAbove_lowerBounds`

English:
theorem Set.Nonempty.bddAbove_lowerBounds
  given: (hs : s.Nonempty)
  statement: BddAbove (lowerBounds s)
  proof: hs.mono (subset_upperBounds_lowerBounds s)

中文:
定理 Set.Nonempty.bddAbove_lowerBounds
  条件: (hs : s.Nonempty)
  结论: BddAbove (lowerBounds s)
  证明: hs.mono (subset_upperBounds_lowerBounds s)

Depends on / 依赖: hs.mono, subset_upperBounds_lowerBounds
-/
theorem Set.Nonempty.bddAbove_lowerBounds (hs : s.Nonempty) : BddAbove (lowerBounds s) :=
  hs.mono (subset_upperBounds_lowerBounds s)

/-!
### Conversions
-/


@[to_dual]
/--
theorem `IsLeast.isGLB` / 定理 `IsLeast.isGLB`

English:
theorem IsLeast.isGLB
  given: (h : IsLeast s a)
  statement: IsGLB s a
  proof: ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual]

中文:
定理 IsLeast.isGLB
  条件: (h : IsLeast s a)
  结论: IsGLB s a
  证明: ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual]
-/
theorem IsLeast.isGLB (h : IsLeast s a) : IsGLB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual]
/--
theorem `IsLUB.upperBounds_eq` / 定理 `IsLUB.upperBounds_eq`

English:
theorem IsLUB.upperBounds_eq
  given: (h : IsLUB s a)
  statement: upperBounds s = Ici a
  proof: Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩

@[to_dual]

中文:
定理 IsLUB.upperBounds_eq
  条件: (h : IsLUB s a)
  结论: upperBounds s = Ici a
  证明: Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩

@[to_dual]

Depends on / 依赖: Set.ext, upperBounds_mono_mem
-/
theorem IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a :=
  Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩

@[to_dual]
/--
theorem `IsLeast.lowerBounds_eq` / 定理 `IsLeast.lowerBounds_eq`

English:
theorem IsLeast.lowerBounds_eq
  given: (h : IsLeast s a)
  statement: lowerBounds s = Iic a
  proof: h.isGLB.lowerBounds_eq

@[to_dual]

中文:
定理 IsLeast.lowerBounds_eq
  条件: (h : IsLeast s a)
  结论: lowerBounds s = Iic a
  证明: h.isGLB.lowerBounds_eq

@[to_dual]

Depends on / 依赖: h.isGLB.lowerBounds_eq, lowerBounds_eq
-/
theorem IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGLB.lowerBounds_eq

@[to_dual]
/--
theorem `IsGreatest.lt_iff` / 定理 `IsGreatest.lt_iff`

English:
theorem IsGreatest.lt_iff
  given: (h : IsGreatest s a)
  statement: a < b ↔ forall x in s, x < b
  proof: ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

@[to_dual le_isGLB_iff]

中文:
定理 IsGreatest.lt_iff
  条件: (h : IsGreatest s a)
  结论: a < b ↔ 对任意 x in s, x < b
  证明: ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

@[to_dual le_isGLB_iff]

Depends on / 依赖: trans_lt
-/
theorem IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ forall x in s, x < b :=
  ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

@[to_dual le_isGLB_iff]
/--
theorem `isLUB_le_iff` / 定理 `isLUB_le_iff`

English:
theorem isLUB_le_iff
  given: (h : IsLUB s a)
  statement: a <= b ↔ b in upperBounds s
  proof: by
  rw [h.upperBounds_eq]
  rfl

@[to_dual]

中文:
定理 isLUB_le_iff
  条件: (h : IsLUB s a)
  结论: a <= b ↔ b in upperBounds s
  证明: by
  rw [h.upperBounds_eq]
  rfl

@[to_dual]

Depends on / 依赖: h.upperBounds_eq, upperBounds_eq
-/
theorem isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s := by
  rw [h.upperBounds_eq]
  rfl

@[to_dual]
/--
theorem `isLUB_iff_le_iff` / 定理 `isLUB_iff_le_iff`

English:
theorem isLUB_iff_le_iff
  statement: IsLUB s a ↔ forall b, a <= b ↔ b in upperBounds s
  proof: ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

中文:
定理 isLUB_iff_le_iff
  结论: IsLUB s a ↔ 对任意 b, a <= b ↔ b in upperBounds s
  证明: ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

Depends on / 依赖: isLUB_le_iff, le_rfl
-/
theorem isLUB_iff_le_iff : IsLUB s a ↔ forall b, a <= b ↔ b in upperBounds s :=
  ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

/-- If `s` has a least upper bound, then it is bounded above. -/
@[to_dual /-- If `s` has a greatest lower bound, then it is bounded below. -/]
/--
theorem `IsLUB.bddAbove` / 定理 `IsLUB.bddAbove`

English:
theorem IsLUB.bddAbove
  given: (h : IsLUB s a)
  statement: BddAbove s
  proof: ⟨a, h.1⟩

中文:
定理 IsLUB.bddAbove
  条件: (h : IsLUB s a)
  结论: BddAbove s
  证明: ⟨a, h.1⟩
-/
theorem IsLUB.bddAbove (h : IsLUB s a) : BddAbove s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest element, then it is bounded above. -/
@[to_dual /-- If `s` has a least element, then it is bounded below. -/]
/--
theorem `IsGreatest.bddAbove` / 定理 `IsGreatest.bddAbove`

English:
theorem IsGreatest.bddAbove
  given: (h : IsGreatest s a)
  statement: BddAbove s
  proof: ⟨a, h.2⟩

@[to_dual]

中文:
定理 IsGreatest.bddAbove
  条件: (h : IsGreatest s a)
  结论: BddAbove s
  证明: ⟨a, h.2⟩

@[to_dual]
-/
theorem IsGreatest.bddAbove (h : IsGreatest s a) : BddAbove s :=
  ⟨a, h.2⟩

@[to_dual]
/--
theorem `IsLeast.nonempty` / 定理 `IsLeast.nonempty`

English:
theorem IsLeast.nonempty
  given: (h : IsLeast s a)
  statement: s.Nonempty
  proof: ⟨a, h.1⟩

中文:
定理 IsLeast.nonempty
  条件: (h : IsLeast s a)
  结论: s.Nonempty
  证明: ⟨a, h.1⟩
-/
theorem IsLeast.nonempty (h : IsLeast s a) : s.Nonempty :=
  ⟨a, h.1⟩

/-!
### Union and intersection
-/

@[to_dual (attr := simp)]
/--
theorem `upperBounds_union` / 定理 `upperBounds_union`

English:
theorem upperBounds_union
  statement: upperBounds (s union t) = upperBounds s inter upperBounds t
  proof: Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[to_dual]

中文:
定理 upperBounds_union
  结论: upperBounds (s union t) = upperBounds s inter upperBounds t
  证明: Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[to_dual]

Depends on / 依赖: Or.inl, Or.inr, Subset, Subset.antisymm, antisymm, hx.elim
-/
theorem upperBounds_union : upperBounds (s union t) = upperBounds s inter upperBounds t :=
  Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[to_dual]
/--
theorem `union_upperBounds_subset_upperBounds_inter` / 定理 `union_upperBounds_subset_upperBounds_inter`

English:
theorem union_upperBounds_subset_upperBounds_inter
  proof: union_subset (upperBounds_mono_set inter_subset_left)
    (upperBounds_mono_set inter_subset_right)

@[to_dual]

中文:
定理 union_upperBounds_subset_upperBounds_inter
  证明: union_subset (upperBounds_mono_set inter_subset_left)
    (upperBounds_mono_set inter_subset_right)

@[to_dual]

Depends on / 依赖: inter_subset_left, inter_subset_right, union_subset, upperBounds_mono_set
-/
theorem union_upperBounds_subset_upperBounds_inter :
    upperBounds s union upperBounds t subseteq upperBounds (s inter t) :=
  union_subset (upperBounds_mono_set inter_subset_left)
    (upperBounds_mono_set inter_subset_right)

@[to_dual]
/--
theorem `isLeast_union_iff` / 定理 `isLeast_union_iff`

English:
theorem isLeast_union_iff
  given: {a : α} {s t : Set α}
  proof: by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a in t), and_assoc]

中文:
定理 isLeast_union_iff
  条件: {a : α} {s t : Set α}
  证明: by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a in t), and_assoc]

Depends on / 依赖: IsLeast, and_assoc, and_comm, lowerBounds_union, or_and_right
-/
theorem isLeast_union_iff {a : α} {s t : Set α} :
    IsLeast (s union t) a ↔ IsLeast s a ∧ a in lowerBounds t ∨ a in lowerBounds s ∧ IsLeast t a := by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a in t), and_assoc]

/-- If `s` is bounded, then so is `s ∩ t` -/
@[to_dual /-- If `s` is bounded, then so is `s ∩ t` -/]
/--
theorem `BddAbove.inter_of_left` / 定理 `BddAbove.inter_of_left`

English:
theorem BddAbove.inter_of_left
  given: (h : BddAbove s)
  statement: BddAbove (s inter t)
  proof: h.mono inter_subset_left

中文:
定理 BddAbove.inter_of_left
  条件: (h : BddAbove s)
  结论: BddAbove (s inter t)
  证明: h.mono inter_subset_left

Depends on / 依赖: h.mono, inter_subset_left
-/
theorem BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s inter t) :=
  h.mono inter_subset_left

/-- If `t` is bounded, then so is `s ∩ t` -/
@[to_dual /-- If `t` is bounded, then so is `s ∩ t` -/]
/--
theorem `BddAbove.inter_of_right` / 定理 `BddAbove.inter_of_right`

English:
theorem BddAbove.inter_of_right
  given: (h : BddAbove t)
  statement: BddAbove (s inter t)
  proof: h.mono inter_subset_right

中文:
定理 BddAbove.inter_of_right
  条件: (h : BddAbove t)
  结论: BddAbove (s inter t)
  证明: h.mono inter_subset_right

Depends on / 依赖: h.mono, inter_subset_right
-/
theorem BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s inter t) :=
  h.mono inter_subset_right

/-- In a directed order, the union of bounded above sets is bounded above. -/
@[to_dual /-- In a codirected order, the union of bounded below sets is bounded below. -/]
/--
theorem `BddAbove.union` / 定理 `BddAbove.union`

English:
theorem BddAbove.union
  given: [IsDirectedOrder α] {s t : Set α}
  proof: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove]; rw [upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩

中文:
定理 BddAbove.union
  条件: [IsDirectedOrder α] {s t : Set α}
  证明: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove]; rw [upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩

Depends on / 依赖: BddAbove, exists_ge_ge, upperBounds_mono_mem, upperBounds_union
-/
theorem BddAbove.union [IsDirectedOrder α] {s t : Set α} :
    BddAbove s -> BddAbove t -> BddAbove (s union t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove]; rw [upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩

/-- In a directed order, the union of two sets is bounded above if and only if both sets are. -/
@[to_dual
/-- In a codirected order, the union of two sets is bounded below if and only if both sets are. -/]
/--
theorem `bddAbove_union` / 定理 `bddAbove_union`

English:
theorem bddAbove_union
  given: [IsDirectedOrder α] {s t : Set α}
  proof: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[to_dual]

中文:
定理 bddAbove_union
  条件: [IsDirectedOrder α] {s t : Set α}
  证明: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[to_dual]

Depends on / 依赖: h.mono, subset_union_left, subset_union_right
-/
theorem bddAbove_union [IsDirectedOrder α] {s t : Set α} :
    BddAbove (s union t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[to_dual]
/--
theorem `bbdAbove_range_sup` / 定理 `bbdAbove_range_sup`

English:
theorem bbdAbove_range_sup
  statement: {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
  proof: by
  have ⟨af, haf⟩ := hf
  have ⟨ag, hag⟩ := hg
  exact ⟨af ⊔ ag, fun a ⟨i, ha⟩ => ha ▸ sup_le_sup (haf ⟨i, rfl⟩) (hag ⟨i, rfl⟩)⟩

@[to_dual]

中文:
定理 bbdAbove_range_sup
  结论: {ι : Sort*} {α : 类型} [SemilatticeSup α] {f g : ι -> α}
  证明: by
  have ⟨af, haf⟩ := hf
  have ⟨ag, hag⟩ := hg
  exact ⟨af ⊔ ag, fun a ⟨i, ha⟩ => ha ▸ sup_le_sup (haf ⟨i, rfl⟩) (hag ⟨i, rfl⟩)⟩

@[to_dual]

Depends on / 依赖: sup_le_sup
-/
theorem bbdAbove_range_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
    (hf : BddAbove <| range f) (hg : BddAbove <| range g) :
BddAbove range fun x => f x ⊔ g x := by
  have ⟨af, haf⟩ := hf
  have ⟨ag, hag⟩ := hg
  exact ⟨af ⊔ ag, fun a ⟨i, ha⟩ => ha ▸ sup_le_sup (haf ⟨i, rfl⟩) (hag ⟨i, rfl⟩)⟩

@[to_dual]
/--
theorem `bbdAbove_range_left_of_sup` / 定理 `bbdAbove_range_left_of_sup`

English:
theorem bbdAbove_range_left_of_sup
  statement: {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
  proof: by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ => ha ▸ le_sup_left.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]

中文:
定理 bbdAbove_range_left_of_sup
  结论: {ι : Sort*} {α : 类型} [SemilatticeSup α] {f g : ι -> α}
  证明: by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ => ha ▸ le_sup_left.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]

Depends on / 依赖: le_sup_left, le_sup_left.trans
-/
theorem bbdAbove_range_left_of_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
(h : BddAbove <| range fun x => f x ⊔ g x) : BddAbove range f := by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ => ha ▸ le_sup_left.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]
/--
theorem `bbdAbove_range_right_of_sup` / 定理 `bbdAbove_range_right_of_sup`

English:
theorem bbdAbove_range_right_of_sup
  statement: {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
  proof: by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ => ha ▸ le_sup_right.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]

中文:
定理 bbdAbove_range_right_of_sup
  结论: {ι : Sort*} {α : 类型} [SemilatticeSup α] {f g : ι -> α}
  证明: by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ => ha ▸ le_sup_right.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]

Depends on / 依赖: le_sup_right, le_sup_right.trans
-/
theorem bbdAbove_range_right_of_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
(h : BddAbove <| range fun x => f x ⊔ g x) : BddAbove range g := by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ => ha ▸ le_sup_right.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]
/--
theorem `bbdAbove_range_sup_iff` / 定理 `bbdAbove_range_sup_iff`

English:
theorem bbdAbove_range_sup_iff
  given: {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α}
  proof: ⟨bbdAbove_range_left_of_sup h, bbdAbove_range_right_of_sup h⟩
  mpr := fun ⟨hf, hg⟩ => bbdAbove_range_sup hf hg

中文:
定理 bbdAbove_range_sup_iff
  条件: {ι : Sort*} {α : 类型} [SemilatticeSup α] {f g : ι -> α}
  证明: ⟨bbdAbove_range_left_of_sup h, bbdAbove_range_right_of_sup h⟩
  mpr := fun ⟨hf, hg⟩ => bbdAbove_range_sup hf hg

Depends on / 依赖: bbdAbove_range_left_of_sup, bbdAbove_range_right_of_sup
-/
theorem bbdAbove_range_sup_iff {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> α} :
    BddAbove (range fun x => f x ⊔ g x) ↔ BddAbove (range f) ∧ BddAbove (range g) where
  mp h := ⟨bbdAbove_range_left_of_sup h, bbdAbove_range_right_of_sup h⟩
  mpr := fun ⟨hf, hg⟩ => bbdAbove_range_sup hf hg

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
@[to_dual /-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/]
/--
theorem `IsLUB.union` / 定理 `IsLUB.union`

English:
theorem IsLUB.union
  given: [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b)
  proof: ⟨fun _ h =>
h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩

中文:
定理 IsLUB.union
  条件: [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b)
  证明: ⟨fun _ h =>
h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩

Depends on / 依赖: Or.inl, Or.inr, casesOn, h.casesOn, hs.left, hs.right, ht.left, ht.right, le_sup_of_le_left, le_sup_of_le_right, sup_le
-/
theorem IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s union t) (a ⊔ b) :=
  ⟨fun _ h =>
h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
@[to_dual /-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/]
/--
theorem `IsLeast.union` / 定理 `IsLeast.union`

English:
theorem IsLeast.union
  statement: [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
  proof: ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩

@[to_dual]

中文:
定理 IsLeast.union
  结论: [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
  证明: ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩

@[to_dual]

Depends on / 依赖: ha.isGLB.union, hb.isGLB, le_total
-/
theorem IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
    (hb : IsLeast t b) : IsLeast (s union t) (min a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩

@[to_dual]
/--
theorem `IsLUB.inter_Ici_of_mem` / 定理 `IsLUB.inter_Ici_of_mem`

English:
theorem IsLUB.inter_Ici_of_mem
  given: [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b in s)
  proof: ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b <= c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩

中文:
定理 IsLUB.inter_Ici_of_mem
  条件: [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b in s)
  证明: ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b <= c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩

Depends on / 依赖: hxb.trans, le_rfl, le_total
-/
theorem IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b in s) :
    IsLUB (s inter Ici b) a :=
  ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b <= c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩

/--
theorem `bddAbove_iff_exists_ge` / 定理 `bddAbove_iff_exists_ge`

English:
theorem bddAbove_iff_exists_ge
  given: [SemilatticeSup γ] {s : Set γ} (x₀ : γ)
  proof: by
  rw [bddAbove_def]; rw [exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le

@[to_dual existing bddAbove_iff_exists_ge]

中文:
定理 bddAbove_iff_exists_ge
  条件: [SemilatticeSup γ] {s : Set γ} (x₀ : γ)
  证明: by
  rw [bddAbove_def]; rw [exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le

@[to_dual existing bddAbove_iff_exists_ge]

Depends on / 依赖: Monotone, Monotone.ball, bddAbove_def, exists_ge_and_iff_exists, monotone_le
-/
theorem bddAbove_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ exists x, x₀ <= x ∧ forall y in s, y <= x := by
  rw [bddAbove_def]; rw [exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le

@[to_dual existing bddAbove_iff_exists_ge]
/--
theorem `bddBelow_iff_exists_le` / 定理 `bddBelow_iff_exists_le`

English:
theorem bddBelow_iff_exists_le
  given: [SemilatticeInf γ] {s : Set γ} (x₀ : γ)
  proof: bddAbove_iff_exists_ge (toDual x₀)

@[to_dual exists_le]

中文:
定理 bddBelow_iff_exists_le
  条件: [SemilatticeInf γ] {s : Set γ} (x₀ : γ)
  证明: bddAbove_iff_exists_ge (toDual x₀)

@[to_dual exists_le]

Depends on / 依赖: bddAbove_iff_exists_ge, toDual
-/
theorem bddBelow_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ exists x, x <= x₀ ∧ forall y in s, x <= y :=
  bddAbove_iff_exists_ge (toDual x₀)

@[to_dual exists_le]
/--
theorem `BddAbove.exists_ge` / 定理 `BddAbove.exists_ge`

English:
theorem BddAbove.exists_ge
  given: [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ)
  proof: (bddAbove_iff_exists_ge x₀).mp hs

中文:
定理 BddAbove.exists_ge
  条件: [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ)
  证明: (bddAbove_iff_exists_ge x₀).mp hs

Depends on / 依赖: bddAbove_iff_exists_ge
-/
theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    exists x, x₀ <= x ∧ forall y in s, y <= x :=
  (bddAbove_iff_exists_ge x₀).mp hs

/-!
### Specific sets

#### Unbounded intervals
-/


@[to_dual]
/--
theorem `isLeast_Ici` / 定理 `isLeast_Ici`

English:
theorem isLeast_Ici
  statement: IsLeast (Ici a) a
  proof: ⟨self_mem_Ici, fun _ => id⟩

@[to_dual]

中文:
定理 isLeast_Ici
  结论: IsLeast (Ici a) a
  证明: ⟨self_mem_Ici, fun _ => id⟩

@[to_dual]

Depends on / 依赖: self_mem_Ici
-/
theorem isLeast_Ici : IsLeast (Ici a) a :=
  ⟨self_mem_Ici, fun _ => id⟩

@[to_dual]
/--
theorem `isLUB_Iic` / 定理 `isLUB_Iic`

English:
theorem isLUB_Iic
  statement: IsLUB (Iic a) a
  proof: isGreatest_Iic.isLUB

@[to_dual]

中文:
定理 isLUB_Iic
  结论: IsLUB (Iic a) a
  证明: isGreatest_Iic.isLUB

@[to_dual]

Depends on / 依赖: isGreatest_Iic, isGreatest_Iic.isLUB
-/
theorem isLUB_Iic : IsLUB (Iic a) a :=
  isGreatest_Iic.isLUB

@[to_dual]
/--
theorem `upperBounds_Iic` / 定理 `upperBounds_Iic`

English:
theorem upperBounds_Iic
  statement: upperBounds (Iic a) = Ici a
  proof: isLUB_Iic.upperBounds_eq

@[to_dual]

中文:
定理 upperBounds_Iic
  结论: upperBounds (Iic a) = Ici a
  证明: isLUB_Iic.upperBounds_eq

@[to_dual]

Depends on / 依赖: isLUB_Iic, isLUB_Iic.upperBounds_eq, upperBounds_eq
-/
theorem upperBounds_Iic : upperBounds (Iic a) = Ici a :=
  isLUB_Iic.upperBounds_eq

@[to_dual]
/--
theorem `bddAbove_Iic` / 定理 `bddAbove_Iic`

English:
theorem bddAbove_Iic
  statement: BddAbove (Iic a)
  proof: isLUB_Iic.bddAbove

@[to_dual]

中文:
定理 bddAbove_Iic
  结论: BddAbove (Iic a)
  证明: isLUB_Iic.bddAbove

@[to_dual]

Depends on / 依赖: bddAbove, isLUB_Iic, isLUB_Iic.bddAbove
-/
theorem bddAbove_Iic : BddAbove (Iic a) :=
  isLUB_Iic.bddAbove

@[to_dual]
/--
theorem `bddAbove_Iio` / 定理 `bddAbove_Iio`

English:
theorem bddAbove_Iio
  statement: BddAbove (Iio a)
  proof: ⟨a, fun _ hx => le_of_lt hx⟩

@[to_dual]

中文:
定理 bddAbove_Iio
  结论: BddAbove (Iio a)
  证明: ⟨a, fun _ hx => le_of_lt hx⟩

@[to_dual]

Depends on / 依赖: le_of_lt
-/
theorem bddAbove_Iio : BddAbove (Iio a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩

@[to_dual]
/--
theorem `le_of_isLUB_Iio` / 定理 `le_of_isLUB_Iio`

English:
theorem le_of_isLUB_Iio
  given: (a : α) (hb : IsLUB (Iio a) b)
  statement: b <= a
  proof: (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk

@[deprecated (since := "2026-01-17")] alias lub_Iio_le := le_of_isLUB_Iio
@[deprecated (since := "2026-01-17")] alias le_glb_Ioi := le_of_isGLB_Ioi

@[to_dual]

中文:
定理 le_of_isLUB_Iio
  条件: (a : α) (hb : IsLUB (Iio a) b)
  结论: b <= a
  证明: (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk

@[deprecated (since := "2026-01-17")] alias lub_Iio_le := le_of_isLUB_Iio
@[deprecated (since := "2026-01-17")] alias le_glb_Ioi := le_of_isGLB_Ioi

@[to_dual]

Depends on / 依赖: isLUB_le_iff, le_of_lt
-/
theorem le_of_isLUB_Iio (a : α) (hb : IsLUB (Iio a) b) : b <= a :=
  (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk

@[deprecated (since := "2026-01-17")] alias lub_Iio_le := le_of_isLUB_Iio
@[deprecated (since := "2026-01-17")] alias le_glb_Ioi := le_of_isGLB_Ioi

@[to_dual]
/--
theorem `lub_Iio_eq_self_or_Iio_eq_Iic` / 定理 `lub_Iio_eq_self_or_Iio_eq_Iic`

English:
theorem lub_Iio_eq_self_or_Iio_eq_Iic
  given: [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j)
  proof: by
  rcases eq_or_lt_of_le (le_of_isLUB_Iio i hj) with hj_eq_i | hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩

中文:
定理 lub_Iio_eq_self_or_Iio_eq_Iic
  条件: [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j)
  证明: by
  rcases eq_or_lt_of_le (le_of_isLUB_Iio i hj) with hj_eq_i | hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩

Depends on / 依赖: Or.inl, Set.ext, eq_or_lt_of_le, hj_eq_i, hj_lt_i, hk_le_j, hk_lt, le_of_isLUB_Iio, lt_of_le_of_lt
-/
theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j) :
    j = i ∨ Iio i = Iic j := by
  rcases eq_or_lt_of_le (le_of_isLUB_Iio i hj) with hj_eq_i | hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩
section

variable [LinearOrder γ]

@[to_dual]
/--
theorem `exists_lub_Iio` / 定理 `exists_lub_Iio`

English:
theorem exists_lub_Iio
  given: (i : γ)
  statement: exists j, IsLUB (Iio i) j
  proof: by
  by_cases! h_exists_lt : exists j, j in upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine ⟨i, fun j hj => le_of_lt hj, ?_⟩
    rw [mem_lowerBounds]
    exact h_exists_lt

中文:
定理 exists_lub_Iio
  条件: (i : γ)
  结论: 存在 j, IsLUB (Iio i) j
  证明: by
  by_cases! h_exists_lt : exists j, j in upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine ⟨i, fun j hj => le_of_lt hj, ?_⟩
    rw [mem_lowerBounds]
    exact h_exists_lt

Depends on / 依赖: h_exists_lt, hj_lt_i, hj_ub, hk_ub, le_of_lt, mem_lowerBounds, upperBounds
-/
theorem exists_lub_Iio (i : γ) : exists j, IsLUB (Iio i) j := by
  by_cases! h_exists_lt : exists j, j in upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine ⟨i, fun j hj => le_of_lt hj, ?_⟩
    rw [mem_lowerBounds]
    exact h_exists_lt

variable [DenselyOrdered γ]

@[to_dual]
/--
theorem `isLUB_Iio` / 定理 `isLUB_Iio`

English:
theorem isLUB_Iio
  given: {a : γ}
  statement: IsLUB (Iio a) a
  proof: ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_lt_imp_le_of_dense hy⟩

@[to_dual]

中文:
定理 isLUB_Iio
  条件: {a : γ}
  结论: IsLUB (Iio a) a
  证明: ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_lt_imp_le_of_dense hy⟩

@[to_dual]

Depends on / 依赖: le_of_forall_lt_imp_le_of_dense, le_of_lt
-/
theorem isLUB_Iio {a : γ} : IsLUB (Iio a) a :=
  ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_lt_imp_le_of_dense hy⟩

@[to_dual]
/--
theorem `upperBounds_Iio` / 定理 `upperBounds_Iio`

English:
theorem upperBounds_Iio
  given: {a : γ}
  statement: upperBounds (Iio a) = Ici a
  proof: isLUB_Iio.upperBounds_eq

中文:
定理 upperBounds_Iio
  条件: {a : γ}
  结论: upperBounds (Iio a) = Ici a
  证明: isLUB_Iio.upperBounds_eq

Depends on / 依赖: isLUB_Iio, isLUB_Iio.upperBounds_eq, upperBounds_eq
-/
theorem upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a :=
  isLUB_Iio.upperBounds_eq

end

/-!
#### Singleton
-/


@[to_dual (attr := simp)]
/--
theorem `isGreatest_singleton` / 定理 `isGreatest_singleton`

English:
theorem isGreatest_singleton
  statement: IsGreatest {a} a
  proof: ⟨mem_singleton a, fun _ hx => le_of_eq eq_of_mem_singleton hx⟩

@[to_dual (attr := simp)]

中文:
定理 isGreatest_singleton
  结论: IsGreatest {a} a
  证明: ⟨mem_singleton a, fun _ hx => le_of_eq eq_of_mem_singleton hx⟩

@[to_dual (attr := simp)]

Depends on / 依赖: eq_of_mem_singleton, le_of_eq, mem_singleton
-/
theorem isGreatest_singleton : IsGreatest {a} a :=
⟨mem_singleton a, fun _ hx => le_of_eq eq_of_mem_singleton hx⟩

@[to_dual (attr := simp)]
/--
theorem `isLUB_singleton` / 定理 `isLUB_singleton`

English:
theorem isLUB_singleton
  statement: IsLUB {a} a
  proof: isGreatest_singleton.isLUB

@[to_dual (attr := simp)]

中文:
定理 isLUB_singleton
  结论: IsLUB {a} a
  证明: isGreatest_singleton.isLUB

@[to_dual (attr := simp)]

Depends on / 依赖: isGreatest_singleton, isGreatest_singleton.isLUB
-/
theorem isLUB_singleton : IsLUB {a} a :=
  isGreatest_singleton.isLUB

@[to_dual (attr := simp)]
/--
lemma `bddAbove_singleton` / 引理 `bddAbove_singleton`

English:
lemma bddAbove_singleton
  statement: BddAbove ({a} : Set α)
  proof: isLUB_singleton.bddAbove

@[to_dual (attr := simp)]

中文:
引理 bddAbove_singleton
  结论: BddAbove ({a} : Set α)
  证明: isLUB_singleton.bddAbove

@[to_dual (attr := simp)]

Depends on / 依赖: bddAbove, isLUB_singleton, isLUB_singleton.bddAbove
-/
lemma bddAbove_singleton : BddAbove ({a} : Set α) := isLUB_singleton.bddAbove

@[to_dual (attr := simp)]
/--
theorem `upperBounds_singleton` / 定理 `upperBounds_singleton`

English:
theorem upperBounds_singleton
  statement: upperBounds {a} = Ici a
  proof: isLUB_singleton.upperBounds_eq

中文:
定理 upperBounds_singleton
  结论: upperBounds {a} = Ici a
  证明: isLUB_singleton.upperBounds_eq

Depends on / 依赖: isLUB_singleton, isLUB_singleton.upperBounds_eq, upperBounds_eq
-/
theorem upperBounds_singleton : upperBounds {a} = Ici a :=
  isLUB_singleton.upperBounds_eq

/-!
#### Bounded intervals
-/


@[to_dual (attr := simp)]
/--
lemma `bddAbove_Icc` / 引理 `bddAbove_Icc`

English:
lemma bddAbove_Icc
  statement: BddAbove (Icc a b)
  proof: ⟨b, fun _ => And.right⟩
@[to_dual (attr := simp)]

中文:
引理 bddAbove_Icc
  结论: BddAbove (Icc a b)
  证明: ⟨b, fun _ => And.right⟩
@[to_dual (attr := simp)]

Depends on / 依赖: And.right
-/
lemma bddAbove_Icc : BddAbove (Icc a b) := ⟨b, fun _ => And.right⟩
@[to_dual (attr := simp)]
/--
lemma `bddAbove_Ico` / 引理 `bddAbove_Ico`

English:
lemma bddAbove_Ico
  statement: BddAbove (Ico a b)
  proof: bddAbove_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]

中文:
引理 bddAbove_Ico
  结论: BddAbove (Ico a b)
  证明: bddAbove_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]

Depends on / 依赖: Ico_subset_Icc_self, bddAbove_Icc, bddAbove_Icc.mono
-/
lemma bddAbove_Ico : BddAbove (Ico a b) := bddAbove_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]
/--
lemma `bddBelow_Ico` / 引理 `bddBelow_Ico`

English:
lemma bddBelow_Ico
  statement: BddBelow (Ico a b)
  proof: bddBelow_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]

中文:
引理 bddBelow_Ico
  结论: BddBelow (Ico a b)
  证明: bddBelow_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]

Depends on / 依赖: Ico_subset_Icc_self, bddBelow_Icc, bddBelow_Icc.mono
-/
lemma bddBelow_Ico : BddBelow (Ico a b) := bddBelow_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]
/--
lemma `bddAbove_Ioo` / 引理 `bddAbove_Ioo`

English:
lemma bddAbove_Ioo
  statement: BddAbove (Ioo a b)
  proof: bddAbove_Icc.mono Ioo_subset_Icc_self

@[to_dual]

中文:
引理 bddAbove_Ioo
  结论: BddAbove (Ioo a b)
  证明: bddAbove_Icc.mono Ioo_subset_Icc_self

@[to_dual]

Depends on / 依赖: Ioo_subset_Icc_self, bddAbove_Icc, bddAbove_Icc.mono
-/
lemma bddAbove_Ioo : BddAbove (Ioo a b) := bddAbove_Icc.mono Ioo_subset_Icc_self

@[to_dual]
/--
theorem `isGreatest_Icc` / 定理 `isGreatest_Icc`

English:
theorem isGreatest_Icc
  given: (h : a <= b)
  statement: IsGreatest (Icc a b) b
  proof: ⟨right_mem_Icc.2 h, fun _ => And.right⟩

@[to_dual]

中文:
定理 isGreatest_Icc
  条件: (h : a <= b)
  结论: IsGreatest (Icc a b) b
  证明: ⟨right_mem_Icc.2 h, fun _ => And.right⟩

@[to_dual]

Depends on / 依赖: And.right, right_mem_Icc
-/
theorem isGreatest_Icc (h : a <= b) : IsGreatest (Icc a b) b :=
  ⟨right_mem_Icc.2 h, fun _ => And.right⟩

@[to_dual]
/--
theorem `isLUB_Icc` / 定理 `isLUB_Icc`

English:
theorem isLUB_Icc
  given: (h : a <= b)
  statement: IsLUB (Icc a b) b
  proof: (isGreatest_Icc h).isLUB

@[to_dual]

中文:
定理 isLUB_Icc
  条件: (h : a <= b)
  结论: IsLUB (Icc a b) b
  证明: (isGreatest_Icc h).isLUB

@[to_dual]

Depends on / 依赖: isGreatest_Icc
-/
theorem isLUB_Icc (h : a <= b) : IsLUB (Icc a b) b :=
  (isGreatest_Icc h).isLUB

@[to_dual]
/--
theorem `upperBounds_Icc` / 定理 `upperBounds_Icc`

English:
theorem upperBounds_Icc
  given: (h : a <= b)
  statement: upperBounds (Icc a b) = Ici b
  proof: (isLUB_Icc h).upperBounds_eq

@[to_dual]

中文:
定理 upperBounds_Icc
  条件: (h : a <= b)
  结论: upperBounds (Icc a b) = Ici b
  证明: (isLUB_Icc h).upperBounds_eq

@[to_dual]

Depends on / 依赖: isLUB_Icc, upperBounds_eq
-/
theorem upperBounds_Icc (h : a <= b) : upperBounds (Icc a b) = Ici b :=
  (isLUB_Icc h).upperBounds_eq

@[to_dual]
/--
theorem `isGreatest_Ioc` / 定理 `isGreatest_Ioc`

English:
theorem isGreatest_Ioc
  given: (h : a < b)
  statement: IsGreatest (Ioc a b) b
  proof: ⟨right_mem_Ioc.2 h, fun _ => And.right⟩

@[to_dual]

中文:
定理 isGreatest_Ioc
  条件: (h : a < b)
  结论: IsGreatest (Ioc a b) b
  证明: ⟨right_mem_Ioc.2 h, fun _ => And.right⟩

@[to_dual]

Depends on / 依赖: And.right, right_mem_Ioc
-/
theorem isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b :=
  ⟨right_mem_Ioc.2 h, fun _ => And.right⟩

@[to_dual]
/--
theorem `isLUB_Ioc` / 定理 `isLUB_Ioc`

English:
theorem isLUB_Ioc
  given: (h : a < b)
  statement: IsLUB (Ioc a b) b
  proof: (isGreatest_Ioc h).isLUB

@[to_dual]

中文:
定理 isLUB_Ioc
  条件: (h : a < b)
  结论: IsLUB (Ioc a b) b
  证明: (isGreatest_Ioc h).isLUB

@[to_dual]

Depends on / 依赖: isGreatest_Ioc
-/
theorem isLUB_Ioc (h : a < b) : IsLUB (Ioc a b) b :=
  (isGreatest_Ioc h).isLUB

@[to_dual]
/--
theorem `upperBounds_Ioc` / 定理 `upperBounds_Ioc`

English:
theorem upperBounds_Ioc
  given: (h : a < b)
  statement: upperBounds (Ioc a b) = Ici b
  proof: (isLUB_Ioc h).upperBounds_eq

中文:
定理 upperBounds_Ioc
  条件: (h : a < b)
  结论: upperBounds (Ioc a b) = Ici b
  证明: (isLUB_Ioc h).upperBounds_eq

Depends on / 依赖: isLUB_Ioc, upperBounds_eq
-/
theorem upperBounds_Ioc (h : a < b) : upperBounds (Ioc a b) = Ici b :=
  (isLUB_Ioc h).upperBounds_eq

section

variable [SemilatticeSup γ] [DenselyOrdered γ]

@[to_dual]
/--
theorem `isGLB_Ioo` / 定理 `isGLB_Ioo`

English:
theorem isGLB_Ioo
  given: {a b : γ} (h : a < b)
  statement: IsGLB (Ioo a b) a
  proof: ⟨fun _ hx => hx.1.le, fun x hx => by
    rcases eq_or_lt_of_le (le_sup_right : a <= x ⊔ a) with h₁ | h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_ge (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ :=

中文:
定理 isGLB_Ioo
  条件: {a b : γ} (h : a < b)
  结论: IsGLB (Ioo a b) a
  证明: ⟨fun _ hx => hx.1.le, fun x hx => by
    rcases eq_or_lt_of_le (le_sup_right : a <= x ⊔ a) with h₁ | h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_ge (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ :=

Depends on / 依赖: eq_or_lt_of_le, exists_between, h.le, le_sup_left, le_sup_right, lty.le, not_lt_of_ge, sup_le, trans_le, ub.le, ylt.trans_le
-/
theorem isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a :=
  ⟨fun _ hx => hx.1.le, fun x hx => by
    rcases eq_or_lt_of_le (le_sup_right : a <= x ⊔ a) with h₁ | h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_ge (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ := exists_between h
    apply (hx ⟨au, ub⟩).trans ub.le⟩

@[to_dual]
/--
theorem `lowerBounds_Ioo` / 定理 `lowerBounds_Ioo`

English:
theorem lowerBounds_Ioo
  given: {a b : γ} (hab : a < b)
  statement: lowerBounds (Ioo a b) = Iic a
  proof: (isGLB_Ioo hab).lowerBounds_eq

@[to_dual]

中文:
定理 lowerBounds_Ioo
  条件: {a b : γ} (hab : a < b)
  结论: lowerBounds (Ioo a b) = Iic a
  证明: (isGLB_Ioo hab).lowerBounds_eq

@[to_dual]

Depends on / 依赖: isGLB_Ioo, lowerBounds_eq
-/
theorem lowerBounds_Ioo {a b : γ} (hab : a < b) : lowerBounds (Ioo a b) = Iic a :=
  (isGLB_Ioo hab).lowerBounds_eq

@[to_dual]
/--
theorem `isGLB_Ioc` / 定理 `isGLB_Ioc`

English:
theorem isGLB_Ioc
  given: {a b : γ} (hab : a < b)
  statement: IsGLB (Ioc a b) a
  proof: (isGLB_Ioo hab).of_subset_of_superset (isGLB_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self

@[to_dual]

中文:
定理 isGLB_Ioc
  条件: {a b : γ} (hab : a < b)
  结论: IsGLB (Ioc a b) a
  证明: (isGLB_Ioo hab).of_subset_of_superset (isGLB_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self

@[to_dual]

Depends on / 依赖: Ioc_subset_Icc_self, Ioo_subset_Ioc_self, hab.le, isGLB_Icc, isGLB_Ioo, of_subset_of_superset
-/
theorem isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a :=
  (isGLB_Ioo hab).of_subset_of_superset (isGLB_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self

@[to_dual]
/--
theorem `lowerBounds_Ioc` / 定理 `lowerBounds_Ioc`

English:
theorem lowerBounds_Ioc
  given: {a b : γ} (hab : a < b)
  statement: lowerBounds (Ioc a b) = Iic a
  proof: (isGLB_Ioc hab).lowerBounds_eq

中文:
定理 lowerBounds_Ioc
  条件: {a b : γ} (hab : a < b)
  结论: lowerBounds (Ioc a b) = Iic a
  证明: (isGLB_Ioc hab).lowerBounds_eq

Depends on / 依赖: isGLB_Ioc, lowerBounds_eq
-/
theorem lowerBounds_Ioc {a b : γ} (hab : a < b) : lowerBounds (Ioc a b) = Iic a :=
  (isGLB_Ioc hab).lowerBounds_eq

end

@[to_dual]
/--
theorem `bddBelow_iff_subset_Ici` / 定理 `bddBelow_iff_subset_Ici`

English:
theorem bddBelow_iff_subset_Ici
  statement: BddBelow s ↔ exists a, s subseteq Ici a
  proof: Iff.rfl

@[to_dual none]

中文:
定理 bddBelow_iff_subset_Ici
  结论: BddBelow s ↔ 存在 a, s subseteq Ici a
  证明: Iff.rfl

@[to_dual none]

Depends on / 依赖: Iff.rfl
-/
theorem bddBelow_iff_subset_Ici : BddBelow s ↔ exists a, s subseteq Ici a :=
  Iff.rfl

@[to_dual none]
/--
theorem `bddBelow_bddAbove_iff_subset_Icc` / 定理 `bddBelow_bddAbove_iff_subset_Icc`

English:
theorem bddBelow_bddAbove_iff_subset_Icc
  statement: BddBelow s ∧ BddAbove s ↔ exists a b, s subseteq Icc a b
  proof: by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]

中文:
定理 bddBelow_bddAbove_iff_subset_Icc
  结论: BddBelow s ∧ BddAbove s ↔ 存在 a b, s subseteq Icc a b
  证明: by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]

Depends on / 依赖: Ici_inter_Iic, Ici_inter_Iic.symm, bddAbove_iff_subset_Iic, bddBelow_iff_subset_Ici, exists_and_left, exists_and_right, subset_inter_iff
-/
theorem bddBelow_bddAbove_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ exists a b, s subseteq Icc a b := by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]


/--
theorem `isGreatest_univ_iff` / 定理 `isGreatest_univ_iff`

English:
theorem isGreatest_univ_iff
  statement: IsGreatest univ a ↔ IsTop a
  proof: by
  simp [IsGreatest, mem_upperBounds, IsTop]

@[to_dual]

中文:
定理 isGreatest_univ_iff
  结论: IsGreatest univ a ↔ IsTop a
  证明: by
  simp [IsGreatest, mem_upperBounds, IsTop]

@[to_dual]
-/
@[to_dual (attr := simp)] theorem isGreatest_univ_iff : IsGreatest univ a ↔ IsTop a := by
  simp [IsGreatest, mem_upperBounds, IsTop]

@[to_dual]
/--
theorem `isGreatest_univ` / 定理 `isGreatest_univ`

English:
theorem isGreatest_univ
  given: [OrderTop α]
  statement: IsGreatest (univ : Set α) ⊤
  proof: isGreatest_univ_iff.2 isTop_top

@[to_dual (attr := simp)]

中文:
定理 isGreatest_univ
  条件: [OrderTop α]
  结论: IsGreatest (univ : Set α) ⊤
  证明: isGreatest_univ_iff.2 isTop_top

@[to_dual (attr := simp)]

Depends on / 依赖: isGreatest_univ_iff, isTop_top
-/
theorem isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α) ⊤ :=
  isGreatest_univ_iff.2 isTop_top

@[to_dual (attr := simp)]
/--
theorem `OrderTop.upperBounds_univ` / 定理 `OrderTop.upperBounds_univ`

English:
theorem OrderTop.upperBounds_univ
  given: [PartialOrder γ] [OrderTop γ]
  proof: by rw [isGreatest_univ.upperBounds_eq, Ici_top]

@[to_dual]

中文:
定理 OrderTop.upperBounds_univ
  条件: [PartialOrder γ] [OrderTop γ]
  证明: by rw [isGreatest_univ.upperBounds_eq, Ici_top]

@[to_dual]

Depends on / 依赖: Ici_top, isGreatest_univ, isGreatest_univ.upperBounds_eq, upperBounds_eq
-/
theorem OrderTop.upperBounds_univ [PartialOrder γ] [OrderTop γ] :
    upperBounds (univ : Set γ) = {⊤} := by rw [isGreatest_univ.upperBounds_eq, Ici_top]

@[to_dual]
/--
theorem `isLUB_univ` / 定理 `isLUB_univ`

English:
theorem isLUB_univ
  given: [OrderTop α]
  statement: IsLUB (univ : Set α) ⊤
  proof: isGreatest_univ.isLUB

@[to_dual (attr := simp)]

中文:
定理 isLUB_univ
  条件: [OrderTop α]
  结论: IsLUB (univ : Set α) ⊤
  证明: isGreatest_univ.isLUB

@[to_dual (attr := simp)]

Depends on / 依赖: isGreatest_univ, isGreatest_univ.isLUB
-/
theorem isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤ :=
  isGreatest_univ.isLUB

@[to_dual (attr := simp)]
/--
theorem `NoTopOrder.upperBounds_univ` / 定理 `NoTopOrder.upperBounds_univ`

English:
theorem NoTopOrder.upperBounds_univ
  given: [NoTopOrder α]
  statement: upperBounds (univ : Set α) = ∅
  proof: eq_empty_of_subset_empty fun b hb =>
    not_isTop b fun x => hb (mem_univ x)

@[to_dual (attr := simp)]

中文:
定理 NoTopOrder.upperBounds_univ
  条件: [NoTopOrder α]
  结论: upperBounds (univ : Set α) = ∅
  证明: eq_empty_of_subset_empty fun b hb =>
    not_isTop b fun x => hb (mem_univ x)

@[to_dual (attr := simp)]

Depends on / 依赖: eq_empty_of_subset_empty, mem_univ, not_isTop
-/
theorem NoTopOrder.upperBounds_univ [NoTopOrder α] : upperBounds (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    not_isTop b fun x => hb (mem_univ x)

@[to_dual (attr := simp)]
/--
theorem `not_bddAbove_univ` / 定理 `not_bddAbove_univ`

English:
theorem not_bddAbove_univ
  given: [NoTopOrder α]
  statement: ¬BddAbove (univ : Set α)
  proof: by simp [BddAbove]

中文:
定理 not_bddAbove_univ
  条件: [NoTopOrder α]
  结论: ¬BddAbove (univ : Set α)
  证明: by simp [BddAbove]

Depends on / 依赖: BddAbove
-/
theorem not_bddAbove_univ [NoTopOrder α] : ¬BddAbove (univ : Set α) := by simp [BddAbove]

/-!
#### Empty set
-/


@[to_dual (attr := simp)]
/--
theorem `upperBounds_empty` / 定理 `upperBounds_empty`

English:
theorem upperBounds_empty
  statement: upperBounds (∅ : Set α) = univ
  proof: by
  simp only [upperBounds, eq_univ_iff_forall, mem_ofPred_eq, forall_mem_empty, forall_true_iff]

@[to_dual (attr := simp)]

中文:
定理 upperBounds_empty
  结论: upperBounds (∅ : Set α) = univ
  证明: by
  simp only [upperBounds, eq_univ_iff_forall, mem_ofPred_eq, forall_mem_empty, forall_true_iff]

@[to_dual (attr := simp)]

Depends on / 依赖: eq_univ_iff_forall, forall_mem_empty, forall_true_iff, mem_ofPred_eq, upperBounds
-/
theorem upperBounds_empty : upperBounds (∅ : Set α) = univ := by
  simp only [upperBounds, eq_univ_iff_forall, mem_ofPred_eq, forall_mem_empty, forall_true_iff]

@[to_dual (attr := simp)]
/--
theorem `bddAbove_empty` / 定理 `bddAbove_empty`

English:
theorem bddAbove_empty
  given: [Nonempty α]
  statement: BddAbove (∅ : Set α)
  proof: by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]

中文:
定理 bddAbove_empty
  条件: [Nonempty α]
  结论: BddAbove (∅ : Set α)
  证明: by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]

Depends on / 依赖: BddAbove, univ_nonempty, upperBounds_empty
-/
theorem bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]

/--
theorem `isGLB_empty_iff` / 定理 `isGLB_empty_iff`

English:
theorem isGLB_empty_iff
  statement: IsGLB ∅ a ↔ IsTop a
  proof: by
  simp [IsGLB]

@[to_dual]

中文:
定理 isGLB_empty_iff
  结论: IsGLB ∅ a ↔ IsTop a
  证明: by
  simp [IsGLB]

@[to_dual]
-/
@[to_dual (attr := simp)] theorem isGLB_empty_iff : IsGLB ∅ a ↔ IsTop a := by
  simp [IsGLB]

@[to_dual]
/--
theorem `isGLB_empty` / 定理 `isGLB_empty`

English:
theorem isGLB_empty
  given: [OrderTop α]
  statement: IsGLB ∅ (⊤ : α)
  proof: isGLB_empty_iff.2 isTop_top

@[to_dual]

中文:
定理 isGLB_empty
  条件: [OrderTop α]
  结论: IsGLB ∅ (⊤ : α)
  证明: isGLB_empty_iff.2 isTop_top

@[to_dual]

Depends on / 依赖: isGLB_empty_iff, isTop_top
-/
theorem isGLB_empty [OrderTop α] : IsGLB ∅ (⊤ : α) :=
  isGLB_empty_iff.2 isTop_top

@[to_dual]
/--
theorem `IsLUB.nonempty` / 定理 `IsLUB.nonempty`

English:
theorem IsLUB.nonempty
  given: [NoBotOrder α] (hs : IsLUB s a)
  statement: s.Nonempty
  proof: nonempty_iff_ne_empty.2 fun h =>
not_isBot a fun _ => hs.right by rw [h, upperBounds_empty]; exact mem_univ _

@[to_dual]

中文:
定理 IsLUB.nonempty
  条件: [NoBotOrder α] (hs : IsLUB s a)
  结论: s.Nonempty
  证明: nonempty_iff_ne_empty.2 fun h =>
not_isBot a fun _ => hs.right by rw [h, upperBounds_empty]; exact mem_univ _

@[to_dual]

Depends on / 依赖: hs.right, mem_univ, nonempty_iff_ne_empty, not_isBot, upperBounds_empty
-/
theorem IsLUB.nonempty [NoBotOrder α] (hs : IsLUB s a) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h =>
not_isBot a fun _ => hs.right by rw [h, upperBounds_empty]; exact mem_univ _

@[to_dual]
/--
theorem `nonempty_of_not_bddAbove` / 定理 `nonempty_of_not_bddAbove`

English:
theorem nonempty_of_not_bddAbove
  given: [ha : Nonempty α] (h : ¬BddAbove s)
  statement: s.Nonempty
  proof: (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1

中文:
定理 nonempty_of_not_bddAbove
  条件: [ha : Nonempty α] (h : ¬BddAbove s)
  结论: s.Nonempty
  证明: (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1

Depends on / 依赖: Nonempty, Nonempty.elim, not_bddAbove_iff
-/
theorem nonempty_of_not_bddAbove [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[to_dual (attr := simp) /-- Adding a point to a set preserves its boundedness below. -/]
/--
theorem `bddAbove_insert` / 定理 `bddAbove_insert`

English:
theorem bddAbove_insert
  given: [IsDirectedOrder α] {s : Set α} {a : α}
  proof: by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and]

@[to_dual]

中文:
定理 bddAbove_insert
  条件: [IsDirectedOrder α] {s : Set α} {a : α}
  证明: by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and]

@[to_dual]

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.sigmaFiniteFiltration, Measure, Preorder, bddAbove_singleton, bddAbove_union, insert_eq, sigmaFiniteFiltration, true_and
-/
theorem bddAbove_insert [IsDirectedOrder α] {s : Set α} {a : α} :
    BddAbove (insert a s) ↔ BddAbove s := by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and]

@[to_dual]
/--
theorem `BddAbove.insert` / 定理 `BddAbove.insert`

English:
theorem BddAbove.insert
  given: [IsDirectedOrder α] {s : Set α} (a : α)
  proof: bddAbove_insert.2

@[to_dual]

中文:
定理 BddAbove.insert
  条件: [IsDirectedOrder α] {s : Set α} (a : α)
  证明: bddAbove_insert.2

@[to_dual]
-/
protected theorem BddAbove.insert [IsDirectedOrder α] {s : Set α} (a : α) :
    BddAbove s -> BddAbove (insert a s) :=
  bddAbove_insert.2

@[to_dual]
/--
theorem `IsLUB.insert` / 定理 `IsLUB.insert`

English:
theorem IsLUB.insert
  given: [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b)
  proof: by
  rw [insert_eq]
  exact isLUB_singleton.union hs

@[to_dual]

中文:
定理 IsLUB.insert
  条件: [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b)
  证明: by
  rw [insert_eq]
  exact isLUB_singleton.union hs

@[to_dual]
-/
protected theorem IsLUB.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b) :
    IsLUB (insert a s) (a ⊔ b) := by
  rw [insert_eq]
  exact isLUB_singleton.union hs

@[to_dual]
/--
theorem `IsGreatest.insert` / 定理 `IsGreatest.insert`

English:
theorem IsGreatest.insert
  given: [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b)
  proof: by
  rw [insert_eq]
  exact isGreatest_singleton.union hs

@[to_dual (attr := simp)]

中文:
定理 IsGreatest.insert
  条件: [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b)
  证明: by
  rw [insert_eq]
  exact isGreatest_singleton.union hs

@[to_dual (attr := simp)]
-/
protected theorem IsGreatest.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact isGreatest_singleton.union hs

@[to_dual (attr := simp)]
/--
theorem `upperBounds_insert` / 定理 `upperBounds_insert`

English:
theorem upperBounds_insert
  given: (a : α) (s : Set α)
  proof: by
  rw [insert_eq]; rw [upperBounds_union]; rw [upperBounds_singleton]

中文:
定理 upperBounds_insert
  条件: (a : α) (s : Set α)
  证明: by
  rw [insert_eq]; rw [upperBounds_union]; rw [upperBounds_singleton]

Depends on / 依赖: insert_eq, upperBounds_singleton, upperBounds_union
-/
theorem upperBounds_insert (a : α) (s : Set α) :
    upperBounds (insert a s) = Ici a inter upperBounds s := by
  rw [insert_eq]; rw [upperBounds_union]; rw [upperBounds_singleton]

/-- When there is a global maximum, every set is bounded above. -/
@[to_dual (attr := simp) /-- When there is a global minimum, every set is bounded below. -/]
/--
theorem `OrderTop.bddAbove` / 定理 `OrderTop.bddAbove`

English:
theorem OrderTop.bddAbove
  given: [OrderTop α] (s : Set α)
  statement: BddAbove s
  proof: ⟨⊤, fun a _ => OrderTop.le_top a⟩

中文:
定理 OrderTop.bddAbove
  条件: [OrderTop α] (s : Set α)
  结论: BddAbove s
  证明: ⟨⊤, fun a _ => OrderTop.le_top a⟩
-/
protected theorem OrderTop.bddAbove [OrderTop α] (s : Set α) : BddAbove s :=
  ⟨⊤, fun a _ => OrderTop.le_top a⟩

/-- Sets are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `bddDefault` in the statements,
in the form `(hA : BddAbove A := by bddDefault)`. -/
macro "bddDefault" : tactic =>
  `(tactic| first
    | apply OrderTop.bddAbove
    | apply OrderBot.bddBelow)

/-!
#### Pair
-/


@[to_dual]
/--
theorem `isLUB_pair` / 定理 `isLUB_pair`

English:
theorem isLUB_pair
  given: [SemilatticeSup γ] {a b : γ}
  statement: IsLUB {a, b} (a ⊔ b)
  proof: isLUB_singleton.insert _

@[to_dual]

中文:
定理 isLUB_pair
  条件: [SemilatticeSup γ] {a b : γ}
  结论: IsLUB {a, b} (a ⊔ b)
  证明: isLUB_singleton.insert _

@[to_dual]

Depends on / 依赖: insert, isLUB_singleton, isLUB_singleton.insert
-/
theorem isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ b) :=
  isLUB_singleton.insert _

@[to_dual]
/--
theorem `isGreatest_pair` / 定理 `isGreatest_pair`

English:
theorem isGreatest_pair
  given: [LinearOrder γ] {a b : γ}
  statement: IsGreatest {a, b} (max a b)
  proof: isGreatest_singleton.insert _

中文:
定理 isGreatest_pair
  条件: [LinearOrder γ] {a b : γ}
  结论: IsGreatest {a, b} (max a b)
  证明: isGreatest_singleton.insert _

Depends on / 依赖: insert, isGreatest_singleton, isGreatest_singleton.insert
-/
theorem isGreatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  isGreatest_singleton.insert _

/-!
#### Lower/upper bounds
-/


@[to_dual (attr := simp)]
/--
theorem `isLUB_lowerBounds` / 定理 `isLUB_lowerBounds`

English:
theorem isLUB_lowerBounds
  statement: IsLUB (lowerBounds s) a ↔ IsGLB s a
  proof: ⟨fun H => ⟨fun _ hx => H.2 subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

中文:
定理 isLUB_lowerBounds
  结论: IsLUB (lowerBounds s) a ↔ IsGLB s a
  证明: ⟨fun H => ⟨fun _ hx => H.2 subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

Depends on / 依赖: IsGreatest, IsGreatest.isLUB, subset_upperBounds_lowerBounds
-/
theorem isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
⟨fun H => ⟨fun _ hx => H.2 subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

end

section Minimal

variable [Preorder α] {s : Set α} {a b : α}

@[to_dual]
/--
theorem `DirectedOn.le_of_minimal` / 定理 `DirectedOn.le_of_minimal`

English:
theorem DirectedOn.le_of_minimal
  statement: (h : DirectedOn (fun x y => y <= x) s) (hMin : Minimal (· in s) a)
  proof: by
  obtain ⟨z, hz, hza, hzb⟩ := h a hMin.1 b hb
  exact (hMin.2 hz hza).trans hzb

@[to_dual]

中文:
定理 DirectedOn.le_of_minimal
  结论: (h : DirectedOn (fun x y => y <= x) s) (hMin : Minimal (· in s) a)
  证明: by
  obtain ⟨z, hz, hza, hzb⟩ := h a hMin.1 b hb
  exact (hMin.2 hz hza).trans hzb

@[to_dual]
-/
theorem DirectedOn.le_of_minimal (h : DirectedOn (fun x y => y <= x) s) (hMin : Minimal (· in s) a)
    (hb : b in s) : a <= b := by
  obtain ⟨z, hz, hza, hzb⟩ := h a hMin.1 b hb
  exact (hMin.2 hz hza).trans hzb

@[to_dual]
/--
theorem `DirectedOn.minimal_iff_isLeast` / 定理 `DirectedOn.minimal_iff_isLeast`

English:
theorem DirectedOn.minimal_iff_isLeast
  given: (h : DirectedOn (fun x y => y <= x) s)
  proof: ⟨fun hMin => ⟨hMin.1, fun _ hy => h.le_of_minimal hMin hy⟩, fun h => ⟨h.1, fun _ hy _ => h.2 hy⟩⟩

中文:
定理 DirectedOn.minimal_iff_isLeast
  条件: (h : DirectedOn (fun x y => y <= x) s)
  证明: ⟨fun hMin => ⟨hMin.1, fun _ hy => h.le_of_minimal hMin hy⟩, fun h => ⟨h.1, fun _ hy _ => h.2 hy⟩⟩

Depends on / 依赖: h.le_of_minimal, le_of_minimal
-/
theorem DirectedOn.minimal_iff_isLeast (h : DirectedOn (fun x y => y <= x) s) :
    Minimal (· in s) a ↔ IsLeast s a :=
  ⟨fun hMin => ⟨hMin.1, fun _ hy => h.le_of_minimal hMin hy⟩, fun h => ⟨h.1, fun _ hy _ => h.2 hy⟩⟩

end Minimal

@[to_dual]
/--
theorem `minimal_iff_isLeast` / 定理 `minimal_iff_isLeast`

English:
theorem minimal_iff_isLeast
  given: [LinearOrder α] {s : Set α} {a : α}
  proof: (Std.Total.directedOn s).minimal_iff_isLeast

中文:
定理 minimal_iff_isLeast
  条件: [LinearOrder α] {s : Set α} {a : α}
  证明: (Std.Total.directedOn s).minimal_iff_isLeast

Depends on / 依赖: Std.Total.directedOn, directedOn, minimal_iff_isLeast
-/
theorem minimal_iff_isLeast [LinearOrder α] {s : Set α} {a : α} :
    Minimal (· in s) a ↔ IsLeast s a :=
  (Std.Total.directedOn s).minimal_iff_isLeast

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorder

variable [Preorder α] [Preorder β] {s s' : Set α} {t : Set β} {a b : α}

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `lowerBounds_le_upperBounds` / 定理 `lowerBounds_le_upperBounds`

English:
theorem lowerBounds_le_upperBounds
  given: (ha : a in lowerBounds s) (hb : b in upperBounds s)

中文:
定理 lowerBounds_le_upperBounds
  条件: (ha : a in lowerBounds s) (hb : b in upperBounds s)
-/
theorem lowerBounds_le_upperBounds (ha : a in lowerBounds s) (hb : b in upperBounds s) :
    s.Nonempty -> a <= b
  | ⟨_, hc⟩ => le_trans (ha hc) (hb hc)

@[to_dual none]
/--
theorem `lowerBounds_le_upperBounds_of_nonempty_inter` / 定理 `lowerBounds_le_upperBounds_of_nonempty_inter`

English:
theorem lowerBounds_le_upperBounds_of_nonempty_inter
  statement: (h : (s inter s').Nonempty)
  proof: by
  have ⟨x, hx, hx'⟩ := h
  exact le_trans (ha hx) (hb hx')

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 lowerBounds_le_upperBounds_of_nonempty_inter
  结论: (h : (s inter s').Nonempty)
  证明: by
  have ⟨x, hx, hx'⟩ := h
  exact le_trans (ha hx) (hb hx')

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: le_trans
-/
theorem lowerBounds_le_upperBounds_of_nonempty_inter (h : (s inter s').Nonempty)
    (ha : a in lowerBounds s) (hb : b in upperBounds s') : a <= b := by
  have ⟨x, hx, hx'⟩ := h
  exact le_trans (ha hx) (hb hx')

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `isGLB_le_isLUB` / 定理 `isGLB_le_isLUB`

English:
theorem isGLB_le_isLUB
  given: (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty)
  statement: a <= b
  proof: lowerBounds_le_upperBounds ha.1 hb.1 hs

@[to_dual none]

中文:
定理 isGLB_le_isLUB
  条件: (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty)
  结论: a <= b
  证明: lowerBounds_le_upperBounds ha.1 hb.1 hs

@[to_dual none]

Depends on / 依赖: lowerBounds_le_upperBounds
-/
theorem isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty) : a <= b :=
  lowerBounds_le_upperBounds ha.1 hb.1 hs

@[to_dual none]
/--
theorem `isGLB_le_isLUB_of_nonempty_inter` / 定理 `isGLB_le_isLUB_of_nonempty_inter`

English:
theorem isGLB_le_isLUB_of_nonempty_inter
  statement: (h : (s inter s').Nonempty) (ha : IsGLB s a)
  proof: lowerBounds_le_upperBounds_of_nonempty_inter h ha.left hb.left

@[to_dual lt_isGLB_iff]

中文:
定理 isGLB_le_isLUB_of_nonempty_inter
  结论: (h : (s inter s').Nonempty) (ha : IsGLB s a)
  证明: lowerBounds_le_upperBounds_of_nonempty_inter h ha.left hb.left

@[to_dual lt_isGLB_iff]

Depends on / 依赖: ha.left, hb.left, lowerBounds_le_upperBounds_of_nonempty_inter, rightCont_self
-/
theorem isGLB_le_isLUB_of_nonempty_inter (h : (s inter s').Nonempty) (ha : IsGLB s a)
    (hb : IsLUB s' b) : a <= b :=
  lowerBounds_le_upperBounds_of_nonempty_inter h ha.left hb.left

@[to_dual lt_isGLB_iff]
/--
theorem `isLUB_lt_iff` / 定理 `isLUB_lt_iff`

English:
theorem isLUB_lt_iff
  given: (ha : IsLUB s a)
  statement: a < b ↔ exists c in upperBounds s, c < b
  proof: ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩

@[to_dual self (reorder := a b, x y, ha hb, hx hy)]

中文:
定理 isLUB_lt_iff
  条件: (ha : IsLUB s a)
  结论: a < b ↔ 存在 c in upperBounds s, c < b
  证明: ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩

@[to_dual self (reorder := a b, x y, ha hb, hx hy)]

Depends on / 依赖: lt_of_le_of_lt
-/
theorem isLUB_lt_iff (ha : IsLUB s a) : a < b ↔ exists c in upperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩

@[to_dual self (reorder := a b, x y, ha hb, hx hy)]
/--
theorem `le_of_isLUB_le_isGLB` / 定理 `le_of_isLUB_le_isGLB`

English:
theorem le_of_isLUB_le_isGLB
  statement: {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b <= a) (hx : x in s)
  proof: calc
    x <= b := hb.1 hx
    _ <= a := hab
    _ <= y := ha.1 hy

@[to_dual (attr := simp)]

中文:
定理 le_of_isLUB_le_isGLB
  结论: {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b <= a) (hx : x in s)
  证明: calc
    x <= b := hb.1 hx
    _ <= a := hab
    _ <= y := ha.1 hy

@[to_dual (attr := simp)]
-/
theorem le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b <= a) (hx : x in s)
    (hy : y in s) : x <= y :=
  calc
    x <= b := hb.1 hx
    _ <= a := hab
    _ <= y := ha.1 hy

@[to_dual (attr := simp)]
/--
lemma `upperBounds_prod` / 引理 `upperBounds_prod`

English:
lemma upperBounds_prod
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  ext; rw [← nonempty_coe_sort] at hs ht; aesop (add simp [upperBounds, Prod.le_def, forall_and])

@[to_dual]

中文:
引理 upperBounds_prod
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  证明: by
  ext; rw [← nonempty_coe_sort] at hs ht; aesop (add simp [upperBounds, Prod.le_def, forall_and])

@[to_dual]

Depends on / 依赖: Prod.le_def, forall_and, le_def, nonempty_coe_sort, upperBounds
-/
lemma upperBounds_prod (hs : s.Nonempty) (ht : t.Nonempty) :
    upperBounds (s ×ˢ t) = upperBounds s ×ˢ upperBounds t := by
  ext; rw [← nonempty_coe_sort] at hs ht; aesop (add simp [upperBounds, Prod.le_def, forall_and])

@[to_dual]
/--
lemma `IsLUB.prod` / 引理 `IsLUB.prod`

English:
lemma IsLUB.prod
  given: {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha : IsLUB s a) (hb : IsLUB t b)
  proof: by simp_all +contextual [IsLUB, IsLeast, lowerBounds]

中文:
引理 IsLUB.prod
  条件: {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha : IsLUB s a) (hb : IsLUB t b)
  证明: by simp_all +contextual [IsLUB, IsLeast, lowerBounds]

Depends on / 依赖: IsLeast, contextual, lowerBounds
-/
lemma IsLUB.prod {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha : IsLUB s a) (hb : IsLUB t b) :
    IsLUB (s ×ˢ t) (a, b) := by simp_all +contextual [IsLUB, IsLeast, lowerBounds]

/--
theorem `isLUB_congr_of_antisymmRel` / 定理 `isLUB_congr_of_antisymmRel`

English:
theorem isLUB_congr_of_antisymmRel
  given: {a b : α} (h : AntisymmRel (· <= ·) a b)
  proof: by
  simp [isLUB_iff_le_iff, h.le_congr_left]

中文:
定理 isLUB_congr_of_antisymmRel
  条件: {a b : α} (h : AntisymmRel (· <= ·) a b)
  证明: by
  simp [isLUB_iff_le_iff, h.le_congr_left]

Depends on / 依赖: h.le_congr_left, isLUB_iff_le_iff, le_congr_left
-/
theorem isLUB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· <= ·) a b) :
    IsLUB s a ↔ IsLUB s b := by
  simp [isLUB_iff_le_iff, h.le_congr_left]

-- TODO: `to_dual` doesn't work with `AntisymmRel`.
/--
theorem `isGLB_congr_of_antisymmRel` / 定理 `isGLB_congr_of_antisymmRel`

English:
theorem isGLB_congr_of_antisymmRel
  given: {a b : α} (h : AntisymmRel (· <= ·) a b)
  proof: by
  simp [isGLB_iff_le_iff, h.le_congr_right]

中文:
定理 isGLB_congr_of_antisymmRel
  条件: {a b : α} (h : AntisymmRel (· <= ·) a b)
  证明: by
  simp [isGLB_iff_le_iff, h.le_congr_right]

Depends on / 依赖: h.le_congr_right, isGLB_iff_le_iff, le_congr_right
-/
theorem isGLB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· <= ·) a b) :
    IsGLB s a ↔ IsGLB s b := by
  simp [isGLB_iff_le_iff, h.le_congr_right]

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

@[to_dual]
/--
theorem `IsLeast.unique` / 定理 `IsLeast.unique`

English:
theorem IsLeast.unique
  given: (Ha : IsLeast s a) (Hb : IsLeast s b)
  statement: a = b
  proof: le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

@[to_dual]

中文:
定理 IsLeast.unique
  条件: (Ha : IsLeast s a) (Hb : IsLeast s b)
  结论: a = b
  证明: le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

@[to_dual]

Depends on / 依赖: Ha.left, Ha.right, Hb.left, Hb.right, le_antisymm
-/
theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

@[to_dual]
/--
theorem `IsLeast.isLeast_iff_eq` / 定理 `IsLeast.isLeast_iff_eq`

English:
theorem IsLeast.isLeast_iff_eq
  given: (Ha : IsLeast s a)
  statement: IsLeast s b ↔ a = b
  proof: Iff.intro Ha.unique fun h => h ▸ Ha

@[to_dual]

中文:
定理 IsLeast.isLeast_iff_eq
  条件: (Ha : IsLeast s a)
  结论: IsLeast s b ↔ a = b
  证明: Iff.intro Ha.unique fun h => h ▸ Ha

@[to_dual]

Depends on / 依赖: Ha.unique, Iff.intro, unique
-/
theorem IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

@[to_dual]
/--
theorem `IsLUB.unique` / 定理 `IsLUB.unique`

English:
theorem IsLUB.unique
  given: (Ha : IsLUB s a) (Hb : IsLUB s b)
  statement: a = b
  proof: IsLeast.unique Ha Hb

@[to_dual self (reorder := a b, Ha Hb)]

中文:
定理 IsLUB.unique
  条件: (Ha : IsLUB s a) (Hb : IsLUB s b)
  结论: a = b
  证明: IsLeast.unique Ha Hb

@[to_dual self (reorder := a b, Ha Hb)]

Depends on / 依赖: IsLeast, IsLeast.unique, unique
-/
theorem IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
  IsLeast.unique Ha Hb

@[to_dual self (reorder := a b, Ha Hb)]
/--
theorem `Set.subsingleton_of_isLUB_le_isGLB` / 定理 `Set.subsingleton_of_isLUB_le_isGLB`

English:
theorem Set.subsingleton_of_isLUB_le_isGLB
  given: (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b <= a)
  proof: fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

@[to_dual self (reorder := a b, Ha Hb)]

中文:
定理 Set.subsingleton_of_isLUB_le_isGLB
  条件: (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b <= a)
  证明: fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

@[to_dual self (reorder := a b, Ha Hb)]
-/
theorem Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b <= a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

@[to_dual self (reorder := a b, Ha Hb)]
/--
theorem `isGLB_lt_isLUB_of_ne` / 定理 `isGLB_lt_isLUB_of_ne`

English:
theorem isGLB_lt_isLUB_of_ne
  statement: (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x in s) (Hy : y in s)
  proof: lt_iff_le_not_ge.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
Hxy Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩

中文:
定理 isGLB_lt_isLUB_of_ne
  结论: (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x in s) (Hy : y in s)
  证明: lt_iff_le_not_ge.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
Hxy Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩

Depends on / 依赖: Set.subsingleton_of_isLUB_le_isGLB, lowerBounds_le_upperBounds, lt_iff_le_not_ge, subsingleton_of_isLUB_le_isGLB
-/
theorem isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x in s) (Hy : y in s)
    (Hxy : x != y) : a < b :=
  lt_iff_le_not_ge.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
Hxy Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

@[to_dual isGLB_lt_iff]
/--
theorem `lt_isLUB_iff` / 定理 `lt_isLUB_iff`

English:
theorem lt_isLUB_iff
  given: (h : IsLUB s a)
  statement: b < a ↔ exists c in s, b < c
  proof: by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]

@[to_dual none]

中文:
定理 lt_isLUB_iff
  条件: (h : IsLUB s a)
  结论: b < a ↔ 存在 c in s, b < c
  证明: by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]

@[to_dual none]

Depends on / 依赖: exists_prop, isLUB_le_iff, mem_upperBounds, not_forall, not_le, simp_rw
-/
theorem lt_isLUB_iff (h : IsLUB s a) : b < a ↔ exists c in s, b < c := by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]

@[to_dual none]
/--
theorem `IsLUB.exists_between` / 定理 `IsLUB.exists_between`

English:
theorem IsLUB.exists_between
  given: (h : IsLUB s a) (hb : b < a)
  statement: exists c in s, b < c ∧ c <= a
  proof: let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

@[to_dual none]

中文:
定理 IsLUB.exists_between
  条件: (h : IsLUB s a) (hb : b < a)
  结论: 存在 c in s, b < c ∧ c <= a
  证明: let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

@[to_dual none]

Depends on / 依赖: lt_isLUB_iff
-/
theorem IsLUB.exists_between (h : IsLUB s a) (hb : b < a) : exists c in s, b < c ∧ c <= a :=
  let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

@[to_dual none]
/--
theorem `IsLUB.exists_between'` / 定理 `IsLUB.exists_between'`

English:
theorem IsLUB.exists_between'
  given: (h : IsLUB s a) (h' : a ∉ s) (hb : b < a)
  statement: exists c in s, b < c ∧ c < a
  proof: let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' hac ▸ hcs⟩

@[to_dual none]

中文:
定理 IsLUB.exists_between'
  条件: (h : IsLUB s a) (h' : a ∉ s) (hb : b < a)
  结论: 存在 c in s, b < c ∧ c < a
  证明: let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' hac ▸ hcs⟩

@[to_dual none]

Depends on / 依赖: exists_between, h.exists_between, hca.lt_of_ne, lt_of_ne
-/
theorem IsLUB.exists_between' (h : IsLUB s a) (h' : a ∉ s) (hb : b < a) : exists c in s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' hac ▸ hcs⟩

@[to_dual none]
/--
theorem `IsGLB.exists_between` / 定理 `IsGLB.exists_between`

English:
theorem IsGLB.exists_between
  given: (h : IsGLB s a) (hb : a < b)
  statement: exists c in s, a <= c ∧ c < b
  proof: let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

@[to_dual none]

中文:
定理 IsGLB.exists_between
  条件: (h : IsGLB s a) (hb : a < b)
  结论: 存在 c in s, a <= c ∧ c < b
  证明: let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

@[to_dual none]

Depends on / 依赖: isGLB_lt_iff
-/
theorem IsGLB.exists_between (h : IsGLB s a) (hb : a < b) : exists c in s, a <= c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

@[to_dual none]
/--
theorem `IsGLB.exists_between'` / 定理 `IsGLB.exists_between'`

English:
theorem IsGLB.exists_between'
  given: (h : IsGLB s a) (h' : a ∉ s) (hb : a < b)
  statement: exists c in s, a < c ∧ c < b
  proof: let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
⟨c, hcs, hac.lt_of_ne fun hac => h' hac.symm ▸ hcs, hcb⟩

中文:
定理 IsGLB.exists_between'
  条件: (h : IsGLB s a) (h' : a ∉ s) (hb : a < b)
  结论: 存在 c in s, a < c ∧ c < b
  证明: let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
⟨c, hcs, hac.lt_of_ne fun hac => h' hac.symm ▸ hcs, hcb⟩

Depends on / 依赖: exists_between, h.exists_between, hac.lt_of_ne, hac.symm, lt_of_ne
-/
theorem IsGLB.exists_between' (h : IsGLB s a) (h' : a ∉ s) (hb : a < b) : exists c in s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
⟨c, hcs, hac.lt_of_ne fun hac => h' hac.symm ▸ hcs, hcb⟩

end LinearOrder

/--
theorem `isGreatest_himp` / 定理 `isGreatest_himp`

English:
theorem isGreatest_himp
  given: [GeneralizedHeytingAlgebra α] (a b : α)
  proof: by
  simp [IsGreatest, mem_upperBounds]

中文:
定理 isGreatest_himp
  条件: [GeneralizedHeytingAlgebra α] (a b : α)
  证明: by
  simp [IsGreatest, mem_upperBounds]

Depends on / 依赖: IsGreatest, mem_upperBounds
-/
theorem isGreatest_himp [GeneralizedHeytingAlgebra α] (a b : α) :
    IsGreatest {w | w ⊓ a <= b} (a ⇨ b) := by
  simp [IsGreatest, mem_upperBounds]

/--
theorem `isLeast_sdiff` / 定理 `isLeast_sdiff`

English:
theorem isLeast_sdiff
  given: [GeneralizedCoheytingAlgebra α] (a b : α)
  proof: by
  simp [IsLeast, mem_lowerBounds]

中文:
定理 isLeast_sdiff
  条件: [GeneralizedCoheytingAlgebra α] (a b : α)
  证明: by
  simp [IsLeast, mem_lowerBounds]

Depends on / 依赖: IsLeast, mem_lowerBounds
-/
theorem isLeast_sdiff [GeneralizedCoheytingAlgebra α] (a b : α) :
    IsLeast {w | a <= b ⊔ w} (a \ b) := by
  simp [IsLeast, mem_lowerBounds]

/--
theorem `isGreatest_compl` / 定理 `isGreatest_compl`

English:
theorem isGreatest_compl
  given: [HeytingAlgebra α] (a : α)
  proof: by
  simpa only [himp_bot, disjoint_iff_inf_le] using isGreatest_himp a ⊥

中文:
定理 isGreatest_compl
  条件: [HeytingAlgebra α] (a : α)
  证明: by
  simpa only [himp_bot, disjoint_iff_inf_le] using isGreatest_himp a ⊥

Depends on / 依赖: disjoint_iff_inf_le, himp_bot, isGreatest_himp
-/
theorem isGreatest_compl [HeytingAlgebra α] (a : α) :
    IsGreatest {w | Disjoint w a} (aᶜ) := by
  simpa only [himp_bot, disjoint_iff_inf_le] using isGreatest_himp a ⊥

/--
theorem `isLeast_hnot` / 定理 `isLeast_hnot`

English:
theorem isLeast_hnot
  given: [CoheytingAlgebra α] (a : α)
  proof: by
  simpa only [CoheytingAlgebra.top_sdiff, codisjoint_iff_le_sup] using isLeast_sdiff ⊤ a

中文:
定理 isLeast_hnot
  条件: [CoheytingAlgebra α] (a : α)
  证明: by
  simpa only [CoheytingAlgebra.top_sdiff, codisjoint_iff_le_sup] using isLeast_sdiff ⊤ a

Depends on / 依赖: CoheytingAlgebra, CoheytingAlgebra.top_sdiff, codisjoint_iff_le_sup, isLeast_sdiff, top_sdiff
-/
theorem isLeast_hnot [CoheytingAlgebra α] (a : α) :
    IsLeast {w | Codisjoint a w} (￢a) := by
  simpa only [CoheytingAlgebra.top_sdiff, codisjoint_iff_le_sup] using isLeast_sdiff ⊤ a

/--
Instance `Nat.instDecidableIsLeast` / 实例 `Nat.instDecidableIsLeast`

English:
instance Nat.instDecidableIsLeast
  signature: (p : Nat -> Prop) (n : Nat) [DecidablePred p]
  body: decidable_of_iff (p n ∧ forall k < n, ¬p k) .and .rfl by
    simp [mem_lowerBounds, @imp_not_comm _ (p _)]

中文:
实例 Nat.instDecidableIsLeast
  签名: (p : 自然数 -> 命题) (n : 自然数) [DecidablePred p]
  定义体: decidable_of_iff (p n ∧ forall k < n, ¬p k) .and .rfl by
    simp [mem_lowerBounds, @imp_not_comm _ (p _)]

Depends on / 依赖: decidable_of_iff, imp_not_comm, mem_lowerBounds
-/
instance Nat.instDecidableIsLeast (p : Nat -> Prop) (n : Nat) [DecidablePred p] :
    Decidable (IsLeast { n : Nat | p n } n) :=
decidable_of_iff (p n ∧ forall k < n, ¬p k) .and .rfl by
    simp [mem_lowerBounds, @imp_not_comm _ (p _)]

/-- An alternative constructor for `SemilatticeSup` using `IsLUB`. -/
@[to_dual (attr := instance_reducible)
/-- An alternative constructor for `SemilatticeInf` using `IsGLB`. -/]
/--
Definition of `SemilatticeSup.ofIsLUB` / `SemilatticeSup.ofIsLUB` 的定义

English:
definition SemilatticeSup.ofIsLUB
  signature: [PartialOrder α] (sup : α -> α -> α)
  body: sup
  le_sup_left a b := (isLUB_pair a b).1 (mem_insert _ _)
  le_sup_right a b := (isLUB_pair a b).1 (mem_insert_of_mem _ (mem_singleton _))
  sup_le a b _ hac hbc := (isLUB_pair a b).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac)

中文:
定义 SemilatticeSup.ofIsLUB
  签名: [PartialOrder α] (sup : α -> α -> α)
  定义体: sup
  le_sup_left a b := (isLUB_pair a b).1 (mem_insert _ _)
  le_sup_right a b := (isLUB_pair a b).1 (mem_insert_of_mem _ (mem_singleton _))
  sup_le a b _ hac hbc := (isLUB_pair a b).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac)
-/
def SemilatticeSup.ofIsLUB [PartialOrder α] (sup : α -> α -> α)
    (isLUB_pair : forall a b, IsLUB {a, b} (sup a b)) :
    SemilatticeSup α where
  sup := sup
  le_sup_left a b := (isLUB_pair a b).1 (mem_insert _ _)
  le_sup_right a b := (isLUB_pair a b).1 (mem_insert_of_mem _ (mem_singleton _))
  sup_le a b _ hac hbc := (isLUB_pair a b).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac)

/-- An alternative constructor for `Lattice` using `IsLUB` and `IsGLB`. -/
@[instance_reducible, to_dual self (reorder := 3 4, 5 6)]
/--
Definition of `Lattice.ofIsLUBofIsGLB` / `Lattice.ofIsLUBofIsGLB` 的定义

English:
definition Lattice.ofIsLUBofIsGLB
  signature: [PartialOrder α] (sup inf : α -> α -> α)
  body: SemilatticeSup.ofIsLUB sup isLUB_pair
  __ := SemilatticeInf.ofIsGLB inf isGLB_pair

中文:
定义 Lattice.ofIsLUBofIsGLB
  签名: [PartialOrder α] (sup inf : α -> α -> α)
  定义体: SemilatticeSup.ofIsLUB sup isLUB_pair
  __ := SemilatticeInf.ofIsGLB inf isGLB_pair

Depends on / 依赖: SemilatticeSup, SemilatticeSup.ofIsLUB, isLUB_pair, ofIsLUB
-/
def Lattice.ofIsLUBofIsGLB [PartialOrder α] (sup inf : α -> α -> α)
    (isLUB_pair : forall a b, IsLUB {a, b} (sup a b)) (isGLB_pair : forall a b, IsGLB {a, b} (inf a b)) :
    Lattice α where
  __ := SemilatticeSup.ofIsLUB sup isLUB_pair
  __ := SemilatticeInf.ofIsGLB inf isGLB_pair
