/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Logic.Pairwise
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# The set lattice

This file is a collection of results on the complete atomic Boolean algebra structure of `Set α`.
Notation for the complete lattice operations can be found in `Mathlib/Order/SetNotation.lean`.

## Main declarations
* `Set.sInter_eq_biInter`, `Set.sUnion_eq_biInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `Set.completeAtomicBooleanAlgebra`: `Set α` is a `CompleteAtomicBooleanAlgebra` with `≤ = ⊆`,
  `< = ⊂`, `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference.
  See `Set.instBooleanAlgebra`.
* `Set.unionEqSigmaOfDisjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

@[expose] public section

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ κ₁ κ₂ : ι -> Sort*} {κ' : ι' -> Sort*}

namespace Set


/--
theorem `mem_iUnion₂` / 定理 `mem_iUnion₂`

English:
theorem mem_iUnion₂
  given: {x : γ} {s : forall i, κ i -> Set γ}
  statement: (x in ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
  proof: by
  simp_rw [mem_iUnion]

中文:
定理 mem_iUnion₂
  条件: {x : γ} {s : 对任意 i, κ i -> 集合 γ}
  结论: (x in ⋃ (i) (j), s i j) ↔ 存在 i j, x in s i j
  证明: by
  simp_rw [mem_iUnion]

Depends on / 依赖: mem_iUnion, simp_rw
-/
theorem mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x in ⋃ (i) (j), s i j) ↔ exists i j, x in s i j := by
  simp_rw [mem_iUnion]

/--
theorem `mem_iInter₂` / 定理 `mem_iInter₂`

English:
theorem mem_iInter₂
  given: {x : γ} {s : forall i, κ i -> Set γ}
  statement: (x in ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
  proof: by
  simp_rw [mem_iInter]

中文:
定理 mem_i整数er₂
  条件: {x : γ} {s : 对任意 i, κ i -> 集合 γ}
  结论: (x in ⋂ (i) (j), s i j) ↔ 对任意 i j, x in s i j
  证明: by
  simp_rw [mem_iInter]

Depends on / 依赖: mem_iInter, simp_rw
-/
theorem mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x in ⋂ (i) (j), s i j) ↔ forall i j, x in s i j := by
  simp_rw [mem_iInter]

/--
theorem `mem_iUnion_of_mem` / 定理 `mem_iUnion_of_mem`

English:
theorem mem_iUnion_of_mem
  given: {s : ι -> Set α} {a : α} (i : ι) (ha : a in s i)
  statement: a in ⋃ i, s i
  proof: mem_iUnion.2 ⟨i, ha⟩

中文:
定理 mem_iUnion_of_mem
  条件: {s : ι -> 集合 α} {a : α} (i : ι) (ha : a in s i)
  结论: a in ⋃ i, s i
  证明: mem_iUnion.2 ⟨i, ha⟩

Depends on / 依赖: mem_iUnion
-/
theorem mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι) (ha : a in s i) : a in ⋃ i, s i :=
  mem_iUnion.2 ⟨i, ha⟩

/--
theorem `mem_iUnion₂_of_mem` / 定理 `mem_iUnion₂_of_mem`

English:
theorem mem_iUnion₂_of_mem
  given: {s : forall i, κ i -> Set α} {a : α} {i : ι} (j : κ i) (ha : a in s i j)
  proof: mem_iUnion₂.2 ⟨i, j, ha⟩

中文:
定理 mem_iUnion₂_of_mem
  条件: {s : 对任意 i, κ i -> 集合 α} {a : α} {i : ι} (j : κ i) (ha : a in s i j)
  证明: mem_iUnion₂.2 ⟨i, j, ha⟩
-/
theorem mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} {a : α} {i : ι} (j : κ i) (ha : a in s i j) :
    a in ⋃ (i) (j), s i j :=
  mem_iUnion₂.2 ⟨i, j, ha⟩

/--
theorem `mem_iInter_of_mem` / 定理 `mem_iInter_of_mem`

English:
theorem mem_iInter_of_mem
  given: {s : ι -> Set α} {a : α} (h : forall i, a in s i)
  statement: a in ⋂ i, s i
  proof: mem_iInter.2 h

中文:
定理 mem_i整数er_of_mem
  条件: {s : ι -> 集合 α} {a : α} (h : 对任意 i, a in s i)
  结论: a in ⋂ i, s i
  证明: mem_iInter.2 h

Depends on / 依赖: mem_iInter
-/
theorem mem_iInter_of_mem {s : ι -> Set α} {a : α} (h : forall i, a in s i) : a in ⋂ i, s i :=
  mem_iInter.2 h

/--
theorem `mem_iInter₂_of_mem` / 定理 `mem_iInter₂_of_mem`

English:
theorem mem_iInter₂_of_mem
  given: {s : forall i, κ i -> Set α} {a : α} (h : forall i j, a in s i j)
  proof: mem_iInter₂.2 h

中文:
定理 mem_i整数er₂_of_mem
  条件: {s : 对任意 i, κ i -> 集合 α} {a : α} (h : 对任意 i j, a in s i j)
  证明: mem_iInter₂.2 h
-/
theorem mem_iInter₂_of_mem {s : forall i, κ i -> Set α} {a : α} (h : forall i j, a in s i j) :
    a in ⋂ (i) (j), s i j :=
  mem_iInter₂.2 h

/-! ### Union and intersection over an indexed family of sets -/

@[congr]
/--
theorem `iUnion_congr_Prop` / 定理 `iUnion_congr_Prop`

English:
theorem iUnion_congr_Prop
  statement: {p q : Prop} {f₁ : p -> Set α} {f₂ : q -> Set α} (pq : p ↔ q)
  proof: iSup_congr_Prop pq f

@[congr]

中文:
定理 iUnion_congr_Prop
  结论: {p q : 命题} {f₁ : p -> 集合 α} {f₂ : q -> 集合 α} (pq : p ↔ q)
  证明: iSup_congr_Prop pq f

@[congr]

Depends on / 依赖: iSup_congr_Prop
-/
theorem iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} {f₂ : q -> Set α} (pq : p ↔ q)
    (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ = iUnion f₂ :=
  iSup_congr_Prop pq f

@[congr]
/--
theorem `iInter_congr_Prop` / 定理 `iInter_congr_Prop`

English:
theorem iInter_congr_Prop
  statement: {p q : Prop} {f₁ : p -> Set α} {f₂ : q -> Set α} (pq : p ↔ q)
  proof: iInf_congr_Prop pq f

中文:
定理 i整数er_congr_Prop
  结论: {p q : 命题} {f₁ : p -> 集合 α} {f₂ : q -> 集合 α} (pq : p ↔ q)
  证明: iInf_congr_Prop pq f

Depends on / 依赖: iInf_congr_Prop
-/
theorem iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} {f₂ : q -> Set α} (pq : p ↔ q)
    (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ = iInter f₂ :=
  iInf_congr_Prop pq f

/--
theorem `iUnion_plift_up` / 定理 `iUnion_plift_up`

English:
theorem iUnion_plift_up
  given: (f : PLift ι -> Set α)
  statement: ⋃ i, f (PLift.up i) = ⋃ i, f i
  proof: iSup_plift_up _

中文:
定理 iUnion_plift_up
  条件: (f : 命题层提升 ι -> 集合 α)
  结论: ⋃ i, f (命题层提升.up i) = ⋃ i, f i
  证明: iSup_plift_up _

Depends on / 依赖: iSup_plift_up
-/
theorem iUnion_plift_up (f : PLift ι -> Set α) : ⋃ i, f (PLift.up i) = ⋃ i, f i :=
  iSup_plift_up _

/--
theorem `iUnion_plift_down` / 定理 `iUnion_plift_down`

English:
theorem iUnion_plift_down
  given: (f : ι -> Set α)
  statement: ⋃ i, f (PLift.down i) = ⋃ i, f i
  proof: iSup_plift_down _

中文:
定理 iUnion_plift_down
  条件: (f : ι -> 集合 α)
  结论: ⋃ i, f (命题层提升.down i) = ⋃ i, f i
  证明: iSup_plift_down _

Depends on / 依赖: iSup_plift_down
-/
theorem iUnion_plift_down (f : ι -> Set α) : ⋃ i, f (PLift.down i) = ⋃ i, f i :=
  iSup_plift_down _

/--
theorem `iInter_plift_up` / 定理 `iInter_plift_up`

English:
theorem iInter_plift_up
  given: (f : PLift ι -> Set α)
  statement: ⋂ i, f (PLift.up i) = ⋂ i, f i
  proof: iInf_plift_up _

中文:
定理 i整数er_plift_up
  条件: (f : 命题层提升 ι -> 集合 α)
  结论: ⋂ i, f (命题层提升.up i) = ⋂ i, f i
  证明: iInf_plift_up _

Depends on / 依赖: iInf_plift_up
-/
theorem iInter_plift_up (f : PLift ι -> Set α) : ⋂ i, f (PLift.up i) = ⋂ i, f i :=
  iInf_plift_up _

/--
theorem `iInter_plift_down` / 定理 `iInter_plift_down`

English:
theorem iInter_plift_down
  given: (f : ι -> Set α)
  statement: ⋂ i, f (PLift.down i) = ⋂ i, f i
  proof: iInf_plift_down _

中文:
定理 i整数er_plift_down
  条件: (f : ι -> 集合 α)
  结论: ⋂ i, f (命题层提升.down i) = ⋂ i, f i
  证明: iInf_plift_down _

Depends on / 依赖: iInf_plift_down
-/
theorem iInter_plift_down (f : ι -> Set α) : ⋂ i, f (PLift.down i) = ⋂ i, f i :=
  iInf_plift_down _

/--
theorem `iUnion_eq_if` / 定理 `iUnion_eq_if`

English:
theorem iUnion_eq_if
  given: {p : Prop} [Decidable p] (s : Set α)
  statement: ⋃ _ : p, s = if p then s else ∅
  proof: iSup_eq_if _

中文:
定理 iUnion_eq_if
  条件: {p : 命题} [可判定 p] (s : 集合 α)
  结论: ⋃ _ : p, s = if p then s else ∅
  证明: iSup_eq_if _

Depends on / 依赖: iSup_eq_if
-/
theorem iUnion_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋃ _ : p, s = if p then s else ∅ :=
  iSup_eq_if _

/--
theorem `iUnion_eq_dif` / 定理 `iUnion_eq_dif`

English:
theorem iUnion_eq_dif
  given: {p : Prop} [Decidable p] (s : p -> Set α)
  proof: iSup_eq_dif _

中文:
定理 iUnion_eq_dif
  条件: {p : 命题} [可判定 p] (s : p -> 集合 α)
  证明: iSup_eq_dif _

Depends on / 依赖: iSup_eq_dif
-/
theorem iUnion_eq_dif {p : Prop} [Decidable p] (s : p -> Set α) :
    ⋃ h : p, s h = if h : p then s h else ∅ :=
  iSup_eq_dif _

/--
theorem `iInter_eq_if` / 定理 `iInter_eq_if`

English:
theorem iInter_eq_if
  given: {p : Prop} [Decidable p] (s : Set α)
  statement: ⋂ _ : p, s = if p then s else univ
  proof: iInf_eq_if _

中文:
定理 i整数er_eq_if
  条件: {p : 命题} [可判定 p] (s : 集合 α)
  结论: ⋂ _ : p, s = if p then s else univ
  证明: iInf_eq_if _

Depends on / 依赖: iInf_eq_if
-/
theorem iInter_eq_if {p : Prop} [Decidable p] (s : Set α) : ⋂ _ : p, s = if p then s else univ :=
  iInf_eq_if _

/--
theorem `iInf_eq_dif` / 定理 `iInf_eq_dif`

English:
theorem iInf_eq_dif
  given: {p : Prop} [Decidable p] (s : p -> Set α)
  proof: _root_.iInf_eq_dif _

中文:
定理 iInf_eq_dif
  条件: {p : 命题} [可判定 p] (s : p -> 集合 α)
  证明: _root_.iInf_eq_dif _

Depends on / 依赖: _root_, _root_.iInf_eq_dif, iInf_eq_dif
-/
theorem iInf_eq_dif {p : Prop} [Decidable p] (s : p -> Set α) :
    ⋂ h : p, s h = if h : p then s h else univ :=
  _root_.iInf_eq_dif _

/--
theorem `exists_set_mem_of_union_eq_top` / 定理 `exists_set_mem_of_union_eq_top`

English:
theorem exists_set_mem_of_union_eq_top
  statement: {ι : Type*} (t : Set ι) (s : ι -> Set β)
  proof: by
  have p : x in ⊤ := Set.mem_univ x
  rw [← w]; rw [Set.mem_iUnion] at p
  simpa using p

中文:
定理 存在_set_mem_of_union_eq_top
  结论: {ι : 类型} (t : 集合 ι) (s : ι -> 集合 β)
  证明: by
  have p : x in ⊤ := Set.mem_univ x
  rw [← w]; rw [Set.mem_iUnion] at p
  simpa using p

Depends on / 依赖: Set.mem_iUnion, Set.mem_univ, mem_iUnion, mem_univ
-/
theorem exists_set_mem_of_union_eq_top {ι : Type*} (t : Set ι) (s : ι -> Set β)
    (w : ⋃ i in t, s i = ⊤) (x : β) : exists i in t, x in s i := by
  have p : x in ⊤ := Set.mem_univ x
  rw [← w]; rw [Set.mem_iUnion] at p
  simpa using p

/--
theorem `nonempty_of_union_eq_top_of_nonempty` / 定理 `nonempty_of_union_eq_top_of_nonempty`

English:
theorem nonempty_of_union_eq_top_of_nonempty
  statement: {ι : Type*} (t : Set ι) (s : ι -> Set α)
  proof: by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩

中文:
定理 nonempty_of_union_eq_top_of_nonempty
  结论: {ι : 类型} (t : 集合 ι) (s : ι -> 集合 α)
  证明: by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩

Depends on / 依赖: H.some, exists_set_mem_of_union_eq_top
-/
theorem nonempty_of_union_eq_top_of_nonempty {ι : Type*} (t : Set ι) (s : ι -> Set α)
    (H : Nonempty α) (w : ⋃ i in t, s i = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩

/--
theorem `nonempty_of_nonempty_iUnion` / 定理 `nonempty_of_nonempty_iUnion`

English:
theorem nonempty_of_nonempty_iUnion
  proof: by
  obtain ⟨x, hx⟩ := h_Union
exact ⟨Classical.choose mem_iUnion.mp hx⟩

中文:
定理 nonempty_of_nonempty_iUnion
  证明: by
  obtain ⟨x, hx⟩ := h_Union
exact ⟨Classical.choose mem_iUnion.mp hx⟩

Depends on / 依赖: Classical, Classical.choose, h_Union, mem_iUnion, mem_iUnion.mp
-/
theorem nonempty_of_nonempty_iUnion
    {s : ι -> Set α} (h_Union : (⋃ i, s i).Nonempty) : Nonempty ι := by
  obtain ⟨x, hx⟩ := h_Union
exact ⟨Classical.choose mem_iUnion.mp hx⟩

/--
theorem `nonempty_of_nonempty_iUnion_eq_univ` / 定理 `nonempty_of_nonempty_iUnion_eq_univ`

English:
theorem nonempty_of_nonempty_iUnion_eq_univ
  proof: nonempty_of_nonempty_iUnion (s := s) (by simpa only [h_Union] using univ_nonempty)

中文:
定理 nonempty_of_nonempty_iUnion_eq_univ
  证明: nonempty_of_nonempty_iUnion (s := s) (by simpa only [h_Union] using univ_nonempty)

Depends on / 依赖: h_Union, nonempty_of_nonempty_iUnion, univ_nonempty
-/
theorem nonempty_of_nonempty_iUnion_eq_univ
    {s : ι -> Set α} [Nonempty α] (h_Union : ⋃ i, s i = univ) : Nonempty ι :=
  nonempty_of_nonempty_iUnion (s := s) (by simpa only [h_Union] using univ_nonempty)

/--
theorem `ofPred_exists` / 定理 `ofPred_exists`

English:
theorem ofPred_exists
  given: (p : ι -> β -> Prop)
  statement: { x | exists i, p i x } = ⋃ i, { x | p i x }
  proof: ext fun _ => .symm mem_iUnion

@[deprecated (since := "2026-07-09")] alias setOf_exists := ofPred_exists

中文:
定理 ofPred_存在
  条件: (p : ι -> β -> 命题)
  结论: { x | 存在 i, p i x } = ⋃ i, { x | p i x }
  证明: ext fun _ => .symm mem_iUnion

@[deprecated (since := "2026-07-09")] alias setOf_exists := ofPred_exists

Depends on / 依赖: mem_iUnion
-/
theorem ofPred_exists (p : ι -> β -> Prop) : { x | exists i, p i x } = ⋃ i, { x | p i x } :=
ext fun _ => .symm mem_iUnion

@[deprecated (since := "2026-07-09")] alias setOf_exists := ofPred_exists

/--
theorem `ofPred_forall` / 定理 `ofPred_forall`

English:
theorem ofPred_forall
  given: (p : ι -> β -> Prop)
  statement: { x | forall i, p i x } = ⋂ i, { x | p i x }
  proof: ext fun _ => .symm mem_iInter

@[deprecated (since := "2026-07-09")] alias setOf_forall := ofPred_forall

中文:
定理 ofPred_对任意
  条件: (p : ι -> β -> 命题)
  结论: { x | 对任意 i, p i x } = ⋂ i, { x | p i x }
  证明: ext fun _ => .symm mem_iInter

@[deprecated (since := "2026-07-09")] alias setOf_forall := ofPred_forall

Depends on / 依赖: mem_iInter
-/
theorem ofPred_forall (p : ι -> β -> Prop) : { x | forall i, p i x } = ⋂ i, { x | p i x } :=
ext fun _ => .symm mem_iInter

@[deprecated (since := "2026-07-09")] alias setOf_forall := ofPred_forall

/--
theorem `iUnion_subset` / 定理 `iUnion_subset`

English:
theorem iUnion_subset
  given: {s : ι -> Set α} {t : Set α} (h : forall i, s i subseteq t)
  statement: ⋃ i, s i subseteq t
  proof: iSup_le h

中文:
定理 iUnion_subset
  条件: {s : ι -> 集合 α} {t : 集合 α} (h : 对任意 i, s i subseteq t)
  结论: ⋃ i, s i subseteq t
  证明: iSup_le h

Depends on / 依赖: iSup_le
-/
theorem iUnion_subset {s : ι -> Set α} {t : Set α} (h : forall i, s i subseteq t) : ⋃ i, s i subseteq t :=
  iSup_le h

/--
theorem `iUnion₂_subset` / 定理 `iUnion₂_subset`

English:
theorem iUnion₂_subset
  given: {s : forall i, κ i -> Set α} {t : Set α} (h : forall i j, s i j subseteq t)
  proof: iUnion_subset fun x => iUnion_subset (h x)

中文:
定理 iUnion₂_subset
  条件: {s : 对任意 i, κ i -> 集合 α} {t : 集合 α} (h : 对任意 i j, s i j subseteq t)
  证明: iUnion_subset fun x => iUnion_subset (h x)

Depends on / 依赖: iUnion_subset
-/
theorem iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set α} (h : forall i j, s i j subseteq t) :
    ⋃ (i) (j), s i j subseteq t :=
  iUnion_subset fun x => iUnion_subset (h x)

/--
theorem `subset_iInter` / 定理 `subset_iInter`

English:
theorem subset_iInter
  given: {t : Set β} {s : ι -> Set β} (h : forall i, t subseteq s i)
  statement: t subseteq ⋂ i, s i
  proof: le_iInf h

中文:
定理 subset_i整数er
  条件: {t : 集合 β} {s : ι -> 集合 β} (h : 对任意 i, t subseteq s i)
  结论: t subseteq ⋂ i, s i
  证明: le_iInf h

Depends on / 依赖: le_iInf
-/
theorem subset_iInter {t : Set β} {s : ι -> Set β} (h : forall i, t subseteq s i) : t subseteq ⋂ i, s i :=
  le_iInf h

/--
theorem `subset_iInter₂` / 定理 `subset_iInter₂`

English:
theorem subset_iInter₂
  given: {s : Set α} {t : forall i, κ i -> Set α} (h : forall i j, s subseteq t i j)
  proof: subset_iInter fun x => subset_iInter h x

@[simp]

中文:
定理 subset_i整数er₂
  条件: {s : 集合 α} {t : 对任意 i, κ i -> 集合 α} (h : 对任意 i j, s subseteq t i j)
  证明: subset_iInter fun x => subset_iInter h x

@[simp]

Depends on / 依赖: subset_iInter
-/
theorem subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set α} (h : forall i j, s subseteq t i j) :
    s subseteq ⋂ (i) (j), t i j :=
subset_iInter fun x => subset_iInter h x

@[simp]
/--
theorem `iUnion_subset_iff` / 定理 `iUnion_subset_iff`

English:
theorem iUnion_subset_iff
  given: {s : ι -> Set α} {t : Set α}
  statement: ⋃ i, s i subseteq t ↔ forall i, s i subseteq t
  proof: ⟨fun h _ => Subset.trans (le_iSup s _) h, iUnion_subset⟩

中文:
定理 iUnion_subset_iff
  条件: {s : ι -> 集合 α} {t : 集合 α}
  结论: ⋃ i, s i subseteq t ↔ 对任意 i, s i subseteq t
  证明: ⟨fun h _ => Subset.trans (le_iSup s _) h, iUnion_subset⟩

Depends on / 依赖: Subset, Subset.trans, iUnion_subset, le_iSup
-/
theorem iUnion_subset_iff {s : ι -> Set α} {t : Set α} : ⋃ i, s i subseteq t ↔ forall i, s i subseteq t :=
  ⟨fun h _ => Subset.trans (le_iSup s _) h, iUnion_subset⟩

/--
theorem `iUnion₂_subset_iff` / 定理 `iUnion₂_subset_iff`

English:
theorem iUnion₂_subset_iff
  given: {s : forall i, κ i -> Set α} {t : Set α}
  proof: by simp_rw [iUnion_subset_iff]

@[simp]

中文:
定理 iUnion₂_subset_iff
  条件: {s : 对任意 i, κ i -> 集合 α} {t : 集合 α}
  证明: by simp_rw [iUnion_subset_iff]

@[simp]

Depends on / 依赖: iUnion_subset_iff, simp_rw
-/
theorem iUnion₂_subset_iff {s : forall i, κ i -> Set α} {t : Set α} :
    ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t := by simp_rw [iUnion_subset_iff]

@[simp]
/--
theorem `subset_iInter_iff` / 定理 `subset_iInter_iff`

English:
theorem subset_iInter_iff
  given: {s : Set α} {t : ι -> Set α}
  statement: (s subseteq ⋂ i, t i) ↔ forall i, s subseteq t i
  proof: le_iInf_iff

中文:
定理 subset_i整数er_iff
  条件: {s : 集合 α} {t : ι -> 集合 α}
  结论: (s subseteq ⋂ i, t i) ↔ 对任意 i, s subseteq t i
  证明: le_iInf_iff

Depends on / 依赖: le_iInf_iff
-/
theorem subset_iInter_iff {s : Set α} {t : ι -> Set α} : (s subseteq ⋂ i, t i) ↔ forall i, s subseteq t i :=
  le_iInf_iff

/--
theorem `subset_iInter₂_iff` / 定理 `subset_iInter₂_iff`

English:
theorem subset_iInter₂_iff
  given: {s : Set α} {t : forall i, κ i -> Set α}
  proof: by simp_rw [subset_iInter_iff]

中文:
定理 subset_i整数er₂_iff
  条件: {s : 集合 α} {t : 对任意 i, κ i -> 集合 α}
  证明: by simp_rw [subset_iInter_iff]

Depends on / 依赖: simp_rw, subset_iInter_iff
-/
theorem subset_iInter₂_iff {s : Set α} {t : forall i, κ i -> Set α} :
    (s subseteq ⋂ (i) (j), t i j) ↔ forall i j, s subseteq t i j := by simp_rw [subset_iInter_iff]

/--
theorem `subset_iUnion` / 定理 `subset_iUnion`

English:
theorem subset_iUnion
  statement: forall (s : ι -> Set β) (i : ι), s i subseteq ⋃ i, s i
  proof: le_iSup

中文:
定理 subset_iUnion
  结论: 对任意 (s : ι -> 集合 β) (i : ι), s i subseteq ⋃ i, s i
  证明: le_iSup

Depends on / 依赖: le_iSup
-/
theorem subset_iUnion : forall (s : ι -> Set β) (i : ι), s i subseteq ⋃ i, s i :=
  le_iSup

/--
theorem `iInter_subset` / 定理 `iInter_subset`

English:
theorem iInter_subset
  statement: forall (s : ι -> Set β) (i : ι), ⋂ i, s i subseteq s i
  proof: iInf_le

中文:
定理 i整数er_subset
  结论: 对任意 (s : ι -> 集合 β) (i : ι), ⋂ i, s i subseteq s i
  证明: iInf_le

Depends on / 依赖: iInf_le
-/
theorem iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i, s i subseteq s i :=
  iInf_le

/--
lemma `iInter_subset_iUnion` / 引理 `iInter_subset_iUnion`

English:
lemma iInter_subset_iUnion
  given: [Nonempty ι] {s : ι -> Set α}
  statement: ⋂ i, s i subseteq ⋃ i, s i
  proof: iInf_le_iSup

中文:
引理 i整数er_subset_iUnion
  条件: [非空 ι] {s : ι -> 集合 α}
  结论: ⋂ i, s i subseteq ⋃ i, s i
  证明: iInf_le_iSup

Depends on / 依赖: iInf_le_iSup
-/
lemma iInter_subset_iUnion [Nonempty ι] {s : ι -> Set α} : ⋂ i, s i subseteq ⋃ i, s i := iInf_le_iSup

/--
theorem `subset_iUnion₂` / 定理 `subset_iUnion₂`

English:
theorem subset_iUnion₂
  given: {s : forall i, κ i -> Set α} (i : ι) (j : κ i)
  statement: s i j subseteq ⋃ (i') (j'), s i' j'
  proof: le_iSup₂ i j

中文:
定理 subset_iUnion₂
  条件: {s : 对任意 i, κ i -> 集合 α} (i : ι) (j : κ i)
  结论: s i j subseteq ⋃ (i') (j'), s i' j'
  证明: le_iSup₂ i j
-/
theorem subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) (j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j' :=
  le_iSup₂ i j

/--
theorem `iInter₂_subset` / 定理 `iInter₂_subset`

English:
theorem iInter₂_subset
  given: {s : forall i, κ i -> Set α} (i : ι) (j : κ i)
  statement: ⋂ (i) (j), s i j subseteq s i j
  proof: iInf₂_le i j

中文:
定理 i整数er₂_subset
  条件: {s : 对任意 i, κ i -> 集合 α} (i : ι) (j : κ i)
  结论: ⋂ (i) (j), s i j subseteq s i j
  证明: iInf₂_le i j
-/
theorem iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) (j : κ i) : ⋂ (i) (j), s i j subseteq s i j :=
  iInf₂_le i j

/--
theorem `subset_iUnion_of_subset` / 定理 `subset_iUnion_of_subset`

English:
theorem subset_iUnion_of_subset
  given: {s : Set α} {t : ι -> Set α} (i : ι) (h : s subseteq t i)
  statement: s subseteq ⋃ i, t i
  proof: le_iSup_of_le i h

中文:
定理 subset_iUnion_of_subset
  条件: {s : 集合 α} {t : ι -> 集合 α} (i : ι) (h : s subseteq t i)
  结论: s subseteq ⋃ i, t i
  证明: le_iSup_of_le i h

Depends on / 依赖: le_iSup_of_le
-/
theorem subset_iUnion_of_subset {s : Set α} {t : ι -> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i :=
  le_iSup_of_le i h

/--
theorem `iInter_subset_of_subset` / 定理 `iInter_subset_of_subset`

English:
theorem iInter_subset_of_subset
  given: {s : ι -> Set α} {t : Set α} (i : ι) (h : s i subseteq t)
  proof: iInf_le_of_le i h

中文:
定理 i整数er_subset_of_subset
  条件: {s : ι -> 集合 α} {t : 集合 α} (i : ι) (h : s i subseteq t)
  证明: iInf_le_of_le i h

Depends on / 依赖: iInf_le_of_le
-/
theorem iInter_subset_of_subset {s : ι -> Set α} {t : Set α} (i : ι) (h : s i subseteq t) :
    ⋂ i, s i subseteq t :=
  iInf_le_of_le i h

/--
theorem `subset_iUnion₂_of_subset` / 定理 `subset_iUnion₂_of_subset`

English:
theorem subset_iUnion₂_of_subset
  statement: {s : Set α} {t : forall i, κ i -> Set α} (i : ι) (j : κ i)
  proof: le_iSup₂_of_le i j h

中文:
定理 subset_iUnion₂_of_subset
  结论: {s : 集合 α} {t : 对任意 i, κ i -> 集合 α} (i : ι) (j : κ i)
  证明: le_iSup₂_of_le i j h
-/
theorem subset_iUnion₂_of_subset {s : Set α} {t : forall i, κ i -> Set α} (i : ι) (j : κ i)
    (h : s subseteq t i j) : s subseteq ⋃ (i) (j), t i j :=
  le_iSup₂_of_le i j h

/--
theorem `iInter₂_subset_of_subset` / 定理 `iInter₂_subset_of_subset`

English:
theorem iInter₂_subset_of_subset
  statement: {s : forall i, κ i -> Set α} {t : Set α} (i : ι) (j : κ i)
  proof: iInf₂_le_of_le i j h

中文:
定理 i整数er₂_subset_of_subset
  结论: {s : 对任意 i, κ i -> 集合 α} {t : 集合 α} (i : ι) (j : κ i)
  证明: iInf₂_le_of_le i j h
-/
theorem iInter₂_subset_of_subset {s : forall i, κ i -> Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j subseteq t) : ⋂ (i) (j), s i j subseteq t :=
  iInf₂_le_of_le i j h

/--
theorem `iUnion_mono` / 定理 `iUnion_mono`

English:
theorem iUnion_mono
  given: {s t : ι -> Set α} (h : forall i, s i subseteq t i)
  statement: ⋃ i, s i subseteq ⋃ i, t i
  proof: iSup_mono h

@[gcongr]

中文:
定理 iUnion_mono
  条件: {s t : ι -> 集合 α} (h : 对任意 i, s i subseteq t i)
  结论: ⋃ i, s i subseteq ⋃ i, t i
  证明: iSup_mono h

@[gcongr]

Depends on / 依赖: iSup_mono
-/
theorem iUnion_mono {s t : ι -> Set α} (h : forall i, s i subseteq t i) : ⋃ i, s i subseteq ⋃ i, t i :=
  iSup_mono h

@[gcongr]
/--
theorem `iUnion_mono''` / 定理 `iUnion_mono''`

English:
theorem iUnion_mono''
  given: {s t : ι -> Set α} (h : forall i, s i subseteq t i)
  statement: iUnion s subseteq iUnion t
  proof: iSup_mono h

中文:
定理 iUnion_mono''
  条件: {s t : ι -> 集合 α} (h : 对任意 i, s i subseteq t i)
  结论: iUnion s subseteq iUnion t
  证明: iSup_mono h

Depends on / 依赖: iSup_mono
-/
theorem iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i subseteq t i) : iUnion s subseteq iUnion t :=
  iSup_mono h

/--
theorem `iUnion₂_mono` / 定理 `iUnion₂_mono`

English:
theorem iUnion₂_mono
  given: {s t : forall i, κ i -> Set α} (h : forall i j, s i j subseteq t i j)
  proof: iSup₂_mono h

中文:
定理 iUnion₂_mono
  条件: {s t : 对任意 i, κ i -> 集合 α} (h : 对任意 i j, s i j subseteq t i j)
  证明: iSup₂_mono h
-/
theorem iUnion₂_mono {s t : forall i, κ i -> Set α} (h : forall i j, s i j subseteq t i j) :
    ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j :=
  iSup₂_mono h

/--
theorem `iInter_mono` / 定理 `iInter_mono`

English:
theorem iInter_mono
  given: {s t : ι -> Set α} (h : forall i, s i subseteq t i)
  statement: ⋂ i, s i subseteq ⋂ i, t i
  proof: iInf_mono h

@[gcongr]

中文:
定理 i整数er_mono
  条件: {s t : ι -> 集合 α} (h : 对任意 i, s i subseteq t i)
  结论: ⋂ i, s i subseteq ⋂ i, t i
  证明: iInf_mono h

@[gcongr]

Depends on / 依赖: iInf_mono
-/
theorem iInter_mono {s t : ι -> Set α} (h : forall i, s i subseteq t i) : ⋂ i, s i subseteq ⋂ i, t i :=
  iInf_mono h

@[gcongr]
/--
theorem `iInter_mono''` / 定理 `iInter_mono''`

English:
theorem iInter_mono''
  given: {s t : ι -> Set α} (h : forall i, s i subseteq t i)
  statement: iInter s subseteq iInter t
  proof: iInf_mono h

中文:
定理 i整数er_mono''
  条件: {s t : ι -> 集合 α} (h : 对任意 i, s i subseteq t i)
  结论: i整数er s subseteq i整数er t
  证明: iInf_mono h

Depends on / 依赖: iInf_mono
-/
theorem iInter_mono'' {s t : ι -> Set α} (h : forall i, s i subseteq t i) : iInter s subseteq iInter t :=
  iInf_mono h

/--
theorem `iInter₂_mono` / 定理 `iInter₂_mono`

English:
theorem iInter₂_mono
  given: {s t : forall i, κ i -> Set α} (h : forall i j, s i j subseteq t i j)
  proof: iInf₂_mono h

中文:
定理 i整数er₂_mono
  条件: {s t : 对任意 i, κ i -> 集合 α} (h : 对任意 i j, s i j subseteq t i j)
  证明: iInf₂_mono h
-/
theorem iInter₂_mono {s t : forall i, κ i -> Set α} (h : forall i j, s i j subseteq t i j) :
    ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j :=
  iInf₂_mono h

/--
theorem `iUnion_mono'` / 定理 `iUnion_mono'`

English:
theorem iUnion_mono'
  given: {s : ι -> Set α} {t : ι₂ -> Set α} (h : forall i, exists j, s i subseteq t j)
  proof: iSup_mono' h

中文:
定理 iUnion_mono'
  条件: {s : ι -> 集合 α} {t : ι₂ -> 集合 α} (h : 对任意 i, 存在 j, s i subseteq t j)
  证明: iSup_mono' h

Depends on / 依赖: iSup_mono
-/
theorem iUnion_mono' {s : ι -> Set α} {t : ι₂ -> Set α} (h : forall i, exists j, s i subseteq t j) :
    ⋃ i, s i subseteq ⋃ i, t i :=
  iSup_mono' h

/--
theorem `iUnion₂_mono'` / 定理 `iUnion₂_mono'`

English:
theorem iUnion₂_mono'
  statement: {s : forall i, κ i -> Set α} {t : forall i', κ' i' -> Set α}
  proof: iSup₂_mono' h

中文:
定理 iUnion₂_mono'
  结论: {s : 对任意 i, κ i -> 集合 α} {t : 对任意 i', κ' i' -> 集合 α}
  证明: iSup₂_mono' h
-/
theorem iUnion₂_mono' {s : forall i, κ i -> Set α} {t : forall i', κ' i' -> Set α}
    (h : forall i j, exists i' j', s i j subseteq t i' j') : ⋃ (i) (j), s i j subseteq ⋃ (i') (j'), t i' j' :=
  iSup₂_mono' h

/--
theorem `iInter_mono'` / 定理 `iInter_mono'`

English:
theorem iInter_mono'
  given: {s : ι -> Set α} {t : ι' -> Set α} (h : forall j, exists i, s i subseteq t j)
  proof: Set.subset_iInter fun j =>
    let ⟨i, hi⟩ := h j
    iInter_subset_of_subset i hi

中文:
定理 i整数er_mono'
  条件: {s : ι -> 集合 α} {t : ι' -> 集合 α} (h : 对任意 j, 存在 i, s i subseteq t j)
  证明: Set.subset_iInter fun j =>
    let ⟨i, hi⟩ := h j
    iInter_subset_of_subset i hi

Depends on / 依赖: Set.subset_iInter, iInter_subset_of_subset, subset_iInter
-/
theorem iInter_mono' {s : ι -> Set α} {t : ι' -> Set α} (h : forall j, exists i, s i subseteq t j) :
    ⋂ i, s i subseteq ⋂ j, t j :=
  Set.subset_iInter fun j =>
    let ⟨i, hi⟩ := h j
    iInter_subset_of_subset i hi

/--
theorem `iInter₂_mono'` / 定理 `iInter₂_mono'`

English:
theorem iInter₂_mono'
  statement: {s : forall i, κ i -> Set α} {t : forall i', κ' i' -> Set α}
  proof: subset_iInter₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (iInter₂_subset _ _).trans hst

中文:
定理 i整数er₂_mono'
  结论: {s : 对任意 i, κ i -> 集合 α} {t : 对任意 i', κ' i' -> 集合 α}
  证明: subset_iInter₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (iInter₂_subset _ _).trans hst
-/
theorem iInter₂_mono' {s : forall i, κ i -> Set α} {t : forall i', κ' i' -> Set α}
    (h : forall i' j', exists i j, s i j subseteq t i' j') : ⋂ (i) (j), s i j subseteq ⋂ (i') (j'), t i' j' :=
  subset_iInter₂_iff.2 fun i' j' =>
    let ⟨_, _, hst⟩ := h i' j'
    (iInter₂_subset _ _).trans hst

/--
theorem `iUnion₂_subset_iUnion` / 定理 `iUnion₂_subset_iUnion`

English:
theorem iUnion₂_subset_iUnion
  given: (κ : ι -> Sort*) (s : ι -> Set α)
  proof: iUnion_mono fun _ => iUnion_subset fun _ => Subset.rfl

中文:
定理 iUnion₂_subset_iUnion
  条件: (κ : ι -> 类型层*) (s : ι -> 集合 α)
  证明: iUnion_mono fun _ => iUnion_subset fun _ => Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, iUnion_mono, iUnion_subset
-/
theorem iUnion₂_subset_iUnion (κ : ι -> Sort*) (s : ι -> Set α) :
    ⋃ (i) (_ : κ i), s i subseteq ⋃ i, s i :=
  iUnion_mono fun _ => iUnion_subset fun _ => Subset.rfl

/--
theorem `iInter_subset_iInter₂` / 定理 `iInter_subset_iInter₂`

English:
theorem iInter_subset_iInter₂
  given: (κ : ι -> Sort*) (s : ι -> Set α)
  proof: iInter_mono fun _ => subset_iInter fun _ => Subset.rfl

中文:
定理 i整数er_subset_i整数er₂
  条件: (κ : ι -> 类型层*) (s : ι -> 集合 α)
  证明: iInter_mono fun _ => subset_iInter fun _ => Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, iInter_mono, subset_iInter
-/
theorem iInter_subset_iInter₂ (κ : ι -> Sort*) (s : ι -> Set α) :
    ⋂ i, s i subseteq ⋂ (i) (_ : κ i), s i :=
  iInter_mono fun _ => subset_iInter fun _ => Subset.rfl

/--
theorem `iUnion_ofPred` / 定理 `iUnion_ofPred`

English:
theorem iUnion_ofPred
  given: (P : ι -> α -> Prop)
  statement: ⋃ i, { x : α | P i x } = { x : α | exists i, P i x }
  proof: by
  ext
  exact mem_iUnion

@[deprecated (since := "2026-07-09")] alias iUnion_setOf := iUnion_ofPred

中文:
定理 iUnion_ofPred
  条件: (P : ι -> α -> 命题)
  结论: ⋃ i, { x : α | P i x } = { x : α | 存在 i, P i x }
  证明: by
  ext
  exact mem_iUnion

@[deprecated (since := "2026-07-09")] alias iUnion_setOf := iUnion_ofPred

Depends on / 依赖: mem_iUnion
-/
theorem iUnion_ofPred (P : ι -> α -> Prop) : ⋃ i, { x : α | P i x } = { x : α | exists i, P i x } := by
  ext
  exact mem_iUnion

@[deprecated (since := "2026-07-09")] alias iUnion_setOf := iUnion_ofPred

/--
theorem `iInter_ofPred` / 定理 `iInter_ofPred`

English:
theorem iInter_ofPred
  given: (P : ι -> α -> Prop)
  statement: ⋂ i, { x : α | P i x } = { x : α | forall i, P i x }
  proof: by
  ext
  exact mem_iInter

@[deprecated (since := "2026-07-09")] alias iInter_setOf := iInter_ofPred

中文:
定理 i整数er_ofPred
  条件: (P : ι -> α -> 命题)
  结论: ⋂ i, { x : α | P i x } = { x : α | 对任意 i, P i x }
  证明: by
  ext
  exact mem_iInter

@[deprecated (since := "2026-07-09")] alias iInter_setOf := iInter_ofPred

Depends on / 依赖: mem_iInter
-/
theorem iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P i x } = { x : α | forall i, P i x } := by
  ext
  exact mem_iInter

@[deprecated (since := "2026-07-09")] alias iInter_setOf := iInter_ofPred

/--
theorem `iUnion_congr_of_surjective` / 定理 `iUnion_congr_of_surjective`

English:
theorem iUnion_congr_of_surjective
  statement: {f : ι -> Set α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h)
  proof: h1.iSup_congr h h2

中文:
定理 iUnion_congr_of_surjective
  结论: {f : ι -> 集合 α} {g : ι₂ -> 集合 α} (h : ι -> ι₂) (h1 : 满射 h)
  证明: h1.iSup_congr h h2

Depends on / 依赖: h1.iSup_congr, iSup_congr
-/
theorem iUnion_congr_of_surjective {f : ι -> Set α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h)
    (h2 : forall x, g (h x) = f x) : ⋃ x, f x = ⋃ y, g y :=
  h1.iSup_congr h h2

/--
theorem `iInter_congr_of_surjective` / 定理 `iInter_congr_of_surjective`

English:
theorem iInter_congr_of_surjective
  statement: {f : ι -> Set α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h)
  proof: h1.iInf_congr h h2

中文:
定理 i整数er_congr_of_surjective
  结论: {f : ι -> 集合 α} {g : ι₂ -> 集合 α} (h : ι -> ι₂) (h1 : 满射 h)
  证明: h1.iInf_congr h h2

Depends on / 依赖: h1.iInf_congr, iInf_congr
-/
theorem iInter_congr_of_surjective {f : ι -> Set α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h)
    (h2 : forall x, g (h x) = f x) : ⋂ x, f x = ⋂ y, g y :=
  h1.iInf_congr h h2

/--
lemma `iUnion_congr` / 引理 `iUnion_congr`

English:
lemma iUnion_congr
  given: {s t : ι -> Set α} (h : forall i, s i = t i)
  statement: ⋃ i, s i = ⋃ i, t i
  proof: iSup_congr h

中文:
引理 iUnion_congr
  条件: {s t : ι -> 集合 α} (h : 对任意 i, s i = t i)
  结论: ⋃ i, s i = ⋃ i, t i
  证明: iSup_congr h

Depends on / 依赖: iSup_congr
-/
lemma iUnion_congr {s t : ι -> Set α} (h : forall i, s i = t i) : ⋃ i, s i = ⋃ i, t i := iSup_congr h
/--
lemma `iInter_congr` / 引理 `iInter_congr`

English:
lemma iInter_congr
  given: {s t : ι -> Set α} (h : forall i, s i = t i)
  statement: ⋂ i, s i = ⋂ i, t i
  proof: iInf_congr h

中文:
引理 i整数er_congr
  条件: {s t : ι -> 集合 α} (h : 对任意 i, s i = t i)
  结论: ⋂ i, s i = ⋂ i, t i
  证明: iInf_congr h

Depends on / 依赖: iInf_congr
-/
lemma iInter_congr {s t : ι -> Set α} (h : forall i, s i = t i) : ⋂ i, s i = ⋂ i, t i := iInf_congr h

/--
lemma `iUnion₂_congr` / 引理 `iUnion₂_congr`

English:
lemma iUnion₂_congr
  given: {s t : forall i, κ i -> Set α} (h : forall i j, s i j = t i j)
  proof: iUnion_congr fun i => iUnion_congr h i

中文:
引理 iUnion₂_congr
  条件: {s t : 对任意 i, κ i -> 集合 α} (h : 对任意 i j, s i j = t i j)
  证明: iUnion_congr fun i => iUnion_congr h i

Depends on / 依赖: iUnion_congr
-/
lemma iUnion₂_congr {s t : forall i, κ i -> Set α} (h : forall i j, s i j = t i j) :
    ⋃ (i) (j), s i j = ⋃ (i) (j), t i j :=
iUnion_congr fun i => iUnion_congr h i

/--
lemma `iInter₂_congr` / 引理 `iInter₂_congr`

English:
lemma iInter₂_congr
  given: {s t : forall i, κ i -> Set α} (h : forall i j, s i j = t i j)
  proof: iInter_congr fun i => iInter_congr h i

中文:
引理 i整数er₂_congr
  条件: {s t : 对任意 i, κ i -> 集合 α} (h : 对任意 i j, s i j = t i j)
  证明: iInter_congr fun i => iInter_congr h i

Depends on / 依赖: iInter_congr
-/
lemma iInter₂_congr {s t : forall i, κ i -> Set α} (h : forall i j, s i j = t i j) :
    ⋂ (i) (j), s i j = ⋂ (i) (j), t i j :=
iInter_congr fun i => iInter_congr h i

/--
theorem `BijOn.iUnion_comp` / 定理 `BijOn.iUnion_comp`

English:
theorem BijOn.iUnion_comp
  statement: {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> Set α)
  proof: hf.iSup_comp g

中文:
定理 双射限制.iUnion_comp
  结论: {s : 集合 β} {t : 集合 γ} {f : β -> γ} (g : γ -> 集合 α)
  证明: hf.iSup_comp g

Depends on / 依赖: hf.iSup_comp, iSup_comp
-/
theorem BijOn.iUnion_comp {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> Set α)
    (hf : Set.BijOn f s t) : ⋃ x in s, g (f x) = ⋃ y in t, g y := hf.iSup_comp g

/--
theorem `BijOn.iInter_comp` / 定理 `BijOn.iInter_comp`

English:
theorem BijOn.iInter_comp
  statement: {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> Set α)
  proof: hf.iInf_comp g

中文:
定理 双射限制.i整数er_comp
  结论: {s : 集合 β} {t : 集合 γ} {f : β -> γ} (g : γ -> 集合 α)
  证明: hf.iInf_comp g

Depends on / 依赖: hf.iInf_comp, iInf_comp
-/
theorem BijOn.iInter_comp {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> Set α)
    (hf : Set.BijOn f s t) : ⋂ x in s, g (f x) = ⋂ y in t, g y := hf.iInf_comp g

/--
theorem `BijOn.iUnion_congr` / 定理 `BijOn.iUnion_congr`

English:
theorem BijOn.iUnion_congr
  statement: {s : Set β} {t : Set γ} (f : β -> Set α) (g : γ -> Set α) {h : β -> γ}
  proof: h1.iSup_congr f g h2

中文:
定理 双射限制.iUnion_congr
  结论: {s : 集合 β} {t : 集合 γ} (f : β -> 集合 α) (g : γ -> 集合 α) {h : β -> γ}
  证明: h1.iSup_congr f g h2

Depends on / 依赖: h1.iSup_congr, iSup_congr
-/
theorem BijOn.iUnion_congr {s : Set β} {t : Set γ} (f : β -> Set α) (g : γ -> Set α) {h : β -> γ}
    (h1 : Set.BijOn h s t) (h2 : forall x, g (h x) = f x) : ⋃ x in s, f x = ⋃ y in t, g y :=
  h1.iSup_congr f g h2

/--
theorem `BijOn.iInter_congr` / 定理 `BijOn.iInter_congr`

English:
theorem BijOn.iInter_congr
  statement: {s : Set β} {t : Set γ} (f : β -> Set α) (g : γ -> Set α) {h : β -> γ}
  proof: h1.iInf_congr f g h2

中文:
定理 双射限制.i整数er_congr
  结论: {s : 集合 β} {t : 集合 γ} (f : β -> 集合 α) (g : γ -> 集合 α) {h : β -> γ}
  证明: h1.iInf_congr f g h2

Depends on / 依赖: h1.iInf_congr, iInf_congr
-/
theorem BijOn.iInter_congr {s : Set β} {t : Set γ} (f : β -> Set α) (g : γ -> Set α) {h : β -> γ}
    (h1 : Set.BijOn h s t) (h2 : forall x, g (h x) = f x) : ⋂ x in s, f x = ⋂ y in t, g y :=
  h1.iInf_congr f g h2

section Nonempty
variable [Nonempty ι] {f : ι -> Set α} {s : Set α}

/--
lemma `iUnion_const` / 引理 `iUnion_const`

English:
lemma iUnion_const
  given: (s : Set β)
  statement: ⋃ _ : ι, s = s
  proof: iSup_const

中文:
引理 iUnion_const
  条件: (s : 集合 β)
  结论: ⋃ _ : ι, s = s
  证明: iSup_const

Depends on / 依赖: iSup_const
-/
lemma iUnion_const (s : Set β) : ⋃ _ : ι, s = s := iSup_const
/--
lemma `iInter_const` / 引理 `iInter_const`

English:
lemma iInter_const
  given: (s : Set β)
  statement: ⋂ _ : ι, s = s
  proof: iInf_const

中文:
引理 i整数er_const
  条件: (s : 集合 β)
  结论: ⋂ _ : ι, s = s
  证明: iInf_const

Depends on / 依赖: iInf_const
-/
lemma iInter_const (s : Set β) : ⋂ _ : ι, s = s := iInf_const

/--
lemma `iUnion_eq_const` / 引理 `iUnion_eq_const`

English:
lemma iUnion_eq_const
  given: (hf : forall i, f i = s)
  statement: ⋃ i, f i = s
  proof: (iUnion_congr hf).trans iUnion_const _

中文:
引理 iUnion_eq_const
  条件: (hf : 对任意 i, f i = s)
  结论: ⋃ i, f i = s
  证明: (iUnion_congr hf).trans iUnion_const _

Depends on / 依赖: iUnion_congr, iUnion_const
-/
lemma iUnion_eq_const (hf : forall i, f i = s) : ⋃ i, f i = s :=
(iUnion_congr hf).trans iUnion_const _

/--
lemma `iInter_eq_const` / 引理 `iInter_eq_const`

English:
lemma iInter_eq_const
  given: (hf : forall i, f i = s)
  statement: ⋂ i, f i = s
  proof: (iInter_congr hf).trans iInter_const _

中文:
引理 i整数er_eq_const
  条件: (hf : 对任意 i, f i = s)
  结论: ⋂ i, f i = s
  证明: (iInter_congr hf).trans iInter_const _

Depends on / 依赖: iInter_congr, iInter_const
-/
lemma iInter_eq_const (hf : forall i, f i = s) : ⋂ i, f i = s :=
(iInter_congr hf).trans iInter_const _

end Nonempty

@[simp]
/--
theorem `compl_iUnion` / 定理 `compl_iUnion`

English:
theorem compl_iUnion
  given: (s : ι -> Set β)
  statement: (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ
  proof: compl_iSup

中文:
定理 compl_iUnion
  条件: (s : ι -> 集合 β)
  结论: (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ
  证明: compl_iSup

Depends on / 依赖: compl_iSup
-/
theorem compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ :=
  compl_iSup

/--
theorem `compl_iUnion₂` / 定理 `compl_iUnion₂`

English:
theorem compl_iUnion₂
  given: (s : forall i, κ i -> Set α)
  statement: (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ
  proof: by
  simp_rw [compl_iUnion]

@[simp]

中文:
定理 compl_iUnion₂
  条件: (s : 对任意 i, κ i -> 集合 α)
  结论: (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ
  证明: by
  simp_rw [compl_iUnion]

@[simp]

Depends on / 依赖: IsContMDiffRiemannianBundle, IsContMDiffRiemannianBundle.of_le, compl_iUnion, h.out, of_le, simp_rw
-/
theorem compl_iUnion₂ (s : forall i, κ i -> Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iUnion]

@[simp]
/--
theorem `compl_iInter` / 定理 `compl_iInter`

English:
theorem compl_iInter
  given: (s : ι -> Set β)
  statement: (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ
  proof: compl_iInf

中文:
定理 compl_i整数er
  条件: (s : ι -> 集合 β)
  结论: (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ
  证明: compl_iInf

Depends on / 依赖: IsContMDiffRiemannianBundle, IsContMDiffRiemannianBundle.of_le, compl_iInf, le_top, of_le
-/
theorem compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ :=
  compl_iInf

/--
theorem `compl_iInter₂` / 定理 `compl_iInter₂`

English:
theorem compl_iInter₂
  given: (s : forall i, κ i -> Set α)
  statement: (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ
  proof: by
  simp_rw [compl_iInter]

中文:
定理 compl_i整数er₂
  条件: (s : 对任意 i, κ i -> 集合 α)
  结论: (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ
  证明: by
  simp_rw [compl_iInter]

Depends on / 依赖: compl_iInter, simp_rw
-/
theorem compl_iInter₂ (s : forall i, κ i -> Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ := by
  simp_rw [compl_iInter]

-- classical -- complete_boolean_algebra
/--
theorem `iUnion_eq_compl_iInter_compl` / 定理 `iUnion_eq_compl_iInter_compl`

English:
theorem iUnion_eq_compl_iInter_compl
  given: (s : ι -> Set β)
  statement: ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ
  proof: by
  simp only [compl_iInter, compl_compl]

中文:
定理 iUnion_eq_compl_i整数er_compl
  条件: (s : ι -> 集合 β)
  结论: ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ
  证明: by
  simp only [compl_iInter, compl_compl]

Depends on / 依赖: compl_compl, compl_iInter
-/
theorem iUnion_eq_compl_iInter_compl (s : ι -> Set β) : ⋃ i, s i = (⋂ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iInter, compl_compl]

-- classical -- complete_boolean_algebra
/--
theorem `iInter_eq_compl_iUnion_compl` / 定理 `iInter_eq_compl_iUnion_compl`

English:
theorem iInter_eq_compl_iUnion_compl
  given: (s : ι -> Set β)
  statement: ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ
  proof: by
  simp only [compl_iUnion, compl_compl]

中文:
定理 i整数er_eq_compl_iUnion_compl
  条件: (s : ι -> 集合 β)
  结论: ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ
  证明: by
  simp only [compl_iUnion, compl_compl]

Depends on / 依赖: compl_compl, compl_iUnion
-/
theorem iInter_eq_compl_iUnion_compl (s : ι -> Set β) : ⋂ i, s i = (⋃ i, (s i)ᶜ)ᶜ := by
  simp only [compl_iUnion, compl_compl]

/--
theorem `inter_iUnion` / 定理 `inter_iUnion`

English:
theorem inter_iUnion
  given: (s : Set β) (t : ι -> Set β)
  statement: (s inter ⋃ i, t i) = ⋃ i, s inter t i
  proof: inf_iSup_eq _ _

中文:
定理 inter_iUnion
  条件: (s : 集合 β) (t : ι -> 集合 β)
  结论: (s inter ⋃ i, t i) = ⋃ i, s inter t i
  证明: inf_iSup_eq _ _

Depends on / 依赖: inf_iSup_eq
-/
theorem inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃ i, t i) = ⋃ i, s inter t i :=
  inf_iSup_eq _ _

/--
theorem `iUnion_inter` / 定理 `iUnion_inter`

English:
theorem iUnion_inter
  given: (s : Set β) (t : ι -> Set β)
  statement: (⋃ i, t i) inter s = ⋃ i, t i inter s
  proof: iSup_inf_eq _ _

中文:
定理 iUnion_inter
  条件: (s : 集合 β) (t : ι -> 集合 β)
  结论: (⋃ i, t i) inter s = ⋃ i, t i inter s
  证明: iSup_inf_eq _ _

Depends on / 依赖: iSup_inf_eq
-/
theorem iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i) inter s = ⋃ i, t i inter s :=
  iSup_inf_eq _ _

/--
theorem `iUnion_union_distrib` / 定理 `iUnion_union_distrib`

English:
theorem iUnion_union_distrib
  given: (s : ι -> Set β) (t : ι -> Set β)
  proof: iSup_sup_eq

中文:
定理 iUnion_union_distrib
  条件: (s : ι -> 集合 β) (t : ι -> 集合 β)
  证明: iSup_sup_eq

Depends on / 依赖: iSup_sup_eq
-/
theorem iUnion_union_distrib (s : ι -> Set β) (t : ι -> Set β) :
    ⋃ i, s i union t i = (⋃ i, s i) union ⋃ i, t i :=
  iSup_sup_eq

/--
theorem `iInter_inter_distrib` / 定理 `iInter_inter_distrib`

English:
theorem iInter_inter_distrib
  given: (s : ι -> Set β) (t : ι -> Set β)
  proof: iInf_inf_eq

中文:
定理 i整数er_inter_distrib
  条件: (s : ι -> 集合 β) (t : ι -> 集合 β)
  证明: iInf_inf_eq

Depends on / 依赖: iInf_inf_eq
-/
theorem iInter_inter_distrib (s : ι -> Set β) (t : ι -> Set β) :
    ⋂ i, s i inter t i = (⋂ i, s i) inter ⋂ i, t i :=
  iInf_inf_eq

/--
theorem `union_iUnion` / 定理 `union_iUnion`

English:
theorem union_iUnion
  given: [Nonempty ι] (s : Set β) (t : ι -> Set β)
  statement: (s union ⋃ i, t i) = ⋃ i, s union t i
  proof: sup_iSup

中文:
定理 union_iUnion
  条件: [非空 ι] (s : 集合 β) (t : ι -> 集合 β)
  结论: (s union ⋃ i, t i) = ⋃ i, s union t i
  证明: sup_iSup

Depends on / 依赖: sup_iSup
-/
theorem union_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β) : (s union ⋃ i, t i) = ⋃ i, s union t i :=
  sup_iSup

/--
theorem `iUnion_union` / 定理 `iUnion_union`

English:
theorem iUnion_union
  given: [Nonempty ι] (s : Set β) (t : ι -> Set β)
  statement: (⋃ i, t i) union s = ⋃ i, t i union s
  proof: iSup_sup

中文:
定理 iUnion_union
  条件: [非空 ι] (s : 集合 β) (t : ι -> 集合 β)
  结论: (⋃ i, t i) union s = ⋃ i, t i union s
  证明: iSup_sup

Depends on / 依赖: iSup_sup
-/
theorem iUnion_union [Nonempty ι] (s : Set β) (t : ι -> Set β) : (⋃ i, t i) union s = ⋃ i, t i union s :=
  iSup_sup

/--
theorem `inter_iInter` / 定理 `inter_iInter`

English:
theorem inter_iInter
  given: [Nonempty ι] (s : Set β) (t : ι -> Set β)
  statement: (s inter ⋂ i, t i) = ⋂ i, s inter t i
  proof: inf_iInf

中文:
定理 inter_i整数er
  条件: [非空 ι] (s : 集合 β) (t : ι -> 集合 β)
  结论: (s inter ⋂ i, t i) = ⋂ i, s inter t i
  证明: inf_iInf

Depends on / 依赖: inf_iInf
-/
theorem inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β) : (s inter ⋂ i, t i) = ⋂ i, s inter t i :=
  inf_iInf

/--
theorem `iInter_inter` / 定理 `iInter_inter`

English:
theorem iInter_inter
  given: [Nonempty ι] (s : Set β) (t : ι -> Set β)
  statement: (⋂ i, t i) inter s = ⋂ i, t i inter s
  proof: iInf_inf

中文:
定理 i整数er_inter
  条件: [非空 ι] (s : 集合 β) (t : ι -> 集合 β)
  结论: (⋂ i, t i) inter s = ⋂ i, t i inter s
  证明: iInf_inf

Depends on / 依赖: iInf_inf
-/
theorem iInter_inter [Nonempty ι] (s : Set β) (t : ι -> Set β) : (⋂ i, t i) inter s = ⋂ i, t i inter s :=
  iInf_inf

/--
theorem `insert_iUnion` / 定理 `insert_iUnion`

English:
theorem insert_iUnion
  given: [Nonempty ι] (x : β) (t : ι -> Set β)
  proof: by
  simp_rw [← union_singleton, iUnion_union]

中文:
定理 insert_iUnion
  条件: [非空 ι] (x : β) (t : ι -> 集合 β)
  证明: by
  simp_rw [← union_singleton, iUnion_union]

Depends on / 依赖: iUnion_union, simp_rw, union_singleton
-/
theorem insert_iUnion [Nonempty ι] (x : β) (t : ι -> Set β) :
    insert x (⋃ i, t i) = ⋃ i, insert x (t i) := by
  simp_rw [← union_singleton, iUnion_union]

-- classical
/--
theorem `union_iInter` / 定理 `union_iInter`

English:
theorem union_iInter
  given: (s : Set β) (t : ι -> Set β)
  statement: (s union ⋂ i, t i) = ⋂ i, s union t i
  proof: sup_iInf_eq _ _

中文:
定理 union_i整数er
  条件: (s : 集合 β) (t : ι -> 集合 β)
  结论: (s union ⋂ i, t i) = ⋂ i, s union t i
  证明: sup_iInf_eq _ _

Depends on / 依赖: sup_iInf_eq
-/
theorem union_iInter (s : Set β) (t : ι -> Set β) : (s union ⋂ i, t i) = ⋂ i, s union t i :=
  sup_iInf_eq _ _

/--
theorem `iInter_union` / 定理 `iInter_union`

English:
theorem iInter_union
  given: (s : ι -> Set β) (t : Set β)
  statement: (⋂ i, s i) union t = ⋂ i, s i union t
  proof: iInf_sup_eq _ _

中文:
定理 i整数er_union
  条件: (s : ι -> 集合 β) (t : 集合 β)
  结论: (⋂ i, s i) union t = ⋂ i, s i union t
  证明: iInf_sup_eq _ _

Depends on / 依赖: iInf_sup_eq
-/
theorem iInter_union (s : ι -> Set β) (t : Set β) : (⋂ i, s i) union t = ⋂ i, s i union t :=
  iInf_sup_eq _ _

/--
theorem `insert_iInter` / 定理 `insert_iInter`

English:
theorem insert_iInter
  given: (x : β) (t : ι -> Set β)
  statement: insert x (⋂ i, t i) = ⋂ i, insert x (t i)
  proof: by
  simp_rw [← union_singleton, iInter_union]

中文:
定理 insert_i整数er
  条件: (x : β) (t : ι -> 集合 β)
  结论: insert x (⋂ i, t i) = ⋂ i, insert x (t i)
  证明: by
  simp_rw [← union_singleton, iInter_union]

Depends on / 依赖: g.toRiemannianMetric, iInter_union, simp_rw, toRiemannianMetric, union_singleton
-/
theorem insert_iInter (x : β) (t : ι -> Set β) : insert x (⋂ i, t i) = ⋂ i, insert x (t i) := by
  simp_rw [← union_singleton, iInter_union]

/--
theorem `iUnion_sdiff` / 定理 `iUnion_sdiff`

English:
theorem iUnion_sdiff
  given: (s : Set β) (t : ι -> Set β)
  statement: (⋃ i, t i) \ s = ⋃ i, t i \ s
  proof: by
  simp only [sdiff_eq, iUnion_inter]

@[deprecated (since := "2026-06-03")] alias iUnion_diff := iUnion_sdiff

中文:
定理 iUnion_sdiff
  条件: (s : 集合 β) (t : ι -> 集合 β)
  结论: (⋃ i, t i) \ s = ⋃ i, t i \ s
  证明: by
  simp only [sdiff_eq, iUnion_inter]

@[deprecated (since := "2026-06-03")] alias iUnion_diff := iUnion_sdiff

Depends on / 依赖: iUnion_inter, sdiff_eq
-/
theorem iUnion_sdiff (s : Set β) (t : ι -> Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s := by
  simp only [sdiff_eq, iUnion_inter]

@[deprecated (since := "2026-06-03")] alias iUnion_diff := iUnion_sdiff

/--
theorem `sdiff_iUnion` / 定理 `sdiff_iUnion`

English:
theorem sdiff_iUnion
  given: [Nonempty ι] (s : Set β) (t : ι -> Set β)
  statement: (s \ ⋃ i, t i) = ⋂ i, s \ t i
  proof: by
  simp only [sdiff_eq, compl_iUnion, inter_iInter]

@[deprecated (since := "2026-06-03")] alias diff_iUnion := sdiff_iUnion

中文:
定理 sdiff_iUnion
  条件: [非空 ι] (s : 集合 β) (t : ι -> 集合 β)
  结论: (s \ ⋃ i, t i) = ⋂ i, s \ t i
  证明: by
  simp only [sdiff_eq, compl_iUnion, inter_iInter]

@[deprecated (since := "2026-06-03")] alias diff_iUnion := sdiff_iUnion

Depends on / 依赖: compl_iUnion, inter_iInter, sdiff_eq
-/
theorem sdiff_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  simp only [sdiff_eq, compl_iUnion, inter_iInter]

@[deprecated (since := "2026-06-03")] alias diff_iUnion := sdiff_iUnion

/--
theorem `sdiff_iInter` / 定理 `sdiff_iInter`

English:
theorem sdiff_iInter
  given: (s : Set β) (t : ι -> Set β)
  statement: (s \ ⋂ i, t i) = ⋃ i, s \ t i
  proof: by
  simp only [sdiff_eq, compl_iInter, inter_iUnion]

@[deprecated (since := "2026-06-03")] alias diff_iInter := sdiff_iInter

中文:
定理 sdiff_i整数er
  条件: (s : 集合 β) (t : ι -> 集合 β)
  结论: (s \ ⋂ i, t i) = ⋃ i, s \ t i
  证明: by
  simp only [sdiff_eq, compl_iInter, inter_iUnion]

@[deprecated (since := "2026-06-03")] alias diff_iInter := sdiff_iInter

Depends on / 依赖: compl_iInter, inter_iUnion, sdiff_eq
-/
theorem sdiff_iInter (s : Set β) (t : ι -> Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  simp only [sdiff_eq, compl_iInter, inter_iUnion]

@[deprecated (since := "2026-06-03")] alias diff_iInter := sdiff_iInter

section SymmDiff

open scoped symmDiff

/--
lemma `iUnion_symmDiff_subset` / 引理 `iUnion_symmDiff_subset`

English:
lemma iUnion_symmDiff_subset
  given: {s : Set α} [Nonempty ι] {f : ι -> Set α}
  proof: iSup_symmDiff_le

中文:
引理 iUnion_symmDiff_subset
  条件: {s : 集合 α} [非空 ι] {f : ι -> 集合 α}
  证明: iSup_symmDiff_le

Depends on / 依赖: iSup_symmDiff_le
-/
lemma iUnion_symmDiff_subset {s : Set α} [Nonempty ι] {f : ι -> Set α} :
    (⋃ n, f n) ∆ s subseteq ⋃ n, f n ∆ s :=
  iSup_symmDiff_le

/--
lemma `symmDiff_iUnion_subset` / 引理 `symmDiff_iUnion_subset`

English:
lemma symmDiff_iUnion_subset
  given: {s : Set α} [Nonempty ι] {f : ι -> Set α}
  proof: symmDiff_iSup_le

中文:
引理 symmDiff_iUnion_subset
  条件: {s : 集合 α} [非空 ι] {f : ι -> 集合 α}
  证明: symmDiff_iSup_le

Depends on / 依赖: symmDiff_iSup_le
-/
lemma symmDiff_iUnion_subset {s : Set α} [Nonempty ι] {f : ι -> Set α} :
    s ∆ (⋃ n, f n) subseteq ⋃ n, s ∆ f n :=
  symmDiff_iSup_le

/--
lemma `iUnion_symmDiff_iUnion_subset` / 引理 `iUnion_symmDiff_iUnion_subset`

English:
lemma iUnion_symmDiff_iUnion_subset
  given: {f g : ι -> Set α}
  proof: iSup_symmDiff_iSup_le

中文:
引理 iUnion_symmDiff_iUnion_subset
  条件: {f g : ι -> 集合 α}
  证明: iSup_symmDiff_iSup_le

Depends on / 依赖: iSup_symmDiff_iSup_le
-/
lemma iUnion_symmDiff_iUnion_subset {f g : ι -> Set α} :
    (⋃ n, f n) ∆ ⋃ n, g n subseteq ⋃ n, f n ∆ g n :=
  iSup_symmDiff_iSup_le

/--
lemma `sUnion_symmDiff_subset` / 引理 `sUnion_symmDiff_subset`

English:
lemma sUnion_symmDiff_subset
  given: {s : Set α} {S : Set (Set α)} (hS : S.Nonempty)
  proof: sSup_symmDiff_le hS

中文:
引理 sUnion_symmDiff_subset
  条件: {s : 集合 α} {S : 集合 (集合 α)} (hS : S.非空)
  证明: sSup_symmDiff_le hS

Depends on / 依赖: sSup_symmDiff_le
-/
lemma sUnion_symmDiff_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) :
    (⋃₀ S) ∆ s subseteq ⋃₀ ((· ∆ s) '' S) :=
  sSup_symmDiff_le hS

/--
lemma `symmDiff_sUnion_subset` / 引理 `symmDiff_sUnion_subset`

English:
lemma symmDiff_sUnion_subset
  given: {s : Set α} {S : Set (Set α)} (hS : S.Nonempty)
  proof: symmDiff_sSup_le hS

中文:
引理 symmDiff_sUnion_subset
  条件: {s : 集合 α} {S : 集合 (集合 α)} (hS : S.非空)
  证明: symmDiff_sSup_le hS

Depends on / 依赖: symmDiff_sSup_le
-/
lemma symmDiff_sUnion_subset {s : Set α} {S : Set (Set α)} (hS : S.Nonempty) :
    s ∆ (⋃₀ S) subseteq ⋃₀ ((s ∆ ·) '' S) :=
  symmDiff_sSup_le hS

/--
lemma `sUnion_symmDiff_sUnion_subset` / 引理 `sUnion_symmDiff_sUnion_subset`

English:
lemma sUnion_symmDiff_sUnion_subset
  statement: {S T : Set (Set α)} (hS : S.Nonempty)
  proof: sSup_symmDiff_sSup_le hS hT

中文:
引理 sUnion_symmDiff_sUnion_subset
  结论: {S T : 集合 (集合 α)} (hS : S.非空)
  证明: sSup_symmDiff_sSup_le hS hT

Depends on / 依赖: sSup_symmDiff_sSup_le
-/
lemma sUnion_symmDiff_sUnion_subset {S T : Set (Set α)} (hS : S.Nonempty)
    (hT : T.Nonempty) :
    (⋃₀ S) ∆ ⋃₀ T subseteq ⋃₀ (image2 (· ∆ ·) S T) :=
  sSup_symmDiff_sSup_le hS hT

end SymmDiff

/--
theorem `iUnion_inter_subset` / 定理 `iUnion_inter_subset`

English:
theorem iUnion_inter_subset
  given: {ι α} {s t : ι -> Set α}
  statement: ⋃ i, s i inter t i subseteq (⋃ i, s i) inter ⋃ i, t i
  proof: le_iSup_inf_iSup s t

中文:
定理 iUnion_inter_subset
  条件: {ι α} {s t : ι -> 集合 α}
  结论: ⋃ i, s i inter t i subseteq (⋃ i, s i) inter ⋃ i, t i
  证明: le_iSup_inf_iSup s t

Depends on / 依赖: le_iSup_inf_iSup
-/
theorem iUnion_inter_subset {ι α} {s t : ι -> Set α} : ⋃ i, s i inter t i subseteq (⋃ i, s i) inter ⋃ i, t i :=
  le_iSup_inf_iSup s t

/--
theorem `iUnion_inter_of_monotone` / 定理 `iUnion_inter_of_monotone`

English:
theorem iUnion_inter_of_monotone
  statement: {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι -> Set α}
  proof: iSup_inf_of_monotone hs ht

中文:
定理 iUnion_inter_of_monotone
  结论: {ι α} [预序 ι] [IsDirectedOrder ι] {s t : ι -> 集合 α}
  证明: iSup_inf_of_monotone hs ht

Depends on / 依赖: iSup_inf_of_monotone
-/
theorem iUnion_inter_of_monotone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι -> Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋃ i, s i inter t i = (⋃ i, s i) inter ⋃ i, t i :=
  iSup_inf_of_monotone hs ht

/--
theorem `iUnion_inter_of_antitone` / 定理 `iUnion_inter_of_antitone`

English:
theorem iUnion_inter_of_antitone
  statement: {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι -> Set α}
  proof: iSup_inf_of_antitone hs ht

中文:
定理 iUnion_inter_of_antitone
  结论: {ι α} [预序 ι] [IsCodirectedOrder ι] {s t : ι -> 集合 α}
  证明: iSup_inf_of_antitone hs ht

Depends on / 依赖: iSup_inf_of_antitone
-/
theorem iUnion_inter_of_antitone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι -> Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋃ i, s i inter t i = (⋃ i, s i) inter ⋃ i, t i :=
  iSup_inf_of_antitone hs ht

/--
theorem `iInter_union_of_monotone` / 定理 `iInter_union_of_monotone`

English:
theorem iInter_union_of_monotone
  statement: {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι -> Set α}
  proof: iInf_sup_of_monotone hs ht

中文:
定理 i整数er_union_of_monotone
  结论: {ι α} [预序 ι] [IsCodirectedOrder ι] {s t : ι -> 集合 α}
  证明: iInf_sup_of_monotone hs ht

Depends on / 依赖: iInf_sup_of_monotone
-/
theorem iInter_union_of_monotone {ι α} [Preorder ι] [IsCodirectedOrder ι] {s t : ι -> Set α}
    (hs : Monotone s) (ht : Monotone t) : ⋂ i, s i union t i = (⋂ i, s i) union ⋂ i, t i :=
  iInf_sup_of_monotone hs ht

/--
theorem `iInter_union_of_antitone` / 定理 `iInter_union_of_antitone`

English:
theorem iInter_union_of_antitone
  statement: {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι -> Set α}
  proof: iInf_sup_of_antitone hs ht

中文:
定理 i整数er_union_of_antitone
  结论: {ι α} [预序 ι] [IsDirectedOrder ι] {s t : ι -> 集合 α}
  证明: iInf_sup_of_antitone hs ht

Depends on / 依赖: iInf_sup_of_antitone
-/
theorem iInter_union_of_antitone {ι α} [Preorder ι] [IsDirectedOrder ι] {s t : ι -> Set α}
    (hs : Antitone s) (ht : Antitone t) : ⋂ i, s i union t i = (⋂ i, s i) union ⋂ i, t i :=
  iInf_sup_of_antitone hs ht

/--
theorem `iUnion_iInter_subset` / 定理 `iUnion_iInter_subset`

English:
theorem iUnion_iInter_subset
  given: {s : ι -> ι' -> Set α}
  statement: (⋃ j, ⋂ i, s i j) subseteq ⋂ i, ⋃ j, s i j
  proof: iSup_iInf_le_iInf_iSup (flip s)

中文:
定理 iUnion_i整数er_subset
  条件: {s : ι -> ι' -> 集合 α}
  结论: (⋃ j, ⋂ i, s i j) subseteq ⋂ i, ⋃ j, s i j
  证明: iSup_iInf_le_iInf_iSup (flip s)

Depends on / 依赖: iSup_iInf_le_iInf_iSup
-/
theorem iUnion_iInter_subset {s : ι -> ι' -> Set α} : (⋃ j, ⋂ i, s i j) subseteq ⋂ i, ⋃ j, s i j :=
  iSup_iInf_le_iInf_iSup (flip s)

/--
theorem `iUnion_option` / 定理 `iUnion_option`

English:
theorem iUnion_option
  given: {ι} (s : Option ι -> Set α)
  statement: ⋃ o, s o = s none union ⋃ i, s (some i)
  proof: iSup_option s

中文:
定理 iUnion_option
  条件: {ι} (s : 选项类型 ι -> 集合 α)
  结论: ⋃ o, s o = s none union ⋃ i, s (some i)
  证明: iSup_option s

Depends on / 依赖: iSup_option
-/
theorem iUnion_option {ι} (s : Option ι -> Set α) : ⋃ o, s o = s none union ⋃ i, s (some i) :=
  iSup_option s

/--
theorem `iInter_option` / 定理 `iInter_option`

English:
theorem iInter_option
  given: {ι} (s : Option ι -> Set α)
  statement: ⋂ o, s o = s none inter ⋂ i, s (some i)
  proof: iInf_option s

中文:
定理 i整数er_option
  条件: {ι} (s : 选项类型 ι -> 集合 α)
  结论: ⋂ o, s o = s none inter ⋂ i, s (some i)
  证明: iInf_option s

Depends on / 依赖: iInf_option
-/
theorem iInter_option {ι} (s : Option ι -> Set α) : ⋂ o, s o = s none inter ⋂ i, s (some i) :=
  iInf_option s

section

variable (p : ι -> Prop) [DecidablePred p]

/--
theorem `iUnion_dite` / 定理 `iUnion_dite`

English:
theorem iUnion_dite
  given: (f : forall i, p i -> Set α) (g : forall i, ¬p i -> Set α)
  proof: iSup_dite _ _ _

中文:
定理 iUnion_dite
  条件: (f : 对任意 i, p i -> 集合 α) (g : 对任意 i, ¬p i -> 集合 α)
  证明: iSup_dite _ _ _

Depends on / 依赖: iSup_dite
-/
theorem iUnion_dite (f : forall i, p i -> Set α) (g : forall i, ¬p i -> Set α) :
    ⋃ i, (if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) union ⋃ (i) (h : ¬p i), g i h :=
  iSup_dite _ _ _

/--
theorem `iUnion_ite` / 定理 `iUnion_ite`

English:
theorem iUnion_ite
  given: (f g : ι -> Set α)
  proof: iUnion_dite _ _ _

中文:
定理 iUnion_ite
  条件: (f g : ι -> 集合 α)
  证明: iUnion_dite _ _ _

Depends on / 依赖: iUnion_dite
-/
theorem iUnion_ite (f g : ι -> Set α) :
    ⋃ i, (if p i then f i else g i) = (⋃ (i) (_ : p i), f i) union ⋃ (i) (_ : ¬p i), g i :=
  iUnion_dite _ _ _

/--
theorem `iInter_dite` / 定理 `iInter_dite`

English:
theorem iInter_dite
  given: (f : forall i, p i -> Set α) (g : forall i, ¬p i -> Set α)
  proof: iInf_dite _ _ _

中文:
定理 i整数er_dite
  条件: (f : 对任意 i, p i -> 集合 α) (g : 对任意 i, ¬p i -> 集合 α)
  证明: iInf_dite _ _ _

Depends on / 依赖: iInf_dite
-/
theorem iInter_dite (f : forall i, p i -> Set α) (g : forall i, ¬p i -> Set α) :
    ⋂ i, (if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) inter ⋂ (i) (h : ¬p i), g i h :=
  iInf_dite _ _ _

/--
theorem `iInter_ite` / 定理 `iInter_ite`

English:
theorem iInter_ite
  given: (f g : ι -> Set α)
  proof: iInter_dite _ _ _

中文:
定理 i整数er_ite
  条件: (f g : ι -> 集合 α)
  证明: iInter_dite _ _ _

Depends on / 依赖: iInter_dite
-/
theorem iInter_ite (f g : ι -> Set α) :
    ⋂ i, (if p i then f i else g i) = (⋂ (i) (_ : p i), f i) inter ⋂ (i) (_ : ¬p i), g i :=
  iInter_dite _ _ _

end



/--
theorem `iInter_false` / 定理 `iInter_false`

English:
theorem iInter_false
  given: {s : False -> Set α}
  statement: iInter s = univ
  proof: iInf_false

中文:
定理 i整数er_false
  条件: {s : 假 -> 集合 α}
  结论: i整数er s = univ
  证明: iInf_false

Depends on / 依赖: iInf_false
-/
theorem iInter_false {s : False -> Set α} : iInter s = univ :=
  iInf_false

/--
theorem `iUnion_false` / 定理 `iUnion_false`

English:
theorem iUnion_false
  given: {s : False -> Set α}
  statement: iUnion s = ∅
  proof: iSup_false

@[simp]

中文:
定理 iUnion_false
  条件: {s : 假 -> 集合 α}
  结论: iUnion s = ∅
  证明: iSup_false

@[simp]

Depends on / 依赖: iSup_false
-/
theorem iUnion_false {s : False -> Set α} : iUnion s = ∅ :=
  iSup_false

@[simp]
/--
theorem `iInter_true` / 定理 `iInter_true`

English:
theorem iInter_true
  given: {s : True -> Set α}
  statement: iInter s = s trivial
  proof: iInf_true

@[simp]

中文:
定理 i整数er_true
  条件: {s : 真 -> 集合 α}
  结论: i整数er s = s trivial
  证明: iInf_true

@[simp]

Depends on / 依赖: iInf_true
-/
theorem iInter_true {s : True -> Set α} : iInter s = s trivial :=
  iInf_true

@[simp]
/--
theorem `iUnion_true` / 定理 `iUnion_true`

English:
theorem iUnion_true
  given: {s : True -> Set α}
  statement: iUnion s = s trivial
  proof: iSup_true

@[simp]

中文:
定理 iUnion_true
  条件: {s : 真 -> 集合 α}
  结论: iUnion s = s trivial
  证明: iSup_true

@[simp]

Depends on / 依赖: iSup_true
-/
theorem iUnion_true {s : True -> Set α} : iUnion s = s trivial :=
  iSup_true

@[simp]
/--
theorem `iInter_exists` / 定理 `iInter_exists`

English:
theorem iInter_exists
  given: {p : ι -> Prop} {f : Exists p -> Set α}
  proof: iInf_exists

@[simp]

中文:
定理 i整数er_存在
  条件: {p : ι -> 命题} {f : 存在 p -> 集合 α}
  证明: iInf_exists

@[simp]

Depends on / 依赖: iInf_exists
-/
theorem iInter_exists {p : ι -> Prop} {f : Exists p -> Set α} :
    ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  iInf_exists

@[simp]
/--
theorem `iUnion_exists` / 定理 `iUnion_exists`

English:
theorem iUnion_exists
  given: {p : ι -> Prop} {f : Exists p -> Set α}
  proof: iSup_exists

@[simp]

中文:
定理 iUnion_存在
  条件: {p : ι -> 命题} {f : 存在 p -> 集合 α}
  证明: iSup_exists

@[simp]

Depends on / 依赖: iSup_exists
-/
theorem iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α} :
    ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  iSup_exists

@[simp]
/--
theorem `iUnion_empty` / 定理 `iUnion_empty`

English:
theorem iUnion_empty
  statement: (⋃ _ : ι, ∅ : Set α) = ∅
  proof: iSup_bot

@[simp]

中文:
定理 iUnion_empty
  结论: (⋃ _ : ι, ∅ : 集合 α) = ∅
  证明: iSup_bot

@[simp]

Depends on / 依赖: iSup_bot
-/
theorem iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅ :=
  iSup_bot

@[simp]
/--
theorem `iInter_univ` / 定理 `iInter_univ`

English:
theorem iInter_univ
  statement: (⋂ _ : ι, univ : Set α) = univ
  proof: iInf_top

中文:
定理 i整数er_univ
  结论: (⋂ _ : ι, univ : 集合 α) = univ
  证明: iInf_top

Depends on / 依赖: iInf_top
-/
theorem iInter_univ : (⋂ _ : ι, univ : Set α) = univ :=
  iInf_top

section

variable {s : ι -> Set α}

@[simp]
/--
theorem `iUnion_eq_empty` / 定理 `iUnion_eq_empty`

English:
theorem iUnion_eq_empty
  statement: ⋃ i, s i = ∅ ↔ forall i, s i = ∅
  proof: iSup_eq_bot

@[simp]

中文:
定理 iUnion_eq_empty
  结论: ⋃ i, s i = ∅ ↔ 对任意 i, s i = ∅
  证明: iSup_eq_bot

@[simp]

Depends on / 依赖: iSup_eq_bot
-/
theorem iUnion_eq_empty : ⋃ i, s i = ∅ ↔ forall i, s i = ∅ :=
  iSup_eq_bot

@[simp]
/--
theorem `iInter_eq_univ` / 定理 `iInter_eq_univ`

English:
theorem iInter_eq_univ
  statement: ⋂ i, s i = univ ↔ forall i, s i = univ
  proof: iInf_eq_top

@[simp]

中文:
定理 i整数er_eq_univ
  结论: ⋂ i, s i = univ ↔ 对任意 i, s i = univ
  证明: iInf_eq_top

@[simp]

Depends on / 依赖: iInf_eq_top
-/
theorem iInter_eq_univ : ⋂ i, s i = univ ↔ forall i, s i = univ :=
  iInf_eq_top

@[simp]
/--
theorem `nonempty_iUnion` / 定理 `nonempty_iUnion`

English:
theorem nonempty_iUnion
  statement: (⋃ i, s i).Nonempty ↔ exists i, (s i).Nonempty
  proof: by
  simp [nonempty_iff_ne_empty]

中文:
定理 nonempty_iUnion
  结论: (⋃ i, s i).非空 ↔ 存在 i, (s i).非空
  证明: by
  simp [nonempty_iff_ne_empty]

Depends on / 依赖: nonempty_iff_ne_empty
-/
theorem nonempty_iUnion : (⋃ i, s i).Nonempty ↔ exists i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]

/--
theorem `nonempty_biUnion` / 定理 `nonempty_biUnion`

English:
theorem nonempty_biUnion
  given: {t : Set α} {s : α -> Set β}
  proof: by simp

中文:
定理 nonempty_biUnion
  条件: {t : 集合 α} {s : α -> 集合 β}
  证明: by simp
-/
theorem nonempty_biUnion {t : Set α} {s : α -> Set β} :
    (⋃ i in t, s i).Nonempty ↔ exists i in t, (s i).Nonempty := by simp

/--
theorem `iUnion_nonempty_index` / 定理 `iUnion_nonempty_index`

English:
theorem iUnion_nonempty_index
  given: (s : Set α) (t : s.Nonempty -> Set β)
  proof: iSup_exists

中文:
定理 iUnion_nonempty_index
  条件: (s : 集合 α) (t : s.非空 -> 集合 β)
  证明: iSup_exists

Depends on / 依赖: iSup_exists
-/
theorem iUnion_nonempty_index (s : Set α) (t : s.Nonempty -> Set β) :
    ⋃ h, t h = ⋃ x in s, t ⟨x, ‹_›⟩ :=
  iSup_exists

end

@[simp]
/--
theorem `iInter_iInter_eq_left` / 定理 `iInter_iInter_eq_left`

English:
theorem iInter_iInter_eq_left
  given: {b : β} {s : forall x : β, x = b -> Set α}
  proof: iInf_iInf_eq_left

@[simp]

中文:
定理 i整数er_i整数er_eq_left
  条件: {b : β} {s : 对任意 x : β, x = b -> 集合 α}
  证明: iInf_iInf_eq_left

@[simp]

Depends on / 依赖: iInf_iInf_eq_left
-/
theorem iInter_iInter_eq_left {b : β} {s : forall x : β, x = b -> Set α} :
    ⋂ (x) (h : x = b), s x h = s b rfl :=
  iInf_iInf_eq_left

@[simp]
/--
theorem `iInter_iInter_eq_right` / 定理 `iInter_iInter_eq_right`

English:
theorem iInter_iInter_eq_right
  given: {b : β} {s : forall x : β, b = x -> Set α}
  proof: iInf_iInf_eq_right

@[simp]

中文:
定理 i整数er_i整数er_eq_right
  条件: {b : β} {s : 对任意 x : β, b = x -> 集合 α}
  证明: iInf_iInf_eq_right

@[simp]

Depends on / 依赖: iInf_iInf_eq_right
-/
theorem iInter_iInter_eq_right {b : β} {s : forall x : β, b = x -> Set α} :
    ⋂ (x) (h : b = x), s x h = s b rfl :=
  iInf_iInf_eq_right

@[simp]
/--
theorem `iUnion_iUnion_eq_left` / 定理 `iUnion_iUnion_eq_left`

English:
theorem iUnion_iUnion_eq_left
  given: {b : β} {s : forall x : β, x = b -> Set α}
  proof: iSup_iSup_eq_left

@[simp]

中文:
定理 iUnion_iUnion_eq_left
  条件: {b : β} {s : 对任意 x : β, x = b -> 集合 α}
  证明: iSup_iSup_eq_left

@[simp]

Depends on / 依赖: iSup_iSup_eq_left
-/
theorem iUnion_iUnion_eq_left {b : β} {s : forall x : β, x = b -> Set α} :
    ⋃ (x) (h : x = b), s x h = s b rfl :=
  iSup_iSup_eq_left

@[simp]
/--
theorem `iUnion_iUnion_eq_right` / 定理 `iUnion_iUnion_eq_right`

English:
theorem iUnion_iUnion_eq_right
  given: {b : β} {s : forall x : β, b = x -> Set α}
  proof: iSup_iSup_eq_right

中文:
定理 iUnion_iUnion_eq_right
  条件: {b : β} {s : 对任意 x : β, b = x -> 集合 α}
  证明: iSup_iSup_eq_right

Depends on / 依赖: iSup_iSup_eq_right
-/
theorem iUnion_iUnion_eq_right {b : β} {s : forall x : β, b = x -> Set α} :
    ⋃ (x) (h : b = x), s x h = s b rfl :=
  iSup_iSup_eq_right

/--
theorem `iInter_or` / 定理 `iInter_or`

English:
theorem iInter_or
  given: {p q : Prop} (s : p ∨ q -> Set α)
  proof: iInf_or

中文:
定理 i整数er_or
  条件: {p q : 命题} (s : p ∨ q -> 集合 α)
  证明: iInf_or

Depends on / 依赖: iInf_or
-/
theorem iInter_or {p q : Prop} (s : p ∨ q -> Set α) :
    ⋂ h, s h = (⋂ h : p, s (Or.inl h)) inter ⋂ h : q, s (Or.inr h) :=
  iInf_or

/--
theorem `iUnion_or` / 定理 `iUnion_or`

English:
theorem iUnion_or
  given: {p q : Prop} (s : p ∨ q -> Set α)
  proof: iSup_or

中文:
定理 iUnion_or
  条件: {p q : 命题} (s : p ∨ q -> 集合 α)
  证明: iSup_or

Depends on / 依赖: iSup_or
-/
theorem iUnion_or {p q : Prop} (s : p ∨ q -> Set α) :
    ⋃ h, s h = (⋃ i, s (Or.inl i)) union ⋃ j, s (Or.inr j) :=
  iSup_or

/--
theorem `iUnion_and` / 定理 `iUnion_and`

English:
theorem iUnion_and
  given: {p q : Prop} (s : p ∧ q -> Set α)
  statement: ⋃ h, s h = ⋃ (hp) (hq), s ⟨hp, hq⟩
  proof: iSup_and

中文:
定理 iUnion_and
  条件: {p q : 命题} (s : p ∧ q -> 集合 α)
  结论: ⋃ h, s h = ⋃ (hp) (hq), s ⟨hp, hq⟩
  证明: iSup_and

Depends on / 依赖: iSup_and
-/
theorem iUnion_and {p q : Prop} (s : p ∧ q -> Set α) : ⋃ h, s h = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  iSup_and

/--
theorem `iInter_and` / 定理 `iInter_and`

English:
theorem iInter_and
  given: {p q : Prop} (s : p ∧ q -> Set α)
  statement: ⋂ h, s h = ⋂ (hp) (hq), s ⟨hp, hq⟩
  proof: iInf_and

中文:
定理 i整数er_and
  条件: {p q : 命题} (s : p ∧ q -> 集合 α)
  结论: ⋂ h, s h = ⋂ (hp) (hq), s ⟨hp, hq⟩
  证明: iInf_and

Depends on / 依赖: iInf_and
-/
theorem iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  iInf_and

/--
theorem `iUnion_comm` / 定理 `iUnion_comm`

English:
theorem iUnion_comm
  given: (s : ι -> ι' -> Set α)
  statement: ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i i'
  proof: iSup_comm

中文:
定理 iUnion_comm
  条件: (s : ι -> ι' -> 集合 α)
  结论: ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i i'
  证明: iSup_comm

Depends on / 依赖: iSup_comm
-/
theorem iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i' = ⋃ (i') (i), s i i' :=
  iSup_comm

/--
theorem `iInter_comm` / 定理 `iInter_comm`

English:
theorem iInter_comm
  given: (s : ι -> ι' -> Set α)
  statement: ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i i'
  proof: iInf_comm

中文:
定理 i整数er_comm
  条件: (s : ι -> ι' -> 集合 α)
  结论: ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i i'
  证明: iInf_comm

Depends on / 依赖: iInf_comm
-/
theorem iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i' = ⋂ (i') (i), s i i' :=
  iInf_comm

/--
theorem `iUnion_sigma` / 定理 `iUnion_sigma`

English:
theorem iUnion_sigma
  given: {γ : α -> Type*} (s : Sigma γ -> Set β)
  statement: ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩
  proof: iSup_sigma

中文:
定理 iUnion_sigma
  条件: {γ : α -> 类型} (s : 依赖和类型 γ -> 集合 β)
  结论: ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩
  证明: iSup_sigma

Depends on / 依赖: iSup_sigma
-/
theorem iUnion_sigma {γ : α -> Type*} (s : Sigma γ -> Set β) : ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩ :=
  iSup_sigma

/--
theorem `iUnion_sigma'` / 定理 `iUnion_sigma'`

English:
theorem iUnion_sigma'
  given: {γ : α -> Type*} (s : forall i, γ i -> Set β)
  proof: iSup_sigma' _

中文:
定理 iUnion_sigma'
  条件: {γ : α -> 类型} (s : 对任意 i, γ i -> 集合 β)
  证明: iSup_sigma' _

Depends on / 依赖: iSup_sigma
-/
theorem iUnion_sigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) :
    ⋃ i, ⋃ a, s i a = ⋃ ia : Sigma γ, s ia.1 ia.2 :=
  iSup_sigma' _

/--
theorem `iInter_sigma` / 定理 `iInter_sigma`

English:
theorem iInter_sigma
  given: {γ : α -> Type*} (s : Sigma γ -> Set β)
  statement: ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩
  proof: iInf_sigma

中文:
定理 i整数er_sigma
  条件: {γ : α -> 类型} (s : 依赖和类型 γ -> 集合 β)
  结论: ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩
  证明: iInf_sigma

Depends on / 依赖: iInf_sigma
-/
theorem iInter_sigma {γ : α -> Type*} (s : Sigma γ -> Set β) : ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩ :=
  iInf_sigma

/--
theorem `iInter_sigma'` / 定理 `iInter_sigma'`

English:
theorem iInter_sigma'
  given: {γ : α -> Type*} (s : forall i, γ i -> Set β)
  proof: iInf_sigma' _

中文:
定理 i整数er_sigma'
  条件: {γ : α -> 类型} (s : 对任意 i, γ i -> 集合 β)
  证明: iInf_sigma' _

Depends on / 依赖: iInf_sigma
-/
theorem iInter_sigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) :
    ⋂ i, ⋂ a, s i a = ⋂ ia : Sigma γ, s ia.1 ia.2 :=
  iInf_sigma' _

/--
theorem `iUnion₂_comm` / 定理 `iUnion₂_comm`

English:
theorem iUnion₂_comm
  given: (s : forall i, κ i -> forall i', κ' i' -> Set α)
  proof: iSup₂_comm _

中文:
定理 iUnion₂_comm
  条件: (s : 对任意 i, κ i -> 对任意 i', κ' i' -> 集合 α)
  证明: iSup₂_comm _
-/
theorem iUnion₂_comm (s : forall i, κ i -> forall i', κ' i' -> Set α) :
    ⋃ (i) (j) (i') (j'), s i j i' j' = ⋃ (i') (j') (i) (j), s i j i' j' :=
  iSup₂_comm _

/--
theorem `iInter₂_comm` / 定理 `iInter₂_comm`

English:
theorem iInter₂_comm
  given: (s : forall i, κ i -> forall i', κ' i' -> Set α)
  proof: iInf₂_comm _

@[simp]

中文:
定理 i整数er₂_comm
  条件: (s : 对任意 i, κ i -> 对任意 i', κ' i' -> 集合 α)
  证明: iInf₂_comm _

@[simp]
-/
theorem iInter₂_comm (s : forall i, κ i -> forall i', κ' i' -> Set α) :
    ⋂ (i) (j) (i') (j'), s i j i' j' = ⋂ (i') (j') (i) (j), s i j i' j' :=
  iInf₂_comm _

@[simp]
/--
theorem `biUnion_and` / 定理 `biUnion_and`

English:
theorem biUnion_and
  given: (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p x ∧ q x y -> Set α)
  proof: by
  simp only [iUnion_and, @iUnion_comm _ ι']

@[simp]

中文:
定理 biUnion_and
  条件: (p : ι -> 命题) (q : ι -> ι' -> 命题) (s : 对任意 x y, p x ∧ q x y -> 集合 α)
  证明: by
  simp only [iUnion_and, @iUnion_comm _ ι']

@[simp]

Depends on / 依赖: iUnion_and, iUnion_comm
-/
theorem biUnion_and (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p x ∧ q x y -> Set α) :
    ⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι']

@[simp]
/--
theorem `biUnion_and'` / 定理 `biUnion_and'`

English:
theorem biUnion_and'
  given: (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p y ∧ q x y -> Set α)
  proof: by
  simp only [iUnion_and, @iUnion_comm _ ι]

@[simp]

中文:
定理 biUnion_and'
  条件: (p : ι' -> 命题) (q : ι -> ι' -> 命题) (s : 对任意 x y, p y ∧ q x y -> 集合 α)
  证明: by
  simp only [iUnion_and, @iUnion_comm _ ι]

@[simp]

Depends on / 依赖: iUnion_and, iUnion_comm
-/
theorem biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p y ∧ q x y -> Set α) :
    ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iUnion_and, @iUnion_comm _ ι]

@[simp]
/--
theorem `biInter_and` / 定理 `biInter_and`

English:
theorem biInter_and
  given: (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p x ∧ q x y -> Set α)
  proof: by
  simp only [iInter_and, @iInter_comm _ ι']

@[simp]

中文:
定理 bi整数er_and
  条件: (p : ι -> 命题) (q : ι -> ι' -> 命题) (s : 对任意 x y, p x ∧ q x y -> 集合 α)
  证明: by
  simp only [iInter_and, @iInter_comm _ ι']

@[simp]

Depends on / 依赖: iInter_and, iInter_comm
-/
theorem biInter_and (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p x ∧ q x y -> Set α) :
    ⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ := by
  simp only [iInter_and, @iInter_comm _ ι']

@[simp]
/--
theorem `biInter_and'` / 定理 `biInter_and'`

English:
theorem biInter_and'
  given: (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p y ∧ q x y -> Set α)
  proof: by
  simp only [iInter_and, @iInter_comm _ ι]

@[simp]

中文:
定理 bi整数er_and'
  条件: (p : ι' -> 命题) (q : ι -> ι' -> 命题) (s : 对任意 x y, p y ∧ q x y -> 集合 α)
  证明: by
  simp only [iInter_and, @iInter_comm _ ι]

@[simp]

Depends on / 依赖: iInter_and, iInter_comm
-/
theorem biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall x y, p y ∧ q x y -> Set α) :
    ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ := by
  simp only [iInter_and, @iInter_comm _ ι]

@[simp]
/--
theorem `iUnion_iUnion_eq_or_left` / 定理 `iUnion_iUnion_eq_or_left`

English:
theorem iUnion_iUnion_eq_or_left
  given: {b : β} {p : β -> Prop} {s : forall x : β, x = b ∨ p x -> Set α}
  proof: by
  simp only [iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]

@[simp]

中文:
定理 iUnion_iUnion_eq_or_left
  条件: {b : β} {p : β -> 命题} {s : 对任意 x : β, x = b ∨ p x -> 集合 α}
  证明: by
  simp only [iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]

@[simp]

Depends on / 依赖: iUnion_iUnion_eq_left, iUnion_or, iUnion_union_distrib
-/
theorem iUnion_iUnion_eq_or_left {b : β} {p : β -> Prop} {s : forall x : β, x = b ∨ p x -> Set α} :
    ⋃ (x) (h), s x h = s b (Or.inl rfl) union ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]

@[simp]
/--
theorem `iInter_iInter_eq_or_left` / 定理 `iInter_iInter_eq_or_left`

English:
theorem iInter_iInter_eq_or_left
  given: {b : β} {p : β -> Prop} {s : forall x : β, x = b ∨ p x -> Set α}
  proof: by
  simp only [iInter_or, iInter_inter_distrib, iInter_iInter_eq_left]

中文:
定理 i整数er_i整数er_eq_or_left
  条件: {b : β} {p : β -> 命题} {s : 对任意 x : β, x = b ∨ p x -> 集合 α}
  证明: by
  simp only [iInter_or, iInter_inter_distrib, iInter_iInter_eq_left]

Depends on / 依赖: iInter_iInter_eq_left, iInter_inter_distrib, iInter_or
-/
theorem iInter_iInter_eq_or_left {b : β} {p : β -> Prop} {s : forall x : β, x = b ∨ p x -> Set α} :
    ⋂ (x) (h), s x h = s b (Or.inl rfl) inter ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [iInter_or, iInter_inter_distrib, iInter_iInter_eq_left]

/--
lemma `iUnion_sum` / 引理 `iUnion_sum`

English:
lemma iUnion_sum
  given: {s : α oplus β -> Set γ}
  statement: ⋃ x, s x = (⋃ x, s (.inl x)) union ⋃ x, s (.inr x)
  proof: iSup_sum

中文:
引理 iUnion_sum
  条件: {s : α oplus β -> 集合 γ}
  结论: ⋃ x, s x = (⋃ x, s (.inl x)) union ⋃ x, s (.inr x)
  证明: iSup_sum

Depends on / 依赖: iSup_sum
-/
lemma iUnion_sum {s : α oplus β -> Set γ} : ⋃ x, s x = (⋃ x, s (.inl x)) union ⋃ x, s (.inr x) := iSup_sum

/--
lemma `iInter_sum` / 引理 `iInter_sum`

English:
lemma iInter_sum
  given: {s : α oplus β -> Set γ}
  statement: ⋂ x, s x = (⋂ x, s (.inl x)) inter ⋂ x, s (.inr x)
  proof: iInf_sum

中文:
引理 i整数er_sum
  条件: {s : α oplus β -> 集合 γ}
  结论: ⋂ x, s x = (⋂ x, s (.inl x)) inter ⋂ x, s (.inr x)
  证明: iInf_sum

Depends on / 依赖: iInf_sum
-/
lemma iInter_sum {s : α oplus β -> Set γ} : ⋂ x, s x = (⋂ x, s (.inl x)) inter ⋂ x, s (.inr x) := iInf_sum

/--
theorem `iUnion_psigma` / 定理 `iUnion_psigma`

English:
theorem iUnion_psigma
  given: {γ : α -> Type*} (s : PSigma γ -> Set β)
  statement: ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩
  proof: iSup_psigma _

中文:
定理 iUnion_psigma
  条件: {γ : α -> 类型} (s : 命题和类型 γ -> 集合 β)
  结论: ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩
  证明: iSup_psigma _

Depends on / 依赖: iSup_psigma
-/
theorem iUnion_psigma {γ : α -> Type*} (s : PSigma γ -> Set β) : ⋃ ia, s ia = ⋃ i, ⋃ a, s ⟨i, a⟩ :=
  iSup_psigma _

/--
theorem `iUnion_psigma'` / 定理 `iUnion_psigma'`

English:
theorem iUnion_psigma'
  given: {γ : α -> Type*} (s : forall i, γ i -> Set β)
  proof: iSup_psigma' _

中文:
定理 iUnion_psigma'
  条件: {γ : α -> 类型} (s : 对任意 i, γ i -> 集合 β)
  证明: iSup_psigma' _

Depends on / 依赖: iSup_psigma
-/
theorem iUnion_psigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) :
    ⋃ i, ⋃ a, s i a = ⋃ ia : PSigma γ, s ia.1 ia.2 :=
  iSup_psigma' _

/--
theorem `iInter_psigma` / 定理 `iInter_psigma`

English:
theorem iInter_psigma
  given: {γ : α -> Type*} (s : PSigma γ -> Set β)
  statement: ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩
  proof: iInf_psigma _

中文:
定理 i整数er_psigma
  条件: {γ : α -> 类型} (s : 命题和类型 γ -> 集合 β)
  结论: ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩
  证明: iInf_psigma _

Depends on / 依赖: iInf_psigma
-/
theorem iInter_psigma {γ : α -> Type*} (s : PSigma γ -> Set β) : ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩ :=
  iInf_psigma _

/--
theorem `iInter_psigma'` / 定理 `iInter_psigma'`

English:
theorem iInter_psigma'
  given: {γ : α -> Type*} (s : forall i, γ i -> Set β)
  proof: iInf_psigma' _

中文:
定理 i整数er_psigma'
  条件: {γ : α -> 类型} (s : 对任意 i, γ i -> 集合 β)
  证明: iInf_psigma' _

Depends on / 依赖: iInf_psigma
-/
theorem iInter_psigma' {γ : α -> Type*} (s : forall i, γ i -> Set β) :
    ⋂ i, ⋂ a, s i a = ⋂ ia : PSigma γ, s ia.1 ia.2 :=
  iInf_psigma' _

/-! ### Bounded unions and intersections -/


/--
theorem `mem_biUnion` / 定理 `mem_biUnion`

English:
theorem mem_biUnion
  given: {s : Set α} {t : α -> Set β} {x : α} {y : β} (xs : x in s) (ytx : y in t x)
  proof: mem_iUnion₂_of_mem xs ytx

中文:
定理 mem_biUnion
  条件: {s : 集合 α} {t : α -> 集合 β} {x : α} {y : β} (xs : x in s) (ytx : y in t x)
  证明: mem_iUnion₂_of_mem xs ytx
-/
theorem mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β} (xs : x in s) (ytx : y in t x) :
    y in ⋃ x in s, t x :=
  mem_iUnion₂_of_mem xs ytx

/--
theorem `mem_biInter` / 定理 `mem_biInter`

English:
theorem mem_biInter
  given: {s : Set α} {t : α -> Set β} {y : β} (h : forall x in s, y in t x)
  proof: mem_iInter₂_of_mem h

中文:
定理 mem_bi整数er
  条件: {s : 集合 α} {t : α -> 集合 β} {y : β} (h : 对任意 x in s, y in t x)
  证明: mem_iInter₂_of_mem h
-/
theorem mem_biInter {s : Set α} {t : α -> Set β} {y : β} (h : forall x in s, y in t x) :
    y in ⋂ x in s, t x :=
  mem_iInter₂_of_mem h

/--
theorem `subset_biUnion_of_mem` / 定理 `subset_biUnion_of_mem`

English:
theorem subset_biUnion_of_mem
  given: {s : Set α} {u : α -> Set β} {x : α} (xs : x in s)
  proof: subset_iUnion₂ (s := fun i _ => u i) x xs

中文:
定理 subset_biUnion_of_mem
  条件: {s : 集合 α} {u : α -> 集合 β} {x : α} (xs : x in s)
  证明: subset_iUnion₂ (s := fun i _ => u i) x xs
-/
theorem subset_biUnion_of_mem {s : Set α} {u : α -> Set β} {x : α} (xs : x in s) :
    u x subseteq ⋃ x in s, u x :=
  subset_iUnion₂ (s := fun i _ => u i) x xs

/--
theorem `biInter_subset_of_mem` / 定理 `biInter_subset_of_mem`

English:
theorem biInter_subset_of_mem
  given: {s : Set α} {t : α -> Set β} {x : α} (xs : x in s)
  proof: iInter₂_subset x xs

中文:
定理 bi整数er_subset_of_mem
  条件: {s : 集合 α} {t : α -> 集合 β} {x : α} (xs : x in s)
  证明: iInter₂_subset x xs
-/
theorem biInter_subset_of_mem {s : Set α} {t : α -> Set β} {x : α} (xs : x in s) :
    ⋂ x in s, t x subseteq t x :=
  iInter₂_subset x xs

/--
lemma `biInter_subset_biUnion` / 引理 `biInter_subset_biUnion`

English:
lemma biInter_subset_biUnion
  given: {s : Set α} (hs : s.Nonempty) {t : α -> Set β}
  proof: biInf_le_biSup hs

中文:
引理 bi整数er_subset_biUnion
  条件: {s : 集合 α} (hs : s.非空) {t : α -> 集合 β}
  证明: biInf_le_biSup hs

Depends on / 依赖: biInf_le_biSup
-/
lemma biInter_subset_biUnion {s : Set α} (hs : s.Nonempty) {t : α -> Set β} :
    ⋂ x in s, t x subseteq ⋃ x in s, t x := biInf_le_biSup hs

/--
theorem `biUnion_subset_biUnion_left` / 定理 `biUnion_subset_biUnion_left`

English:
theorem biUnion_subset_biUnion_left
  given: {s s' : Set α} {t : α -> Set β} (h : s subseteq s')
  proof: iUnion₂_subset fun _ hx => subset_biUnion_of_mem h hx

中文:
定理 biUnion_subset_biUnion_left
  条件: {s s' : 集合 α} {t : α -> 集合 β} (h : s subseteq s')
  证明: iUnion₂_subset fun _ hx => subset_biUnion_of_mem h hx

Depends on / 依赖: subset_biUnion_of_mem
-/
theorem biUnion_subset_biUnion_left {s s' : Set α} {t : α -> Set β} (h : s subseteq s') :
    ⋃ x in s, t x subseteq ⋃ x in s', t x :=
iUnion₂_subset fun _ hx => subset_biUnion_of_mem h hx

/--
theorem `biInter_subset_biInter_left` / 定理 `biInter_subset_biInter_left`

English:
theorem biInter_subset_biInter_left
  given: {s s' : Set α} {t : α -> Set β} (h : s' subseteq s)
  proof: subset_iInter₂ fun _ hx => biInter_subset_of_mem h hx

中文:
定理 bi整数er_subset_bi整数er_left
  条件: {s s' : 集合 α} {t : α -> 集合 β} (h : s' subseteq s)
  证明: subset_iInter₂ fun _ hx => biInter_subset_of_mem h hx

Depends on / 依赖: biInter_subset_of_mem
-/
theorem biInter_subset_biInter_left {s s' : Set α} {t : α -> Set β} (h : s' subseteq s) :
    ⋂ x in s, t x subseteq ⋂ x in s', t x :=
subset_iInter₂ fun _ hx => biInter_subset_of_mem h hx

/--
theorem `biUnion_mono` / 定理 `biUnion_mono`

English:
theorem biUnion_mono
  given: {s s' : Set α} {t t' : α -> Set β} (hs : s' subseteq s) (h : forall x in s, t x subseteq t' x)
  proof: (biUnion_subset_biUnion_left hs).trans iUnion₂_mono h

中文:
定理 biUnion_mono
  条件: {s s' : 集合 α} {t t' : α -> 集合 β} (hs : s' subseteq s) (h : 对任意 x in s, t x subseteq t' x)
  证明: (biUnion_subset_biUnion_left hs).trans iUnion₂_mono h

Depends on / 依赖: biUnion_subset_biUnion_left
-/
theorem biUnion_mono {s s' : Set α} {t t' : α -> Set β} (hs : s' subseteq s) (h : forall x in s, t x subseteq t' x) :
    ⋃ x in s', t x subseteq ⋃ x in s, t' x :=
(biUnion_subset_biUnion_left hs).trans iUnion₂_mono h

/--
theorem `biInter_mono` / 定理 `biInter_mono`

English:
theorem biInter_mono
  given: {s s' : Set α} {t t' : α -> Set β} (hs : s subseteq s') (h : forall x in s, t x subseteq t' x)
  proof: (biInter_subset_biInter_left hs).trans iInter₂_mono h

中文:
定理 bi整数er_mono
  条件: {s s' : 集合 α} {t t' : α -> 集合 β} (hs : s subseteq s') (h : 对任意 x in s, t x subseteq t' x)
  证明: (biInter_subset_biInter_left hs).trans iInter₂_mono h

Depends on / 依赖: biInter_subset_biInter_left
-/
theorem biInter_mono {s s' : Set α} {t t' : α -> Set β} (hs : s subseteq s') (h : forall x in s, t x subseteq t' x) :
    ⋂ x in s', t x subseteq ⋂ x in s, t' x :=
(biInter_subset_biInter_left hs).trans iInter₂_mono h

/--
theorem `biUnion_eq_iUnion` / 定理 `biUnion_eq_iUnion`

English:
theorem biUnion_eq_iUnion
  given: (s : Set α) (t : forall x in s, Set β)
  proof: iSup_subtype'

中文:
定理 biUnion_eq_iUnion
  条件: (s : 集合 α) (t : 对任意 x in s, 集合 β)
  证明: iSup_subtype'

Depends on / 依赖: iSup_subtype
-/
theorem biUnion_eq_iUnion (s : Set α) (t : forall x in s, Set β) :
    ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2 :=
  iSup_subtype'

/--
theorem `biInter_eq_iInter` / 定理 `biInter_eq_iInter`

English:
theorem biInter_eq_iInter
  given: (s : Set α) (t : forall x in s, Set β)
  proof: iInf_subtype'

中文:
定理 bi整数er_eq_i整数er
  条件: (s : 集合 α) (t : 对任意 x in s, 集合 β)
  证明: iInf_subtype'

Depends on / 依赖: iInf_subtype
-/
theorem biInter_eq_iInter (s : Set α) (t : forall x in s, Set β) :
    ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2 :=
  iInf_subtype'

/--
lemma `biUnion_const` / 引理 `biUnion_const`

English:
lemma biUnion_const
  given: {s : Set α} (hs : s.Nonempty) (t : Set β)
  statement: ⋃ a in s, t = t
  proof: biSup_const hs

中文:
引理 biUnion_const
  条件: {s : 集合 α} (hs : s.非空) (t : 集合 β)
  结论: ⋃ a in s, t = t
  证明: biSup_const hs
-/
@[simp] lemma biUnion_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋃ a in s, t = t :=
  biSup_const hs

/--
lemma `biInter_const` / 引理 `biInter_const`

English:
lemma biInter_const
  given: {s : Set α} (hs : s.Nonempty) (t : Set β)
  statement: ⋂ a in s, t = t
  proof: biInf_const hs

中文:
引理 bi整数er_const
  条件: {s : 集合 α} (hs : s.非空) (t : 集合 β)
  结论: ⋂ a in s, t = t
  证明: biInf_const hs
-/
@[simp] lemma biInter_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋂ a in s, t = t :=
  biInf_const hs

/--
theorem `iUnion_subtype` / 定理 `iUnion_subtype`

English:
theorem iUnion_subtype
  given: (p : α -> Prop) (s : { x // p x } -> Set β)
  proof: iSup_subtype

中文:
定理 iUnion_subtype
  条件: (p : α -> 命题) (s : { x // p x } -> 集合 β)
  证明: iSup_subtype

Depends on / 依赖: iSup_subtype
-/
theorem iUnion_subtype (p : α -> Prop) (s : { x // p x } -> Set β) :
    ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  iSup_subtype

/--
theorem `iInter_subtype` / 定理 `iInter_subtype`

English:
theorem iInter_subtype
  given: (p : α -> Prop) (s : { x // p x } -> Set β)
  proof: iInf_subtype

中文:
定理 i整数er_subtype
  条件: (p : α -> 命题) (s : { x // p x } -> 集合 β)
  证明: iInf_subtype

Depends on / 依赖: iInf_subtype
-/
theorem iInter_subtype (p : α -> Prop) (s : { x // p x } -> Set β) :
    ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  iInf_subtype

/--
theorem `biInter_empty` / 定理 `biInter_empty`

English:
theorem biInter_empty
  given: (u : α -> Set β)
  statement: ⋂ x in (∅ : Set α), u x = univ
  proof: iInf_emptyset

中文:
定理 bi整数er_empty
  条件: (u : α -> 集合 β)
  结论: ⋂ x in (∅ : 集合 α), u x = univ
  证明: iInf_emptyset

Depends on / 依赖: iInf_emptyset
-/
theorem biInter_empty (u : α -> Set β) : ⋂ x in (∅ : Set α), u x = univ :=
  iInf_emptyset

/--
theorem `biInter_univ` / 定理 `biInter_univ`

English:
theorem biInter_univ
  given: (u : α -> Set β)
  statement: ⋂ x in @univ α, u x = ⋂ x, u x
  proof: iInf_univ

@[simp]

中文:
定理 bi整数er_univ
  条件: (u : α -> 集合 β)
  结论: ⋂ x in @univ α, u x = ⋂ x, u x
  证明: iInf_univ

@[simp]

Depends on / 依赖: iInf_univ
-/
theorem biInter_univ (u : α -> Set β) : ⋂ x in @univ α, u x = ⋂ x, u x :=
  iInf_univ

@[simp]
/--
theorem `biUnion_self` / 定理 `biUnion_self`

English:
theorem biUnion_self
  given: (s : Set α)
  statement: ⋃ x in s, s = s
  proof: Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx

@[simp]

中文:
定理 biUnion_self
  条件: (s : 集合 α)
  结论: ⋃ x in s, s = s
  证明: Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, Subset.refl, antisymm, mem_biUnion
-/
theorem biUnion_self (s : Set α) : ⋃ x in s, s = s :=
  Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx

@[simp]
/--
theorem `iUnion_nonempty_self` / 定理 `iUnion_nonempty_self`

English:
theorem iUnion_nonempty_self
  given: (s : Set α)
  statement: ⋃ _ : s.Nonempty, s = s
  proof: by
  rw [iUnion_nonempty_index]; rw [biUnion_self]

中文:
定理 iUnion_nonempty_self
  条件: (s : 集合 α)
  结论: ⋃ _ : s.非空, s = s
  证明: by
  rw [iUnion_nonempty_index]; rw [biUnion_self]

Depends on / 依赖: biUnion_self, iUnion_nonempty_index
-/
theorem iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Nonempty, s = s := by
  rw [iUnion_nonempty_index]; rw [biUnion_self]

/--
theorem `biInter_singleton` / 定理 `biInter_singleton`

English:
theorem biInter_singleton
  given: (a : α) (s : α -> Set β)
  statement: ⋂ x in ({a} : Set α), s x = s a
  proof: iInf_singleton

中文:
定理 bi整数er_singleton
  条件: (a : α) (s : α -> 集合 β)
  结论: ⋂ x in ({a} : 集合 α), s x = s a
  证明: iInf_singleton

Depends on / 依赖: iInf_singleton
-/
theorem biInter_singleton (a : α) (s : α -> Set β) : ⋂ x in ({a} : Set α), s x = s a :=
  iInf_singleton

/--
theorem `biInter_union` / 定理 `biInter_union`

English:
theorem biInter_union
  given: (s t : Set α) (u : α -> Set β)
  proof: iInf_union

中文:
定理 bi整数er_union
  条件: (s t : 集合 α) (u : α -> 集合 β)
  证明: iInf_union

Depends on / 依赖: iInf_union
-/
theorem biInter_union (s t : Set α) (u : α -> Set β) :
    ⋂ x in s union t, u x = (⋂ x in s, u x) inter ⋂ x in t, u x :=
  iInf_union

/--
theorem `biInter_insert` / 定理 `biInter_insert`

English:
theorem biInter_insert
  given: (a : α) (s : Set α) (t : α -> Set β)
  proof: by simp

中文:
定理 bi整数er_insert
  条件: (a : α) (s : 集合 α) (t : α -> 集合 β)
  证明: by simp
-/
theorem biInter_insert (a : α) (s : Set α) (t : α -> Set β) :
    ⋂ x in insert a s, t x = t a inter ⋂ x in s, t x := by simp

/--
theorem `biInter_pair` / 定理 `biInter_pair`

English:
theorem biInter_pair
  given: (a b : α) (s : α -> Set β)
  statement: ⋂ x in ({a, b} : Set α), s x = s a inter s b
  proof: by
  rw [biInter_insert]; rw [biInter_singleton]

中文:
定理 bi整数er_pair
  条件: (a b : α) (s : α -> 集合 β)
  结论: ⋂ x in ({a, b} : 集合 α), s x = s a inter s b
  证明: by
  rw [biInter_insert]; rw [biInter_singleton]

Depends on / 依赖: biInter_insert, biInter_singleton
-/
theorem biInter_pair (a b : α) (s : α -> Set β) : ⋂ x in ({a, b} : Set α), s x = s a inter s b := by
  rw [biInter_insert]; rw [biInter_singleton]

/--
theorem `biInter_inter` / 定理 `biInter_inter`

English:
theorem biInter_inter
  given: {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Set α) (t : Set α)
  proof: by
  have : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]

中文:
定理 bi整数er_inter
  条件: {ι α : 类型} {s : 集合 ι} (hs : s.非空) (f : ι -> 集合 α) (t : 集合 α)
  证明: by
  have : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]

Depends on / 依赖: Nonempty, biInter_eq_iInter, hs.to_subtype, iInter_inter, to_subtype
-/
theorem biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Set α) (t : Set α) :
    ⋂ i in s, f i inter t = (⋂ i in s, f i) inter t := by
  have : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]

/--
theorem `inter_biInter` / 定理 `inter_biInter`

English:
theorem inter_biInter
  given: {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Set α) (t : Set α)
  proof: by
  rw [inter_comm]; rw [← biInter_inter hs]
  simp [inter_comm]

中文:
定理 inter_bi整数er
  条件: {ι α : 类型} {s : 集合 ι} (hs : s.非空) (f : ι -> 集合 α) (t : 集合 α)
  证明: by
  rw [inter_comm]; rw [← biInter_inter hs]
  simp [inter_comm]

Depends on / 依赖: biInter_inter, inter_comm
-/
theorem inter_biInter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Set α) (t : Set α) :
    ⋂ i in s, t inter f i = t inter ⋂ i in s, f i := by
  rw [inter_comm]; rw [← biInter_inter hs]
  simp [inter_comm]

/--
theorem `biUnion_empty` / 定理 `biUnion_empty`

English:
theorem biUnion_empty
  given: (s : α -> Set β)
  statement: ⋃ x in (∅ : Set α), s x = ∅
  proof: iSup_emptyset

中文:
定理 biUnion_empty
  条件: (s : α -> 集合 β)
  结论: ⋃ x in (∅ : 集合 α), s x = ∅
  证明: iSup_emptyset

Depends on / 依赖: iSup_emptyset
-/
theorem biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), s x = ∅ :=
  iSup_emptyset

/--
theorem `biUnion_univ` / 定理 `biUnion_univ`

English:
theorem biUnion_univ
  given: (s : α -> Set β)
  statement: ⋃ x in @univ α, s x = ⋃ x, s x
  proof: iSup_univ

中文:
定理 biUnion_univ
  条件: (s : α -> 集合 β)
  结论: ⋃ x in @univ α, s x = ⋃ x, s x
  证明: iSup_univ

Depends on / 依赖: iSup_univ
-/
theorem biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = ⋃ x, s x :=
  iSup_univ

/--
theorem `biUnion_singleton` / 定理 `biUnion_singleton`

English:
theorem biUnion_singleton
  given: (a : α) (s : α -> Set β)
  statement: ⋃ x in ({a} : Set α), s x = s a
  proof: iSup_singleton

@[simp]

中文:
定理 biUnion_singleton
  条件: (a : α) (s : α -> 集合 β)
  结论: ⋃ x in ({a} : 集合 α), s x = s a
  证明: iSup_singleton

@[simp]

Depends on / 依赖: iSup_singleton
-/
theorem biUnion_singleton (a : α) (s : α -> Set β) : ⋃ x in ({a} : Set α), s x = s a :=
  iSup_singleton

@[simp]
/--
theorem `biUnion_of_singleton` / 定理 `biUnion_of_singleton`

English:
theorem biUnion_of_singleton
  given: (s : Set α)
  statement: ⋃ x in s, {x} = s
  proof: ext by simp

中文:
定理 biUnion_of_singleton
  条件: (s : 集合 α)
  结论: ⋃ x in s, {x} = s
  证明: ext by simp
-/
theorem biUnion_of_singleton (s : Set α) : ⋃ x in s, {x} = s :=
ext by simp

/--
theorem `biUnion_union` / 定理 `biUnion_union`

English:
theorem biUnion_union
  given: (s t : Set α) (u : α -> Set β)
  proof: iSup_union

@[simp]

中文:
定理 biUnion_union
  条件: (s t : 集合 α) (u : α -> 集合 β)
  证明: iSup_union

@[simp]

Depends on / 依赖: iSup_union
-/
theorem biUnion_union (s t : Set α) (u : α -> Set β) :
    ⋃ x in s union t, u x = (⋃ x in s, u x) union ⋃ x in t, u x :=
  iSup_union

@[simp]
/--
theorem `iUnion_coe_set` / 定理 `iUnion_coe_set`

English:
theorem iUnion_coe_set
  given: {α β : Type*} (s : Set α) (f : s -> Set β)
  proof: iUnion_subtype _ _

@[simp]

中文:
定理 iUnion_coe_set
  条件: {α β : 类型} (s : 集合 α) (f : s -> 集合 β)
  证明: iUnion_subtype _ _

@[simp]

Depends on / 依赖: iUnion_subtype
-/
theorem iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> Set β) :
    ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩ :=
  iUnion_subtype _ _

@[simp]
/--
theorem `iInter_coe_set` / 定理 `iInter_coe_set`

English:
theorem iInter_coe_set
  given: {α β : Type*} (s : Set α) (f : s -> Set β)
  proof: iInter_subtype _ _

中文:
定理 i整数er_coe_set
  条件: {α β : 类型} (s : 集合 α) (f : s -> 集合 β)
  证明: iInter_subtype _ _

Depends on / 依赖: iInter_subtype
-/
theorem iInter_coe_set {α β : Type*} (s : Set α) (f : s -> Set β) :
    ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩ :=
  iInter_subtype _ _

/--
theorem `biUnion_insert` / 定理 `biUnion_insert`

English:
theorem biUnion_insert
  given: (a : α) (s : Set α) (t : α -> Set β)
  proof: by simp

中文:
定理 biUnion_insert
  条件: (a : α) (s : 集合 α) (t : α -> 集合 β)
  证明: by simp
-/
theorem biUnion_insert (a : α) (s : Set α) (t : α -> Set β) :
    ⋃ x in insert a s, t x = t a union ⋃ x in s, t x := by simp

/--
theorem `biUnion_pair` / 定理 `biUnion_pair`

English:
theorem biUnion_pair
  given: (a b : α) (s : α -> Set β)
  statement: ⋃ x in ({a, b} : Set α), s x = s a union s b
  proof: by
  simp

中文:
定理 biUnion_pair
  条件: (a b : α) (s : α -> 集合 β)
  结论: ⋃ x in ({a, b} : 集合 α), s x = s a union s b
  证明: by
  simp
-/
theorem biUnion_pair (a b : α) (s : α -> Set β) : ⋃ x in ({a, b} : Set α), s x = s a union s b := by
  simp

/--
theorem `inter_iUnion₂` / 定理 `inter_iUnion₂`

English:
theorem inter_iUnion₂
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: by simp only [inter_iUnion]

中文:
定理 inter_iUnion₂
  条件: (s : 集合 α) (t : 对任意 i, κ i -> 集合 α)
  证明: by simp only [inter_iUnion]

Depends on / 依赖: inter_iUnion
-/
theorem inter_iUnion₂ (s : Set α) (t : forall i, κ i -> Set α) :
    (s inter ⋃ (i) (j), t i j) = ⋃ (i) (j), s inter t i j := by simp only [inter_iUnion]

/--
theorem `iUnion₂_inter` / 定理 `iUnion₂_inter`

English:
theorem iUnion₂_inter
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: by simp_rw [iUnion_inter]

中文:
定理 iUnion₂_inter
  条件: (s : 对任意 i, κ i -> 集合 α) (t : 集合 α)
  证明: by simp_rw [iUnion_inter]

Depends on / 依赖: iUnion_inter, simp_rw
-/
theorem iUnion₂_inter (s : forall i, κ i -> Set α) (t : Set α) :
    (⋃ (i) (j), s i j) inter t = ⋃ (i) (j), s i j inter t := by simp_rw [iUnion_inter]

/--
theorem `union_iInter₂` / 定理 `union_iInter₂`

English:
theorem union_iInter₂
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: by simp_rw [union_iInter]

中文:
定理 union_i整数er₂
  条件: (s : 集合 α) (t : 对任意 i, κ i -> 集合 α)
  证明: by simp_rw [union_iInter]

Depends on / 依赖: simp_rw, union_iInter
-/
theorem union_iInter₂ (s : Set α) (t : forall i, κ i -> Set α) :
    (s union ⋂ (i) (j), t i j) = ⋂ (i) (j), s union t i j := by simp_rw [union_iInter]

/--
theorem `iInter₂_union` / 定理 `iInter₂_union`

English:
theorem iInter₂_union
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: by simp_rw [iInter_union]

中文:
定理 i整数er₂_union
  条件: (s : 对任意 i, κ i -> 集合 α) (t : 集合 α)
  证明: by simp_rw [iInter_union]

Depends on / 依赖: iInter_union, simp_rw
-/
theorem iInter₂_union (s : forall i, κ i -> Set α) (t : Set α) :
    (⋂ (i) (j), s i j) union t = ⋂ (i) (j), s i j union t := by simp_rw [iInter_union]

/--
theorem `mem_sUnion_of_mem` / 定理 `mem_sUnion_of_mem`

English:
theorem mem_sUnion_of_mem
  given: {x : α} {t : Set α} {S : Set (Set α)} (hx : x in t) (ht : t in S)
  proof: ⟨t, ht, hx⟩

中文:
定理 mem_sUnion_of_mem
  条件: {x : α} {t : 集合 α} {S : 集合 (集合 α)} (hx : x in t) (ht : t in S)
  证明: ⟨t, ht, hx⟩
-/
theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x in t) (ht : t in S) :
    x in ⋃₀ S :=
  ⟨t, ht, hx⟩

-- is this theorem really necessary?
/--
theorem `notMem_of_notMem_sUnion` / 定理 `notMem_of_notMem_sUnion`

English:
theorem notMem_of_notMem_sUnion
  statement: {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀ S)
  proof: fun h => hx ⟨t, ht, h⟩

中文:
定理 notMem_of_notMem_sUnion
  结论: {x : α} {t : 集合 α} {S : 集合 (集合 α)} (hx : x ∉ ⋃₀ S)
  证明: fun h => hx ⟨t, ht, h⟩
-/
theorem notMem_of_notMem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀ S)
    (ht : t in S) : x ∉ t := fun h => hx ⟨t, ht, h⟩

/--
theorem `sInter_subset_of_mem` / 定理 `sInter_subset_of_mem`

English:
theorem sInter_subset_of_mem
  given: {S : Set (Set α)} {t : Set α} (tS : t in S)
  statement: ⋂₀ S subseteq t
  proof: sInf_le tS

中文:
定理 s整数er_subset_of_mem
  条件: {S : 集合 (集合 α)} {t : 集合 α} (tS : t in S)
  结论: ⋂₀ S subseteq t
  证明: sInf_le tS

Depends on / 依赖: sInf_le
-/
theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t in S) : ⋂₀ S subseteq t :=
  sInf_le tS

/--
theorem `subset_sUnion_of_mem` / 定理 `subset_sUnion_of_mem`

English:
theorem subset_sUnion_of_mem
  given: {S : Set (Set α)} {t : Set α} (tS : t in S)
  statement: t subseteq ⋃₀ S
  proof: le_sSup tS

中文:
定理 subset_sUnion_of_mem
  条件: {S : 集合 (集合 α)} {t : 集合 α} (tS : t in S)
  结论: t subseteq ⋃₀ S
  证明: le_sSup tS

Depends on / 依赖: le_sSup
-/
theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t in S) : t subseteq ⋃₀ S :=
  le_sSup tS

/--
theorem `subset_sUnion_of_subset` / 定理 `subset_sUnion_of_subset`

English:
theorem subset_sUnion_of_subset
  statement: {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s subseteq u)
  proof: Subset.trans h₁ (subset_sUnion_of_mem h₂)

中文:
定理 subset_sUnion_of_subset
  结论: {s : 集合 α} (t : 集合 (集合 α)) (u : 集合 α) (h₁ : s subseteq u)
  证明: Subset.trans h₁ (subset_sUnion_of_mem h₂)

Depends on / 依赖: Subset, Subset.trans, subset_sUnion_of_mem
-/
theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s subseteq u)
    (h₂ : u in t) : s subseteq ⋃₀ t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)

/--
theorem `sUnion_subset` / 定理 `sUnion_subset`

English:
theorem sUnion_subset
  given: {S : Set (Set α)} {t : Set α} (h : forall t' in S, t' subseteq t)
  statement: ⋃₀ S subseteq t
  proof: sSup_le h

@[simp]

中文:
定理 sUnion_subset
  条件: {S : 集合 (集合 α)} {t : 集合 α} (h : 对任意 t' in S, t' subseteq t)
  结论: ⋃₀ S subseteq t
  证明: sSup_le h

@[simp]

Depends on / 依赖: sSup_le
-/
theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : forall t' in S, t' subseteq t) : ⋃₀ S subseteq t :=
  sSup_le h

@[simp]
/--
theorem `sUnion_subset_iff` / 定理 `sUnion_subset_iff`

English:
theorem sUnion_subset_iff
  given: {s : Set (Set α)} {t : Set α}
  statement: ⋃₀ s subseteq t ↔ forall t' in s, t' subseteq t
  proof: sSup_le_iff

中文:
定理 sUnion_subset_iff
  条件: {s : 集合 (集合 α)} {t : 集合 α}
  结论: ⋃₀ s subseteq t ↔ 对任意 t' in s, t' subseteq t
  证明: sSup_le_iff

Depends on / 依赖: sSup_le_iff
-/
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s subseteq t ↔ forall t' in s, t' subseteq t :=
  sSup_le_iff

/--
lemma `sUnion_mono_subsets` / 引理 `sUnion_mono_subsets`

English:
lemma sUnion_mono_subsets
  given: {s : Set (Set α)} {f : Set α -> Set α} (hf : forall t : Set α, t subseteq f t)
  proof: fun _ ⟨t, htx, hxt⟩ => ⟨f t, mem_image_of_mem f htx, hf t hxt⟩

中文:
引理 sUnion_mono_subsets
  条件: {s : 集合 (集合 α)} {f : 集合 α -> 集合 α} (hf : 对任意 t : 集合 α, t subseteq f t)
  证明: fun _ ⟨t, htx, hxt⟩ => ⟨f t, mem_image_of_mem f htx, hf t hxt⟩

Depends on / 依赖: mem_image_of_mem
-/
lemma sUnion_mono_subsets {s : Set (Set α)} {f : Set α -> Set α} (hf : forall t : Set α, t subseteq f t) :
    ⋃₀ s subseteq ⋃₀ (f '' s) :=
  fun _ ⟨t, htx, hxt⟩ => ⟨f t, mem_image_of_mem f htx, hf t hxt⟩

/--
lemma `sUnion_mono_supsets` / 引理 `sUnion_mono_supsets`

English:
lemma sUnion_mono_supsets
  given: {s : Set (Set α)} {f : Set α -> Set α} (hf : forall t : Set α, f t subseteq t)
  proof: -- If t ∈ f '' s is arbitrary; t = f u for some u : Set α.
  fun _ ⟨_, ⟨u, hus, hut⟩, hxt⟩ => ⟨u, hus, (hut ▸ hf u) hxt⟩

中文:
引理 sUnion_mono_supsets
  条件: {s : 集合 (集合 α)} {f : 集合 α -> 集合 α} (hf : 对任意 t : 集合 α, f t subseteq t)
  证明: -- If t ∈ f '' s is arbitrary; t = f u for some u : Set α.
  fun _ ⟨_, ⟨u, hus, hut⟩, hxt⟩ => ⟨u, hus, (hut ▸ hf u) hxt⟩
-/
lemma sUnion_mono_supsets {s : Set (Set α)} {f : Set α -> Set α} (hf : forall t : Set α, f t subseteq t) :
    ⋃₀ (f '' s) subseteq ⋃₀ s :=
  -- If t ∈ f '' s is arbitrary; t = f u for some u : Set α.
  fun _ ⟨_, ⟨u, hus, hut⟩, hxt⟩ => ⟨u, hus, (hut ▸ hf u) hxt⟩

/--
theorem `subset_sInter` / 定理 `subset_sInter`

English:
theorem subset_sInter
  given: {S : Set (Set α)} {t : Set α} (h : forall t' in S, t subseteq t')
  statement: t subseteq ⋂₀ S
  proof: le_sInf h

@[simp]

中文:
定理 subset_s整数er
  条件: {S : 集合 (集合 α)} {t : 集合 α} (h : 对任意 t' in S, t subseteq t')
  结论: t subseteq ⋂₀ S
  证明: le_sInf h

@[simp]

Depends on / 依赖: le_sInf
-/
theorem subset_sInter {S : Set (Set α)} {t : Set α} (h : forall t' in S, t subseteq t') : t subseteq ⋂₀ S :=
  le_sInf h

@[simp]
/--
theorem `subset_sInter_iff` / 定理 `subset_sInter_iff`

English:
theorem subset_sInter_iff
  given: {S : Set (Set α)} {t : Set α}
  statement: t subseteq ⋂₀ S ↔ forall t' in S, t subseteq t'
  proof: le_sInf_iff

@[gcongr]

中文:
定理 subset_s整数er_iff
  条件: {S : 集合 (集合 α)} {t : 集合 α}
  结论: t subseteq ⋂₀ S ↔ 对任意 t' in S, t subseteq t'
  证明: le_sInf_iff

@[gcongr]

Depends on / 依赖: le_sInf_iff
-/
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t subseteq ⋂₀ S ↔ forall t' in S, t subseteq t' :=
  le_sInf_iff

@[gcongr]
/--
theorem `sUnion_subset_sUnion` / 定理 `sUnion_subset_sUnion`

English:
theorem sUnion_subset_sUnion
  given: {S T : Set (Set α)} (h : S subseteq T)
  statement: ⋃₀ S subseteq ⋃₀ T
  proof: sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)

@[gcongr]

中文:
定理 sUnion_subset_sUnion
  条件: {S T : 集合 (集合 α)} (h : S subseteq T)
  结论: ⋃₀ S subseteq ⋃₀ T
  证明: sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)

@[gcongr]

Depends on / 依赖: sUnion_subset, subset_sUnion_of_mem
-/
theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S subseteq T) : ⋃₀ S subseteq ⋃₀ T :=
  sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)

@[gcongr]
/--
theorem `sInter_subset_sInter` / 定理 `sInter_subset_sInter`

English:
theorem sInter_subset_sInter
  given: {S T : Set (Set α)} (h : S subseteq T)
  statement: ⋂₀ T subseteq ⋂₀ S
  proof: subset_sInter fun _ hs => sInter_subset_of_mem (h hs)

@[simp]

中文:
定理 s整数er_subset_s整数er
  条件: {S T : 集合 (集合 α)} (h : S subseteq T)
  结论: ⋂₀ T subseteq ⋂₀ S
  证明: subset_sInter fun _ hs => sInter_subset_of_mem (h hs)

@[simp]

Depends on / 依赖: sInter_subset_of_mem, subset_sInter
-/
theorem sInter_subset_sInter {S T : Set (Set α)} (h : S subseteq T) : ⋂₀ T subseteq ⋂₀ S :=
  subset_sInter fun _ hs => sInter_subset_of_mem (h hs)

@[simp]
/--
theorem `sUnion_empty` / 定理 `sUnion_empty`

English:
theorem sUnion_empty
  statement: ⋃₀ ∅ = (∅ : Set α)
  proof: sSup_empty

@[simp]

中文:
定理 sUnion_empty
  结论: ⋃₀ ∅ = (∅ : 集合 α)
  证明: sSup_empty

@[simp]

Depends on / 依赖: sSup_empty
-/
theorem sUnion_empty : ⋃₀ ∅ = (∅ : Set α) :=
  sSup_empty

@[simp]
/--
theorem `sInter_empty` / 定理 `sInter_empty`

English:
theorem sInter_empty
  statement: ⋂₀ ∅ = (univ : Set α)
  proof: sInf_empty

@[simp]

中文:
定理 s整数er_empty
  结论: ⋂₀ ∅ = (univ : 集合 α)
  证明: sInf_empty

@[simp]

Depends on / 依赖: sInf_empty
-/
theorem sInter_empty : ⋂₀ ∅ = (univ : Set α) :=
  sInf_empty

@[simp]
/--
theorem `sUnion_singleton` / 定理 `sUnion_singleton`

English:
theorem sUnion_singleton
  given: (s : Set α)
  statement: ⋃₀ {s} = s
  proof: sSup_singleton

@[simp]

中文:
定理 sUnion_singleton
  条件: (s : 集合 α)
  结论: ⋃₀ {s} = s
  证明: sSup_singleton

@[simp]

Depends on / 依赖: sSup_singleton
-/
theorem sUnion_singleton (s : Set α) : ⋃₀ {s} = s :=
  sSup_singleton

@[simp]
/--
theorem `sInter_singleton` / 定理 `sInter_singleton`

English:
theorem sInter_singleton
  given: (s : Set α)
  statement: ⋂₀ {s} = s
  proof: sInf_singleton

@[simp]

中文:
定理 s整数er_singleton
  条件: (s : 集合 α)
  结论: ⋂₀ {s} = s
  证明: sInf_singleton

@[simp]

Depends on / 依赖: sInf_singleton
-/
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  sInf_singleton

@[simp]
/--
theorem `sUnion_eq_empty` / 定理 `sUnion_eq_empty`

English:
theorem sUnion_eq_empty
  given: {S : Set (Set α)}
  statement: ⋃₀ S = ∅ ↔ forall s in S, s = ∅
  proof: sSup_eq_bot

@[simp]

中文:
定理 sUnion_eq_empty
  条件: {S : 集合 (集合 α)}
  结论: ⋃₀ S = ∅ ↔ 对任意 s in S, s = ∅
  证明: sSup_eq_bot

@[simp]

Depends on / 依赖: sSup_eq_bot
-/
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀ S = ∅ ↔ forall s in S, s = ∅ :=
  sSup_eq_bot

@[simp]
/--
theorem `sInter_eq_univ` / 定理 `sInter_eq_univ`

English:
theorem sInter_eq_univ
  given: {S : Set (Set α)}
  statement: ⋂₀ S = univ ↔ forall s in S, s = univ
  proof: sInf_eq_top

中文:
定理 s整数er_eq_univ
  条件: {S : 集合 (集合 α)}
  结论: ⋂₀ S = univ ↔ 对任意 s in S, s = univ
  证明: sInf_eq_top

Depends on / 依赖: sInf_eq_top
-/
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ forall s in S, s = univ :=
  sInf_eq_top

/--
theorem `subset_powerset_iff` / 定理 `subset_powerset_iff`

English:
theorem subset_powerset_iff
  given: {s : Set (Set α)} {t : Set α}
  statement: s subseteq 𝒫 t ↔ ⋃₀ s subseteq t
  proof: sUnion_subset_iff.symm

中文:
定理 subset_powerset_iff
  条件: {s : 集合 (集合 α)} {t : 集合 α}
  结论: s subseteq 𝒫 t ↔ ⋃₀ s subseteq t
  证明: sUnion_subset_iff.symm

Depends on / 依赖: sUnion_subset_iff, sUnion_subset_iff.symm
-/
theorem subset_powerset_iff {s : Set (Set α)} {t : Set α} : s subseteq 𝒫 t ↔ ⋃₀ s subseteq t :=
  sUnion_subset_iff.symm

/--
theorem `sUnion_powerset_gc` / 定理 `sUnion_powerset_gc`

English:
theorem sUnion_powerset_gc
  proof: gc_sSup_Iic

中文:
定理 sUnion_powerset_gc
  证明: gc_sSup_Iic

Depends on / 依赖: gc_sSup_Iic
-/
theorem sUnion_powerset_gc :
    GaloisConnection (⋃₀ · : Set (Set α) -> Set α) (𝒫 · : Set α -> Set (Set α)) :=
  gc_sSup_Iic

/--
Definition of `sUnionPowersetGI` / `sUnionPowersetGI` 的定义

English:
definition sUnionPowersetGI
  signature: :
  body: giSSupIic

中文:
定义 sUnionPowersetGI
  签名: :
  定义体: giSSupIic

Depends on / 依赖: giSSupIic
-/
def sUnionPowersetGI :
    GaloisInsertion (⋃₀ · : Set (Set α) -> Set α) (𝒫 · : Set α -> Set (Set α)) :=
  giSSupIic

/--
theorem `sUnion_mem_empty_univ` / 定理 `sUnion_mem_empty_univ`

English:
theorem sUnion_mem_empty_univ
  given: {S : Set (Set α)} (h : S subseteq {∅, univ})
  proof: by
  grind

@[simp]

中文:
定理 sUnion_mem_empty_univ
  条件: {S : 集合 (集合 α)} (h : S subseteq {∅, univ})
  证明: by
  grind

@[simp]
-/
theorem sUnion_mem_empty_univ {S : Set (Set α)} (h : S subseteq {∅, univ}) :
    ⋃₀ S in ({∅, univ} : Set (Set α)) := by
  grind

@[simp]
/--
theorem `nonempty_sUnion` / 定理 `nonempty_sUnion`

English:
theorem nonempty_sUnion
  given: {S : Set (Set α)}
  statement: (⋃₀ S).Nonempty ↔ exists s in S, Set.Nonempty s
  proof: by
  simp [nonempty_iff_ne_empty]

中文:
定理 nonempty_sUnion
  条件: {S : 集合 (集合 α)}
  结论: (⋃₀ S).非空 ↔ 存在 s in S, 集合.非空 s
  证明: by
  simp [nonempty_iff_ne_empty]

Depends on / 依赖: nonempty_iff_ne_empty
-/
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀ S).Nonempty ↔ exists s in S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]

/--
theorem `Nonempty.of_sUnion` / 定理 `Nonempty.of_sUnion`

English:
theorem Nonempty.of_sUnion
  given: {s : Set (Set α)} (h : (⋃₀ s).Nonempty)
  statement: s.Nonempty
  proof: let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩

中文:
定理 非空.of_sUnion
  条件: {s : 集合 (集合 α)} (h : (⋃₀ s).非空)
  结论: s.非空
  证明: let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩

Depends on / 依赖: nonempty_sUnion
-/
theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀ s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩

/--
theorem `Nonempty.of_sUnion_eq_univ` / 定理 `Nonempty.of_sUnion_eq_univ`

English:
theorem Nonempty.of_sUnion_eq_univ
  given: [Nonempty α] {s : Set (Set α)} (h : ⋃₀ s = univ)
  statement: s.Nonempty
  proof: Nonempty.of_sUnion h.symm ▸ univ_nonempty

中文:
定理 非空.of_sUnion_eq_univ
  条件: [非空 α] {s : 集合 (集合 α)} (h : ⋃₀ s = univ)
  结论: s.非空
  证明: Nonempty.of_sUnion h.symm ▸ univ_nonempty

Depends on / 依赖: Nonempty, Nonempty.of_sUnion, h.symm, of_sUnion, univ_nonempty
-/
theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀ s = univ) : s.Nonempty :=
Nonempty.of_sUnion h.symm ▸ univ_nonempty

/--
theorem `sUnion_union` / 定理 `sUnion_union`

English:
theorem sUnion_union
  given: (S T : Set (Set α))
  statement: ⋃₀ (S union T) = ⋃₀ S union ⋃₀ T
  proof: sSup_union

中文:
定理 sUnion_union
  条件: (S T : 集合 (集合 α))
  结论: ⋃₀ (S union T) = ⋃₀ S union ⋃₀ T
  证明: sSup_union

Depends on / 依赖: sSup_union
-/
theorem sUnion_union (S T : Set (Set α)) : ⋃₀ (S union T) = ⋃₀ S union ⋃₀ T :=
  sSup_union

/--
theorem `sInter_union` / 定理 `sInter_union`

English:
theorem sInter_union
  given: (S T : Set (Set α))
  statement: ⋂₀ (S union T) = ⋂₀ S inter ⋂₀ T
  proof: sInf_union

@[simp]

中文:
定理 s整数er_union
  条件: (S T : 集合 (集合 α))
  结论: ⋂₀ (S union T) = ⋂₀ S inter ⋂₀ T
  证明: sInf_union

@[simp]

Depends on / 依赖: sInf_union
-/
theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S union T) = ⋂₀ S inter ⋂₀ T :=
  sInf_union

@[simp]
/--
theorem `sUnion_insert` / 定理 `sUnion_insert`

English:
theorem sUnion_insert
  given: (s : Set α) (T : Set (Set α))
  statement: ⋃₀ insert s T = s union ⋃₀ T
  proof: sSup_insert

@[simp]

中文:
定理 sUnion_insert
  条件: (s : 集合 α) (T : 集合 (集合 α))
  结论: ⋃₀ insert s T = s union ⋃₀ T
  证明: sSup_insert

@[simp]

Depends on / 依赖: sSup_insert
-/
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ insert s T = s union ⋃₀ T :=
  sSup_insert

@[simp]
/--
theorem `sInter_insert` / 定理 `sInter_insert`

English:
theorem sInter_insert
  given: (s : Set α) (T : Set (Set α))
  statement: ⋂₀ insert s T = s inter ⋂₀ T
  proof: sInf_insert

@[simp]

中文:
定理 s整数er_insert
  条件: (s : 集合 α) (T : 集合 (集合 α))
  结论: ⋂₀ insert s T = s inter ⋂₀ T
  证明: sInf_insert

@[simp]

Depends on / 依赖: sInf_insert
-/
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s inter ⋂₀ T :=
  sInf_insert

@[simp]
/--
theorem `sUnion_sdiff_singleton_empty` / 定理 `sUnion_sdiff_singleton_empty`

English:
theorem sUnion_sdiff_singleton_empty
  given: (s : Set (Set α))
  statement: ⋃₀ (s \ {∅}) = ⋃₀ s
  proof: sSup_sdiff_singleton_bot s

@[deprecated (since := "2026-06-03")]
alias sUnion_diff_singleton_empty := sUnion_sdiff_singleton_empty

@[simp]

中文:
定理 sUnion_sdiff_singleton_empty
  条件: (s : 集合 (集合 α))
  结论: ⋃₀ (s \ {∅}) = ⋃₀ s
  证明: sSup_sdiff_singleton_bot s

@[deprecated (since := "2026-06-03")]
alias sUnion_diff_singleton_empty := sUnion_sdiff_singleton_empty

@[simp]

Depends on / 依赖: sSup_sdiff_singleton_bot
-/
theorem sUnion_sdiff_singleton_empty (s : Set (Set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s :=
  sSup_sdiff_singleton_bot s

@[deprecated (since := "2026-06-03")]
alias sUnion_diff_singleton_empty := sUnion_sdiff_singleton_empty

@[simp]
/--
theorem `sInter_sdiff_singleton_univ` / 定理 `sInter_sdiff_singleton_univ`

English:
theorem sInter_sdiff_singleton_univ
  given: (s : Set (Set α))
  statement: ⋂₀ (s \ {univ}) = ⋂₀ s
  proof: sInf_sdiff_singleton_top s

@[deprecated (since := "2026-06-03")]
alias sInter_diff_singleton_univ := sInter_sdiff_singleton_univ

中文:
定理 s整数er_sdiff_singleton_univ
  条件: (s : 集合 (集合 α))
  结论: ⋂₀ (s \ {univ}) = ⋂₀ s
  证明: sInf_sdiff_singleton_top s

@[deprecated (since := "2026-06-03")]
alias sInter_diff_singleton_univ := sInter_sdiff_singleton_univ

Depends on / 依赖: sInf_sdiff_singleton_top
-/
theorem sInter_sdiff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  sInf_sdiff_singleton_top s

@[deprecated (since := "2026-06-03")]
alias sInter_diff_singleton_univ := sInter_sdiff_singleton_univ

/--
theorem `sUnion_pair` / 定理 `sUnion_pair`

English:
theorem sUnion_pair
  given: (s t : Set α)
  statement: ⋃₀ {s, t} = s union t
  proof: sSup_pair

中文:
定理 sUnion_pair
  条件: (s t : 集合 α)
  结论: ⋃₀ {s, t} = s union t
  证明: sSup_pair

Depends on / 依赖: sSup_pair
-/
theorem sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s union t :=
  sSup_pair

/--
theorem `sInter_pair` / 定理 `sInter_pair`

English:
theorem sInter_pair
  given: (s t : Set α)
  statement: ⋂₀ {s, t} = s inter t
  proof: sInf_pair

@[simp]

中文:
定理 s整数er_pair
  条件: (s t : 集合 α)
  结论: ⋂₀ {s, t} = s inter t
  证明: sInf_pair

@[simp]

Depends on / 依赖: sInf_pair
-/
theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s inter t :=
  sInf_pair

@[simp]
/--
theorem `sUnion_image` / 定理 `sUnion_image`

English:
theorem sUnion_image
  given: (f : α -> Set β) (s : Set α)
  statement: ⋃₀ (f '' s) = ⋃ a in s, f a
  proof: sSup_image

@[simp]

中文:
定理 sUnion_image
  条件: (f : α -> 集合 β) (s : 集合 α)
  结论: ⋃₀ (f '' s) = ⋃ a in s, f a
  证明: sSup_image

@[simp]

Depends on / 依赖: sSup_image
-/
theorem sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s) = ⋃ a in s, f a :=
  sSup_image

@[simp]
/--
theorem `sInter_image` / 定理 `sInter_image`

English:
theorem sInter_image
  given: (f : α -> Set β) (s : Set α)
  statement: ⋂₀ (f '' s) = ⋂ a in s, f a
  proof: sInf_image

@[simp]

中文:
定理 s整数er_image
  条件: (f : α -> 集合 β) (s : 集合 α)
  结论: ⋂₀ (f '' s) = ⋂ a in s, f a
  证明: sInf_image

@[simp]

Depends on / 依赖: sInf_image
-/
theorem sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ a in s, f a :=
  sInf_image

@[simp]
/--
lemma `sUnion_image2` / 引理 `sUnion_image2`

English:
lemma sUnion_image2
  given: (f : α -> β -> Set γ) (s : Set α) (t : Set β)
  proof: sSup_image2

@[simp]

中文:
引理 sUnion_image2
  条件: (f : α -> β -> 集合 γ) (s : 集合 α) (t : 集合 β)
  证明: sSup_image2

@[simp]

Depends on / 依赖: sSup_image2
-/
lemma sUnion_image2 (f : α -> β -> Set γ) (s : Set α) (t : Set β) :
    ⋃₀ (image2 f s t) = ⋃ (a in s) (b in t), f a b := sSup_image2

@[simp]
/--
lemma `sInter_image2` / 引理 `sInter_image2`

English:
lemma sInter_image2
  given: (f : α -> β -> Set γ) (s : Set α) (t : Set β)
  proof: sInf_image2

@[simp]

中文:
引理 s整数er_image2
  条件: (f : α -> β -> 集合 γ) (s : 集合 α) (t : 集合 β)
  证明: sInf_image2

@[simp]

Depends on / 依赖: sInf_image2
-/
lemma sInter_image2 (f : α -> β -> Set γ) (s : Set α) (t : Set β) :
    ⋂₀ (image2 f s t) = ⋂ (a in s) (b in t), f a b := sInf_image2

@[simp]
/--
theorem `sUnion_range` / 定理 `sUnion_range`

English:
theorem sUnion_range
  given: (f : ι -> Set β)
  statement: ⋃₀ range f = ⋃ x, f x
  proof: rfl

@[simp]

中文:
定理 sUnion_range
  条件: (f : ι -> 集合 β)
  结论: ⋃₀ range f = ⋃ x, f x
  证明: rfl

@[simp]
-/
theorem sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x :=
  rfl

@[simp]
/--
theorem `sInter_range` / 定理 `sInter_range`

English:
theorem sInter_range
  given: (f : ι -> Set β)
  statement: ⋂₀ range f = ⋂ x, f x
  proof: rfl

中文:
定理 s整数er_range
  条件: (f : ι -> 集合 β)
  结论: ⋂₀ range f = ⋂ x, f x
  证明: rfl
-/
theorem sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl

/--
theorem `iUnion_eq_univ_iff` / 定理 `iUnion_eq_univ_iff`

English:
theorem iUnion_eq_univ_iff
  given: {f : ι -> Set α}
  statement: ⋃ i, f i = univ ↔ forall x, exists i, x in f i
  proof: by
  simp only [eq_univ_iff_forall, mem_iUnion]

中文:
定理 iUnion_eq_univ_iff
  条件: {f : ι -> 集合 α}
  结论: ⋃ i, f i = univ ↔ 对任意 x, 存在 i, x in f i
  证明: by
  simp only [eq_univ_iff_forall, mem_iUnion]

Depends on / 依赖: eq_univ_iff_forall, mem_iUnion
-/
theorem iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i = univ ↔ forall x, exists i, x in f i := by
  simp only [eq_univ_iff_forall, mem_iUnion]

/--
theorem `iUnion₂_eq_univ_iff` / 定理 `iUnion₂_eq_univ_iff`

English:
theorem iUnion₂_eq_univ_iff
  given: {s : forall i, κ i -> Set α}
  proof: by
  simp only [iUnion_eq_univ_iff, mem_iUnion]

中文:
定理 iUnion₂_eq_univ_iff
  条件: {s : 对任意 i, κ i -> 集合 α}
  证明: by
  simp only [iUnion_eq_univ_iff, mem_iUnion]

Depends on / 依赖: iUnion_eq_univ_iff, mem_iUnion
-/
theorem iUnion₂_eq_univ_iff {s : forall i, κ i -> Set α} :
    ⋃ (i) (j), s i j = univ ↔ forall a, exists i j, a in s i j := by
  simp only [iUnion_eq_univ_iff, mem_iUnion]

/--
theorem `sUnion_eq_univ_iff` / 定理 `sUnion_eq_univ_iff`

English:
theorem sUnion_eq_univ_iff
  given: {c : Set (Set α)}
  statement: ⋃₀ c = univ ↔ forall a, exists b in c, a in b
  proof: by
  simp only [eq_univ_iff_forall, mem_sUnion]

中文:
定理 sUnion_eq_univ_iff
  条件: {c : 集合 (集合 α)}
  结论: ⋃₀ c = univ ↔ 对任意 a, 存在 b in c, a in b
  证明: by
  simp only [eq_univ_iff_forall, mem_sUnion]

Depends on / 依赖: eq_univ_iff_forall, mem_sUnion
-/
theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = univ ↔ forall a, exists b in c, a in b := by
  simp only [eq_univ_iff_forall, mem_sUnion]

/--
theorem `iInter_eq_empty_of_eq_empty` / 定理 `iInter_eq_empty_of_eq_empty`

English:
theorem iInter_eq_empty_of_eq_empty
  given: {i : ι} {f : ι -> Set α} (h : f i = ∅)
  proof: subset_eq_empty (iInter_subset _ i) h

中文:
定理 i整数er_eq_empty_of_eq_empty
  条件: {i : ι} {f : ι -> 集合 α} (h : f i = ∅)
  证明: subset_eq_empty (iInter_subset _ i) h

Depends on / 依赖: iInter_subset, subset_eq_empty
-/
theorem iInter_eq_empty_of_eq_empty {i : ι} {f : ι -> Set α} (h : f i = ∅) :
    ⋂ j, f j = ∅ :=
  subset_eq_empty (iInter_subset _ i) h

-- classical
/--
theorem `iInter_eq_empty_iff` / 定理 `iInter_eq_empty_iff`

English:
theorem iInter_eq_empty_iff
  given: {f : ι -> Set α}
  statement: ⋂ i, f i = ∅ ↔ forall x, exists i, x ∉ f i
  proof: by
  simp [Set.eq_empty_iff_forall_notMem]

中文:
定理 i整数er_eq_empty_iff
  条件: {f : ι -> 集合 α}
  结论: ⋂ i, f i = ∅ ↔ 对任意 x, 存在 i, x ∉ f i
  证明: by
  simp [Set.eq_empty_iff_forall_notMem]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem
-/
theorem iInter_eq_empty_iff {f : ι -> Set α} : ⋂ i, f i = ∅ ↔ forall x, exists i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
/--
theorem `iInter₂_eq_empty_iff` / 定理 `iInter₂_eq_empty_iff`

English:
theorem iInter₂_eq_empty_iff
  given: {s : forall i, κ i -> Set α}
  proof: by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

中文:
定理 i整数er₂_eq_empty_iff
  条件: {s : 对任意 i, κ i -> 集合 α}
  证明: by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

Depends on / 依赖: eq_empty_iff_forall_notMem, mem_iInter, not_forall
-/
theorem iInter₂_eq_empty_iff {s : forall i, κ i -> Set α} :
    ⋂ (i) (j), s i j = ∅ ↔ forall a, exists i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

-- classical
/--
theorem `sInter_eq_empty_iff` / 定理 `sInter_eq_empty_iff`

English:
theorem sInter_eq_empty_iff
  given: {c : Set (Set α)}
  statement: ⋂₀ c = ∅ ↔ forall a, exists b in c, a ∉ b
  proof: by
  simp [Set.eq_empty_iff_forall_notMem]

中文:
定理 s整数er_eq_empty_iff
  条件: {c : 集合 (集合 α)}
  结论: ⋂₀ c = ∅ ↔ 对任意 a, 存在 b in c, a ∉ b
  证明: by
  simp [Set.eq_empty_iff_forall_notMem]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem
-/
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ forall a, exists b in c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
@[simp]
/--
theorem `nonempty_iInter` / 定理 `nonempty_iInter`

English:
theorem nonempty_iInter
  given: {f : ι -> Set α}
  statement: (⋂ i, f i).Nonempty ↔ exists x, forall i, x in f i
  proof: by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]

中文:
定理 nonempty_i整数er
  条件: {f : ι -> 集合 α}
  结论: (⋂ i, f i).非空 ↔ 存在 x, 对任意 i, x in f i
  证明: by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]

Depends on / 依赖: iInter_eq_empty_iff, nonempty_iff_ne_empty
-/
theorem nonempty_iInter {f : ι -> Set α} : (⋂ i, f i).Nonempty ↔ exists x, forall i, x in f i := by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]

-- classical
/--
theorem `nonempty_iInter₂` / 定理 `nonempty_iInter₂`

English:
theorem nonempty_iInter₂
  given: {s : forall i, κ i -> Set α}
  proof: by
  simp

中文:
定理 nonempty_i整数er₂
  条件: {s : 对任意 i, κ i -> 集合 α}
  证明: by
  simp
-/
theorem nonempty_iInter₂ {s : forall i, κ i -> Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ exists a, forall i j, a in s i j := by
  simp

-- classical
@[simp]
/--
theorem `nonempty_sInter` / 定理 `nonempty_sInter`

English:
theorem nonempty_sInter
  given: {c : Set (Set α)}
  statement: (⋂₀ c).Nonempty ↔ exists a, forall b in c, a in b
  proof: by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

中文:
定理 nonempty_s整数er
  条件: {c : 集合 (集合 α)}
  结论: (⋂₀ c).非空 ↔ 存在 a, 对任意 b in c, a in b
  证明: by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

Depends on / 依赖: nonempty_iff_ne_empty, sInter_eq_empty_iff
-/
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ exists a, forall b in c, a in b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

-- classical
/--
theorem `compl_sUnion` / 定理 `compl_sUnion`

English:
theorem compl_sUnion
  given: (S : Set (Set α))
  statement: (⋃₀ S)ᶜ = ⋂₀ (compl '' S)
  proof: ext fun x => by simp

中文:
定理 compl_sUnion
  条件: (S : 集合 (集合 α))
  结论: (⋃₀ S)ᶜ = ⋂₀ (compl '' S)
  证明: ext fun x => by simp
-/
theorem compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp

-- classical
/--
theorem `sUnion_eq_compl_sInter_compl` / 定理 `sUnion_eq_compl_sInter_compl`

English:
theorem sUnion_eq_compl_sInter_compl
  given: (S : Set (Set α))
  statement: ⋃₀ S = (⋂₀ (compl '' S))ᶜ
  proof: by
  rw [← compl_compl (⋃₀ S)]; rw [compl_sUnion]

中文:
定理 sUnion_eq_compl_s整数er_compl
  条件: (S : 集合 (集合 α))
  结论: ⋃₀ S = (⋂₀ (compl '' S))ᶜ
  证明: by
  rw [← compl_compl (⋃₀ S)]; rw [compl_sUnion]

Depends on / 依赖: compl_compl, compl_sUnion
-/
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀ S)]; rw [compl_sUnion]

-- classical
/--
theorem `compl_sInter` / 定理 `compl_sInter`

English:
theorem compl_sInter
  given: (S : Set (Set α))
  statement: (⋂₀ S)ᶜ = ⋃₀ (compl '' S)
  proof: by
  rw [sUnion_eq_compl_sInter_compl]; rw [compl_compl_image]

中文:
定理 compl_s整数er
  条件: (S : 集合 (集合 α))
  结论: (⋂₀ S)ᶜ = ⋃₀ (compl '' S)
  证明: by
  rw [sUnion_eq_compl_sInter_compl]; rw [compl_compl_image]

Depends on / 依赖: compl_compl_image, sUnion_eq_compl_sInter_compl
-/
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl]; rw [compl_compl_image]

-- classical
/--
theorem `sInter_eq_compl_sUnion_compl` / 定理 `sInter_eq_compl_sUnion_compl`

English:
theorem sInter_eq_compl_sUnion_compl
  given: (S : Set (Set α))
  statement: ⋂₀ S = (⋃₀ (compl '' S))ᶜ
  proof: by
  rw [← compl_compl (⋂₀ S)]; rw [compl_sInter]

中文:
定理 s整数er_eq_compl_sUnion_compl
  条件: (S : 集合 (集合 α))
  结论: ⋂₀ S = (⋃₀ (compl '' S))ᶜ
  证明: by
  rw [← compl_compl (⋂₀ S)]; rw [compl_sInter]

Depends on / 依赖: compl_compl, compl_sInter
-/
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S)]; rw [compl_sInter]

/--
theorem `inter_empty_of_inter_sUnion_empty` / 定理 `inter_empty_of_inter_sUnion_empty`

English:
theorem inter_empty_of_inter_sUnion_empty
  statement: {s t : Set α} {S : Set (Set α)} (hs : t in S)
  proof: eq_empty_of_subset_empty by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)

中文:
定理 inter_empty_of_inter_sUnion_empty
  结论: {s t : 集合 α} {S : 集合 (集合 α)} (hs : t in S)
  证明: eq_empty_of_subset_empty by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)

Depends on / 依赖: eq_empty_of_subset_empty, inter_subset_inter_right, subset_sUnion_of_mem
-/
theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t in S)
    (h : s inter ⋃₀ S = ∅) : s inter t = ∅ :=
eq_empty_of_subset_empty by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)

/--
theorem `range_sigma_eq_iUnion_range` / 定理 `range_sigma_eq_iUnion_range`

English:
theorem range_sigma_eq_iUnion_range
  given: {γ : α -> Type*} (f : Sigma γ -> β)
  proof: Set.ext by simp

中文:
定理 range_sigma_eq_iUnion_range
  条件: {γ : α -> 类型} (f : 依赖和类型 γ -> β)
  证明: Set.ext by simp

Depends on / 依赖: Set.ext
-/
theorem range_sigma_eq_iUnion_range {γ : α -> Type*} (f : Sigma γ -> β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
Set.ext by simp

/--
theorem `iUnion_eq_range_sigma` / 定理 `iUnion_eq_range_sigma`

English:
theorem iUnion_eq_range_sigma
  given: (s : α -> Set β)
  statement: ⋃ i, s i = range fun a : Σ i, s i => a.2
  proof: by
  simp [Set.ext_iff]

中文:
定理 iUnion_eq_range_sigma
  条件: (s : α -> 集合 β)
  结论: ⋃ i, s i = range fun a : Σ i, s i => a.2
  证明: by
  simp [Set.ext_iff]

Depends on / 依赖: Set.ext_iff, ext_iff
-/
theorem iUnion_eq_range_sigma (s : α -> Set β) : ⋃ i, s i = range fun a : Σ i, s i => a.2 := by
  simp [Set.ext_iff]

/--
theorem `iUnion_eq_range_psigma` / 定理 `iUnion_eq_range_psigma`

English:
theorem iUnion_eq_range_psigma
  given: (s : ι -> Set β)
  statement: ⋃ i, s i = range fun a : Σ' i, s i => a.2
  proof: by
  simp [Set.ext_iff]

中文:
定理 iUnion_eq_range_psigma
  条件: (s : ι -> 集合 β)
  结论: ⋃ i, s i = range fun a : Σ' i, s i => a.2
  证明: by
  simp [Set.ext_iff]

Depends on / 依赖: Set.ext_iff, ext_iff
-/
theorem iUnion_eq_range_psigma (s : ι -> Set β) : ⋃ i, s i = range fun a : Σ' i, s i => a.2 := by
  simp [Set.ext_iff]

/--
theorem `iUnion_image_preimage_sigma_mk_eq_self` / 定理 `iUnion_image_preimage_sigma_mk_eq_self`

English:
theorem iUnion_image_preimage_sigma_mk_eq_self
  given: {ι : Type*} {σ : ι -> Type*} (s : Set (Sigma σ))
  proof: by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  grind

中文:
定理 iUnion_image_preimage_sigma_mk_eq_self
  条件: {ι : 类型} {σ : ι -> 类型} (s : 集合 (依赖和类型 σ))
  证明: by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  grind

Depends on / 依赖: mem_iUnion, mem_image, mem_preimage
-/
theorem iUnion_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι -> Type*} (s : Set (Sigma σ)) :
    ⋃ i, Sigma.mk i '' Sigma.mk i ⁻¹' s = s := by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  grind

/--
theorem `Sigma.univ` / 定理 `Sigma.univ`

English:
theorem Sigma.univ
  given: (X : α -> Type*)
  statement: (Set.univ : Set (Σ a, X a)) = ⋃ a, range (Sigma.mk a)
  proof: Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

alias sUnion_mono := sUnion_subset_sUnion

alias sInter_mono := sInter_subset_sInter

中文:
定理 依赖和类型.univ
  条件: (X : α -> 类型)
  结论: (集合.univ : 集合 (Σ a, X a)) = ⋃ a, range (依赖和类型.mk a)
  证明: Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

alias sUnion_mono := sUnion_subset_sUnion

alias sInter_mono := sInter_subset_sInter

Depends on / 依赖: Set.ext, Set.mem_range_self, Sigma.eta, Sigma.mk, iff_of_true, mem_range_self
-/
theorem Sigma.univ (X : α -> Type*) : (Set.univ : Set (Σ a, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

alias sUnion_mono := sUnion_subset_sUnion

alias sInter_mono := sInter_subset_sInter

/--
theorem `iUnion_subset_iUnion_const` / 定理 `iUnion_subset_iUnion_const`

English:
theorem iUnion_subset_iUnion_const
  given: {s : Set α} (h : ι -> ι₂)
  statement: ⋃ _ : ι, s subseteq ⋃ _ : ι₂, s
  proof: iSup_const_mono (α := Set α) h

@[simp]

中文:
定理 iUnion_subset_iUnion_const
  条件: {s : 集合 α} (h : ι -> ι₂)
  结论: ⋃ _ : ι, s subseteq ⋃ _ : ι₂, s
  证明: iSup_const_mono (α := Set α) h

@[simp]

Depends on / 依赖: iSup_const_mono
-/
theorem iUnion_subset_iUnion_const {s : Set α} (h : ι -> ι₂) : ⋃ _ : ι, s subseteq ⋃ _ : ι₂, s :=
  iSup_const_mono (α := Set α) h

@[simp]
/--
theorem `iUnion_singleton_eq_range` / 定理 `iUnion_singleton_eq_range`

English:
theorem iUnion_singleton_eq_range
  given: (f : α -> β)
  statement: ⋃ x : α, {f x} = range f
  proof: by
  ext x
  simp [@eq_comm _ x]

中文:
定理 iUnion_singleton_eq_range
  条件: (f : α -> β)
  结论: ⋃ x : α, {f x} = range f
  证明: by
  ext x
  simp [@eq_comm _ x]

Depends on / 依赖: eq_comm
-/
theorem iUnion_singleton_eq_range (f : α -> β) : ⋃ x : α, {f x} = range f := by
  ext x
  simp [@eq_comm _ x]

/--
theorem `iUnion_insert_eq_range_union_iUnion` / 定理 `iUnion_insert_eq_range_union_iUnion`

English:
theorem iUnion_insert_eq_range_union_iUnion
  given: {ι : Type*} (x : ι -> β) (t : ι -> Set β)
  proof: by
  simp_rw [← union_singleton, iUnion_union_distrib, union_comm, iUnion_singleton_eq_range]

中文:
定理 iUnion_insert_eq_range_union_iUnion
  条件: {ι : 类型} (x : ι -> β) (t : ι -> 集合 β)
  证明: by
  simp_rw [← union_singleton, iUnion_union_distrib, union_comm, iUnion_singleton_eq_range]

Depends on / 依赖: iUnion_singleton_eq_range, iUnion_union_distrib, simp_rw, union_comm, union_singleton
-/
theorem iUnion_insert_eq_range_union_iUnion {ι : Type*} (x : ι -> β) (t : ι -> Set β) :
    ⋃ i, insert (x i) (t i) = range x union ⋃ i, t i := by
  simp_rw [← union_singleton, iUnion_union_distrib, union_comm, iUnion_singleton_eq_range]

/--
theorem `iUnion_of_singleton` / 定理 `iUnion_of_singleton`

English:
theorem iUnion_of_singleton
  given: (α : Type*)
  statement: (⋃ x, {x} : Set α) = univ
  proof: by simp [Set.ext_iff]

中文:
定理 iUnion_of_singleton
  条件: (α : 类型)
  结论: (⋃ x, {x} : 集合 α) = univ
  证明: by simp [Set.ext_iff]

Depends on / 依赖: IsManifold, IsManifold.of_le, Set.ext_iff, ext_iff, le_minSmoothness, minSmoothness, of_le
-/
theorem iUnion_of_singleton (α : Type*) : (⋃ x, {x} : Set α) = univ := by simp [Set.ext_iff]

/--
theorem `iUnion_of_singleton_coe` / 定理 `iUnion_of_singleton_coe`

English:
theorem iUnion_of_singleton_coe
  given: (s : Set α)
  statement: ⋃ i : s, ({(i : α)} : Set α) = s
  proof: by simp

中文:
定理 iUnion_of_singleton_coe
  条件: (s : 集合 α)
  结论: ⋃ i : s, ({(i : α)} : 集合 α) = s
  证明: by simp
-/
theorem iUnion_of_singleton_coe (s : Set α) : ⋃ i : s, ({(i : α)} : Set α) = s := by simp

/--
theorem `sUnion_eq_biUnion` / 定理 `sUnion_eq_biUnion`

English:
theorem sUnion_eq_biUnion
  given: {s : Set (Set α)}
  statement: ⋃₀ s = ⋃ (i : Set α) (_ : i in s), i
  proof: by
  rw [← sUnion_image]; rw [image_id']

中文:
定理 sUnion_eq_biUnion
  条件: {s : 集合 (集合 α)}
  结论: ⋃₀ s = ⋃ (i : 集合 α) (_ : i in s), i
  证明: by
  rw [← sUnion_image]; rw [image_id']

Depends on / 依赖: image_id, sUnion_image
-/
theorem sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i : Set α) (_ : i in s), i := by
  rw [← sUnion_image]; rw [image_id']

/--
theorem `sInter_eq_biInter` / 定理 `sInter_eq_biInter`

English:
theorem sInter_eq_biInter
  given: {s : Set (Set α)}
  statement: ⋂₀ s = ⋂ (i : Set α) (_ : i in s), i
  proof: by
  rw [← sInter_image]; rw [image_id']

中文:
定理 s整数er_eq_bi整数er
  条件: {s : 集合 (集合 α)}
  结论: ⋂₀ s = ⋂ (i : 集合 α) (_ : i in s), i
  证明: by
  rw [← sInter_image]; rw [image_id']

Depends on / 依赖: image_id, sInter_image
-/
theorem sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_ : i in s), i := by
  rw [← sInter_image]; rw [image_id']

/--
theorem `sUnion_eq_iUnion` / 定理 `sUnion_eq_iUnion`

English:
theorem sUnion_eq_iUnion
  given: {s : Set (Set α)}
  statement: ⋃₀ s = ⋃ i : s, i
  proof: by
  simp only [← sUnion_range, Subtype.range_coe]

中文:
定理 sUnion_eq_iUnion
  条件: {s : 集合 (集合 α)}
  结论: ⋃₀ s = ⋃ i : s, i
  证明: by
  simp only [← sUnion_range, Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.range_coe, range_coe, sUnion_range
-/
theorem sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]

/--
theorem `sInter_eq_iInter` / 定理 `sInter_eq_iInter`

English:
theorem sInter_eq_iInter
  given: {s : Set (Set α)}
  statement: ⋂₀ s = ⋂ i : s, i
  proof: by
  simp only [← sInter_range, Subtype.range_coe]

@[simp]

中文:
定理 s整数er_eq_i整数er
  条件: {s : 集合 (集合 α)}
  结论: ⋂₀ s = ⋂ i : s, i
  证明: by
  simp only [← sInter_range, Subtype.range_coe]

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe, range_coe, sInter_range
-/
theorem sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]

@[simp]
/--
theorem `iUnion_of_empty` / 定理 `iUnion_of_empty`

English:
theorem iUnion_of_empty
  given: [IsEmpty ι] (s : ι -> Set α)
  statement: ⋃ i, s i = ∅
  proof: iSup_of_empty _

@[simp]

中文:
定理 iUnion_of_empty
  条件: [是空 ι] (s : ι -> 集合 α)
  结论: ⋃ i, s i = ∅
  证明: iSup_of_empty _

@[simp]

Depends on / 依赖: iSup_of_empty
-/
theorem iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i, s i = ∅ :=
  iSup_of_empty _

@[simp]
/--
theorem `iInter_of_empty` / 定理 `iInter_of_empty`

English:
theorem iInter_of_empty
  given: [IsEmpty ι] (s : ι -> Set α)
  statement: ⋂ i, s i = univ
  proof: iInf_of_empty _

中文:
定理 i整数er_of_empty
  条件: [是空 ι] (s : ι -> 集合 α)
  结论: ⋂ i, s i = univ
  证明: iInf_of_empty _

Depends on / 依赖: iInf_of_empty
-/
theorem iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i, s i = univ :=
  iInf_of_empty _

/--
theorem `union_eq_iUnion` / 定理 `union_eq_iUnion`

English:
theorem union_eq_iUnion
  given: {s₁ s₂ : Set α}
  statement: s₁ union s₂ = ⋃ b : Bool, cond b s₁ s₂
  proof: sup_eq_iSup s₁ s₂

中文:
定理 union_eq_iUnion
  条件: {s₁ s₂ : 集合 α}
  结论: s₁ union s₂ = ⋃ b : 布尔值, cond b s₁ s₂
  证明: sup_eq_iSup s₁ s₂

Depends on / 依赖: sup_eq_iSup
-/
theorem union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_iSup s₁ s₂

/--
theorem `inter_eq_iInter` / 定理 `inter_eq_iInter`

English:
theorem inter_eq_iInter
  given: {s₁ s₂ : Set α}
  statement: s₁ inter s₂ = ⋂ b : Bool, cond b s₁ s₂
  proof: inf_eq_iInf s₁ s₂

中文:
定理 inter_eq_i整数er
  条件: {s₁ s₂ : 集合 α}
  结论: s₁ inter s₂ = ⋂ b : 布尔值, cond b s₁ s₂
  证明: inf_eq_iInf s₁ s₂

Depends on / 依赖: inf_eq_iInf
-/
theorem inter_eq_iInter {s₁ s₂ : Set α} : s₁ inter s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_iInf s₁ s₂

/--
theorem `sInter_union_sInter` / 定理 `sInter_union_sInter`

English:
theorem sInter_union_sInter
  given: {S T : Set (Set α)}
  proof: sInf_sup_sInf

中文:
定理 s整数er_union_s整数er
  条件: {S T : 集合 (集合 α)}
  证明: sInf_sup_sInf

Depends on / 依赖: sInf_sup_sInf
-/
theorem sInter_union_sInter {S T : Set (Set α)} :
    ⋂₀ S union ⋂₀ T = ⋂ p in S ×ˢ T, (p : Set α × Set α).1 union p.2 :=
  sInf_sup_sInf

/--
theorem `sUnion_inter_sUnion` / 定理 `sUnion_inter_sUnion`

English:
theorem sUnion_inter_sUnion
  given: {s t : Set (Set α)}
  proof: sSup_inf_sSup

中文:
定理 sUnion_inter_sUnion
  条件: {s t : 集合 (集合 α)}
  证明: sSup_inf_sSup

Depends on / 依赖: sSup_inf_sSup
-/
theorem sUnion_inter_sUnion {s t : Set (Set α)} :
    ⋃₀ s inter ⋃₀ t = ⋃ p in s ×ˢ t, (p : Set α × Set α).1 inter p.2 :=
  sSup_inf_sSup

/--
theorem `biUnion_iUnion` / 定理 `biUnion_iUnion`

English:
theorem biUnion_iUnion
  given: (s : ι -> Set α) (t : α -> Set β)
  proof: by simp [@iUnion_comm _ ι]

中文:
定理 biUnion_iUnion
  条件: (s : ι -> 集合 α) (t : α -> 集合 β)
  证明: by simp [@iUnion_comm _ ι]

Depends on / 依赖: iUnion_comm
-/
theorem biUnion_iUnion (s : ι -> Set α) (t : α -> Set β) :
    ⋃ x in ⋃ i, s i, t x = ⋃ (i) (x in s i), t x := by simp [@iUnion_comm _ ι]

/--
theorem `biInter_iUnion` / 定理 `biInter_iUnion`

English:
theorem biInter_iUnion
  given: (s : ι -> Set α) (t : α -> Set β)
  proof: by simp [@iInter_comm _ ι]

中文:
定理 bi整数er_iUnion
  条件: (s : ι -> 集合 α) (t : α -> 集合 β)
  证明: by simp [@iInter_comm _ ι]

Depends on / 依赖: iInter_comm
-/
theorem biInter_iUnion (s : ι -> Set α) (t : α -> Set β) :
    ⋂ x in ⋃ i, s i, t x = ⋂ (i) (x in s i), t x := by simp [@iInter_comm _ ι]

/--
theorem `sUnion_iUnion` / 定理 `sUnion_iUnion`

English:
theorem sUnion_iUnion
  given: (s : ι -> Set (Set α))
  statement: ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i
  proof: by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]

中文:
定理 sUnion_iUnion
  条件: (s : ι -> 集合 (集合 α))
  结论: ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i
  证明: by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]

Depends on / 依赖: biUnion_iUnion, sUnion_eq_biUnion
-/
theorem sUnion_iUnion (s : ι -> Set (Set α)) : ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i := by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]

/--
theorem `sInter_iUnion` / 定理 `sInter_iUnion`

English:
theorem sInter_iUnion
  given: (s : ι -> Set (Set α))
  statement: ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i
  proof: by
  simp only [sInter_eq_biInter, biInter_iUnion]

中文:
定理 s整数er_iUnion
  条件: (s : ι -> 集合 (集合 α))
  结论: ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i
  证明: by
  simp only [sInter_eq_biInter, biInter_iUnion]

Depends on / 依赖: biInter_iUnion, sInter_eq_biInter
-/
theorem sInter_iUnion (s : ι -> Set (Set α)) : ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_biInter, biInter_iUnion]

/--
theorem `iUnion_range_eq_sUnion` / 定理 `iUnion_range_eq_sUnion`

English:
theorem iUnion_range_eq_sUnion
  statement: {α β : Type*} (C : Set (Set α)) {f : forall s : C, β -> (s : Type _)}
  proof: by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := hf ⟨s, hs⟩ ⟨x, hx⟩
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy

中文:
定理 iUnion_range_eq_sUnion
  结论: {α β : 类型} (C : 集合 (集合 α)) {f : 对任意 s : C, β -> (s : 类型 _)}
  证明: by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := hf ⟨s, hs⟩ ⟨x, hx⟩
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy

Depends on / 依赖: Subtype, Subtype.val, congr_arg
-/
theorem iUnion_range_eq_sUnion {α β : Type*} (C : Set (Set α)) {f : forall s : C, β -> (s : Type _)}
    (hf : forall s : C, Surjective (f s)) : ⋃ y : β, range (fun s : C => (f s y).val) = ⋃₀ C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := hf ⟨s, hs⟩ ⟨x, hx⟩
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy

/--
theorem `iUnion_range_eq_iUnion` / 定理 `iUnion_range_eq_iUnion`

English:
theorem iUnion_range_eq_iUnion
  statement: (C : ι -> Set α) {f : forall x : ι, β -> C x}
  proof: by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    obtain ⟨y, hy⟩ := hf i ⟨x, hx⟩
    exact ⟨y, i, congr_arg Subtype.val hy⟩

中文:
定理 iUnion_range_eq_iUnion
  结论: (C : ι -> 集合 α) {f : 对任意 x : ι, β -> C x}
  证明: by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    obtain ⟨y, hy⟩ := hf i ⟨x, hx⟩
    exact ⟨y, i, congr_arg Subtype.val hy⟩

Depends on / 依赖: Subtype, Subtype.val, congr_arg, mem_iUnion
-/
theorem iUnion_range_eq_iUnion (C : ι -> Set α) {f : forall x : ι, β -> C x}
    (hf : forall x : ι, Surjective (f x)) : ⋃ y : β, range (fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    obtain ⟨y, hy⟩ := hf i ⟨x, hx⟩
    exact ⟨y, i, congr_arg Subtype.val hy⟩

/--
lemma `iUnion_sumElim` / 引理 `iUnion_sumElim`

English:
lemma iUnion_sumElim
  given: {ι σ : Type*} (s : ι -> Set α) (t : σ -> Set α)
  proof: by
  ext
  simp

中文:
引理 iUnion_sumElim
  条件: {ι σ : 类型} (s : ι -> 集合 α) (t : σ -> 集合 α)
  证明: by
  ext
  simp
-/
lemma iUnion_sumElim {ι σ : Type*} (s : ι -> Set α) (t : σ -> Set α) :
    ⋃ x, Sum.elim s t x = (⋃ x, s x) union ⋃ x, t x := by
  ext
  simp

/--
theorem `union_distrib_iInter_left` / 定理 `union_distrib_iInter_left`

English:
theorem union_distrib_iInter_left
  given: (s : ι -> Set α) (t : Set α)
  statement: (t union ⋂ i, s i) = ⋂ i, t union s i
  proof: sup_iInf_eq _ _

中文:
定理 union_distrib_i整数er_left
  条件: (s : ι -> 集合 α) (t : 集合 α)
  结论: (t union ⋂ i, s i) = ⋂ i, t union s i
  证明: sup_iInf_eq _ _

Depends on / 依赖: sup_iInf_eq
-/
theorem union_distrib_iInter_left (s : ι -> Set α) (t : Set α) : (t union ⋂ i, s i) = ⋂ i, t union s i :=
  sup_iInf_eq _ _

/--
theorem `union_distrib_iInter₂_left` / 定理 `union_distrib_iInter₂_left`

English:
theorem union_distrib_iInter₂_left
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: by simp_rw [union_distrib_iInter_left]

中文:
定理 union_distrib_i整数er₂_left
  条件: (s : 集合 α) (t : 对任意 i, κ i -> 集合 α)
  证明: by simp_rw [union_distrib_iInter_left]

Depends on / 依赖: simp_rw, union_distrib_iInter_left
-/
theorem union_distrib_iInter₂_left (s : Set α) (t : forall i, κ i -> Set α) :
    (s union ⋂ (i) (j), t i j) = ⋂ (i) (j), s union t i j := by simp_rw [union_distrib_iInter_left]

/--
theorem `union_distrib_iInter_right` / 定理 `union_distrib_iInter_right`

English:
theorem union_distrib_iInter_right
  given: (s : ι -> Set α) (t : Set α)
  statement: (⋂ i, s i) union t = ⋂ i, s i union t
  proof: iInf_sup_eq _ _

中文:
定理 union_distrib_i整数er_right
  条件: (s : ι -> 集合 α) (t : 集合 α)
  结论: (⋂ i, s i) union t = ⋂ i, s i union t
  证明: iInf_sup_eq _ _

Depends on / 依赖: iInf_sup_eq
-/
theorem union_distrib_iInter_right (s : ι -> Set α) (t : Set α) : (⋂ i, s i) union t = ⋂ i, s i union t :=
  iInf_sup_eq _ _

/--
theorem `union_distrib_iInter₂_right` / 定理 `union_distrib_iInter₂_right`

English:
theorem union_distrib_iInter₂_right
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: by simp_rw [union_distrib_iInter_right]

中文:
定理 union_distrib_i整数er₂_right
  条件: (s : 对任意 i, κ i -> 集合 α) (t : 集合 α)
  证明: by simp_rw [union_distrib_iInter_right]

Depends on / 依赖: simp_rw, union_distrib_iInter_right
-/
theorem union_distrib_iInter₂_right (s : forall i, κ i -> Set α) (t : Set α) :
    (⋂ (i) (j), s i j) union t = ⋂ (i) (j), s i j union t := by simp_rw [union_distrib_iInter_right]

/--
lemma `biUnion_lt_eq_iUnion` / 引理 `biUnion_lt_eq_iUnion`

English:
lemma biUnion_lt_eq_iUnion
  given: [LT α] [NoMaxOrder α] {s : α -> Set β}
  proof: biSup_lt_eq_iSup

中文:
引理 biUnion_lt_eq_iUnion
  条件: [LT α] [NoMax序 α] {s : α -> 集合 β}
  证明: biSup_lt_eq_iSup

Depends on / 依赖: biSup_lt_eq_iSup
-/
lemma biUnion_lt_eq_iUnion [LT α] [NoMaxOrder α] {s : α -> Set β} :
    ⋃ (n) (m < n), s m = ⋃ n, s n := biSup_lt_eq_iSup

/--
lemma `biUnion_le_eq_iUnion` / 引理 `biUnion_le_eq_iUnion`

English:
lemma biUnion_le_eq_iUnion
  given: [Preorder α] {s : α -> Set β}
  proof: biSup_le_eq_iSup

中文:
引理 biUnion_le_eq_iUnion
  条件: [预序 α] {s : α -> 集合 β}
  证明: biSup_le_eq_iSup

Depends on / 依赖: biSup_le_eq_iSup
-/
lemma biUnion_le_eq_iUnion [Preorder α] {s : α -> Set β} :
    ⋃ (n) (m <= n), s m = ⋃ n, s n := biSup_le_eq_iSup

/--
lemma `biInter_lt_eq_iInter` / 引理 `biInter_lt_eq_iInter`

English:
lemma biInter_lt_eq_iInter
  given: [LT α] [NoMaxOrder α] {s : α -> Set β}
  proof: biInf_lt_eq_iInf

中文:
引理 bi整数er_lt_eq_i整数er
  条件: [LT α] [NoMax序 α] {s : α -> 集合 β}
  证明: biInf_lt_eq_iInf

Depends on / 依赖: biInf_lt_eq_iInf
-/
lemma biInter_lt_eq_iInter [LT α] [NoMaxOrder α] {s : α -> Set β} :
    ⋂ (n) (m < n), s m = ⋂ (n), s n := biInf_lt_eq_iInf

/--
lemma `biInter_le_eq_iInter` / 引理 `biInter_le_eq_iInter`

English:
lemma biInter_le_eq_iInter
  given: [Preorder α] {s : α -> Set β}
  proof: biInf_le_eq_iInf

中文:
引理 bi整数er_le_eq_i整数er
  条件: [预序 α] {s : α -> 集合 β}
  证明: biInf_le_eq_iInf

Depends on / 依赖: biInf_le_eq_iInf
-/
lemma biInter_le_eq_iInter [Preorder α] {s : α -> Set β} :
    ⋂ (n) (m <= n), s m = ⋂ (n), s n := biInf_le_eq_iInf

/--
lemma `biUnion_gt_eq_iUnion` / 引理 `biUnion_gt_eq_iUnion`

English:
lemma biUnion_gt_eq_iUnion
  given: [LT α] [NoMinOrder α] {s : α -> Set β}
  proof: biSup_gt_eq_iSup

中文:
引理 biUnion_gt_eq_iUnion
  条件: [LT α] [NoMin序 α] {s : α -> 集合 β}
  证明: biSup_gt_eq_iSup

Depends on / 依赖: biSup_gt_eq_iSup
-/
lemma biUnion_gt_eq_iUnion [LT α] [NoMinOrder α] {s : α -> Set β} :
    ⋃ (n) (m > n), s m = ⋃ n, s n := biSup_gt_eq_iSup

/--
lemma `biUnion_ge_eq_iUnion` / 引理 `biUnion_ge_eq_iUnion`

English:
lemma biUnion_ge_eq_iUnion
  given: [Preorder α] {s : α -> Set β}
  proof: biSup_ge_eq_iSup

中文:
引理 biUnion_ge_eq_iUnion
  条件: [预序 α] {s : α -> 集合 β}
  证明: biSup_ge_eq_iSup

Depends on / 依赖: biSup_ge_eq_iSup
-/
lemma biUnion_ge_eq_iUnion [Preorder α] {s : α -> Set β} :
    ⋃ (n) (m >= n), s m = ⋃ n, s n := biSup_ge_eq_iSup

/--
lemma `biInter_gt_eq_iInf` / 引理 `biInter_gt_eq_iInf`

English:
lemma biInter_gt_eq_iInf
  given: [LT α] [NoMinOrder α] {s : α -> Set β}
  proof: biInf_gt_eq_iInf

中文:
引理 bi整数er_gt_eq_iInf
  条件: [LT α] [NoMin序 α] {s : α -> 集合 β}
  证明: biInf_gt_eq_iInf

Depends on / 依赖: biInf_gt_eq_iInf
-/
lemma biInter_gt_eq_iInf [LT α] [NoMinOrder α] {s : α -> Set β} :
    ⋂ (n) (m > n), s m = ⋂ n, s n := biInf_gt_eq_iInf

/--
lemma `biInter_ge_eq_iInf` / 引理 `biInter_ge_eq_iInf`

English:
lemma biInter_ge_eq_iInf
  given: [Preorder α] {s : α -> Set β}
  proof: biInf_ge_eq_iInf

中文:
引理 bi整数er_ge_eq_iInf
  条件: [预序 α] {s : α -> 集合 β}
  证明: biInf_ge_eq_iInf

Depends on / 依赖: biInf_ge_eq_iInf
-/
lemma biInter_ge_eq_iInf [Preorder α] {s : α -> Set β} :
    ⋂ (n) (m >= n), s m = ⋂ n, s n := biInf_ge_eq_iInf

section le

variable {ι : Type*} [PartialOrder ι] (s : ι -> Set α) (i : ι)

/--
theorem `biUnion_le` / 定理 `biUnion_le`

English:
theorem biUnion_le
  statement: (⋃ j <= i, s j) = (⋃ j < i, s j) union s i
  proof: biSup_le_eq_sup s i

中文:
定理 biUnion_le
  结论: (⋃ j <= i, s j) = (⋃ j < i, s j) union s i
  证明: biSup_le_eq_sup s i

Depends on / 依赖: biSup_le_eq_sup
-/
theorem biUnion_le : (⋃ j <= i, s j) = (⋃ j < i, s j) union s i :=
  biSup_le_eq_sup s i

/--
theorem `biInter_le` / 定理 `biInter_le`

English:
theorem biInter_le
  statement: (⋂ j <= i, s j) = (⋂ j < i, s j) inter s i
  proof: biInf_le_eq_inf s i

中文:
定理 bi整数er_le
  结论: (⋂ j <= i, s j) = (⋂ j < i, s j) inter s i
  证明: biInf_le_eq_inf s i

Depends on / 依赖: biInf_le_eq_inf
-/
theorem biInter_le : (⋂ j <= i, s j) = (⋂ j < i, s j) inter s i :=
  biInf_le_eq_inf s i

/--
theorem `biUnion_ge` / 定理 `biUnion_ge`

English:
theorem biUnion_ge
  statement: (⋃ j >= i, s j) = s i union ⋃ j > i, s j
  proof: biSup_ge_eq_sup s i

中文:
定理 biUnion_ge
  结论: (⋃ j >= i, s j) = s i union ⋃ j > i, s j
  证明: biSup_ge_eq_sup s i

Depends on / 依赖: biSup_ge_eq_sup
-/
theorem biUnion_ge : (⋃ j >= i, s j) = s i union ⋃ j > i, s j :=
  biSup_ge_eq_sup s i

/--
theorem `biInter_ge` / 定理 `biInter_ge`

English:
theorem biInter_ge
  statement: (⋂ j >= i, s j) = s i inter ⋂ j > i, s j
  proof: biInf_ge_eq_inf s i

中文:
定理 bi整数er_ge
  结论: (⋂ j >= i, s j) = s i inter ⋂ j > i, s j
  证明: biInf_ge_eq_inf s i

Depends on / 依赖: biInf_ge_eq_inf
-/
theorem biInter_ge : (⋂ j >= i, s j) = s i inter ⋂ j > i, s j :=
  biInf_ge_eq_inf s i

end le

section Pi

variable {π : α -> Type*}

/--
theorem `pi_def` / 定理 `pi_def`

English:
theorem pi_def
  given: (i : Set α) (s : forall a, Set (π a))
  statement: pi i s = ⋂ a in i, eval a ⁻¹' s a
  proof: by
  ext
  simp

中文:
定理 pi_def
  条件: (i : 集合 α) (s : 对任意 a, 集合 (π a))
  结论: pi i s = ⋂ a in i, eval a ⁻¹' s a
  证明: by
  ext
  simp
-/
theorem pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a in i, eval a ⁻¹' s a := by
  ext
  simp

/--
theorem `univ_pi_eq_iInter` / 定理 `univ_pi_eq_iInter`

English:
theorem univ_pi_eq_iInter
  given: (t : forall i, Set (π i))
  statement: pi univ t = ⋂ i, eval i ⁻¹' t i
  proof: by
  simp only [pi_def, iInter_true, mem_univ]

中文:
定理 univ_pi_eq_i整数er
  条件: (t : 对任意 i, 集合 (π i))
  结论: pi univ t = ⋂ i, eval i ⁻¹' t i
  证明: by
  simp only [pi_def, iInter_true, mem_univ]

Depends on / 依赖: iInter_true, mem_univ, pi_def
-/
theorem univ_pi_eq_iInter (t : forall i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, iInter_true, mem_univ]

/--
theorem `pi_sdiff_pi_subset` / 定理 `pi_sdiff_pi_subset`

English:
theorem pi_sdiff_pi_subset
  given: (i : Set α) (s t : forall a, Set (π a))
  proof: by
  refine sdiff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_sdiff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not] at hx
  exact hx.2 _ ha (hx.1 _ ha)

@[deprecated (since := "2026-06-03")] alias pi_diff_pi_subset := pi_sdiff_pi_subset

中文:
定理 pi_sdiff_pi_subset
  条件: (i : 集合 α) (s t : 对任意 a, 集合 (π a))
  证明: by
  refine sdiff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_sdiff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not] at hx
  exact hx.2 _ ha (hx.1 _ ha)

@[deprecated (since := "2026-06-03")] alias pi_diff_pi_subset := pi_sdiff_pi_subset

Depends on / 依赖: mem_iUnion, mem_pi, mem_preimage, mem_sdiff, not_and, not_exists, not_not, sdiff_subset_comm
-/
theorem pi_sdiff_pi_subset (i : Set α) (s t : forall a, Set (π a)) :
    pi i s \ pi i t subseteq ⋃ a in i, eval a ⁻¹' (s a \ t a) := by
  refine sdiff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_sdiff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not] at hx
  exact hx.2 _ ha (hx.1 _ ha)

@[deprecated (since := "2026-06-03")] alias pi_diff_pi_subset := pi_sdiff_pi_subset

/--
theorem `iUnion_univ_pi` / 定理 `iUnion_univ_pi`

English:
theorem iUnion_univ_pi
  given: {ι : α -> Type*} (t : (a : α) -> ι a -> Set (π a))
  proof: by
  ext
  simp [Classical.skolem]

中文:
定理 iUnion_univ_pi
  条件: {ι : α -> 类型} (t : (a : α) -> ι a -> 集合 (π a))
  证明: by
  ext
  simp [Classical.skolem]

Depends on / 依赖: Classical, Classical.skolem, skolem
-/
theorem iUnion_univ_pi {ι : α -> Type*} (t : (a : α) -> ι a -> Set (π a)) :
    ⋃ x : (a : α) -> ι a, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j : ι a, t a j := by
  ext
  simp [Classical.skolem]

/--
theorem `biUnion_univ_pi` / 定理 `biUnion_univ_pi`

English:
theorem biUnion_univ_pi
  given: {ι : α -> Type*} (s : (a : α) -> Set (ι a)) (t : (a : α) -> ι a -> Set (π a))
  proof: by
  ext
  simp [Classical.skolem, forall_and]

中文:
定理 biUnion_univ_pi
  条件: {ι : α -> 类型} (s : (a : α) -> 集合 (ι a)) (t : (a : α) -> ι a -> 集合 (π a))
  证明: by
  ext
  simp [Classical.skolem, forall_and]

Depends on / 依赖: Classical, Classical.skolem, forall_and, skolem
-/
theorem biUnion_univ_pi {ι : α -> Type*} (s : (a : α) -> Set (ι a)) (t : (a : α) -> ι a -> Set (π a)) :
    ⋃ x in univ.pi s, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j in s a, t a j := by
  ext
  simp [Classical.skolem, forall_and]

/--
theorem `pi_iUnion_eq_iInter_pi` / 定理 `pi_iUnion_eq_iInter_pi`

English:
theorem pi_iUnion_eq_iInter_pi
  given: {α' : Type*} (s : α' -> Set α) (t : (a : α) -> Set (π a))
  proof: by
  ext f
  simp
  grind

中文:
定理 pi_iUnion_eq_i整数er_pi
  条件: {α' : 类型} (s : α' -> 集合 α) (t : (a : α) -> 集合 (π a))
  证明: by
  ext f
  simp
  grind
-/
theorem pi_iUnion_eq_iInter_pi {α' : Type*} (s : α' -> Set α) (t : (a : α) -> Set (π a)) :
    (⋃ i, s i).pi t = ⋂ i, (s i).pi t := by
  ext f
  simp
  grind

end Pi

section Directed

/--
theorem `directedOn_iUnion` / 定理 `directedOn_iUnion`

English:
theorem directedOn_iUnion
  statement: {r} {f : ι -> Set α} (hd : Directed (· subseteq ·) f)
  proof: by
  simp only [DirectedOn, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

中文:
定理 directedOn_iUnion
  结论: {r} {f : ι -> 集合 α} (hd : Directed (· subseteq ·) f)
  证明: by
  simp only [DirectedOn, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

Depends on / 依赖: DirectedOn, exists_imp, mem_iUnion
-/
theorem directedOn_iUnion {r} {f : ι -> Set α} (hd : Directed (· subseteq ·) f)
    (h : forall x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

/--
theorem `directedOn_sUnion` / 定理 `directedOn_sUnion`

English:
theorem directedOn_sUnion
  statement: {r} {S : Set (Set α)} (hd : DirectedOn (· subseteq ·) S)
  proof: by
  rw [sUnion_eq_iUnion]
  exact directedOn_iUnion (directedOn_iff_directed.mp hd) (fun i => h i.1 i.2)

中文:
定理 directedOn_sUnion
  结论: {r} {S : 集合 (集合 α)} (hd : DirectedOn (· subseteq ·) S)
  证明: by
  rw [sUnion_eq_iUnion]
  exact directedOn_iUnion (directedOn_iff_directed.mp hd) (fun i => h i.1 i.2)

Depends on / 依赖: directedOn_iUnion, directedOn_iff_directed, directedOn_iff_directed.mp, sUnion_eq_iUnion
-/
theorem directedOn_sUnion {r} {S : Set (Set α)} (hd : DirectedOn (· subseteq ·) S)
    (h : forall x in S, DirectedOn r x) : DirectedOn r (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact directedOn_iUnion (directedOn_iff_directed.mp hd) (fun i => h i.1 i.2)
end Directed

end Set

namespace Function

namespace Surjective

/--
theorem `iUnion_comp` / 定理 `iUnion_comp`

English:
theorem iUnion_comp
  given: {f : ι -> ι₂} (hf : Surjective f) (g : ι₂ -> Set α)
  statement: ⋃ x, g (f x) = ⋃ y, g y
  proof: hf.iSup_comp g

中文:
定理 iUnion_comp
  条件: {f : ι -> ι₂} (hf : 满射 f) (g : ι₂ -> 集合 α)
  结论: ⋃ x, g (f x) = ⋃ y, g y
  证明: hf.iSup_comp g

Depends on / 依赖: hf.iSup_comp, iSup_comp
-/
theorem iUnion_comp {f : ι -> ι₂} (hf : Surjective f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y :=
  hf.iSup_comp g

/--
theorem `iInter_comp` / 定理 `iInter_comp`

English:
theorem iInter_comp
  given: {f : ι -> ι₂} (hf : Surjective f) (g : ι₂ -> Set α)
  statement: ⋂ x, g (f x) = ⋂ y, g y
  proof: hf.iInf_comp g

中文:
定理 i整数er_comp
  条件: {f : ι -> ι₂} (hf : 满射 f) (g : ι₂ -> 集合 α)
  结论: ⋂ x, g (f x) = ⋂ y, g y
  证明: hf.iInf_comp g

Depends on / 依赖: hf.iInf_comp, iInf_comp
-/
theorem iInter_comp {f : ι -> ι₂} (hf : Surjective f) (g : ι₂ -> Set α) : ⋂ x, g (f x) = ⋂ y, g y :=
  hf.iInf_comp g

end Surjective

end Function

/-!
### Disjoint sets
-/


section Disjoint

variable {s t : Set α}

namespace Set

@[simp]
/--
theorem `disjoint_iUnion_left` / 定理 `disjoint_iUnion_left`

English:
theorem disjoint_iUnion_left
  given: {ι : Sort*} {s : ι -> Set α}
  proof: iSup_disjoint_iff

@[simp]

中文:
定理 disjoint_iUnion_left
  条件: {ι : 类型层*} {s : ι -> 集合 α}
  证明: iSup_disjoint_iff

@[simp]

Depends on / 依赖: iSup_disjoint_iff
-/
theorem disjoint_iUnion_left {ι : Sort*} {s : ι -> Set α} :
    Disjoint (⋃ i, s i) t ↔ forall i, Disjoint (s i) t :=
  iSup_disjoint_iff

@[simp]
/--
theorem `disjoint_iUnion_right` / 定理 `disjoint_iUnion_right`

English:
theorem disjoint_iUnion_right
  given: {ι : Sort*} {s : ι -> Set α}
  proof: disjoint_iSup_iff

中文:
定理 disjoint_iUnion_right
  条件: {ι : 类型层*} {s : ι -> 集合 α}
  证明: disjoint_iSup_iff

Depends on / 依赖: disjoint_iSup_iff
-/
theorem disjoint_iUnion_right {ι : Sort*} {s : ι -> Set α} :
    Disjoint t (⋃ i, s i) ↔ forall i, Disjoint t (s i) :=
  disjoint_iSup_iff

/--
theorem `disjoint_iUnion₂_left` / 定理 `disjoint_iUnion₂_left`

English:
theorem disjoint_iUnion₂_left
  given: {s : forall i, κ i -> Set α} {t : Set α}
  proof: iSup₂_disjoint_iff

中文:
定理 disjoint_iUnion₂_left
  条件: {s : 对任意 i, κ i -> 集合 α} {t : 集合 α}
  证明: iSup₂_disjoint_iff
-/
theorem disjoint_iUnion₂_left {s : forall i, κ i -> Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ forall i j, Disjoint (s i j) t :=
  iSup₂_disjoint_iff

/--
theorem `disjoint_iUnion₂_right` / 定理 `disjoint_iUnion₂_right`

English:
theorem disjoint_iUnion₂_right
  given: {s : Set α} {t : forall i, κ i -> Set α}
  proof: disjoint_iSup₂_iff

@[simp]

中文:
定理 disjoint_iUnion₂_right
  条件: {s : 集合 α} {t : 对任意 i, κ i -> 集合 α}
  证明: disjoint_iSup₂_iff

@[simp]
-/
theorem disjoint_iUnion₂_right {s : Set α} {t : forall i, κ i -> Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ forall i j, Disjoint s (t i j) :=
  disjoint_iSup₂_iff

@[simp]
/--
theorem `disjoint_sUnion_left` / 定理 `disjoint_sUnion_left`

English:
theorem disjoint_sUnion_left
  given: {S : Set (Set α)} {t : Set α}
  proof: sSup_disjoint_iff

@[simp]

中文:
定理 disjoint_sUnion_left
  条件: {S : 集合 (集合 α)} {t : 集合 α}
  证明: sSup_disjoint_iff

@[simp]

Depends on / 依赖: sSup_disjoint_iff
-/
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀ S) t ↔ forall s in S, Disjoint s t :=
  sSup_disjoint_iff

@[simp]
/--
theorem `disjoint_sUnion_right` / 定理 `disjoint_sUnion_right`

English:
theorem disjoint_sUnion_right
  given: {s : Set α} {S : Set (Set α)}
  proof: disjoint_sSup_iff

中文:
定理 disjoint_sUnion_right
  条件: {s : 集合 α} {S : 集合 (集合 α)}
  证明: disjoint_sSup_iff

Depends on / 依赖: disjoint_sSup_iff
-/
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀ S) ↔ forall t in S, Disjoint s t :=
  disjoint_sSup_iff

/--
lemma `biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ` / 引理 `biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ`

English:
lemma biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ
  statement: {ι : Type*} {Es : ι -> Set α}
  proof: by
  ext x
  obtain ⟨i, hix⟩ : exists i, x in Es i := by simp [← mem_iUnion, Es_union]
  have obs : forall (J : Set ι), x in ⋃ j in J, Es j ↔ i in J := by
    refine fun J => ⟨?_, fun i_in_J => by simpa only [mem_iUnion, exists_prop] using ⟨i, i_in_J, hix⟩⟩
    intro x_in_U
    simp only [mem_iUnion

中文:
引理 biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ
  结论: {ι : 类型} {Es : ι -> 集合 α}
  证明: by
  ext x
  obtain ⟨i, hix⟩ : exists i, x in Es i := by simp [← mem_iUnion, Es_union]
  have obs : forall (J : Set ι), x in ⋃ j in J, Es j ↔ i in J := by
    refine fun J => ⟨?_, fun i_in_J => by simpa only [mem_iUnion, exists_prop] using ⟨i, i_in_J, hix⟩⟩
    intro x_in_U
    simp only [mem_iUnion

Depends on / 依赖: Disjoint, Disjoint.ne_of_mem, Es_disj, Es_union, exists_prop, i_in_J, i_ne_j, j_in_J, mem_iUnion, ne_of_mem, x_in_U
-/
lemma biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ {ι : Type*} {Es : ι -> Set α}
    (Es_union : ⋃ i, Es i = univ) (Es_disj : Pairwise fun i j => Disjoint (Es i) (Es j))
    (I : Set ι) :
    (⋃ i in I, Es i)ᶜ = ⋃ i in Iᶜ, Es i := by
  ext x
  obtain ⟨i, hix⟩ : exists i, x in Es i := by simp [← mem_iUnion, Es_union]
  have obs : forall (J : Set ι), x in ⋃ j in J, Es j ↔ i in J := by
    refine fun J => ⟨?_, fun i_in_J => by simpa only [mem_iUnion, exists_prop] using ⟨i, i_in_J, hix⟩⟩
    intro x_in_U
    simp only [mem_iUnion, exists_prop] at x_in_U
    obtain ⟨j, j_in_J, hjx⟩ := x_in_U
    rwa [show i = j by by_contra i_ne_j; exact Disjoint.ne_of_mem (Es_disj i_ne_j) hix hjx rfl]
  have obs' : forall (J : Set ι), x in (⋃ j in J, Es j)ᶜ ↔ i ∉ J :=
    fun J => by simpa only [mem_compl_iff, not_iff_not] using obs J
  rw [obs]; rw [obs']; rw [mem_compl_iff]

end Set

end Disjoint

/-! ### Intervals -/

namespace Set

/--
lemma `nonempty_iInter_Iic_iff` / 引理 `nonempty_iInter_Iic_iff`

English:
lemma nonempty_iInter_Iic_iff
  given: [Preorder α] {f : ι -> α}
  proof: by
  have : (⋂ (i : ι), Iic (f i)) = lowerBounds (range f) := by
    ext c; simp [lowerBounds]
  simp [this, BddBelow]

中文:
引理 nonempty_i整数er_Iic_iff
  条件: [预序 α] {f : ι -> α}
  证明: by
  have : (⋂ (i : ι), Iic (f i)) = lowerBounds (range f) := by
    ext c; simp [lowerBounds]
  simp [this, BddBelow]

Depends on / 依赖: BddBelow, lowerBounds
-/
lemma nonempty_iInter_Iic_iff [Preorder α] {f : ι -> α} :
    (⋂ i, Iic (f i)).Nonempty ↔ BddBelow (range f) := by
  have : (⋂ (i : ι), Iic (f i)) = lowerBounds (range f) := by
    ext c; simp [lowerBounds]
  simp [this, BddBelow]

/--
lemma `nonempty_iInter_Ici_iff` / 引理 `nonempty_iInter_Ici_iff`

English:
lemma nonempty_iInter_Ici_iff
  given: [Preorder α] {f : ι -> α}
  proof: nonempty_iInter_Iic_iff (α := αᵒᵈ)

中文:
引理 nonempty_i整数er_Ici_iff
  条件: [预序 α] {f : ι -> α}
  证明: nonempty_iInter_Iic_iff (α := αᵒᵈ)

Depends on / 依赖: nonempty_iInter_Iic_iff
-/
lemma nonempty_iInter_Ici_iff [Preorder α] {f : ι -> α} :
    (⋂ i, Ici (f i)).Nonempty ↔ BddAbove (range f) :=
  nonempty_iInter_Iic_iff (α := αᵒᵈ)

variable [CompleteLattice α]

/--
theorem `Ici_iSup` / 定理 `Ici_iSup`

English:
theorem Ici_iSup
  given: (f : ι -> α)
  statement: Ici (⨆ i, f i) = ⋂ i, Ici (f i)
  proof: ext fun _ => by simp only [mem_Ici, iSup_le_iff, mem_iInter]

中文:
定理 Ici_iSup
  条件: (f : ι -> α)
  结论: 左闭右无界区间 (⨆ i, f i) = ⋂ i, 左闭右无界区间 (f i)
  证明: ext fun _ => by simp only [mem_Ici, iSup_le_iff, mem_iInter]

Depends on / 依赖: iSup_le_iff, mem_Ici, mem_iInter
-/
theorem Ici_iSup (f : ι -> α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, iSup_le_iff, mem_iInter]

/--
theorem `Iic_iInf` / 定理 `Iic_iInf`

English:
theorem Iic_iInf
  given: (f : ι -> α)
  statement: Iic (⨅ i, f i) = ⋂ i, Iic (f i)
  proof: ext fun _ => by simp only [mem_Iic, le_iInf_iff, mem_iInter]

中文:
定理 Iic_iInf
  条件: (f : ι -> α)
  结论: 左无界右闭区间 (⨅ i, f i) = ⋂ i, 左无界右闭区间 (f i)
  证明: ext fun _ => by simp only [mem_Iic, le_iInf_iff, mem_iInter]

Depends on / 依赖: le_iInf_iff, mem_Iic, mem_iInter
-/
theorem Iic_iInf (f : ι -> α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_iInf_iff, mem_iInter]

/--
theorem `Ici_iSup₂` / 定理 `Ici_iSup₂`

English:
theorem Ici_iSup₂
  given: (f : forall i, κ i -> α)
  statement: Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j)
  proof: by
  simp_rw [Ici_iSup]

中文:
定理 Ici_iSup₂
  条件: (f : 对任意 i, κ i -> α)
  结论: 左闭右无界区间 (⨆ (i) (j), f i j) = ⋂ (i) (j), 左闭右无界区间 (f i j)
  证明: by
  simp_rw [Ici_iSup]

Depends on / 依赖: Ici_iSup, simp_rw
-/
theorem Ici_iSup₂ (f : forall i, κ i -> α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_iSup]

/--
theorem `Iic_iInf₂` / 定理 `Iic_iInf₂`

English:
theorem Iic_iInf₂
  given: (f : forall i, κ i -> α)
  statement: Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j)
  proof: by
  simp_rw [Iic_iInf]

中文:
定理 Iic_iInf₂
  条件: (f : 对任意 i, κ i -> α)
  结论: 左无界右闭区间 (⨅ (i) (j), f i j) = ⋂ (i) (j), 左无界右闭区间 (f i j)
  证明: by
  simp_rw [Iic_iInf]

Depends on / 依赖: Iic_iInf, simp_rw
-/
theorem Iic_iInf₂ (f : forall i, κ i -> α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_iInf]

/--
theorem `Ici_sSup` / 定理 `Ici_sSup`

English:
theorem Ici_sSup
  given: (s : Set α)
  statement: Ici (sSup s) = ⋂ a in s, Ici a
  proof: by rw [sSup_eq_iSup, Ici_iSup₂]

中文:
定理 Ici_sSup
  条件: (s : 集合 α)
  结论: 左闭右无界区间 (sSup s) = ⋂ a in s, 左闭右无界区间 a
  证明: by rw [sSup_eq_iSup, Ici_iSup₂]

Depends on / 依赖: sSup_eq_iSup
-/
theorem Ici_sSup (s : Set α) : Ici (sSup s) = ⋂ a in s, Ici a := by rw [sSup_eq_iSup, Ici_iSup₂]

/--
theorem `Iic_sInf` / 定理 `Iic_sInf`

English:
theorem Iic_sInf
  given: (s : Set α)
  statement: Iic (sInf s) = ⋂ a in s, Iic a
  proof: by rw [sInf_eq_iInf, Iic_iInf₂]

中文:
定理 Iic_sInf
  条件: (s : 集合 α)
  结论: 左无界右闭区间 (sInf s) = ⋂ a in s, 左无界右闭区间 a
  证明: by rw [sInf_eq_iInf, Iic_iInf₂]

Depends on / 依赖: sInf_eq_iInf
-/
theorem Iic_sInf (s : Set α) : Iic (sInf s) = ⋂ a in s, Iic a := by rw [sInf_eq_iInf, Iic_iInf₂]

end Set

namespace Set

variable (t : α -> Set β)

/--
theorem `biUnion_sdiff_biUnion_subset` / 定理 `biUnion_sdiff_biUnion_subset`

English:
theorem biUnion_sdiff_biUnion_subset
  given: (s₁ s₂ : Set α)
  proof: by
  simp only [sdiff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_sdiff_self]
  apply subset_union_right

@[deprecated (since := "2026-06-03")]
alias biUnion_diff_biUnion_subset := biUnion_sdiff_biUnion_subset

中文:
定理 biUnion_sdiff_biUnion_subset
  条件: (s₁ s₂ : 集合 α)
  证明: by
  simp only [sdiff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_sdiff_self]
  apply subset_union_right

@[deprecated (since := "2026-06-03")]
alias biUnion_diff_biUnion_subset := biUnion_sdiff_biUnion_subset

Depends on / 依赖: biUnion_subset_biUnion_left, biUnion_union, sdiff_subset_iff, subset_union_right, union_sdiff_self
-/
theorem biUnion_sdiff_biUnion_subset (s₁ s₂ : Set α) :
    ((⋃ x in s₁, t x) \ ⋃ x in s₂, t x) subseteq ⋃ x in s₁ \ s₂, t x := by
  simp only [sdiff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_sdiff_self]
  apply subset_union_right

@[deprecated (since := "2026-06-03")]
alias biUnion_diff_biUnion_subset := biUnion_sdiff_biUnion_subset

/--
Definition of `sigmaToiUnion` / `sigmaToiUnion` 的定义

English:
definition sigmaToiUnion
  signature: (x : Σ i, t i)
  body: ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩

中文:
定义 sigmaToiUnion
  签名: (x : Σ i, t i)
  定义体: ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩

Depends on / 依赖: mem_iUnion
-/
def sigmaToiUnion (x : Σ i, t i) : ⋃ i, t i :=
  ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩

/--
theorem `sigmaToiUnion_surjective` / 定理 `sigmaToiUnion_surjective`

English:
theorem sigmaToiUnion_surjective
  statement: Surjective (sigmaToiUnion t)
  proof: by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩

中文:
定理 sigmaToiUnion_surjective
  结论: 满射 (sigmaToiUnion t)
  证明: by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩
-/
theorem sigmaToiUnion_surjective : Surjective (sigmaToiUnion t)
  | ⟨b, hb⟩ =>
    have : exists a, b in t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩

/--
theorem `sigmaToiUnion_injective` / 定理 `sigmaToiUnion_injective`

English:
theorem sigmaToiUnion_injective
  given: (h : Pairwise (Disjoint on t))
  proof: congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ in t a₁ inter t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
Sigma.eq a_eq Subtype.ext by subst b_eq; subst a_eq; rfl

中文:
定理 sigmaToiUnion_injective
  条件: (h : 两两 (Disjoint on t))
  证明: congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ in t a₁ inter t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
Sigma.eq a_eq Subtype.ext by subst b_eq; subst a_eq; rfl

Depends on / 依赖: Subtype, Subtype.val, congr_arg
-/
theorem sigmaToiUnion_injective (h : Pairwise (Disjoint on t)) :
    Injective (sigmaToiUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ in t a₁ inter t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
Sigma.eq a_eq Subtype.ext by subst b_eq; subst a_eq; rfl

/--
theorem `sigmaToiUnion_bijective` / 定理 `sigmaToiUnion_bijective`

English:
theorem sigmaToiUnion_bijective
  given: (h : Pairwise (Disjoint on t))
  proof: ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩

中文:
定理 sigmaToiUnion_bijective
  条件: (h : 两两 (Disjoint on t))
  证明: ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩

Depends on / 依赖: sigmaToiUnion_injective, sigmaToiUnion_surjective
-/
theorem sigmaToiUnion_bijective (h : Pairwise (Disjoint on t)) :
    Bijective (sigmaToiUnion t) :=
  ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩

/--
Definition of `sigmaEquiv` / `sigmaEquiv` 的定义

English:
definition sigmaEquiv
  signature: (s : α -> Set β) (hs : forall b, exists! i, b in s i)
  body: ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl

中文:
定义 sigmaEquiv
  签名: (s : α -> 集合 β) (hs : 对任意 b, 存在! i, b in s i)
  定义体: ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl

Depends on / 依赖: choose_spec
-/
noncomputable def sigmaEquiv (s : α -> Set β) (hs : forall b, exists! i, b in s i) :
    (Σ i, s i) ≃ β where
  toFun | ⟨_, b⟩ => b
  invFun b := ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl

/--
Definition of `unionEqSigmaOfDisjoint` / `unionEqSigmaOfDisjoint` 的定义

English:
definition unionEqSigmaOfDisjoint
  signature: {t : α -> Set β}
  body: (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm

@[simp]

中文:
定义 unionEqSigmaOfDisjoint
  签名: {t : α -> 集合 β}
  定义体: (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm

@[simp]

Depends on / 依赖: Equiv.ofBijective, ofBijective, sigmaToiUnion_bijective
-/
noncomputable def unionEqSigmaOfDisjoint {t : α -> Set β}
    (h : Pairwise (Disjoint on t)) :
    (⋃ i, t i) ≃ Σ i, t i :=
  (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm

@[simp]
/--
lemma `coe_unionEqSigmaOfDisjoint_symm_apply` / 引理 `coe_unionEqSigmaOfDisjoint_symm_apply`

English:
lemma coe_unionEqSigmaOfDisjoint_symm_apply
  statement: {α β : Type*} {t : α -> Set β}
  proof: by
  rfl

@[simp]

中文:
引理 coe_unionEqSigmaOfDisjoint_symm_apply
  结论: {α β : 类型} {t : α -> 集合 β}
  证明: by
  rfl

@[simp]
-/
lemma coe_unionEqSigmaOfDisjoint_symm_apply {α β : Type*} {t : α -> Set β}
    (h : Pairwise (Disjoint on t)) (x : (i : α) × t i) :
    ((Set.unionEqSigmaOfDisjoint h).symm x : β) = x.2 := by
  rfl

@[simp]
/--
lemma `coe_snd_unionEqSigmaOfDisjoint` / 引理 `coe_snd_unionEqSigmaOfDisjoint`

English:
lemma coe_snd_unionEqSigmaOfDisjoint
  statement: {α β : Type*} {t : α -> Set β}
  proof: by
  conv => right; rw [← unionEqSigmaOfDisjoint h |>.symm_apply_apply x]
  rfl

中文:
引理 coe_snd_unionEqSigmaOfDisjoint
  结论: {α β : 类型} {t : α -> 集合 β}
  证明: by
  conv => right; rw [← unionEqSigmaOfDisjoint h |>.symm_apply_apply x]
  rfl

Depends on / 依赖: symm_apply_apply, unionEqSigmaOfDisjoint
-/
lemma coe_snd_unionEqSigmaOfDisjoint {α β : Type*} {t : α -> Set β}
    (h : Pairwise (Disjoint on t)) (x : ⋃ (i : α), t i) :
    ((Set.unionEqSigmaOfDisjoint h x).snd : β) = x := by
  conv => right; rw [← unionEqSigmaOfDisjoint h |>.symm_apply_apply x]
  rfl

/--
theorem `iUnion_ge_eq_iUnion_nat_add` / 定理 `iUnion_ge_eq_iUnion_nat_add`

English:
theorem iUnion_ge_eq_iUnion_nat_add
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋃ i >= n, u i = ⋃ i, u (i + n)
  proof: iSup_ge_eq_iSup_nat_add u n

中文:
定理 iUnion_ge_eq_iUnion_nat_add
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋃ i >= n, u i = ⋃ i, u (i + n)
  证明: iSup_ge_eq_iSup_nat_add u n

Depends on / 依赖: iSup_ge_eq_iSup_nat_add
-/
theorem iUnion_ge_eq_iUnion_nat_add (u : Nat -> Set α) (n : Nat) : ⋃ i >= n, u i = ⋃ i, u (i + n) :=
  iSup_ge_eq_iSup_nat_add u n

/--
theorem `iInter_ge_eq_iInter_nat_add` / 定理 `iInter_ge_eq_iInter_nat_add`

English:
theorem iInter_ge_eq_iInter_nat_add
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋂ i >= n, u i = ⋂ i, u (i + n)
  proof: iInf_ge_eq_iInf_nat_add u n

中文:
定理 i整数er_ge_eq_i整数er_nat_add
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋂ i >= n, u i = ⋂ i, u (i + n)
  证明: iInf_ge_eq_iInf_nat_add u n

Depends on / 依赖: iInf_ge_eq_iInf_nat_add
-/
theorem iInter_ge_eq_iInter_nat_add (u : Nat -> Set α) (n : Nat) : ⋂ i >= n, u i = ⋂ i, u (i + n) :=
  iInf_ge_eq_iInf_nat_add u n

/--
theorem `_root_.Monotone.iUnion_nat_add` / 定理 `_root_.Monotone.iUnion_nat_add`

English:
theorem _root_.Monotone.iUnion_nat_add
  given: {f : Nat -> Set α} (hf : Monotone f) (k : Nat)
  proof: hf.iSup_nat_add k

中文:
定理 _root_.递增.iUnion_nat_add
  条件: {f : 自然数 -> 集合 α} (hf : 递增 f) (k : 自然数)
  证明: hf.iSup_nat_add k

Depends on / 依赖: hf.iSup_nat_add, iSup_nat_add
-/
theorem _root_.Monotone.iUnion_nat_add {f : Nat -> Set α} (hf : Monotone f) (k : Nat) :
    ⋃ n, f (n + k) = ⋃ n, f n :=
  hf.iSup_nat_add k

/--
theorem `_root_.Antitone.iInter_nat_add` / 定理 `_root_.Antitone.iInter_nat_add`

English:
theorem _root_.Antitone.iInter_nat_add
  given: {f : Nat -> Set α} (hf : Antitone f) (k : Nat)
  proof: hf.iInf_nat_add k

@[simp]

中文:
定理 _root_.递减.i整数er_nat_add
  条件: {f : 自然数 -> 集合 α} (hf : 递减 f) (k : 自然数)
  证明: hf.iInf_nat_add k

@[simp]

Depends on / 依赖: hf.iInf_nat_add, iInf_nat_add
-/
theorem _root_.Antitone.iInter_nat_add {f : Nat -> Set α} (hf : Antitone f) (k : Nat) :
    ⋂ n, f (n + k) = ⋂ n, f n :=
  hf.iInf_nat_add k

@[simp]
/--
theorem `iUnion_iInter_ge_nat_add` / 定理 `iUnion_iInter_ge_nat_add`

English:
theorem iUnion_iInter_ge_nat_add
  given: (f : Nat -> Set α) (k : Nat)
  proof: iSup_iInf_ge_nat_add f k

中文:
定理 iUnion_i整数er_ge_nat_add
  条件: (f : 自然数 -> 集合 α) (k : 自然数)
  证明: iSup_iInf_ge_nat_add f k

Depends on / 依赖: iSup_iInf_ge_nat_add
-/
theorem iUnion_iInter_ge_nat_add (f : Nat -> Set α) (k : Nat) :
    ⋃ n, ⋂ i >= n, f (i + k) = ⋃ n, ⋂ i >= n, f i :=
  iSup_iInf_ge_nat_add f k

/--
theorem `union_iUnion_nat_succ` / 定理 `union_iUnion_nat_succ`

English:
theorem union_iUnion_nat_succ
  given: (u : Nat -> Set α)
  statement: (u 0 union ⋃ i, u (i + 1)) = ⋃ i, u i
  proof: sup_iSup_nat_succ u

中文:
定理 union_iUnion_nat_succ
  条件: (u : 自然数 -> 集合 α)
  结论: (u 0 union ⋃ i, u (i + 1)) = ⋃ i, u i
  证明: sup_iSup_nat_succ u

Depends on / 依赖: sup_iSup_nat_succ
-/
theorem union_iUnion_nat_succ (u : Nat -> Set α) : (u 0 union ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_iSup_nat_succ u

/--
theorem `inter_iInter_nat_succ` / 定理 `inter_iInter_nat_succ`

English:
theorem inter_iInter_nat_succ
  given: (u : Nat -> Set α)
  statement: (u 0 inter ⋂ i, u (i + 1)) = ⋂ i, u i
  proof: inf_iInf_nat_succ u

中文:
定理 inter_i整数er_nat_succ
  条件: (u : 自然数 -> 集合 α)
  结论: (u 0 inter ⋂ i, u (i + 1)) = ⋂ i, u i
  证明: inf_iInf_nat_succ u

Depends on / 依赖: inf_iInf_nat_succ
-/
theorem inter_iInter_nat_succ (u : Nat -> Set α) : (u 0 inter ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_iInf_nat_succ u

/--
theorem `iUnion_le_nat` / 定理 `iUnion_le_nat`

English:
theorem iUnion_le_nat
  statement: ⋃ n : Nat, {i | i <= n} = Set.univ
  proof: subset_antisymm (Set.subset_univ _)
    (fun i _ => Set.mem_iUnion_of_mem i (Set.mem_ofPred.mpr (le_refl _)))

中文:
定理 iUnion_le_nat
  结论: ⋃ n : 自然数, {i | i <= n} = 集合.univ
  证明: subset_antisymm (Set.subset_univ _)
    (fun i _ => Set.mem_iUnion_of_mem i (Set.mem_ofPred.mpr (le_refl _)))

Depends on / 依赖: Set.mem_iUnion_of_mem, Set.mem_ofPred.mpr, Set.subset_univ, le_refl, mem_iUnion_of_mem, mem_ofPred, subset_antisymm, subset_univ
-/
theorem iUnion_le_nat : ⋃ n : Nat, {i | i <= n} = Set.univ :=
  subset_antisymm (Set.subset_univ _)
    (fun i _ => Set.mem_iUnion_of_mem i (Set.mem_ofPred.mpr (le_refl _)))

end Set

open Set

variable [CompleteLattice β]

/--
theorem `iSup_iUnion` / 定理 `iSup_iUnion`

English:
theorem iSup_iUnion
  given: (s : ι -> Set α) (f : α -> β)
  statement: ⨆ a in ⋃ i, s i, f a = ⨆ (i) (a in s i), f a
  proof: by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]

中文:
定理 iSup_iUnion
  条件: (s : ι -> 集合 α) (f : α -> β)
  结论: ⨆ a in ⋃ i, s i, f a = ⨆ (i) (a in s i), f a
  证明: by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]

Depends on / 依赖: iSup_comm, iSup_exists, mem_iUnion, simp_rw
-/
theorem iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i, f a = ⨆ (i) (a in s i), f a := by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]

/--
theorem `iInf_iUnion` / 定理 `iInf_iUnion`

English:
theorem iInf_iUnion
  given: (s : ι -> Set α) (f : α -> β)
  statement: ⨅ a in ⋃ i, s i, f a = ⨅ (i) (a in s i), f a
  proof: iSup_iUnion (β := βᵒᵈ) s f

中文:
定理 iInf_iUnion
  条件: (s : ι -> 集合 α) (f : α -> β)
  结论: ⨅ a in ⋃ i, s i, f a = ⨅ (i) (a in s i), f a
  证明: iSup_iUnion (β := βᵒᵈ) s f

Depends on / 依赖: X.isLocalRing, iSup_iUnion, isLocalRing
-/
theorem iInf_iUnion (s : ι -> Set α) (f : α -> β) : ⨅ a in ⋃ i, s i, f a = ⨅ (i) (a in s i), f a :=
  iSup_iUnion (β := βᵒᵈ) s f

/--
theorem `sSup_iUnion` / 定理 `sSup_iUnion`

English:
theorem sSup_iUnion
  given: (t : ι -> Set β)
  statement: sSup (⋃ i, t i) = ⨆ i, sSup (t i)
  proof: by
  simp_rw [sSup_eq_iSup, iSup_iUnion]

中文:
定理 sSup_iUnion
  条件: (t : ι -> 集合 β)
  结论: sSup (⋃ i, t i) = ⨆ i, sSup (t i)
  证明: by
  simp_rw [sSup_eq_iSup, iSup_iUnion]

Depends on / 依赖: iSup_iUnion, sSup_eq_iSup, simp_rw
-/
theorem sSup_iUnion (t : ι -> Set β) : sSup (⋃ i, t i) = ⨆ i, sSup (t i) := by
  simp_rw [sSup_eq_iSup, iSup_iUnion]

/--
theorem `sSup_sUnion` / 定理 `sSup_sUnion`

English:
theorem sSup_sUnion
  given: (s : Set (Set β))
  statement: sSup (⋃₀ s) = ⨆ t in s, sSup t
  proof: by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]

中文:
定理 sSup_sUnion
  条件: (s : 集合 (集合 β))
  结论: sSup (⋃₀ s) = ⨆ t in s, sSup t
  证明: by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]

Depends on / 依赖: iSup_iUnion, sSup_eq_iSup, sUnion_eq_biUnion
-/
theorem sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t in s, sSup t := by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]

/--
theorem `sInf_sUnion` / 定理 `sInf_sUnion`

English:
theorem sInf_sUnion
  given: (s : Set (Set β))
  statement: sInf (⋃₀ s) = ⨅ t in s, sInf t
  proof: sSup_sUnion (β := βᵒᵈ) s

中文:
定理 sInf_sUnion
  条件: (s : 集合 (集合 β))
  结论: sInf (⋃₀ s) = ⨅ t in s, sInf t
  证明: sSup_sUnion (β := βᵒᵈ) s

Depends on / 依赖: sSup_sUnion
-/
theorem sInf_sUnion (s : Set (Set β)) : sInf (⋃₀ s) = ⨅ t in s, sInf t :=
  sSup_sUnion (β := βᵒᵈ) s

/--
lemma `iSup_sUnion` / 引理 `iSup_sUnion`

English:
lemma iSup_sUnion
  given: (S : Set (Set α)) (f : α -> β)
  proof: by
  rw [sUnion_eq_iUnion]; rw [iSup_iUnion]; rw [← iSup_subtype'']

中文:
引理 iSup_sUnion
  条件: (S : 集合 (集合 α)) (f : α -> β)
  证明: by
  rw [sUnion_eq_iUnion]; rw [iSup_iUnion]; rw [← iSup_subtype'']

Depends on / 依赖: iSup_iUnion, iSup_subtype, sUnion_eq_iUnion
-/
lemma iSup_sUnion (S : Set (Set α)) (f : α -> β) :
    (⨆ x in ⋃₀ S, f x) = ⨆ (s in S) (x in s), f x := by
  rw [sUnion_eq_iUnion]; rw [iSup_iUnion]; rw [← iSup_subtype'']

/--
lemma `iInf_sUnion` / 引理 `iInf_sUnion`

English:
lemma iInf_sUnion
  given: (S : Set (Set α)) (f : α -> β)
  proof: by
  rw [sUnion_eq_iUnion]; rw [iInf_iUnion]; rw [← iInf_subtype'']

中文:
引理 iInf_sUnion
  条件: (S : 集合 (集合 α)) (f : α -> β)
  证明: by
  rw [sUnion_eq_iUnion]; rw [iInf_iUnion]; rw [← iInf_subtype'']

Depends on / 依赖: iInf_iUnion, iInf_subtype, sUnion_eq_iUnion
-/
lemma iInf_sUnion (S : Set (Set α)) (f : α -> β) :
    (⨅ x in ⋃₀ S, f x) = ⨅ (s in S) (x in s), f x := by
  rw [sUnion_eq_iUnion]; rw [iInf_iUnion]; rw [← iInf_subtype'']

/--
lemma `forall_sUnion` / 引理 `forall_sUnion`

English:
lemma forall_sUnion
  given: {S : Set (Set α)} {p : α -> Prop}
  proof: by
  simp_rw [← iInf_Prop_eq, iInf_sUnion]

中文:
引理 对任意_sUnion
  条件: {S : 集合 (集合 α)} {p : α -> 命题}
  证明: by
  simp_rw [← iInf_Prop_eq, iInf_sUnion]

Depends on / 依赖: iInf_Prop_eq, iInf_sUnion, simp_rw
-/
lemma forall_sUnion {S : Set (Set α)} {p : α -> Prop} :
    (forall x in ⋃₀ S, p x) ↔ forall s in S, forall x in s, p x := by
  simp_rw [← iInf_Prop_eq, iInf_sUnion]

/--
lemma `exists_sUnion` / 引理 `exists_sUnion`

English:
lemma exists_sUnion
  given: {S : Set (Set α)} {p : α -> Prop}
  proof: by
  simp_rw [← exists_prop, ← iSup_Prop_eq, iSup_sUnion]

中文:
引理 存在_sUnion
  条件: {S : 集合 (集合 α)} {p : α -> 命题}
  证明: by
  simp_rw [← exists_prop, ← iSup_Prop_eq, iSup_sUnion]

Depends on / 依赖: exists_prop, iSup_Prop_eq, iSup_sUnion, simp_rw
-/
lemma exists_sUnion {S : Set (Set α)} {p : α -> Prop} :
    (exists x in ⋃₀ S, p x) ↔ exists s in S, exists x in s, p x := by
  simp_rw [← exists_prop, ← iSup_Prop_eq, iSup_sUnion]
