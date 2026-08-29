/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `iSup`/`iInf`/`Set.iUnion`/`Set.iInter` and natural numbers.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Set

namespace Nat

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet Nat
  body: ⟨fun s => if h : exists n, n in s then @Nat.find (fun n => n in s) _ h else 0⟩

中文:
实例 :
  签名: 下确界集 自然数
  定义体: ⟨fun s => if h : exists n, n in s then @Nat.find (fun n => n in s) _ h else 0⟩

Depends on / 依赖: IsTwoSided, Nat.find
-/
noncomputable instance : InfSet Nat :=
  ⟨fun s => if h : exists n, n in s then @Nat.find (fun n => n in s) _ h else 0⟩

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet Nat
  body: ⟨fun s => if h : exists n, forall a in s, a <= n then @Nat.find (fun n => forall a in s, a <= n) _ h else 0⟩

中文:
实例 :
  签名: 上确界集 自然数
  定义体: ⟨fun s => if h : exists n, forall a in s, a <= n then @Nat.find (fun n => forall a in s, a <= n) _ h else 0⟩

Depends on / 依赖: Nat.find
-/
noncomputable instance : SupSet Nat :=
  ⟨fun s => if h : exists n, forall a in s, a <= n then @Nat.find (fun n => forall a in s, a <= n) _ h else 0⟩

open scoped Classical in
/--
theorem `sInf_def` / 定理 `sInf_def`

English:
theorem sInf_def
  given: {s : Set Nat} (h : s.Nonempty)
  statement: sInf s = @Nat.find (fun n => n in s) _ h
  proof: dif_pos _

中文:
定理 sInf_def
  条件: {s : 集合 自然数} (h : s.非空)
  结论: sInf s = @自然数.find (fun n => n in s) _ h
  证明: dif_pos _

Depends on / 依赖: dif_pos
-/
theorem sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.find (fun n => n in s) _ h :=
  dif_pos _

open scoped Classical in
/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: {s : Set Nat} (h : exists n, forall a in s, a <= n)
  proof: dif_pos _

中文:
定理 sSup_def
  条件: {s : 集合 自然数} (h : 存在 n, 对任意 a in s, a <= n)
  证明: dif_pos _

Depends on / 依赖: I.restrictScalars, dif_pos, instIsTorsionFree, restrictScalars
-/
theorem sSup_def {s : Set Nat} (h : exists n, forall a in s, a <= n) :
    sSup s = @Nat.find (fun n => forall a in s, a <= n) _ h :=
  dif_pos _

/--
theorem `_root_.Set.Infinite.Nat.sSup_eq_zero` / 定理 `_root_.Set.Infinite.Nat.sSup_eq_zero`

English:
theorem _root_.Set.Infinite.Nat.sSup_eq_zero
  given: {s : Set Nat} (h : s.Infinite)
  statement: sSup s = 0
  proof: dif_neg fun ⟨n, hn⟩ =>
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_gt hk

中文:
定理 _root_.集合.无限.自然数.sSup_eq_zero
  条件: {s : 集合 自然数} (h : s.无限)
  结论: sSup s = 0
  证明: dif_neg fun ⟨n, hn⟩ =>
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_gt hk

Depends on / 依赖: dif_neg, exists_gt, h.exists_gt, not_gt
-/
theorem _root_.Set.Infinite.Nat.sSup_eq_zero {s : Set Nat} (h : s.Infinite) : sSup s = 0 :=
  dif_neg fun ⟨n, hn⟩ =>
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_gt hk

/--
theorem `sSup_of_not_bddAbove` / 定理 `sSup_of_not_bddAbove`

English:
theorem sSup_of_not_bddAbove
  given: {s : Set Nat} (h : ¬BddAbove s)
  statement: sSup s = 0
  proof: Set.Infinite.Nat.sSup_eq_zero Set.infinite_of_not_bddAbove h

中文:
定理 sSup_of_not_bddAbove
  条件: {s : 集合 自然数} (h : ¬BddAbove s)
  结论: sSup s = 0
  证明: Set.Infinite.Nat.sSup_eq_zero Set.infinite_of_not_bddAbove h

Depends on / 依赖: Infinite, Set.Infinite.Nat.sSup_eq_zero, Set.infinite_of_not_bddAbove, infinite_of_not_bddAbove, sSup_eq_zero
-/
theorem sSup_of_not_bddAbove {s : Set Nat} (h : ¬BddAbove s) : sSup s = 0 :=
Set.Infinite.Nat.sSup_eq_zero Set.infinite_of_not_bddAbove h

/--
lemma `iSup_of_not_bddAbove` / 引理 `iSup_of_not_bddAbove`

English:
lemma iSup_of_not_bddAbove
  given: {ι : Sort*} {f : ι -> Nat} (h : ¬ BddAbove (Set.range f))
  proof: Nat.sSup_of_not_bddAbove h

中文:
引理 iSup_of_not_bddAbove
  条件: {ι : 类型层*} {f : ι -> 自然数} (h : ¬ BddAbove (集合.range f))
  证明: Nat.sSup_of_not_bddAbove h

Depends on / 依赖: Nat.sSup_of_not_bddAbove, sSup_of_not_bddAbove
-/
lemma iSup_of_not_bddAbove {ι : Sort*} {f : ι -> Nat} (h : ¬ BddAbove (Set.range f)) :
    (⨆ i, f i : Nat) = 0 := Nat.sSup_of_not_bddAbove h

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `sInf_eq_zero` / 定理 `sInf_eq_zero`

English:
theorem sInf_eq_zero
  given: {s : Set Nat}
  statement: sInf s = 0 ↔ 0 in s ∨ s = ∅
  proof: by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true, InfSet.sInf,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false, Nat.sInf_def, h, Nat.find_eq_zero]

@[simp]

中文:
定理 sInf_eq_zero
  条件: {s : 集合 自然数}
  结论: sInf s = 0 ↔ 0 in s ∨ s = ∅
  证明: by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true, InfSet.sInf,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false, Nat.sInf_def, h, Nat.find_eq_zero]

@[simp]

Depends on / 依赖: InfSet, InfSet.sInf, Nat.find_eq_zero, Nat.sInf_def, dif_neg, eq_empty_or_nonempty, exists_false, find_eq_zero, h.ne_empty, mem_empty_iff_false, ne_empty, not_false_iff, or_false, or_true, sInf_def
-/
theorem sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s with
  | inl h => subst h
             simp only [or_true, InfSet.sInf,
                        mem_empty_iff_false, exists_false, dif_neg, not_false_iff]
  | inr h => simp only [h.ne_empty, or_false, Nat.sInf_def, h, Nat.find_eq_zero]

@[simp]
/--
theorem `sInf_empty` / 定理 `sInf_empty`

English:
theorem sInf_empty
  statement: sInf ∅ = 0
  proof: by
  rw [sInf_eq_zero]
  right
  rfl

@[simp]

中文:
定理 sInf_empty
  结论: sInf ∅ = 0
  证明: by
  rw [sInf_eq_zero]
  right
  rfl

@[simp]

Depends on / 依赖: sInf_eq_zero
-/
theorem sInf_empty : sInf ∅ = 0 := by
  rw [sInf_eq_zero]
  right
  rfl

@[simp]
/--
theorem `iInf_of_empty` / 定理 `iInf_of_empty`

English:
theorem iInf_of_empty
  given: {ι : Sort*} [IsEmpty ι] (f : ι -> Nat)
  statement: iInf f = 0
  proof: by
  rw [iInf_of_isEmpty]; rw [sInf_empty]

中文:
定理 iInf_of_empty
  条件: {ι : 类型层*} [是空 ι] (f : ι -> 自然数)
  结论: iInf f = 0
  证明: by
  rw [iInf_of_isEmpty]; rw [sInf_empty]

Depends on / 依赖: iInf_of_isEmpty, sInf_empty
-/
theorem iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι -> Nat) : iInf f = 0 := by
  rw [iInf_of_isEmpty]; rw [sInf_empty]

/-- This combines `Nat.iInf_of_empty` with `ciInf_const`. -/
@[simp]
/--
lemma `iInf_const_zero` / 引理 `iInf_const_zero`

English:
lemma iInf_const_zero
  given: {ι : Sort*}
  statement: ⨅ _ : ι, 0 = 0
  proof: (isEmpty_or_nonempty ι).elim (fun h => by simp) fun h => sInf_eq_zero.2 by simp

中文:
引理 iInf_const_zero
  条件: {ι : 类型层*}
  结论: ⨅ _ : ι, 0 = 0
  证明: (isEmpty_or_nonempty ι).elim (fun h => by simp) fun h => sInf_eq_zero.2 by simp

Depends on / 依赖: isEmpty_or_nonempty, sInf_eq_zero
-/
lemma iInf_const_zero {ι : Sort*} : ⨅ _ : ι, 0 = 0 :=
(isEmpty_or_nonempty ι).elim (fun h => by simp) fun h => sInf_eq_zero.2 by simp

/--
theorem `sInf_mem` / 定理 `sInf_mem`

English:
theorem sInf_mem
  given: {s : Set Nat} (h : s.Nonempty)
  statement: sInf s in s
  proof: by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h

中文:
定理 sInf_mem
  条件: {s : 集合 自然数} (h : s.非空)
  结论: sInf s in s
  证明: by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h

Depends on / 依赖: Nat.find_spec, Nat.sInf_def, classical, find_spec, sInf_def
-/
theorem sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s := by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h

/--
theorem `notMem_of_lt_sInf` / 定理 `notMem_of_lt_sInf`

English:
theorem notMem_of_lt_sInf
  given: {s : Set Nat} {m : Nat} (hm : m < sInf s)
  statement: m ∉ s
  proof: by
  classical
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply notMem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm

中文:
定理 notMem_of_lt_sInf
  条件: {s : 集合 自然数} {m : 自然数} (hm : m < sInf s)
  结论: m ∉ s
  证明: by
  classical
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply notMem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm

Depends on / 依赖: Nat.find_min, Nat.sInf_def, classical, eq_empty_or_nonempty, find_min, notMem_empty, sInf_def
-/
theorem notMem_of_lt_sInf {s : Set Nat} {m : Nat} (hm : m < sInf s) : m ∉ s := by
  classical
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply notMem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm

/--
theorem `sInf_le` / 定理 `sInf_le`

English:
theorem sInf_le
  given: {s : Set Nat} {m : Nat} (hm : m in s)
  statement: sInf s <= m
  proof: by
  classical
  rw [Nat.sInf_def ⟨m]; rw [hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm

中文:
定理 sInf_le
  条件: {s : 集合 自然数} {m : 自然数} (hm : m in s)
  结论: sInf s <= m
  证明: by
  classical
  rw [Nat.sInf_def ⟨m]; rw [hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm
-/
protected theorem sInf_le {s : Set Nat} {m : Nat} (hm : m in s) : sInf s <= m := by
  classical
  rw [Nat.sInf_def ⟨m]; rw [hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm

/--
theorem `nonempty_of_pos_sInf` / 定理 `nonempty_of_pos_sInf`

English:
theorem nonempty_of_pos_sInf
  given: {s : Set Nat} (h : 0 < sInf s)
  statement: s.Nonempty
  proof: by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : sInf s != 0 := ne_of_gt h
  apply h'
  rw [Nat.sInf_eq_zero]
  right
  assumption

中文:
定理 nonempty_of_pos_sInf
  条件: {s : 集合 自然数} (h : 0 < sInf s)
  结论: s.非空
  证明: by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : sInf s != 0 := ne_of_gt h
  apply h'
  rw [Nat.sInf_eq_zero]
  right
  assumption

Depends on / 依赖: Nat.sInf_eq_zero, Set.not_nonempty_iff_eq_empty, contra, ne_of_gt, not_nonempty_iff_eq_empty, sInf_eq_zero
-/
theorem nonempty_of_pos_sInf {s : Set Nat} (h : 0 < sInf s) : s.Nonempty := by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : sInf s != 0 := ne_of_gt h
  apply h'
  rw [Nat.sInf_eq_zero]
  right
  assumption

/--
theorem `nonempty_of_sInf_eq_succ` / 定理 `nonempty_of_sInf_eq_succ`

English:
theorem nonempty_of_sInf_eq_succ
  given: {s : Set Nat} {k : Nat} (h : sInf s = k + 1)
  statement: s.Nonempty
  proof: nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)

中文:
定理 nonempty_of_sInf_eq_succ
  条件: {s : 集合 自然数} {k : 自然数} (h : sInf s = k + 1)
  结论: s.非空
  证明: nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)

Depends on / 依赖: h.symm, nonempty_of_pos_sInf, succ_pos
-/
theorem nonempty_of_sInf_eq_succ {s : Set Nat} {k : Nat} (h : sInf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)

/--
theorem `eq_Ici_of_nonempty_of_upward_closed` / 定理 `eq_Ici_of_nonempty_of_upward_closed`

English:
theorem eq_Ici_of_nonempty_of_upward_closed
  statement: {s : Set Nat} (hs : s.Nonempty)
  proof: ext fun n => ⟨fun H => Nat.sInf_le H, fun H => hs' (sInf s) n H (sInf_mem hs)⟩

中文:
定理 eq_Ici_of_nonempty_of_upward_closed
  结论: {s : 集合 自然数} (hs : s.非空)
  证明: ext fun n => ⟨fun H => Nat.sInf_le H, fun H => hs' (sInf s) n H (sInf_mem hs)⟩

Depends on / 依赖: Nat.sInf_le, sInf_le, sInf_mem
-/
theorem eq_Ici_of_nonempty_of_upward_closed {s : Set Nat} (hs : s.Nonempty)
    (hs' : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s) : s = Ici (sInf s) :=
  ext fun n => ⟨fun H => Nat.sInf_le H, fun H => hs' (sInf s) n H (sInf_mem hs)⟩

/--
theorem `sInf_upward_closed_eq_succ_iff` / 定理 `sInf_upward_closed_eq_succ_iff`

English:
theorem sInf_upward_closed_eq_succ_iff
  statement: {s : Set Nat} (hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s)
  proof: by
  classical
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_sInf_eq_succ _) hs]; rw [H]; rw [mem_Ici]; rw [mem_Ici]
    · exact ⟨le_rfl, k.not_succ_le_self⟩
    · exact k
    · assumption
  · rintro ⟨H, H'⟩
    rw [sInf_def (⟨_]; rw [H⟩ : s.Nonempty)]; rw [find_

中文:
定理 sInf_upward_closed_eq_succ_iff
  结论: {s : 集合 自然数} (hs : 对任意 k₁ k₂ : 自然数, k₁ <= k₂ -> k₁ in s -> k₂ in s)
  证明: by
  classical
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_sInf_eq_succ _) hs]; rw [H]; rw [mem_Ici]; rw [mem_Ici]
    · exact ⟨le_rfl, k.not_succ_le_self⟩
    · exact k
    · assumption
  · rintro ⟨H, H'⟩
    rw [sInf_def (⟨_]; rw [H⟩ : s.Nonempty)]; rw [find_

Depends on / 依赖: Nat.lt_succ_iff.mp, Nonempty, classical, eq_Ici_of_nonempty_of_upward_closed, find_eq_iff, k.not_succ_le_self, le_rfl, lt_succ_iff, mem_Ici, nonempty_of_sInf_eq_succ, not_succ_le_self, s.Nonempty, sInf_def
-/
theorem sInf_upward_closed_eq_succ_iff {s : Set Nat} (hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s)
    (k : Nat) : sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s := by
  classical
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_sInf_eq_succ _) hs]; rw [H]; rw [mem_Ici]; rw [mem_Ici]
    · exact ⟨le_rfl, k.not_succ_le_self⟩
    · exact k
    · assumption
  · rintro ⟨H, H'⟩
    rw [sInf_def (⟨_]; rw [H⟩ : s.Nonempty)]; rw [find_eq_iff]
exact ⟨H, fun n hnk hns => H' hs n k (Nat.lt_succ_iff.mp hnk) hns⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice Nat
  body: LinearOrder.toLattice

中文:
实例 :
  签名: 格 自然数
  定义体: LinearOrder.toLattice

Depends on / 依赖: LinearOrder, LinearOrder.toLattice, toLattice
-/
instance : Lattice Nat :=
  LinearOrder.toLattice

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConditionallyCompleteLinearOrderBot Nat
  body: { (inferInstance : OrderBot Nat), (LinearOrder.toLattice : Lattice Nat),
    (inferInstance : LinearOrder Nat) with
    isLUB_csSup _ hn hb := sSup_def hb ▸ Nat.isLeast_find hb
    isGLB_csInf _ hn hb := sInf_def hn ▸ (Nat.isLeast_find hn).isGLB
    csSup_empty := by
      simp only [sSup_def, Set.m

中文:
实例 :
  签名: 余nditionallyCompleteLinearOrderBot 自然数
  定义体: { (inferInstance : OrderBot Nat), (LinearOrder.toLattice : Lattice Nat),
    (inferInstance : LinearOrder Nat) with
    isLUB_csSup _ hn hb := sSup_def hb ▸ Nat.isLeast_find hb
    isGLB_csInf _ hn hb := sInf_def hn ▸ (Nat.isLeast_find hn).isGLB
    csSup_empty := by
      simp only [sSup_def, Set.m

Depends on / 依赖: IsEmpty, IsEmpty.forall_, Lattice, LinearOrder, LinearOrder.toLattice, Nat.find_min, Nat.isLeast_find, OrderBot, Set.mem_empty_iff_false, bot_unique, csSup_empty, csSup_of_not_bddAbove, exists_const, find_min, forall_, forall_const, forall_prop_of_false, isGLB_csInf, isLUB_csSup, isLeast_find
-/
noncomputable instance : ConditionallyCompleteLinearOrderBot Nat :=
  { (inferInstance : OrderBot Nat), (LinearOrder.toLattice : Lattice Nat),
    (inferInstance : LinearOrder Nat) with
    isLUB_csSup _ hn hb := sSup_def hb ▸ Nat.isLeast_find hb
    isGLB_csInf _ hn hb := sInf_def hn ▸ (Nat.isLeast_find hn).isGLB
    csSup_empty := by
      simp only [sSup_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      trivial
    csSup_of_not_bddAbove := by
      intro s hs
      simp only [sSup,
        mem_empty_iff_false, IsEmpty.forall_iff, forall_const, exists_const, dite_true]
      rw [dif_neg]
      · exact le_antisymm (zero_le _) (find_le trivial)
      · exact hs
    csInf_of_not_bddBelow := fun s hs => by simp at hs }

/--
theorem `sSup_mem` / 定理 `sSup_mem`

English:
theorem sSup_mem
  given: {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s)
  statement: sSup s in s
  proof: let ⟨k, hk⟩ := h₂
  h₁.csSup_mem ((finite_le_nat k).subset hk)

中文:
定理 sSup_mem
  条件: {s : 集合 自然数} (h₁ : s.非空) (h₂ : BddAbove s)
  结论: sSup s in s
  证明: let ⟨k, hk⟩ := h₂
  h₁.csSup_mem ((finite_le_nat k).subset hk)

Depends on / 依赖: csSup_mem, finite_le_nat, subset
-/
theorem sSup_mem {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s in s :=
  let ⟨k, hk⟩ := h₂
  h₁.csSup_mem ((finite_le_nat k).subset hk)

/--
theorem `sInf_add` / 定理 `sInf_add`

English:
theorem sInf_add
  given: {n : Nat} {p : Nat -> Prop} (hn : n <= sInf { m | p m })
  proof: by
  classical
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.sInf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (sInf { m | p m } - n + n) from (h.subset hp).elim
    rw [Nat.sub_add_cancel hn]
    exact csInf_mem (nonempty_o

中文:
定理 sInf_add
  条件: {n : 自然数} {p : 自然数 -> 命题} (hn : n <= sInf { m | p m })
  证明: by
  classical
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.sInf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (sInf { m | p m } - n + n) from (h.subset hp).elim
    rw [Nat.sub_add_cancel hn]
    exact csInf_mem (nonempty_o

Depends on / 依赖: Nat.sInf_def, Nat.sInf_empty, Nat.sub_add_cancel, classical, csInf_mem, eq_empty_or_nonempty, eq_or_lt, find_add, h.subset, hn.eq_or_lt, n.zero_le.trans_lt, nonempty_of_pos_sInf, sInf_def, sInf_empty, sub_add_cancel, subset, trans_lt, zero_add, zero_le
-/
theorem sInf_add {n : Nat} {p : Nat -> Prop} (hn : n <= sInf { m | p m }) :
    sInf { m | p (m + n) } + n = sInf { m | p m } := by
  classical
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.sInf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (sInf { m | p m } - n + n) from (h.subset hp).elim
    rw [Nat.sub_add_cancel hn]
    exact csInf_mem (nonempty_of_pos_sInf <| n.zero_le.trans_lt hnp)
  · have hp : exists n, n in { m | p m } := ⟨_, hm⟩
    rw [Nat.sInf_def ⟨m]; rw [hm⟩]; rw [Nat.sInf_def hp]
    rw [Nat.sInf_def hp] at hn
    exact find_add hn

/--
theorem `sInf_add'` / 定理 `sInf_add'`

English:
theorem sInf_add'
  given: {n : Nat} {p : Nat -> Prop} (h : 0 < sInf { m | p m })
  proof: by
  suffices h₁ : n <= sInf {m | p (m - n)} by
    convert! sInf_add h₁
    simp_rw [Nat.add_sub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_sInf h
  refine
    le_csInf ⟨m + n, ?_⟩ fun b hb =>
      le_of_not_gt fun hbn =>
        ne_of_mem_of_not_mem ?_ (notMem_of_lt_sInf h) (Nat.sub_eq_zer

中文:
定理 sInf_add'
  条件: {n : 自然数} {p : 自然数 -> 命题} (h : 0 < sInf { m | p m })
  证明: by
  suffices h₁ : n <= sInf {m | p (m - n)} by
    convert! sInf_add h₁
    simp_rw [Nat.add_sub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_sInf h
  refine
    le_csInf ⟨m + n, ?_⟩ fun b hb =>
      le_of_not_gt fun hbn =>
        ne_of_mem_of_not_mem ?_ (notMem_of_lt_sInf h) (Nat.sub_eq_zer

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.sub_eq_zero_of_le, add_sub_cancel_right, convert, hbn.le, le_csInf, le_of_not_gt, ne_of_mem_of_not_mem, nonempty_of_pos_sInf, notMem_of_lt_sInf, sInf_add, simp_rw, sub_eq_zero_of_le
-/
theorem sInf_add' {n : Nat} {p : Nat -> Prop} (h : 0 < sInf { m | p m }) :
    sInf { m | p m } + n = sInf { m | p (m - n) } := by
  suffices h₁ : n <= sInf {m | p (m - n)} by
    convert! sInf_add h₁
    simp_rw [Nat.add_sub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_sInf h
  refine
    le_csInf ⟨m + n, ?_⟩ fun b hb =>
      le_of_not_gt fun hbn =>
        ne_of_mem_of_not_mem ?_ (notMem_of_lt_sInf h) (Nat.sub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [Nat.add_sub_cancel_right]
  · exact hb

section

variable {α : Type*} [CompleteLattice α]

/--
theorem `iSup_lt_succ` / 定理 `iSup_lt_succ`

English:
theorem iSup_lt_succ
  given: (u : Nat -> α) (n : Nat)
  statement: ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n
  proof: by
  simp_rw [Nat.lt_add_one_iff, biSup_le_eq_sup]

中文:
定理 iSup_lt_succ
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n
  证明: by
  simp_rw [Nat.lt_add_one_iff, biSup_le_eq_sup]

Depends on / 依赖: Nat.lt_add_one_iff, biSup_le_eq_sup, lt_add_one_iff, simp_rw
-/
theorem iSup_lt_succ (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n := by
  simp_rw [Nat.lt_add_one_iff, biSup_le_eq_sup]

/--
theorem `iSup_lt_succ'` / 定理 `iSup_lt_succ'`

English:
theorem iSup_lt_succ'
  given: (u : Nat -> α) (n : Nat)
  statement: ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1)
  proof: by
  rw [← sup_iSup_nat_succ]
  simp

中文:
定理 iSup_lt_succ'
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1)
  证明: by
  rw [← sup_iSup_nat_succ]
  simp

Depends on / 依赖: sup_iSup_nat_succ
-/
theorem iSup_lt_succ' (u : Nat -> α) (n : Nat) : ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_iSup_nat_succ]
  simp

/--
theorem `iInf_lt_succ` / 定理 `iInf_lt_succ`

English:
theorem iInf_lt_succ
  given: (u : Nat -> α) (n : Nat)
  statement: ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n
  proof: @iSup_lt_succ αᵒᵈ _ _ _

中文:
定理 iInf_lt_succ
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n
  证明: @iSup_lt_succ αᵒᵈ _ _ _

Depends on / 依赖: iSup_lt_succ
-/
theorem iInf_lt_succ (u : Nat -> α) (n : Nat) : ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n :=
  @iSup_lt_succ αᵒᵈ _ _ _

/--
theorem `iInf_lt_succ'` / 定理 `iInf_lt_succ'`

English:
theorem iInf_lt_succ'
  given: (u : Nat -> α) (n : Nat)
  statement: ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1)
  proof: @iSup_lt_succ' αᵒᵈ _ _ _

中文:
定理 iInf_lt_succ'
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1)
  证明: @iSup_lt_succ' αᵒᵈ _ _ _

Depends on / 依赖: iSup_lt_succ
-/
theorem iInf_lt_succ' (u : Nat -> α) (n : Nat) : ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @iSup_lt_succ' αᵒᵈ _ _ _

/--
theorem `iSup_le_succ` / 定理 `iSup_le_succ`

English:
theorem iSup_le_succ
  given: (u : Nat -> α) (n : Nat)
  statement: ⨆ k <= n + 1, u k = (⨆ k <= n, u k) ⊔ u (n + 1)
  proof: by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ]

中文:
定理 iSup_le_succ
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨆ k <= n + 1, u k = (⨆ k <= n, u k) ⊔ u (n + 1)
  证明: by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ]

Depends on / 依赖: Nat.lt_succ_iff, iSup_lt_succ, lt_succ_iff, simp_rw
-/
theorem iSup_le_succ (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1, u k = (⨆ k <= n, u k) ⊔ u (n + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ]

/--
theorem `iSup_le_succ'` / 定理 `iSup_le_succ'`

English:
theorem iSup_le_succ'
  given: (u : Nat -> α) (n : Nat)
  statement: ⨆ k <= n + 1, u k = u 0 ⊔ ⨆ k <= n, u (k + 1)
  proof: by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ']

中文:
定理 iSup_le_succ'
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨆ k <= n + 1, u k = u 0 ⊔ ⨆ k <= n, u (k + 1)
  证明: by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ']

Depends on / 依赖: Nat.lt_succ_iff, iSup_lt_succ, lt_succ_iff, simp_rw
-/
theorem iSup_le_succ' (u : Nat -> α) (n : Nat) : ⨆ k <= n + 1, u k = u 0 ⊔ ⨆ k <= n, u (k + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ']

/--
theorem `iInf_le_succ` / 定理 `iInf_le_succ`

English:
theorem iInf_le_succ
  given: (u : Nat -> α) (n : Nat)
  statement: ⨅ k <= n + 1, u k = (⨅ k <= n, u k) ⊓ u (n + 1)
  proof: @iSup_le_succ αᵒᵈ _ _ _

中文:
定理 iInf_le_succ
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨅ k <= n + 1, u k = (⨅ k <= n, u k) ⊓ u (n + 1)
  证明: @iSup_le_succ αᵒᵈ _ _ _

Depends on / 依赖: iSup_le_succ
-/
theorem iInf_le_succ (u : Nat -> α) (n : Nat) : ⨅ k <= n + 1, u k = (⨅ k <= n, u k) ⊓ u (n + 1) :=
  @iSup_le_succ αᵒᵈ _ _ _

/--
theorem `iInf_le_succ'` / 定理 `iInf_le_succ'`

English:
theorem iInf_le_succ'
  given: (u : Nat -> α) (n : Nat)
  statement: ⨅ k <= n + 1, u k = u 0 ⊓ ⨅ k <= n, u (k + 1)
  proof: @iSup_le_succ' αᵒᵈ _ _ _

中文:
定理 iInf_le_succ'
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨅ k <= n + 1, u k = u 0 ⊓ ⨅ k <= n, u (k + 1)
  证明: @iSup_le_succ' αᵒᵈ _ _ _

Depends on / 依赖: iSup_le_succ
-/
theorem iInf_le_succ' (u : Nat -> α) (n : Nat) : ⨅ k <= n + 1, u k = u 0 ⊓ ⨅ k <= n, u (k + 1) :=
  @iSup_le_succ' αᵒᵈ _ _ _

end

end Nat

namespace Set

variable {α : Type*}

/--
theorem `biUnion_lt_succ` / 定理 `biUnion_lt_succ`

English:
theorem biUnion_lt_succ
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋃ k < n + 1, u k = (⋃ k < n, u k) union u n
  proof: Nat.iSup_lt_succ u n

中文:
定理 biUnion_lt_succ
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋃ k < n + 1, u k = (⋃ k < n, u k) union u n
  证明: Nat.iSup_lt_succ u n

Depends on / 依赖: Nat.iSup_lt_succ, iSup_lt_succ
-/
theorem biUnion_lt_succ (u : Nat -> Set α) (n : Nat) : ⋃ k < n + 1, u k = (⋃ k < n, u k) union u n :=
  Nat.iSup_lt_succ u n

/--
theorem `biUnion_lt_succ'` / 定理 `biUnion_lt_succ'`

English:
theorem biUnion_lt_succ'
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋃ k < n + 1, u k = u 0 union ⋃ k < n, u (k + 1)
  proof: Nat.iSup_lt_succ' u n

中文:
定理 biUnion_lt_succ'
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋃ k < n + 1, u k = u 0 union ⋃ k < n, u (k + 1)
  证明: Nat.iSup_lt_succ' u n

Depends on / 依赖: Nat.iSup_lt_succ, iSup_lt_succ
-/
theorem biUnion_lt_succ' (u : Nat -> Set α) (n : Nat) : ⋃ k < n + 1, u k = u 0 union ⋃ k < n, u (k + 1) :=
  Nat.iSup_lt_succ' u n

/--
theorem `biInter_lt_succ` / 定理 `biInter_lt_succ`

English:
theorem biInter_lt_succ
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋂ k < n + 1, u k = (⋂ k < n, u k) inter u n
  proof: Nat.iInf_lt_succ u n

中文:
定理 bi整数er_lt_succ
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋂ k < n + 1, u k = (⋂ k < n, u k) inter u n
  证明: Nat.iInf_lt_succ u n

Depends on / 依赖: Nat.iInf_lt_succ, iInf_lt_succ
-/
theorem biInter_lt_succ (u : Nat -> Set α) (n : Nat) : ⋂ k < n + 1, u k = (⋂ k < n, u k) inter u n :=
  Nat.iInf_lt_succ u n

/--
theorem `biInter_lt_succ'` / 定理 `biInter_lt_succ'`

English:
theorem biInter_lt_succ'
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋂ k < n + 1, u k = u 0 inter ⋂ k < n, u (k + 1)
  proof: Nat.iInf_lt_succ' u n

中文:
定理 bi整数er_lt_succ'
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋂ k < n + 1, u k = u 0 inter ⋂ k < n, u (k + 1)
  证明: Nat.iInf_lt_succ' u n

Depends on / 依赖: Nat.iInf_lt_succ, iInf_lt_succ
-/
theorem biInter_lt_succ' (u : Nat -> Set α) (n : Nat) : ⋂ k < n + 1, u k = u 0 inter ⋂ k < n, u (k + 1) :=
  Nat.iInf_lt_succ' u n

/--
theorem `biUnion_le_succ` / 定理 `biUnion_le_succ`

English:
theorem biUnion_le_succ
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋃ k <= n + 1, u k = (⋃ k <= n, u k) union u (n + 1)
  proof: Nat.iSup_le_succ u n

中文:
定理 biUnion_le_succ
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋃ k <= n + 1, u k = (⋃ k <= n, u k) union u (n + 1)
  证明: Nat.iSup_le_succ u n

Depends on / 依赖: Nat.iSup_le_succ, iSup_le_succ
-/
theorem biUnion_le_succ (u : Nat -> Set α) (n : Nat) : ⋃ k <= n + 1, u k = (⋃ k <= n, u k) union u (n + 1) :=
  Nat.iSup_le_succ u n

/--
theorem `biUnion_le_succ'` / 定理 `biUnion_le_succ'`

English:
theorem biUnion_le_succ'
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋃ k <= n + 1, u k = u 0 union ⋃ k <= n, u (k + 1)
  proof: Nat.iSup_le_succ' u n

中文:
定理 biUnion_le_succ'
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋃ k <= n + 1, u k = u 0 union ⋃ k <= n, u (k + 1)
  证明: Nat.iSup_le_succ' u n

Depends on / 依赖: Nat.iSup_le_succ, iSup_le_succ
-/
theorem biUnion_le_succ' (u : Nat -> Set α) (n : Nat) : ⋃ k <= n + 1, u k = u 0 union ⋃ k <= n, u (k + 1) :=
  Nat.iSup_le_succ' u n

/--
theorem `biInter_le_succ` / 定理 `biInter_le_succ`

English:
theorem biInter_le_succ
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋂ k <= n + 1, u k = (⋂ k <= n, u k) inter u (n + 1)
  proof: Nat.iInf_le_succ u n

中文:
定理 bi整数er_le_succ
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋂ k <= n + 1, u k = (⋂ k <= n, u k) inter u (n + 1)
  证明: Nat.iInf_le_succ u n

Depends on / 依赖: Nat.iInf_le_succ, iInf_le_succ
-/
theorem biInter_le_succ (u : Nat -> Set α) (n : Nat) : ⋂ k <= n + 1, u k = (⋂ k <= n, u k) inter u (n + 1) :=
  Nat.iInf_le_succ u n

/--
theorem `biInter_le_succ'` / 定理 `biInter_le_succ'`

English:
theorem biInter_le_succ'
  given: (u : Nat -> Set α) (n : Nat)
  statement: ⋂ k <= n + 1, u k = u 0 inter ⋂ k <= n, u (k + 1)
  proof: Nat.iInf_le_succ' u n

中文:
定理 bi整数er_le_succ'
  条件: (u : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋂ k <= n + 1, u k = u 0 inter ⋂ k <= n, u (k + 1)
  证明: Nat.iInf_le_succ' u n

Depends on / 依赖: Nat.iInf_le_succ, iInf_le_succ
-/
theorem biInter_le_succ' (u : Nat -> Set α) (n : Nat) : ⋂ k <= n + 1, u k = u 0 inter ⋂ k <= n, u (k + 1) :=
  Nat.iInf_le_succ' u n

end Set
