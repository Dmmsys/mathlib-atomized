/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Bool.Set
public import Mathlib.Data.Nat.Set
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Theory of complete lattices

This file contains results on complete lattices that need more theory to develop.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι -> Sort*} {κ' : ι' -> Sort*}

open OrderDual

section

variable [CompleteLattice α] {f g s : ι -> α} {a b : α}

/-!
### `iSup` and `iInf` under `Bool`
-/

@[to_dual]
/--
theorem `iSup_bool_eq` / 定理 `iSup_bool_eq`

English:
theorem iSup_bool_eq
  given: {f : Bool -> α}
  statement: ⨆ b : Bool, f b = f true ⊔ f false
  proof: by
  rw [iSup]; rw [Bool.range_eq]; rw [sSup_pair]; rw [sup_comm]

@[to_dual]

中文:
定理 iSup_bool_eq
  条件: {f : 布尔值 -> α}
  结论: ⨆ b : 布尔值, f b = f true ⊔ f false
  证明: by
  rw [iSup]; rw [Bool.range_eq]; rw [sSup_pair]; rw [sup_comm]

@[to_dual]

Depends on / 依赖: Bool.range_eq, range_eq, sSup_pair, sup_comm
-/
theorem iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ f false := by
  rw [iSup]; rw [Bool.range_eq]; rw [sSup_pair]; rw [sup_comm]

@[to_dual]
/--
theorem `sup_eq_iSup` / 定理 `sup_eq_iSup`

English:
theorem sup_eq_iSup
  given: (x y : α)
  statement: x ⊔ y = ⨆ b : Bool, cond b x y
  proof: by
  rw [iSup_bool_eq]; rw [Bool.cond_true]; rw [Bool.cond_false]

中文:
定理 sup_eq_iSup
  条件: (x y : α)
  结论: x ⊔ y = ⨆ b : 布尔值, cond b x y
  证明: by
  rw [iSup_bool_eq]; rw [Bool.cond_true]; rw [Bool.cond_false]

Depends on / 依赖: Bool.cond_false, Bool.cond_true, cond_false, cond_true, iSup_bool_eq
-/
theorem sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [iSup_bool_eq]; rw [Bool.cond_true]; rw [Bool.cond_false]

/-!
### `iSup` and `iInf` under `ℕ`
-/

@[to_dual]
/--
theorem `iSup_ge_eq_iSup_nat_add` / 定理 `iSup_ge_eq_iSup_nat_add`

English:
theorem iSup_ge_eq_iSup_nat_add
  given: (u : Nat -> α) (n : Nat)
  statement: ⨆ i >= n, u i = ⨆ i, u (i + n)
  proof: by
  apply le_antisymm <;> simp only [iSup_le_iff]
  · refine fun i hi => le_sSup ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩

中文:
定理 iSup_ge_eq_iSup_nat_add
  条件: (u : 自然数 -> α) (n : 自然数)
  结论: ⨆ i >= n, u i = ⨆ i, u (i + n)
  证明: by
  apply le_antisymm <;> simp only [iSup_le_iff]
  · refine fun i hi => le_sSup ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩

Depends on / 依赖: Nat.le_add_left, Nat.sub_add_cancel, iSup_le_iff, iSup_pos, le_add_left, le_antisymm, le_sSup, sub_add_cancel
-/
theorem iSup_ge_eq_iSup_nat_add (u : Nat -> α) (n : Nat) : ⨆ i >= n, u i = ⨆ i, u (i + n) := by
  apply le_antisymm <;> simp only [iSup_le_iff]
  · refine fun i hi => le_sSup ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩

-- `to_dual` cannot translate between `Monotone` and `Antitone`.
/--
theorem `Monotone.iSup_nat_add` / 定理 `Monotone.iSup_nat_add`

English:
theorem Monotone.iSup_nat_add
  given: {f : Nat -> α} (hf : Monotone f) (k : Nat)
  statement: ⨆ n, f (n + k) = ⨆ n, f n
  proof: le_antisymm (iSup_le fun i => le_iSup _ (i + k)) iSup_mono fun i => hf Nat.le_add_right i k

中文:
定理 递增.iSup_nat_add
  条件: {f : 自然数 -> α} (hf : 递增 f) (k : 自然数)
  结论: ⨆ n, f (n + k) = ⨆ n, f n
  证明: le_antisymm (iSup_le fun i => le_iSup _ (i + k)) iSup_mono fun i => hf Nat.le_add_right i k

Depends on / 依赖: Nat.le_add_right, iSup_le, iSup_mono, le_add_right, le_antisymm, le_iSup
-/
theorem Monotone.iSup_nat_add {f : Nat -> α} (hf : Monotone f) (k : Nat) : ⨆ n, f (n + k) = ⨆ n, f n :=
le_antisymm (iSup_le fun i => le_iSup _ (i + k)) iSup_mono fun i => hf Nat.le_add_right i k

/--
theorem `Antitone.iInf_nat_add` / 定理 `Antitone.iInf_nat_add`

English:
theorem Antitone.iInf_nat_add
  given: {f : Nat -> α} (hf : Antitone f) (k : Nat)
  statement: ⨅ n, f (n + k) = ⨅ n, f n
  proof: hf.dual_right.iSup_nat_add k

中文:
定理 递减.iInf_nat_add
  条件: {f : 自然数 -> α} (hf : 递减 f) (k : 自然数)
  结论: ⨅ n, f (n + k) = ⨅ n, f n
  证明: hf.dual_right.iSup_nat_add k

Depends on / 依赖: dual_right, hf.dual_right.iSup_nat_add, iSup_nat_add
-/
theorem Antitone.iInf_nat_add {f : Nat -> α} (hf : Antitone f) (k : Nat) : ⨅ n, f (n + k) = ⨅ n, f n :=
  hf.dual_right.iSup_nat_add k

-- Not `@[simp]` since the subterm `?f (i + ?k)` produces an ugly higher-order unification problem.
-- (Although the `simpNF` linter does not complain.)
-- See: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
/--
theorem `iSup_iInf_ge_nat_add` / 定理 `iSup_iInf_ge_nat_add`

English:
theorem iSup_iInf_ge_nat_add
  given: (f : Nat -> α) (k : Nat)
  proof: by
  have hf : Monotone fun n => ⨅ i >= n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]

中文:
定理 iSup_iInf_ge_nat_add
  条件: (f : 自然数 -> α) (k : 自然数)
  证明: by
  have hf : Monotone fun n => ⨅ i >= n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]

Depends on / 依赖: Monotone, Monotone.iSup_nat_add, Nat.add_assoc, add_assoc, biInf_mono, h.trans, iInf_ge_eq_iInf_nat_add, iSup_nat_add, simp_rw
-/
theorem iSup_iInf_ge_nat_add (f : Nat -> α) (k : Nat) :
    ⨆ n, ⨅ i >= n, f (i + k) = ⨆ n, ⨅ i >= n, f i := by
  have hf : Monotone fun n => ⨅ i >= n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]

-- Not `@[simp]` since the subterm `?f (i + ?k)` produces an ugly higher-order unification problem.
-- (Although the `simpNF` linter does not complain.)
-- See: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
@[to_dual existing]
/--
theorem `iInf_iSup_ge_nat_add` / 定理 `iInf_iSup_ge_nat_add`

English:
theorem iInf_iSup_ge_nat_add
  proof: @iSup_iInf_ge_nat_add αᵒᵈ _

@[to_dual inf_iInf_nat_succ]

中文:
定理 iInf_iSup_ge_nat_add
  证明: @iSup_iInf_ge_nat_add αᵒᵈ _

@[to_dual inf_iInf_nat_succ]

Depends on / 依赖: iSup_iInf_ge_nat_add
-/
theorem iInf_iSup_ge_nat_add :
    forall (f : Nat -> α) (k : Nat), ⨅ n, ⨆ i >= n, f (i + k) = ⨅ n, ⨆ i >= n, f i :=
  @iSup_iInf_ge_nat_add αᵒᵈ _

@[to_dual inf_iInf_nat_succ]
/--
theorem `sup_iSup_nat_succ` / 定理 `sup_iSup_nat_succ`

English:
theorem sup_iSup_nat_succ
  given: (u : Nat -> α)
  statement: (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i
  proof: calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x in {0} union range Nat.succ, u x := by
      { rw [iSup_union, iSup_singleton, iSup_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]

@[to_dual]

中文:
定理 sup_iSup_nat_succ
  条件: (u : 自然数 -> α)
  结论: (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i
  证明: calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x in {0} union range Nat.succ, u x := by
      { rw [iSup_union, iSup_singleton, iSup_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]

@[to_dual]

Depends on / 依赖: Nat.succ, Nat.zero_union_range_succ, iSup_range, iSup_singleton, iSup_union, iSup_univ, zero_union_range_succ
-/
theorem sup_iSup_nat_succ (u : Nat -> α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x in {0} union range Nat.succ, u x := by
      { rw [iSup_union, iSup_singleton, iSup_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]

@[to_dual]
/--
theorem `iInf_nat_gt_zero_eq` / 定理 `iInf_nat_gt_zero_eq`

English:
theorem iInf_nat_gt_zero_eq
  given: (f : Nat -> α)
  statement: ⨅ i > 0, f i = ⨅ i, f (i + 1)
  proof: by
  rw [← iInf_range]; rw [Nat.range_succ]
  simp

中文:
定理 iInf_nat_gt_zero_eq
  条件: (f : 自然数 -> α)
  结论: ⨅ i > 0, f i = ⨅ i, f (i + 1)
  证明: by
  rw [← iInf_range]; rw [Nat.range_succ]
  simp

Depends on / 依赖: Nat.range_succ, iInf_range, range_succ
-/
theorem iInf_nat_gt_zero_eq (f : Nat -> α) : ⨅ i > 0, f i = ⨅ i, f (i + 1) := by
  rw [← iInf_range]; rw [Nat.range_succ]
  simp

end

/-!
### Instances
-/

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_sInf_eq` -/
@[to_dual iSup_inf_le_inf_sSup /-- This is a weaker version of `inf_sSup_eq` -/]
/--
theorem `sup_sInf_le_iInf_sup` / 定理 `sup_sInf_le_iInf_sup`

English:
theorem sup_sInf_le_iInf_sup
  statement: a ⊔ sInf s <= ⨅ b in s, a ⊔ b
  proof: le_iInf₂ fun _ h => sup_le_sup_left (sInf_le h) _

中文:
定理 sup_sInf_le_iInf_sup
  结论: a ⊔ sInf s <= ⨅ b in s, a ⊔ b
  证明: le_iInf₂ fun _ h => sup_le_sup_left (sInf_le h) _

Depends on / 依赖: sInf_le, sup_le_sup_left
-/
theorem sup_sInf_le_iInf_sup : a ⊔ sInf s <= ⨅ b in s, a ⊔ b :=
  le_iInf₂ fun _ h => sup_le_sup_left (sInf_le h) _

/-- This is a weaker version of `sInf_sup_eq` -/
@[to_dual iSup_inf_le_sSup_inf /-- This is a weaker version of `sSup_inf_eq` -/]
/--
theorem `sInf_sup_le_iInf_sup` / 定理 `sInf_sup_le_iInf_sup`

English:
theorem sInf_sup_le_iInf_sup
  statement: sInf s ⊔ a <= ⨅ b in s, b ⊔ a
  proof: le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _

@[to_dual]

中文:
定理 sInf_sup_le_iInf_sup
  结论: sInf s ⊔ a <= ⨅ b in s, b ⊔ a
  证明: le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _

@[to_dual]

Depends on / 依赖: sInf_le, sup_le_sup_right
-/
theorem sInf_sup_le_iInf_sup : sInf s ⊔ a <= ⨅ b in s, b ⊔ a :=
  le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _

@[to_dual]
/--
theorem `iInf_sup_le_iInf_sup` / 定理 `iInf_sup_le_iInf_sup`

English:
theorem iInf_sup_le_iInf_sup
  given: (f : ι -> α) (a : α)
  proof: le_iInf fun i => sup_le_sup_right (iInf_le f i) a

@[to_dual iSup_inf_le_inf_iSup]

中文:
定理 iInf_sup_le_iInf_sup
  条件: (f : ι -> α) (a : α)
  证明: le_iInf fun i => sup_le_sup_right (iInf_le f i) a

@[to_dual iSup_inf_le_inf_iSup]

Depends on / 依赖: iInf_le, le_iInf, sup_le_sup_right
-/
theorem iInf_sup_le_iInf_sup (f : ι -> α) (a : α) :
    (⨅ i, f i) ⊔ a <= ⨅ i, (f i ⊔ a) :=
  le_iInf fun i => sup_le_sup_right (iInf_le f i) a

@[to_dual iSup_inf_le_inf_iSup]
/--
theorem `sup_iInf_le_iInf_sup` / 定理 `sup_iInf_le_iInf_sup`

English:
theorem sup_iInf_le_iInf_sup
  given: (f : ι -> α) (a : α)
  proof: le_iInf fun i => sup_le_sup_left (iInf_le f i) a

@[to_dual]

中文:
定理 sup_iInf_le_iInf_sup
  条件: (f : ι -> α) (a : α)
  证明: le_iInf fun i => sup_le_sup_left (iInf_le f i) a

@[to_dual]

Depends on / 依赖: iInf_le, le_iInf, sup_le_sup_left
-/
theorem sup_iInf_le_iInf_sup (f : ι -> α) (a : α) :
    a ⊔ (⨅ i, f i) <= ⨅ i, (a ⊔ f i) :=
  le_iInf fun i => sup_le_sup_left (iInf_le f i) a

@[to_dual]
/--
lemma `biInf_sup_le_biInf_sup` / 引理 `biInf_sup_le_biInf_sup`

English:
lemma biInf_sup_le_biInf_sup
  given: (f : β -> α) (s : Set β) (a : α)
  proof: le_iInf₂ fun _ hi => sup_le_sup_right (biInf_le f hi) a

@[to_dual biSup_inf_le_inf_biSup]

中文:
引理 biInf_sup_le_biInf_sup
  条件: (f : β -> α) (s : 集合 β) (a : α)
  证明: le_iInf₂ fun _ hi => sup_le_sup_right (biInf_le f hi) a

@[to_dual biSup_inf_le_inf_biSup]

Depends on / 依赖: biInf_le, sup_le_sup_right
-/
lemma biInf_sup_le_biInf_sup (f : β -> α) (s : Set β) (a : α) :
    (⨅ i in s, f i) ⊔ a <= ⨅ i in s, f i ⊔ a :=
  le_iInf₂ fun _ hi => sup_le_sup_right (biInf_le f hi) a

@[to_dual biSup_inf_le_inf_biSup]
/--
lemma `sup_biInf_le_biInf_sup` / 引理 `sup_biInf_le_biInf_sup`

English:
lemma sup_biInf_le_biInf_sup
  given: (f : β -> α) (s : Set β) (a : α)
  proof: le_iInf₂ fun _ hi => sup_le_sup_left (biInf_le f hi) a

@[to_dual le_iSup_inf_iSup]

中文:
引理 sup_biInf_le_biInf_sup
  条件: (f : β -> α) (s : 集合 β) (a : α)
  证明: le_iInf₂ fun _ hi => sup_le_sup_left (biInf_le f hi) a

@[to_dual le_iSup_inf_iSup]

Depends on / 依赖: biInf_le, sup_le_sup_left
-/
lemma sup_biInf_le_biInf_sup (f : β -> α) (s : Set β) (a : α) :
    a ⊔ (⨅ i in s, f i) <= ⨅ i in s, a ⊔ f i :=
  le_iInf₂ fun _ hi => sup_le_sup_left (biInf_le f hi) a

@[to_dual le_iSup_inf_iSup]
/--
theorem `iInf_sup_iInf_le` / 定理 `iInf_sup_iInf_le`

English:
theorem iInf_sup_iInf_le
  given: (f g : ι -> α)
  statement: (⨅ i, f i) ⊔ ⨅ i, g i <= ⨅ i, f i ⊔ g i
  proof: sup_le (iInf_mono fun _ => le_sup_left) (iInf_mono fun _ => le_sup_right)

@[to_dual]

中文:
定理 iInf_sup_iInf_le
  条件: (f g : ι -> α)
  结论: (⨅ i, f i) ⊔ ⨅ i, g i <= ⨅ i, f i ⊔ g i
  证明: sup_le (iInf_mono fun _ => le_sup_left) (iInf_mono fun _ => le_sup_right)

@[to_dual]

Depends on / 依赖: iInf_mono, le_sup_left, le_sup_right, sup_le
-/
theorem iInf_sup_iInf_le (f g : ι -> α) : (⨅ i, f i) ⊔ ⨅ i, g i <= ⨅ i, f i ⊔ g i :=
  sup_le (iInf_mono fun _ => le_sup_left) (iInf_mono fun _ => le_sup_right)

@[to_dual]
/--
theorem `disjoint_sSup_left` / 定理 `disjoint_sSup_left`

English:
theorem disjoint_sSup_left
  given: {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i in a)
  proof: disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi :)

@[to_dual]

中文:
定理 disjoint_sSup_left
  条件: {a : 集合 α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i in a)
  证明: disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi :)

@[to_dual]

Depends on / 依赖: d.le_bot, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, iSup_inf_le_sSup_inf, iSup_inf_le_sSup_inf.trans, le_bot
-/
theorem disjoint_sSup_left {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i in a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi :)

@[to_dual]
/--
theorem `disjoint_sSup_right` / 定理 `disjoint_sSup_right`

English:
theorem disjoint_sSup_right
  given: {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i in a)
  proof: disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi :)

@[to_dual]

中文:
定理 disjoint_sSup_right
  条件: {a : 集合 α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i in a)
  证明: disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi :)

@[to_dual]

Depends on / 依赖: _le_iff.mp, d.le_bot, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, iSup_inf_le_inf_sSup, iSup_inf_le_inf_sSup.trans, le_bot
-/
theorem disjoint_sSup_right {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i in a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi :)

@[to_dual]
/--
lemma `disjoint_of_sSup_disjoint_of_le_of_le` / 引理 `disjoint_of_sSup_disjoint_of_le_of_le`

English:
lemma disjoint_of_sSup_disjoint_of_le_of_le
  statement: {a b : α} {c d : Set α} (hs : forall e in c, e <= a)
  proof: by
  grind

@[to_dual]

中文:
引理 disjoint_of_sSup_disjoint_of_le_of_le
  结论: {a b : α} {c d : 集合 α} (hs : 对任意 e in c, e <= a)
  证明: by
  grind

@[to_dual]
-/
lemma disjoint_of_sSup_disjoint_of_le_of_le {a b : α} {c d : Set α} (hs : forall e in c, e <= a)
    (ht : forall e in d, e <= b) (hd : Disjoint a b) (he : ⊥ ∉ c ∨ ⊥ ∉ d) : Disjoint c d := by
  grind

@[to_dual]
/--
lemma `disjoint_of_sSup_disjoint` / 引理 `disjoint_of_sSup_disjoint`

English:
lemma disjoint_of_sSup_disjoint
  statement: {a b : Set α} (hd : Disjoint (sSup a) (sSup b))
  proof: disjoint_of_sSup_disjoint_of_le_of_le (fun _ hc => le_sSup hc) (fun _ hc => le_sSup hc) hd he

中文:
引理 disjoint_of_sSup_disjoint
  结论: {a b : 集合 α} (hd : Disjoint (sSup a) (sSup b))
  证明: disjoint_of_sSup_disjoint_of_le_of_le (fun _ hc => le_sSup hc) (fun _ hc => le_sSup hc) hd he

Depends on / 依赖: disjoint_of_sSup_disjoint_of_le_of_le, le_sSup
-/
lemma disjoint_of_sSup_disjoint {a b : Set α} (hd : Disjoint (sSup a) (sSup b))
    (he : ⊥ ∉ a ∨ ⊥ ∉ b) : Disjoint a b :=
  disjoint_of_sSup_disjoint_of_le_of_le (fun _ hc => le_sSup hc) (fun _ hc => le_sSup hc) hd he

end CompleteLattice

namespace ULift

universe v

@[to_dual]
/--
Instance `supSet` / 实例 `supSet`

English:
instance supSet
  signature: [SupSet α]
  body: ULift.up (sSup <| ULift.up ⁻¹' s)

@[to_dual]

中文:
实例 supSet
  签名: [上确界集 α]
  定义体: ULift.up (sSup <| ULift.up ⁻¹' s)

@[to_dual]

Depends on / 依赖: ULift.up
-/
instance supSet [SupSet α] : SupSet (ULift.{v} α) where sSup s := ULift.up (sSup <| ULift.up ⁻¹' s)

@[to_dual]
/--
theorem `down_sSup` / 定理 `down_sSup`

English:
theorem down_sSup
  given: [SupSet α] (s : Set (ULift.{v} α))
  statement: (sSup s).down = sSup (ULift.up ⁻¹' s)
  proof: rfl

@[to_dual]

中文:
定理 down_sSup
  条件: [上确界集 α] (s : 集合 (类型层提升.{v} α))
  结论: (sSup s).down = sSup (类型层提升.up ⁻¹' s)
  证明: rfl

@[to_dual]
-/
theorem down_sSup [SupSet α] (s : Set (ULift.{v} α)) : (sSup s).down = sSup (ULift.up ⁻¹' s) := rfl

@[to_dual]
/--
theorem `up_sSup` / 定理 `up_sSup`

English:
theorem up_sSup
  given: [SupSet α] (s : Set α)
  statement: up (sSup s) = sSup (ULift.down ⁻¹' s)
  proof: rfl

@[to_dual]

中文:
定理 up_sSup
  条件: [上确界集 α] (s : 集合 α)
  结论: up (sSup s) = sSup (类型层提升.down ⁻¹' s)
  证明: rfl

@[to_dual]
-/
theorem up_sSup [SupSet α] (s : Set α) : up (sSup s) = sSup (ULift.down ⁻¹' s) := rfl

@[to_dual]
/--
theorem `down_iSup` / 定理 `down_iSup`

English:
theorem down_iSup
  given: [SupSet α] (f : ι -> ULift.{v} α)
  statement: (⨆ i, f i).down = ⨆ i, (f i).down
  proof: congr_arg sSup (preimage_eq_iff_eq_image ULift.up_bijective).mpr
    Eq.symm (range_comp _ _).symm

@[to_dual]

中文:
定理 down_iSup
  条件: [上确界集 α] (f : ι -> 类型层提升.{v} α)
  结论: (⨆ i, f i).down = ⨆ i, (f i).down
  证明: congr_arg sSup (preimage_eq_iff_eq_image ULift.up_bijective).mpr
    Eq.symm (range_comp _ _).symm

@[to_dual]

Depends on / 依赖: Eq.symm, ULift.up_bijective, congr_arg, preimage_eq_iff_eq_image, range_comp, up_bijective
-/
theorem down_iSup [SupSet α] (f : ι -> ULift.{v} α) : (⨆ i, f i).down = ⨆ i, (f i).down :=
congr_arg sSup (preimage_eq_iff_eq_image ULift.up_bijective).mpr
    Eq.symm (range_comp _ _).symm

@[to_dual]
/--
theorem `up_iSup` / 定理 `up_iSup`

English:
theorem up_iSup
  given: [SupSet α] (f : ι -> α)
  statement: up (⨆ i, f i) = ⨆ i, up (f i)
  proof: congr_arg ULift.up (down_iSup _).symm

中文:
定理 up_iSup
  条件: [上确界集 α] (f : ι -> α)
  结论: up (⨆ i, f i) = ⨆ i, up (f i)
  证明: congr_arg ULift.up (down_iSup _).symm

Depends on / 依赖: ULift.up, congr_arg, down_iSup
-/
theorem up_iSup [SupSet α] (f : ι -> α) : up (⨆ i, f i) = ⨆ i, up (f i) :=
congr_arg ULift.up (down_iSup _).symm

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: [CompleteLattice α]
  body: ULift.down_injective.completeLattice _ .rfl .rfl down_sup down_inf
    (fun s => by rw [sSup_eq_iSup', down_iSup, iSup_subtype''])
    (fun s => by rw [sInf_eq_iInf', down_iInf, iInf_subtype'']) down_top down_bot

中文:
实例 instCompleteLattice
  签名: [完备格 α]
  定义体: ULift.down_injective.completeLattice _ .rfl .rfl down_sup down_inf
    (fun s => by rw [sSup_eq_iSup', down_iSup, iSup_subtype''])
    (fun s => by rw [sInf_eq_iInf', down_iInf, iInf_subtype'']) down_top down_bot

Depends on / 依赖: ULift.down_injective.completeLattice, completeLattice, down_bot, down_iInf, down_iSup, down_inf, down_injective, down_sup, down_top, iInf_subtype, iSup_subtype, sInf_eq_iInf, sSup_eq_iSup
-/
instance instCompleteLattice [CompleteLattice α] : CompleteLattice (ULift.{v} α) :=
  ULift.down_injective.completeLattice _ .rfl .rfl down_sup down_inf
    (fun s => by rw [sSup_eq_iSup', down_iSup, iSup_subtype''])
    (fun s => by rw [sInf_eq_iInf', down_iInf, iInf_subtype'']) down_top down_bot

end ULift

namespace PUnit

/--
Instance `instCompleteLinearOrder` / 实例 `instCompleteLinearOrder`

English:
instance instCompleteLinearOrder
  signature: : CompleteLinearOrder PUnit where
  body: instBooleanAlgebra
  __ := instLinearOrder
  sSup := fun _ => unit
  sInf := fun _ => unit
  isLUB_sSup _ := ⟨top_mem_upperBounds _, bot_mem_lowerBounds _⟩
  isGLB_sInf _ := ⟨bot_mem_lowerBounds _, top_mem_upperBounds _⟩
  le_himp_iff := by intros; trivial
  himp_bot := by intros; trivial
  sdiff_le_iff := by intros; trivial
  top_sdiff := by intros; trivial

中文:
实例 instCompleteLinearOrder
  签名: : 完备线性序 命题单元 where
  定义体: instBooleanAlgebra
  __ := instLinearOrder
  sSup := fun _ => unit
  sInf := fun _ => unit
  isLUB_sSup _ := ⟨top_mem_upperBounds _, bot_mem_lowerBounds _⟩
  isGLB_sInf _ := ⟨bot_mem_lowerBounds _, top_mem_upperBounds _⟩
  le_himp_iff := by intros; trivial
  himp_bot := by intros; trivial
  sdiff_le_iff := by intros; trivial
  top_sdiff := by intros; trivial

Depends on / 依赖: instBooleanAlgebra
-/
instance instCompleteLinearOrder : CompleteLinearOrder PUnit where
  __ := instBooleanAlgebra
  __ := instLinearOrder
  sSup := fun _ => unit
  sInf := fun _ => unit
  isLUB_sSup _ := ⟨top_mem_upperBounds _, bot_mem_lowerBounds _⟩
  isGLB_sInf _ := ⟨bot_mem_lowerBounds _, top_mem_upperBounds _⟩
  le_himp_iff := by intros; trivial
  himp_bot := by intros; trivial
  sdiff_le_iff := by intros; trivial
  top_sdiff := by intros; trivial

end PUnit
