/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Int.LeastGreatest
public import Mathlib.Order.ConditionallyCompleteLattice.Defs

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

public section


open Int


noncomputable section

namespace Int

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConditionallyCompleteLinearOrder Int
  body: instLinearOrder
  __ := LinearOrder.toLattice
  sSup s :=
    if h : s.Nonempty ∧ BddAbove s then
      greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  sInf s :=
    if h : s.Nonempty ∧ BddBelow s then
      leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  isLUB_csSup _ hn hb := by
    rw [dif_pos ⟨hn]; rw [hb⟩]
    exact (isGreatest_coe_greatestOfBdd ..).isLUB
  isGLB_csInf _ hn hb := by
    rw [dif_pos ⟨hn]; rw [hb⟩]
    exact (isLeast_coe_leastOfBdd ..).isGLB
  csSup_of_not_bddAbove := fun s hs => by simp [hs]
  csInf_of_not_bddBelow := fun s hs => by simp [hs]

中文:
实例 :
  签名: 条件完备线性序 整数
  定义体: instLinearOrder
  __ := LinearOrder.toLattice
  sSup s :=
    if h : s.Nonempty ∧ BddAbove s then
      greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  sInf s :=
    if h : s.Nonempty ∧ BddBelow s then
      leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  isLUB_csSup _ hn hb := by
    rw [dif_pos ⟨hn]; rw [hb⟩]
    exact (isGreatest_coe_greatestOfBdd ..).isLUB
  isGLB_csInf _ hn hb := by
    rw [dif_pos ⟨hn]; rw [hb⟩]
    exact (isLeast_coe_leastOfBdd ..).isGLB
  csSup_of_not_bddAbove := fun s hs => by simp [hs]
  csInf_of_not_bddBelow := fun s hs => by simp [hs]

Depends on / 依赖: instLinearOrder
-/
instance : ConditionallyCompleteLinearOrder Int where
  __ := instLinearOrder
  __ := LinearOrder.toLattice
  sSup s :=
    if h : s.Nonempty ∧ BddAbove s then
      greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  sInf s :=
    if h : s.Nonempty ∧ BddBelow s then
      leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  isLUB_csSup _ hn hb := by
    rw [dif_pos ⟨hn]; rw [hb⟩]
    exact (isGreatest_coe_greatestOfBdd ..).isLUB
  isGLB_csInf _ hn hb := by
    rw [dif_pos ⟨hn]; rw [hb⟩]
    exact (isLeast_coe_leastOfBdd ..).isGLB
  csSup_of_not_bddAbove := fun s hs => by simp [hs]
  csInf_of_not_bddBelow := fun s hs => by simp [hs]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `csSup_eq_greatestOfBdd` / 定理 `csSup_eq_greatestOfBdd`

English:
theorem csSup_eq_greatestOfBdd
  statement: {s : Set Int} [DecidablePred (· in s)] (b : Int) (Hb : forall z in s, z <= b)
  proof: by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  simp only [sSup, dif_pos this]
  convert! (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm

@[simp]

中文:
定理 csSup_eq_greatestOfBdd
  结论: {s : 集合 整数} [DecidablePred (· in s)] (b : 整数) (Hb : 对任意 z in s, z <= b)
  证明: by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  simp only [sSup, dif_pos this]
  convert! (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm

@[simp]

Depends on / 依赖: BddAbove, Classical, Classical.choose_spec, Nonempty, choose_spec, coe_greatestOfBdd_eq, convert, dif_pos, s.Nonempty
-/
theorem csSup_eq_greatestOfBdd {s : Set Int} [DecidablePred (· in s)] (b : Int) (Hb : forall z in s, z <= b)
    (Hinh : exists z : Int, z in s) : sSup s = greatestOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  simp only [sSup, dif_pos this]
  convert! (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm

@[simp]
/--
theorem `csSup_empty` / 定理 `csSup_empty`

English:
theorem csSup_empty
  statement: sSup (∅ : Set Int) = 0
  proof: dif_neg (by simp)

中文:
定理 csSup_empty
  结论: sSup (∅ : 集合 整数) = 0
  证明: dif_neg (by simp)

Depends on / 依赖: dif_neg
-/
theorem csSup_empty : sSup (∅ : Set Int) = 0 :=
  dif_neg (by simp)

/--
theorem `csSup_of_not_bddAbove` / 定理 `csSup_of_not_bddAbove`

English:
theorem csSup_of_not_bddAbove
  given: {s : Set Int} (h : ¬BddAbove s)
  statement: sSup s = 0
  proof: dif_neg (by simp [h])

中文:
定理 csSup_of_not_bddAbove
  条件: {s : 集合 整数} (h : ¬BddAbove s)
  结论: sSup s = 0
  证明: dif_neg (by simp [h])

Depends on / 依赖: dif_neg
-/
theorem csSup_of_not_bddAbove {s : Set Int} (h : ¬BddAbove s) : sSup s = 0 :=
  dif_neg (by simp [h])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `csInf_eq_leastOfBdd` / 定理 `csInf_eq_leastOfBdd`

English:
theorem csInf_eq_leastOfBdd
  statement: {s : Set Int} [DecidablePred (· in s)] (b : Int) (Hb : forall z in s, b <= z)
  proof: by
  have : s.Nonempty ∧ BddBelow s := ⟨Hinh, b, Hb⟩
  simp only [sInf, dif_pos this]
  convert! (coe_leastOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) Hinh).symm

@[simp]

中文:
定理 csInf_eq_leastOfBdd
  结论: {s : 集合 整数} [DecidablePred (· in s)] (b : 整数) (Hb : 对任意 z in s, b <= z)
  证明: by
  have : s.Nonempty ∧ BddBelow s := ⟨Hinh, b, Hb⟩
  simp only [sInf, dif_pos this]
  convert! (coe_leastOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) Hinh).symm

@[simp]

Depends on / 依赖: BddBelow, Classical, Classical.choose_spec, Nonempty, choose_spec, coe_leastOfBdd_eq, convert, dif_pos, s.Nonempty
-/
theorem csInf_eq_leastOfBdd {s : Set Int} [DecidablePred (· in s)] (b : Int) (Hb : forall z in s, b <= z)
    (Hinh : exists z : Int, z in s) : sInf s = leastOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddBelow s := ⟨Hinh, b, Hb⟩
  simp only [sInf, dif_pos this]
  convert! (coe_leastOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) Hinh).symm

@[simp]
/--
theorem `csInf_empty` / 定理 `csInf_empty`

English:
theorem csInf_empty
  statement: sInf (∅ : Set Int) = 0
  proof: dif_neg (by simp)

中文:
定理 csInf_empty
  结论: sInf (∅ : 集合 整数) = 0
  证明: dif_neg (by simp)

Depends on / 依赖: dif_neg
-/
theorem csInf_empty : sInf (∅ : Set Int) = 0 :=
  dif_neg (by simp)

/--
theorem `csInf_of_not_bddBelow` / 定理 `csInf_of_not_bddBelow`

English:
theorem csInf_of_not_bddBelow
  given: {s : Set Int} (h : ¬BddBelow s)
  statement: sInf s = 0
  proof: dif_neg (by simp [h])

中文:
定理 csInf_of_not_bddBelow
  条件: {s : 集合 整数} (h : ¬BddBelow s)
  结论: sInf s = 0
  证明: dif_neg (by simp [h])

Depends on / 依赖: dif_neg
-/
theorem csInf_of_not_bddBelow {s : Set Int} (h : ¬BddBelow s) : sInf s = 0 :=
  dif_neg (by simp [h])

/--
theorem `csSup_mem` / 定理 `csSup_mem`

English:
theorem csSup_mem
  given: {s : Set Int} (h1 : s.Nonempty) (h2 : BddAbove s)
  statement: sSup s in s
  proof: by
  convert! (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

中文:
定理 csSup_mem
  条件: {s : 集合 整数} (h1 : s.非空) (h2 : BddAbove s)
  结论: sSup s in s
  证明: by
  convert! (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, convert, dif_pos, greatestOfBdd
-/
theorem csSup_mem {s : Set Int} (h1 : s.Nonempty) (h2 : BddAbove s) : sSup s in s := by
  convert! (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

/--
theorem `csInf_mem` / 定理 `csInf_mem`

English:
theorem csInf_mem
  given: {s : Set Int} (h1 : s.Nonempty) (h2 : BddBelow s)
  statement: sInf s in s
  proof: by
  convert! (leastOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

中文:
定理 csInf_mem
  条件: {s : 集合 整数} (h1 : s.非空) (h2 : BddBelow s)
  结论: sInf s in s
  证明: by
  convert! (leastOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, convert, dif_pos, leastOfBdd
-/
theorem csInf_mem {s : Set Int} (h1 : s.Nonempty) (h2 : BddBelow s) : sInf s in s := by
  convert! (leastOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩

end Int

end

-- this example tests that the `Lattice ℤ` instance is computable;
-- i.e., that it is not found via the noncomputable instance in this file.
example : Lattice Int := inferInstance
