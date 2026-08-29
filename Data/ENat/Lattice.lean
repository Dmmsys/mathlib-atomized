/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.

-/

public section

assert_not_exists Field

open Set

noncomputable section
deriving instance CompleteLinearOrder for Nat∞
end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLinearOrder (WithBot ENat)
  body: inferInstanceAs (CompleteLinearOrder (WithBot (WithTop Nat)))

中文:
实例 :
  签名: 完备线性序 (WithBot E自然数)
  定义体: inferInstanceAs (CompleteLinearOrder (WithBot (WithTop Nat)))

Depends on / 依赖: CompleteLinearOrder, WithBot, WithTop
-/
noncomputable instance : CompleteLinearOrder (WithBot ENat) :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop Nat)))

namespace ENat
variable {ι : Sort*} {f : ι -> Nat} {s : Set Nat}

/--
lemma `iSup_natCast_eq_top` / 引理 `iSup_natCast_eq_top`

English:
lemma iSup_natCast_eq_top
  statement: ⨆ i, (f i : Nat∞) = ⊤ ↔ ¬ BddAbove (range f)
  proof: WithTop.iSup_coe_eq_top

中文:
引理 iSup_natCast_eq_top
  结论: ⨆ i, (f i : 自然数∞) = ⊤ ↔ ¬ BddAbove (range f)
  证明: WithTop.iSup_coe_eq_top

Depends on / 依赖: WithTop, WithTop.iSup_coe_eq_top, iSup_coe_eq_top
-/
lemma iSup_natCast_eq_top : ⨆ i, (f i : Nat∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
/--
lemma `iSup_natCast_ne_top` / 引理 `iSup_natCast_ne_top`

English:
lemma iSup_natCast_ne_top
  statement: ⨆ i, (f i : Nat∞) != ⊤ ↔ BddAbove (range f)
  proof: iSup_natCast_eq_top.not_left

中文:
引理 iSup_natCast_ne_top
  结论: ⨆ i, (f i : 自然数∞) != ⊤ ↔ BddAbove (range f)
  证明: iSup_natCast_eq_top.not_left

Depends on / 依赖: iSup_natCast_eq_top, iSup_natCast_eq_top.not_left, not_left
-/
lemma iSup_natCast_ne_top : ⨆ i, (f i : Nat∞) != ⊤ ↔ BddAbove (range f) := iSup_natCast_eq_top.not_left
/--
lemma `iSup_natCast_lt_top` / 引理 `iSup_natCast_lt_top`

English:
lemma iSup_natCast_lt_top
  statement: ⨆ i, (f i : Nat∞) < ⊤ ↔ BddAbove (range f)
  proof: WithTop.iSup_coe_lt_top

中文:
引理 iSup_natCast_lt_top
  结论: ⨆ i, (f i : 自然数∞) < ⊤ ↔ BddAbove (range f)
  证明: WithTop.iSup_coe_lt_top

Depends on / 依赖: WithTop, WithTop.iSup_coe_lt_top, iSup_coe_lt_top
-/
lemma iSup_natCast_lt_top : ⨆ i, (f i : Nat∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
/--
lemma `iInf_natCast_eq_top` / 引理 `iInf_natCast_eq_top`

English:
lemma iInf_natCast_eq_top
  statement: ⨅ i, (f i : Nat∞) = ⊤ ↔ IsEmpty ι
  proof: WithTop.iInf_coe_eq_top

中文:
引理 iInf_natCast_eq_top
  结论: ⨅ i, (f i : 自然数∞) = ⊤ ↔ 是空 ι
  证明: WithTop.iInf_coe_eq_top

Depends on / 依赖: WithTop, WithTop.iInf_coe_eq_top, iInf_coe_eq_top
-/
lemma iInf_natCast_eq_top : ⨅ i, (f i : Nat∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
/--
lemma `iInf_natCast_ne_top` / 引理 `iInf_natCast_ne_top`

English:
lemma iInf_natCast_ne_top
  statement: ⨅ i, (f i : Nat∞) != ⊤ ↔ Nonempty ι
  proof: by
  rw [Ne]; rw [iInf_natCast_eq_top]; rw [not_isEmpty_iff]

中文:
引理 iInf_natCast_ne_top
  结论: ⨅ i, (f i : 自然数∞) != ⊤ ↔ 非空 ι
  证明: by
  rw [Ne]; rw [iInf_natCast_eq_top]; rw [not_isEmpty_iff]

Depends on / 依赖: iInf_natCast_eq_top, not_isEmpty_iff
-/
lemma iInf_natCast_ne_top : ⨅ i, (f i : Nat∞) != ⊤ ↔ Nonempty ι := by
  rw [Ne]; rw [iInf_natCast_eq_top]; rw [not_isEmpty_iff]
/--
lemma `iInf_natCast_lt_top` / 引理 `iInf_natCast_lt_top`

English:
lemma iInf_natCast_lt_top
  statement: ⨅ i, (f i : Nat∞) < ⊤ ↔ Nonempty ι
  proof: WithTop.iInf_coe_lt_top

@[deprecated (since := "2026-07-17")] alias iSup_coe_eq_top := iSup_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_ne_top := iSup_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_lt_top := iSup_natCast_lt_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_eq_top := iInf_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_ne_top := iInf_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_lt_top := iInf_natCast_lt_top

中文:
引理 iInf_natCast_lt_top
  结论: ⨅ i, (f i : 自然数∞) < ⊤ ↔ 非空 ι
  证明: WithTop.iInf_coe_lt_top

@[deprecated (since := "2026-07-17")] alias iSup_coe_eq_top := iSup_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_ne_top := iSup_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_lt_top := iSup_natCast_lt_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_eq_top := iInf_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_ne_top := iInf_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_lt_top := iInf_natCast_lt_top

Depends on / 依赖: WithTop, WithTop.iInf_coe_lt_top, iInf_coe_lt_top
-/
lemma iInf_natCast_lt_top : ⨅ i, (f i : Nat∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

@[deprecated (since := "2026-07-17")] alias iSup_coe_eq_top := iSup_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_ne_top := iSup_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iSup_coe_lt_top := iSup_natCast_lt_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_eq_top := iInf_natCast_eq_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_ne_top := iInf_natCast_ne_top
@[deprecated (since := "2026-07-17")] alias iInf_coe_lt_top := iInf_natCast_lt_top

/--
lemma `natCast_sSup` / 引理 `natCast_sSup`

English:
lemma natCast_sSup
  statement: BddAbove s -> ↑(sSup s) = ⨆ a in s, (a : Nat∞)
  proof: WithTop.coe_sSup

@[deprecated (since := "2026-07-17")] alias coe_sSup := natCast_sSup

中文:
引理 natCast_sSup
  结论: BddAbove s -> ↑(sSup s) = ⨆ a in s, (a : 自然数∞)
  证明: WithTop.coe_sSup

@[deprecated (since := "2026-07-17")] alias coe_sSup := natCast_sSup

Depends on / 依赖: WithTop, WithTop.coe_sSup, coe_sSup
-/
lemma natCast_sSup : BddAbove s -> ↑(sSup s) = ⨆ a in s, (a : Nat∞) := WithTop.coe_sSup

@[deprecated (since := "2026-07-17")] alias coe_sSup := natCast_sSup

/--
lemma `natCast_sInf` / 引理 `natCast_sInf`

English:
lemma natCast_sInf
  given: (hs : s.Nonempty)
  statement: ↑(sInf s) = ⨅ a in s, (a : Nat∞)
  proof: WithTop.coe_sInf hs (OrderBot.bddBelow s)

@[deprecated (since := "2026-07-17")] alias coe_sInf := natCast_sInf

中文:
引理 natCast_sInf
  条件: (hs : s.非空)
  结论: ↑(sInf s) = ⨅ a in s, (a : 自然数∞)
  证明: WithTop.coe_sInf hs (OrderBot.bddBelow s)

@[deprecated (since := "2026-07-17")] alias coe_sInf := natCast_sInf

Depends on / 依赖: OrderBot, OrderBot.bddBelow, WithTop, WithTop.coe_sInf, bddBelow, coe_sInf
-/
lemma natCast_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a in s, (a : Nat∞) :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

@[deprecated (since := "2026-07-17")] alias coe_sInf := natCast_sInf

/--
lemma `natCast_iSup` / 引理 `natCast_iSup`

English:
lemma natCast_iSup
  statement: BddAbove (range f) -> ↑(⨆ i, f i) = ⨆ i, (f i : Nat∞)
  proof: WithTop.coe_iSup _

@[deprecated (since := "2026-07-17")] alias coe_iSup := natCast_iSup

中文:
引理 natCast_iSup
  结论: BddAbove (range f) -> ↑(⨆ i, f i) = ⨆ i, (f i : 自然数∞)
  证明: WithTop.coe_iSup _

@[deprecated (since := "2026-07-17")] alias coe_iSup := natCast_iSup

Depends on / 依赖: WithTop, WithTop.coe_iSup, coe_iSup
-/
lemma natCast_iSup : BddAbove (range f) -> ↑(⨆ i, f i) = ⨆ i, (f i : Nat∞) := WithTop.coe_iSup _

@[deprecated (since := "2026-07-17")] alias coe_iSup := natCast_iSup

/--
lemma `natCast_iInf` / 引理 `natCast_iInf`

English:
lemma natCast_iInf
  given: [Nonempty ι]
  statement: ↑(⨅ i, f i) = ⨅ i, (f i : Nat∞)
  proof: WithTop.coe_iInf (OrderBot.bddBelow _)

@[deprecated (since := "2026-07-17")] alias coe_iInf := natCast_iInf

@[simp]

中文:
引理 natCast_iInf
  条件: [非空 ι]
  结论: ↑(⨅ i, f i) = ⨅ i, (f i : 自然数∞)
  证明: WithTop.coe_iInf (OrderBot.bddBelow _)

@[deprecated (since := "2026-07-17")] alias coe_iInf := natCast_iInf

@[simp]
-/
@[norm_cast] lemma natCast_iInf [Nonempty ι] : ↑(⨅ i, f i) = ⨅ i, (f i : Nat∞) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

@[deprecated (since := "2026-07-17")] alias coe_iInf := natCast_iInf

@[simp]
/--
lemma `iInf_eq_top_of_isEmpty` / 引理 `iInf_eq_top_of_isEmpty`

English:
lemma iInf_eq_top_of_isEmpty
  given: [IsEmpty ι]
  statement: ⨅ i, (f i : Nat∞) = ⊤
  proof: iInf_natCast_eq_top.mpr ‹_›

中文:
引理 iInf_eq_top_of_isEmpty
  条件: [是空 ι]
  结论: ⨅ i, (f i : 自然数∞) = ⊤
  证明: iInf_natCast_eq_top.mpr ‹_›

Depends on / 依赖: iInf_natCast_eq_top, iInf_natCast_eq_top.mpr
-/
lemma iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (f i : Nat∞) = ⊤ :=
  iInf_natCast_eq_top.mpr ‹_›

/--
lemma `iInf_eq_natCast_iff` / 引理 `iInf_eq_natCast_iff`

English:
lemma iInf_eq_natCast_iff
  given: {f : ι -> Nat∞} {n : Nat}
  proof: by
  by_cases! hι : IsEmpty ι
  · simp [iInf_of_isEmpty]
  apply ciInf_eq_iff

@[deprecated (since := "2026-07-17")] alias iInf_eq_coe_iff := iInf_eq_natCast_iff

中文:
引理 iInf_eq_natCast_iff
  条件: {f : ι -> 自然数∞} {n : 自然数}
  证明: by
  by_cases! hι : IsEmpty ι
  · simp [iInf_of_isEmpty]
  apply ciInf_eq_iff

@[deprecated (since := "2026-07-17")] alias iInf_eq_coe_iff := iInf_eq_natCast_iff

Depends on / 依赖: IsEmpty, ciInf_eq_iff, iInf_of_isEmpty
-/
lemma iInf_eq_natCast_iff {f : ι -> Nat∞} {n : Nat} :
    ⨅ i, f i = n ↔ (exists i, f i = n) ∧ forall i, n <= f i := by
  by_cases! hι : IsEmpty ι
  · simp [iInf_of_isEmpty]
  apply ciInf_eq_iff

@[deprecated (since := "2026-07-17")] alias iInf_eq_coe_iff := iInf_eq_natCast_iff

/--
lemma `iInf_toNat` / 引理 `iInf_toNat`

English:
lemma iInf_toNat
  statement: (⨅ i, (f i : Nat∞)).toNat = ⨅ i, f i
  proof: by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast

中文:
引理 iInf_to自然数
  结论: (⨅ i, (f i : 自然数∞)).to自然数 = ⨅ i, f i
  证明: by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast

Depends on / 依赖: isEmpty_or_nonempty
-/
lemma iInf_toNat : (⨅ i, (f i : Nat∞)).toNat = ⨅ i, f i := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast

/--
lemma `iInf_eq_zero` / 引理 `iInf_eq_zero`

English:
lemma iInf_eq_zero
  given: {f : ι -> Nat∞}
  statement: ⨅ i, f i = 0 ↔ exists i, f i = 0
  proof: by
  simpa [Order.lt_one_iff] using iInf_lt_iff (α := Nat∞) (a := 1)

中文:
引理 iInf_eq_zero
  条件: {f : ι -> 自然数∞}
  结论: ⨅ i, f i = 0 ↔ 存在 i, f i = 0
  证明: by
  simpa [Order.lt_one_iff] using iInf_lt_iff (α := Nat∞) (a := 1)
-/
@[simp] lemma iInf_eq_zero {f : ι -> Nat∞} : ⨅ i, f i = 0 ↔ exists i, f i = 0 := by
  simpa [Order.lt_one_iff] using iInf_lt_iff (α := Nat∞) (a := 1)

variable {f : ι -> Nat∞} {s : Set Nat∞}

/--
lemma `sSup_eq_zero` / 引理 `sSup_eq_zero`

English:
lemma sSup_eq_zero
  statement: sSup s = 0 ↔ forall a in s, a = 0
  proof: sSup_eq_bot

中文:
引理 sSup_eq_zero
  结论: sSup s = 0 ↔ 对任意 a in s, a = 0
  证明: sSup_eq_bot

Depends on / 依赖: sSup_eq_bot
-/
lemma sSup_eq_zero : sSup s = 0 ↔ forall a in s, a = 0 :=
  sSup_eq_bot

/--
lemma `sInf_eq_zero` / 引理 `sInf_eq_zero`

English:
lemma sInf_eq_zero
  statement: sInf s = 0 ↔ 0 in s
  proof: by
  rw [← Order.lt_one_iff]; rw [sInf_lt_iff]
  simp

中文:
引理 sInf_eq_zero
  结论: sInf s = 0 ↔ 0 in s
  证明: by
  rw [← Order.lt_one_iff]; rw [sInf_lt_iff]
  simp

Depends on / 依赖: Order.lt_one_iff, lt_one_iff, sInf_lt_iff
-/
lemma sInf_eq_zero : sInf s = 0 ↔ 0 in s := by
  rw [← Order.lt_one_iff]; rw [sInf_lt_iff]
  simp

/--
lemma `sSup_eq_zero'` / 引理 `sSup_eq_zero'`

English:
lemma sSup_eq_zero'
  statement: sSup s = 0 ↔ s = ∅ ∨ s = {0}
  proof: sSup_eq_bot'

中文:
引理 sSup_eq_zero'
  结论: sSup s = 0 ↔ s = ∅ ∨ s = {0}
  证明: sSup_eq_bot'

Depends on / 依赖: sSup_eq_bot
-/
lemma sSup_eq_zero' : sSup s = 0 ↔ s = ∅ ∨ s = {0} :=
  sSup_eq_bot'

/--
lemma `iSup_eq_zero` / 引理 `iSup_eq_zero`

English:
lemma iSup_eq_zero
  statement: iSup f = 0 ↔ forall i, f i = 0
  proof: iSup_eq_bot

中文:
引理 iSup_eq_zero
  结论: iSup f = 0 ↔ 对任意 i, f i = 0
  证明: iSup_eq_bot
-/
@[simp] lemma iSup_eq_zero : iSup f = 0 ↔ forall i, f i = 0 := iSup_eq_bot
/--
lemma `iSup_zero` / 引理 `iSup_zero`

English:
lemma iSup_zero
  statement: ⨆ _ : ι, (0 : Nat∞) = 0
  proof: by simp

中文:
引理 iSup_zero
  结论: ⨆ _ : ι, (0 : 自然数∞) = 0
  证明: by simp
-/
@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : Nat∞) = 0 := by simp

/--
lemma `sSup_eq_top_of_infinite` / 引理 `sSup_eq_top_of_infinite`

English:
lemma sSup_eq_top_of_infinite
  given: (h : s.Infinite)
  statement: sSup s = ⊤
  proof: by
  apply (sSup_eq_top ..).mpr
  intro x hx
  cases x with
  | top => simp at hx
  | coe x =>
    contrapose! h
apply Finite.subset Finite.Set.finite_image {n : Nat | n <= x} (fun (n : Nat) => (n : Nat∞))
    intro y hy
    specialize h y hy
    have hxt : y < ⊤ := lt_of_le_of_lt h hx
    use y.toNat
    simp [toNat_le_of_le_natCast h, LT.lt.ne_top hxt]

中文:
引理 sSup_eq_top_of_infinite
  条件: (h : s.无限)
  结论: sSup s = ⊤
  证明: by
  apply (sSup_eq_top ..).mpr
  intro x hx
  cases x with
  | top => simp at hx
  | coe x =>
    contrapose! h
apply Finite.subset Finite.Set.finite_image {n : Nat | n <= x} (fun (n : Nat) => (n : Nat∞))
    intro y hy
    specialize h y hy
    have hxt : y < ⊤ := lt_of_le_of_lt h hx
    use y.toNat
    simp [toNat_le_of_le_natCast h, LT.lt.ne_top hxt]

Depends on / 依赖: Finite, Finite.Set.finite_image, Finite.subset, LT.lt.ne_top, contrapose, finite_image, lt_of_le_of_lt, ne_top, sSup_eq_top, specialize, subset, toNat_le_of_le_natCast, y.toNat
-/
lemma sSup_eq_top_of_infinite (h : s.Infinite) : sSup s = ⊤ := by
  apply (sSup_eq_top ..).mpr
  intro x hx
  cases x with
  | top => simp at hx
  | coe x =>
    contrapose! h
apply Finite.subset Finite.Set.finite_image {n : Nat | n <= x} (fun (n : Nat) => (n : Nat∞))
    intro y hy
    specialize h y hy
    have hxt : y < ⊤ := lt_of_le_of_lt h hx
    use y.toNat
    simp [toNat_le_of_le_natCast h, LT.lt.ne_top hxt]

/--
lemma `finite_of_sSup_lt_top` / 引理 `finite_of_sSup_lt_top`

English:
lemma finite_of_sSup_lt_top
  given: (h : sSup s < ⊤)
  statement: s.Finite
  proof: by
  contrapose! h
  simp only [top_le_iff]
  exact sSup_eq_top_of_infinite h

中文:
引理 finite_of_sSup_lt_top
  条件: (h : sSup s < ⊤)
  结论: s.有限
  证明: by
  contrapose! h
  simp only [top_le_iff]
  exact sSup_eq_top_of_infinite h

Depends on / 依赖: contrapose, sSup_eq_top_of_infinite, top_le_iff
-/
lemma finite_of_sSup_lt_top (h : sSup s < ⊤) : s.Finite := by
  contrapose! h
  simp only [top_le_iff]
  exact sSup_eq_top_of_infinite h

/--
lemma `sSup_mem_of_nonempty_of_lt_top` / 引理 `sSup_mem_of_nonempty_of_lt_top`

English:
lemma sSup_mem_of_nonempty_of_lt_top
  given: [Nonempty s] (hs' : sSup s < ⊤)
  statement: sSup s in s
  proof: Nonempty.csSup_mem .of_subtype (finite_of_sSup_lt_top hs')

中文:
引理 sSup_mem_of_nonempty_of_lt_top
  条件: [非空 s] (hs' : sSup s < ⊤)
  结论: sSup s in s
  证明: Nonempty.csSup_mem .of_subtype (finite_of_sSup_lt_top hs')

Depends on / 依赖: Nonempty, Nonempty.csSup_mem, csSup_mem, finite_of_sSup_lt_top, of_subtype
-/
lemma sSup_mem_of_nonempty_of_lt_top [Nonempty s] (hs' : sSup s < ⊤) : sSup s in s :=
  Nonempty.csSup_mem .of_subtype (finite_of_sSup_lt_top hs')

/--
lemma `exists_eq_iSup_of_lt_top` / 引理 `exists_eq_iSup_of_lt_top`

English:
lemma exists_eq_iSup_of_lt_top
  given: [Nonempty ι] (h : ⨆ i, f i < ⊤)
  proof: sSup_mem_of_nonempty_of_lt_top h

中文:
引理 存在_eq_iSup_of_lt_top
  条件: [非空 ι] (h : ⨆ i, f i < ⊤)
  证明: sSup_mem_of_nonempty_of_lt_top h

Depends on / 依赖: sSup_mem_of_nonempty_of_lt_top
-/
lemma exists_eq_iSup_of_lt_top [Nonempty ι] (h : ⨆ i, f i < ⊤) :
    exists i, f i = ⨆ i, f i :=
  sSup_mem_of_nonempty_of_lt_top h

/--
lemma `exists_eq_iInf` / 引理 `exists_eq_iInf`

English:
lemma exists_eq_iInf
  given: [Nonempty ι] (f : ι -> Nat∞)
  statement: exists a, f a = ⨅ x, f x
  proof: csInf_mem (range_nonempty fun i => f i)

中文:
引理 存在_eq_iInf
  条件: [非空 ι] (f : ι -> 自然数∞)
  结论: 存在 a, f a = ⨅ x, f x
  证明: csInf_mem (range_nonempty fun i => f i)

Depends on / 依赖: csInf_mem, range_nonempty
-/
lemma exists_eq_iInf [Nonempty ι] (f : ι -> Nat∞) : exists a, f a = ⨅ x, f x :=
  csInf_mem (range_nonempty fun i => f i)

/--
lemma `exists_eq_iSup₂_of_lt_top` / 引理 `exists_eq_iSup₂_of_lt_top`

English:
lemma exists_eq_iSup₂_of_lt_top
  statement: {ι₁ ι₂ : Type*} {f : ι₁ -> ι₂ -> Nat∞} [Nonempty ι₁] [Nonempty ι₂]
  proof: by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

中文:
引理 存在_eq_iSup₂_of_lt_top
  结论: {ι₁ ι₂ : 类型} {f : ι₁ -> ι₂ -> 自然数∞} [非空 ι₁] [非空 ι₂]
  证明: by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

Depends on / 依赖: Prod.exists, exists_eq_iSup_of_lt_top, iSup_prod
-/
lemma exists_eq_iSup₂_of_lt_top {ι₁ ι₂ : Type*} {f : ι₁ -> ι₂ -> Nat∞} [Nonempty ι₁] [Nonempty ι₂]
    (h : ⨆ i, ⨆ j, f i j < ⊤) : exists i j, f i j = ⨆ i, ⨆ j, f i j := by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

variable {ι κ : Sort*} {f g : ι -> Nat∞} {s : Set Nat∞} {a : Nat∞}

/--
lemma `iSup_natCast` / 引理 `iSup_natCast`

English:
lemma iSup_natCast
  statement: ⨆ n : Nat, (n : Nat∞) = ⊤
  proof: iSup_eq_top.2 fun _b hb => ENat.exists_nat_gt (lt_top_iff_ne_top.1 hb)

中文:
引理 iSup_natCast
  结论: ⨆ n : 自然数, (n : 自然数∞) = ⊤
  证明: iSup_eq_top.2 fun _b hb => ENat.exists_nat_gt (lt_top_iff_ne_top.1 hb)

Depends on / 依赖: ENat.exists_nat_gt, exists_nat_gt, iSup_eq_top, lt_top_iff_ne_top
-/
lemma iSup_natCast : ⨆ n : Nat, (n : Nat∞) = ⊤ :=
  iSup_eq_top.2 fun _b hb => ENat.exists_nat_gt (lt_top_iff_ne_top.1 hb)

/--
lemma `mul_iSup` / 引理 `mul_iSup`

English:
lemma mul_iSup
  given: (a : Nat∞) (f : ι -> Nat∞)
  statement: a * ⨆ i, f i = ⨆ i, a * f i
  proof: by
refine (iSup_le fun i => mul_le_mul' rfl.le <| le_iSup_iff.2 fun _ a => a i).antisymm'
    le_iSup_iff.2 fun d h => ?_
  obtain rfl | hne := eq_or_ne a 0
  · simp
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  cases d with
  | top => simp
  | coe d =>
  have hlt : ⨆ i, f i < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨i, hi : d < f i⟩ := (iSup_eq_top ..).1 htop d (by simp)
    exact (((h i).trans_lt hi).trans_le (ENat.self_le_mul_left _ hne)).false
  obtain ⟨j, hj⟩ := exists_eq_iSup_of_lt_top hlt
  rw [← hj]
  apply h

中文:
引理 mul_iSup
  条件: (a : 自然数∞) (f : ι -> 自然数∞)
  结论: a * ⨆ i, f i = ⨆ i, a * f i
  证明: by
refine (iSup_le fun i => mul_le_mul' rfl.le <| le_iSup_iff.2 fun _ a => a i).antisymm'
    le_iSup_iff.2 fun d h => ?_
  obtain rfl | hne := eq_or_ne a 0
  · simp
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  cases d with
  | top => simp
  | coe d =>
  have hlt : ⨆ i, f i < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨i, hi : d < f i⟩ := (iSup_eq_top ..).1 htop d (by simp)
    exact (((h i).trans_lt hi).trans_le (ENat.self_le_mul_left _ hne)).false
  obtain ⟨j, hj⟩ := exists_eq_iSup_of_lt_top hlt
  rw [← hj]
  apply h

Depends on / 依赖: ENat.self_le_mul_left, antisymm, eq_or_ne, exists_eq_iSup_of_lt_top, iSup_eq_top, iSup_le, isEmpty_or_nonempty, le_iSup_iff, lt_top_iff_ne_top, mul_le_mul, rfl.le, self_le_mul_left, trans_le, trans_lt
-/
lemma mul_iSup (a : Nat∞) (f : ι -> Nat∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
refine (iSup_le fun i => mul_le_mul' rfl.le <| le_iSup_iff.2 fun _ a => a i).antisymm'
    le_iSup_iff.2 fun d h => ?_
  obtain rfl | hne := eq_or_ne a 0
  · simp
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  cases d with
  | top => simp
  | coe d =>
  have hlt : ⨆ i, f i < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨i, hi : d < f i⟩ := (iSup_eq_top ..).1 htop d (by simp)
    exact (((h i).trans_lt hi).trans_le (ENat.self_le_mul_left _ hne)).false
  obtain ⟨j, hj⟩ := exists_eq_iSup_of_lt_top hlt
  rw [← hj]
  apply h

/--
lemma `iSup_mul` / 引理 `iSup_mul`

English:
lemma iSup_mul
  given: (f : ι -> Nat∞) (a : Nat∞)
  statement: (⨆ i, f i) * a = ⨆ i, f i * a
  proof: by
  simp_rw [mul_comm, ENat.mul_iSup]

中文:
引理 iSup_mul
  条件: (f : ι -> 自然数∞) (a : 自然数∞)
  结论: (⨆ i, f i) * a = ⨆ i, f i * a
  证明: by
  simp_rw [mul_comm, ENat.mul_iSup]

Depends on / 依赖: ENat.mul_iSup, mul_comm, mul_iSup, simp_rw
-/
lemma iSup_mul (f : ι -> Nat∞) (a : Nat∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp_rw [mul_comm, ENat.mul_iSup]

/--
lemma `mul_sSup` / 引理 `mul_sSup`

English:
lemma mul_sSup
  statement: a * sSup s = ⨆ b in s, a * b
  proof: by
  simp_rw [sSup_eq_iSup, mul_iSup]

中文:
引理 mul_sSup
  结论: a * sSup s = ⨆ b in s, a * b
  证明: by
  simp_rw [sSup_eq_iSup, mul_iSup]

Depends on / 依赖: mul_iSup, sSup_eq_iSup, simp_rw
-/
lemma mul_sSup : a * sSup s = ⨆ b in s, a * b := by
  simp_rw [sSup_eq_iSup, mul_iSup]

/--
lemma `sSup_mul` / 引理 `sSup_mul`

English:
lemma sSup_mul
  statement: sSup s * a = ⨆ b in s, b * a
  proof: by
  simp_rw [mul_comm, mul_sSup]

中文:
引理 sSup_mul
  结论: sSup s * a = ⨆ b in s, b * a
  证明: by
  simp_rw [mul_comm, mul_sSup]

Depends on / 依赖: mul_comm, mul_sSup, simp_rw
-/
lemma sSup_mul : sSup s * a = ⨆ b in s, b * a := by
  simp_rw [mul_comm, mul_sSup]

/--
lemma `mul_iInf` / 引理 `mul_iInf`

English:
lemma mul_iInf
  given: [Nonempty ι]
  statement: a * ⨅ i, f i = ⨅ i, a * f i
  proof: by
  refine (le_iInf fun x => by grw [iInf_le]).antisymm ?_
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf f
  rw [← hb]; rw [iInf_le_iff]
  exact fun x h => h _

中文:
引理 mul_iInf
  条件: [非空 ι]
  结论: a * ⨅ i, f i = ⨅ i, a * f i
  证明: by
  refine (le_iInf fun x => by grw [iInf_le]).antisymm ?_
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf f
  rw [← hb]; rw [iInf_le_iff]
  exact fun x h => h _

Depends on / 依赖: ENat.exists_eq_iInf, antisymm, exists_eq_iInf, iInf_le, iInf_le_iff, le_iInf
-/
lemma mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i := by
  refine (le_iInf fun x => by grw [iInf_le]).antisymm ?_
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf f
  rw [← hb]; rw [iInf_le_iff]
  exact fun x h => h _

/--
lemma `iInf_mul` / 引理 `iInf_mul`

English:
lemma iInf_mul
  given: [Nonempty ι]
  statement: (⨅ i, f i) * a = ⨅ i, f i * a
  proof: by
  simp_rw [mul_comm, mul_iInf]

中文:
引理 iInf_mul
  条件: [非空 ι]
  结论: (⨅ i, f i) * a = ⨅ i, f i * a
  证明: by
  simp_rw [mul_comm, mul_iInf]

Depends on / 依赖: mul_comm, mul_iInf, simp_rw
-/
lemma iInf_mul [Nonempty ι] : (⨅ i, f i) * a = ⨅ i, f i * a := by
  simp_rw [mul_comm, mul_iInf]

/--
lemma `mul_iInf'` / 引理 `mul_iInf'`

English:
lemma mul_iInf'
  given: (h₀ : a = 0 -> Nonempty ι)
  statement: a * ⨅ i, f i = ⨅ i, a * f i
  proof: by
  obtain hι | hι := isEmpty_or_nonempty ι
  · suffices a != 0 by simpa [iInf_of_empty, ite_eq_right_iff, mul_top']
    aesop
  rw [mul_iInf]

中文:
引理 mul_iInf'
  条件: (h₀ : a = 0 -> 非空 ι)
  结论: a * ⨅ i, f i = ⨅ i, a * f i
  证明: by
  obtain hι | hι := isEmpty_or_nonempty ι
  · suffices a != 0 by simpa [iInf_of_empty, ite_eq_right_iff, mul_top']
    aesop
  rw [mul_iInf]

Depends on / 依赖: iInf_of_empty, isEmpty_or_nonempty, ite_eq_right_iff, mul_iInf, mul_top
-/
lemma mul_iInf' (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · suffices a != 0 by simpa [iInf_of_empty, ite_eq_right_iff, mul_top']
    aesop
  rw [mul_iInf]

/--
lemma `iInf_mul'` / 引理 `iInf_mul'`

English:
lemma iInf_mul'
  given: (h₀ : a = 0 -> Nonempty ι)
  statement: (⨅ i, f i) * a = ⨅ i, f i * a
  proof: by
  simp_rw [mul_comm, mul_iInf' h₀]

中文:
引理 iInf_mul'
  条件: (h₀ : a = 0 -> 非空 ι)
  结论: (⨅ i, f i) * a = ⨅ i, f i * a
  证明: by
  simp_rw [mul_comm, mul_iInf' h₀]

Depends on / 依赖: mul_comm, mul_iInf, simp_rw
-/
lemma iInf_mul' (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a := by
  simp_rw [mul_comm, mul_iInf' h₀]

/--
lemma `mul_iInf_of_ne` / 引理 `mul_iInf_of_ne`

English:
lemma mul_iInf_of_ne
  given: (ha₀ : a != 0)
  statement: a * ⨅ i, f i = ⨅ i, a * f i
  proof: mul_iInf' by simp [ha₀]

中文:
引理 mul_iInf_of_ne
  条件: (ha₀ : a != 0)
  结论: a * ⨅ i, f i = ⨅ i, a * f i
  证明: mul_iInf' by simp [ha₀]

Depends on / 依赖: mul_iInf
-/
lemma mul_iInf_of_ne (ha₀ : a != 0) : a * ⨅ i, f i = ⨅ i, a * f i :=
mul_iInf' by simp [ha₀]

/--
lemma `iInf_mul_of_ne` / 引理 `iInf_mul_of_ne`

English:
lemma iInf_mul_of_ne
  given: (ha₀ : a != 0)
  statement: (⨅ i, f i) * a = ⨅ i, f i * a
  proof: iInf_mul' by simp [ha₀]

中文:
引理 iInf_mul_of_ne
  条件: (ha₀ : a != 0)
  结论: (⨅ i, f i) * a = ⨅ i, f i * a
  证明: iInf_mul' by simp [ha₀]

Depends on / 依赖: iInf_mul
-/
lemma iInf_mul_of_ne (ha₀ : a != 0) : (⨅ i, f i) * a = ⨅ i, f i * a :=
iInf_mul' by simp [ha₀]

/--
lemma `add_iSup` / 引理 `add_iSup`

English:
lemma add_iSup
  given: [Nonempty ι] (f : ι -> Nat∞)
  statement: a + ⨆ i, f i = ⨆ i, a + f i
  proof: by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
refine le_antisymm ?_ iSup_le fun i => by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
exact iSup_le fun i => ENat.le_sub_of_add_le_left ha le_iSup (a + f ·) i

中文:
引理 add_iSup
  条件: [非空 ι] (f : ι -> 自然数∞)
  结论: a + ⨆ i, f i = ⨆ i, a + f i
  证明: by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
refine le_antisymm ?_ iSup_le fun i => by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
exact iSup_le fun i => ENat.le_sub_of_add_le_left ha le_iSup (a + f ·) i

Depends on / 依赖: Classical, Classical.arbitrary, ENat.le_sub_of_add_le_left, add_le_of_le_tsub_left_of_le, arbitrary, eq_or_ne, iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_self_add, le_sub_of_add_le_left
-/
lemma add_iSup [Nonempty ι] (f : ι -> Nat∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
refine le_antisymm ?_ iSup_le fun i => by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
exact iSup_le fun i => ENat.le_sub_of_add_le_left ha le_iSup (a + f ·) i

/--
lemma `iSup_add` / 引理 `iSup_add`

English:
lemma iSup_add
  given: [Nonempty ι] (f : ι -> Nat∞)
  statement: (⨆ i, f i) + a = ⨆ i, f i + a
  proof: by
  simp [add_comm, add_iSup]

中文:
引理 iSup_add
  条件: [非空 ι] (f : ι -> 自然数∞)
  结论: (⨆ i, f i) + a = ⨆ i, f i + a
  证明: by
  simp [add_comm, add_iSup]

Depends on / 依赖: add_comm, add_iSup
-/
lemma iSup_add [Nonempty ι] (f : ι -> Nat∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]

/--
lemma `add_biSup'` / 引理 `add_biSup'`

English:
lemma add_biSup'
  given: {p : ι -> Prop} (h : exists i, p i) (f : ι -> Nat∞)
  proof: by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

中文:
引理 add_biSup'
  条件: {p : ι -> 命题} (h : 存在 i, p i) (f : ι -> 自然数∞)
  证明: by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

Depends on / 依赖: Nonempty, add_iSup, iSup_subtype, nonempty_subtype
-/
lemma add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Nat∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

/--
lemma `biSup_add'` / 引理 `biSup_add'`

English:
lemma biSup_add'
  given: {p : ι -> Prop} (h : exists i, p i) (f : ι -> Nat∞)
  proof: by simp only [add_comm, add_biSup' h]

中文:
引理 biSup_add'
  条件: {p : ι -> 命题} (h : 存在 i, p i) (f : ι -> 自然数∞)
  证明: by simp only [add_comm, add_biSup' h]

Depends on / 依赖: add_biSup, add_comm
-/
lemma biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Nat∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]

/--
lemma `add_biSup` / 引理 `add_biSup`

English:
lemma add_biSup
  given: {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Nat∞)
  proof: add_biSup' hs _

中文:
引理 add_biSup
  条件: {ι : 类型} {s : 集合 ι} (hs : s.非空) (f : ι -> 自然数∞)
  证明: add_biSup' hs _

Depends on / 依赖: add_biSup
-/
lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Nat∞) :
    a + ⨆ i in s, f i = ⨆ i in s, a + f i := add_biSup' hs _

/--
lemma `biSup_add` / 引理 `biSup_add`

English:
lemma biSup_add
  given: {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Nat∞)
  proof: biSup_add' hs _

中文:
引理 biSup_add
  条件: {ι : 类型} {s : 集合 ι} (hs : s.非空) (f : ι -> 自然数∞)
  证明: biSup_add' hs _

Depends on / 依赖: biSup_add
-/
lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Nat∞) :
    (⨆ i in s, f i) + a = ⨆ i in s, f i + a := biSup_add' hs _

/--
lemma `add_sSup` / 引理 `add_sSup`

English:
lemma add_sSup
  given: (hs : s.Nonempty)
  statement: a + sSup s = ⨆ b in s, a + b
  proof: by
  rw [sSup_eq_iSup]; rw [add_biSup hs]

中文:
引理 add_sSup
  条件: (hs : s.非空)
  结论: a + sSup s = ⨆ b in s, a + b
  证明: by
  rw [sSup_eq_iSup]; rw [add_biSup hs]

Depends on / 依赖: add_biSup, sSup_eq_iSup
-/
lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b in s, a + b := by
  rw [sSup_eq_iSup]; rw [add_biSup hs]

/--
lemma `sSup_add` / 引理 `sSup_add`

English:
lemma sSup_add
  given: (hs : s.Nonempty)
  statement: sSup s + a = ⨆ b in s, b + a
  proof: by
  rw [sSup_eq_iSup]; rw [biSup_add hs]

中文:
引理 sSup_add
  条件: (hs : s.非空)
  结论: sSup s + a = ⨆ b in s, b + a
  证明: by
  rw [sSup_eq_iSup]; rw [biSup_add hs]

Depends on / 依赖: biSup_add, sSup_eq_iSup
-/
lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b in s, b + a := by
  rw [sSup_eq_iSup]; rw [biSup_add hs]

/--
lemma `iSup_add_iSup_le` / 引理 `iSup_add_iSup_le`

English:
lemma iSup_add_iSup_le
  given: [Nonempty ι] [Nonempty κ] {g : κ -> Nat∞} (h : forall i j, f i + g j <= a)
  proof: by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

中文:
引理 iSup_add_iSup_le
  条件: [非空 ι] [非空 κ] {g : κ -> 自然数∞} (h : 对任意 i j, f i + g j <= a)
  证明: by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

Depends on / 依赖: add_iSup, iSup_add, simp_rw
-/
lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ -> Nat∞} (h : forall i j, f i + g j <= a) :
    iSup f + iSup g <= a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

/--
lemma `biSup_add_biSup_le'` / 引理 `biSup_add_biSup_le'`

English:
lemma biSup_add_biSup_le'
  statement: {p : ι -> Prop} {q : κ -> Prop} (hp : exists i, p i) (hq : exists j, q j)
  proof: by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

中文:
引理 biSup_add_biSup_le'
  结论: {p : ι -> 命题} {q : κ -> 命题} (hp : 存在 i, p i) (hq : 存在 j, q j)
  证明: by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

Depends on / 依赖: add_biSup, biSup_add, simp_rw
-/
lemma biSup_add_biSup_le' {p : ι -> Prop} {q : κ -> Prop} (hp : exists i, p i) (hq : exists j, q j)
    {g : κ -> Nat∞} (h : forall i, p i -> forall j, q j -> f i + g j <= a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j <= a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

/--
lemma `biSup_add_biSup_le` / 引理 `biSup_add_biSup_le`

English:
lemma biSup_add_biSup_le
  statement: {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
  proof: biSup_add_biSup_le' hs ht h

中文:
引理 biSup_add_biSup_le
  结论: {ι κ : 类型} {s : 集合 ι} {t : 集合 κ} (hs : s.非空) (ht : t.非空)
  证明: biSup_add_biSup_le' hs ht h

Depends on / 依赖: biSup_add_biSup_le
-/
lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι -> Nat∞} {g : κ -> Nat∞} {a : Nat∞} (h : forall i in s, forall j in t, f i + g j <= a) :
    (⨆ i in s, f i) + ⨆ j in t, g j <= a := biSup_add_biSup_le' hs ht h

/--
lemma `iSup_add_iSup` / 引理 `iSup_add_iSup`

English:
lemma iSup_add_iSup
  given: (h : forall i j, exists k, f i + g j <= f k + g k)
  statement: iSup f + iSup g = ⨆ i, f i + g i
  proof: by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

中文:
引理 iSup_add_iSup
  条件: (h : 对任意 i j, 存在 k, f i + g j <= f k + g k)
  结论: iSup f + iSup g = ⨆ i, f i + g i
  证明: by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

Depends on / 依赖: add_le_add, iSup_add_iSup_le, iSup_le, isEmpty_or_nonempty, le_antisymm, le_iSup, le_iSup_of_le
-/
lemma iSup_add_iSup (h : forall i j, exists k, f i + g j <= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

/--
lemma `iSup_add_iSup_of_monotone` / 引理 `iSup_add_iSup_of_monotone`

English:
lemma iSup_add_iSup_of_monotone
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> Nat∞}
  proof: iSup_add_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

中文:
引理 iSup_add_iSup_of_monotone
  结论: {ι : 类型} [预序 ι] [IsDirectedOrder ι] {f g : ι -> 自然数∞}
  证明: iSup_add_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

Depends on / 依赖: apply_rules, exists_ge_ge, iSup_add_iSup
-/
lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> Nat∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

/--
lemma `smul_iSup` / 引理 `smul_iSup`

English:
lemma smul_iSup
  given: {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] (f : ι -> Nat∞) (c : R)
  proof: by
  simpa using mul_iSup (c • 1) f

中文:
引理 smul_iSup
  条件: {R} [标量乘法 R 自然数∞] [标量塔 R 自然数∞ 自然数∞] (f : ι -> 自然数∞) (c : R)
  证明: by
  simpa using mul_iSup (c • 1) f

Depends on / 依赖: mul_iSup
-/
lemma smul_iSup {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] (f : ι -> Nat∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simpa using mul_iSup (c • 1) f

/--
lemma `smul_sSup` / 引理 `smul_sSup`

English:
lemma smul_sSup
  given: {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] (s : Set Nat∞) (c : R)
  proof: by
  simp_rw [sSup_eq_iSup, smul_iSup]

中文:
引理 smul_sSup
  条件: {R} [标量乘法 R 自然数∞] [标量塔 R 自然数∞ 自然数∞] (s : 集合 自然数∞) (c : R)
  证明: by
  simp_rw [sSup_eq_iSup, smul_iSup]

Depends on / 依赖: sSup_eq_iSup, simp_rw, smul_iSup
-/
lemma smul_sSup {R} [SMul R Nat∞] [IsScalarTower R Nat∞ Nat∞] (s : Set Nat∞) (c : R) :
    c • sSup s = ⨆ a in s, c • a := by
  simp_rw [sSup_eq_iSup, smul_iSup]

/--
lemma `sub_iSup` / 引理 `sub_iSup`

English:
lemma sub_iSup
  given: [Nonempty ι] (ha : a != ⊤)
  statement: a - ⨆ i, f i = ⨅ i, a - f i
  proof: by
  obtain ⟨i, hi⟩ | h := em (exists i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx => ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
refine le_antisymm (le_iInf fun i => tsub_le_tsub_left (le_iSup ..) _)
ENat.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h)
add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self)
    iSup_le fun i => ?_
  rw [← ENat.sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _

中文:
引理 sub_iSup
  条件: [非空 ι] (ha : a != ⊤)
  结论: a - ⨆ i, f i = ⨅ i, a - f i
  证明: by
  obtain ⟨i, hi⟩ | h := em (exists i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx => ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
refine le_antisymm (le_iInf fun i => tsub_le_tsub_left (le_iSup ..) _)
ENat.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h)
add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self)
    iSup_le fun i => ?_
  rw [← ENat.sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _

Depends on / 依赖: Classical, Classical.arbitrary, ENat.le_sub_of_add_le_left, ENat.sub_sub_cancel, add_le_of_le_tsub_right_of_le, arbitrary, bot_eq_zero, hi.le, iInf_eq_bot, iInf_le_of_le, iSup_le, le_antisymm, le_iInf, le_iSup, le_iSup_of_le, le_sub_of_add_le_left, ne_top_of_le_ne_top, not_exists, not_lt, simp_rw
-/
lemma sub_iSup [Nonempty ι] (ha : a != ⊤) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (exists i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx => ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
refine le_antisymm (le_iInf fun i => tsub_le_tsub_left (le_iSup ..) _)
ENat.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h)
add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self)
    iSup_le fun i => ?_
  rw [← ENat.sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _

/--
lemma `iInf_add` / 引理 `iInf_add`

English:
lemma iInf_add
  statement: iInf f + a = ⨅ i, f i + a
  proof: le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

中文:
引理 iInf_add
  结论: iInf f + a = ⨅ i, f i + a
  证明: le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

Depends on / 依赖: add_le_add, iInf_le, le_antisymm, le_iInf, le_rfl, tsub_le_iff_right
-/
lemma iInf_add : iInf f + a = ⨅ i, f i + a :=
le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

/--
theorem `sub_iInf` / 定理 `sub_iInf`

English:
theorem sub_iInf
  statement: (a - ⨅ i, f i) = ⨆ i, a - f i
  proof: by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right]; rw [add_comm]; rw [iInf_add]
  simp [tsub_le_iff_right, add_comm]

中文:
定理 sub_iInf
  结论: (a - ⨅ i, f i) = ⨆ i, a - f i
  证明: by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right]; rw [add_comm]; rw [iInf_add]
  simp [tsub_le_iff_right, add_comm]

Depends on / 依赖: add_comm, eq_of_forall_ge_iff, iInf_add, tsub_le_iff_right
-/
theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right]; rw [add_comm]; rw [iInf_add]
  simp [tsub_le_iff_right, add_comm]

/--
theorem `sInf_add` / 定理 `sInf_add`

English:
theorem sInf_add
  given: {s : Set Nat∞}
  statement: sInf s + a = ⨅ b in s, b + a
  proof: by simp [sInf_eq_iInf, iInf_add]

中文:
定理 sInf_add
  条件: {s : 集合 自然数∞}
  结论: sInf s + a = ⨅ b in s, b + a
  证明: by simp [sInf_eq_iInf, iInf_add]

Depends on / 依赖: iInf_add, sInf_eq_iInf
-/
theorem sInf_add {s : Set Nat∞} : sInf s + a = ⨅ b in s, b + a := by simp [sInf_eq_iInf, iInf_add]

/--
theorem `add_iInf` / 定理 `add_iInf`

English:
theorem add_iInf
  given: {a : Nat∞}
  statement: a + iInf f = ⨅ b, a + f b
  proof: by
  rw [add_comm]; rw [iInf_add]; simp [add_comm]

中文:
定理 add_iInf
  条件: {a : 自然数∞}
  结论: a + iInf f = ⨅ b, a + f b
  证明: by
  rw [add_comm]; rw [iInf_add]; simp [add_comm]

Depends on / 依赖: add_comm, iInf_add
-/
theorem add_iInf {a : Nat∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm]; rw [iInf_add]; simp [add_comm]

/--
theorem `iInf_add_iInf` / 定理 `iInf_add_iInf`

English:
theorem iInf_add_iInf
  given: (h : forall i j, exists k, f k + g k <= f i + g j)
  statement: iInf f + iInf g = ⨅ a, f a + g a
  proof: suffices ⨅ a, f a + g a <= iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a <= ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

中文:
定理 iInf_add_iInf
  条件: (h : 对任意 i j, 存在 k, f k + g k <= f i + g j)
  结论: iInf f + iInf g = ⨅ a, f a + g a
  证明: suffices ⨅ a, f a + g a <= iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a <= ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

Depends on / 依赖: add_iInf, add_le_add, iInf_add, iInf_le, iInf_le_of_le, le_antisymm, le_iInf, simp_rw
-/
theorem iInf_add_iInf (h : forall i j, exists k, f k + g k <= f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a <= iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a <= ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

/--
lemma `iInf_add_iInf_of_monotone` / 引理 `iInf_add_iInf_of_monotone`

English:
lemma iInf_add_iInf_of_monotone
  statement: {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> Nat∞}
  proof: iInf_add_iInf fun i j => (exists_le_le i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

中文:
引理 iInf_add_iInf_of_monotone
  结论: {ι : 类型} [预序 ι] [IsCodirectedOrder ι] {f g : ι -> 自然数∞}
  证明: iInf_add_iInf fun i j => (exists_le_le i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

Depends on / 依赖: apply_rules, exists_le_le, iInf_add_iInf
-/
lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> Nat∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j => (exists_le_le i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

/--
lemma `add_iInf₂` / 引理 `add_iInf₂`

English:
lemma add_iInf₂
  given: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Nat∞)
  proof: by
  simp [add_iInf]

中文:
引理 add_iInf₂
  条件: {κ : ι -> 类型层*} (f : (i : ι) -> κ i -> 自然数∞)
  证明: by
  simp [add_iInf]

Depends on / 依赖: add_iInf
-/
lemma add_iInf₂ {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Nat∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]

/--
lemma `iInf₂_add` / 引理 `iInf₂_add`

English:
lemma iInf₂_add
  given: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Nat∞)
  proof: by
  simp only [add_comm, add_iInf₂]

中文:
引理 iInf₂_add
  条件: {κ : ι -> 类型层*} (f : (i : ι) -> κ i -> 自然数∞)
  证明: by
  simp only [add_comm, add_iInf₂]

Depends on / 依赖: add_comm
-/
lemma iInf₂_add {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Nat∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]

/--
lemma `add_sInf` / 引理 `add_sInf`

English:
lemma add_sInf
  given: {s : Set Nat∞}
  statement: a + sInf s = ⨅ b in s, a + b
  proof: by
  rw [sInf_eq_iInf]; rw [add_iInf₂]

中文:
引理 add_sInf
  条件: {s : 集合 自然数∞}
  结论: a + sInf s = ⨅ b in s, a + b
  证明: by
  rw [sInf_eq_iInf]; rw [add_iInf₂]

Depends on / 依赖: sInf_eq_iInf
-/
lemma add_sInf {s : Set Nat∞} : a + sInf s = ⨅ b in s, a + b := by
  rw [sInf_eq_iInf]; rw [add_iInf₂]

variable {κ : Sort*}

/--
lemma `le_iInf_add_iInf` / 引理 `le_iInf_add_iInf`

English:
lemma le_iInf_add_iInf
  given: {g : κ -> Nat∞} (h : forall i j, a <= f i + g j)
  proof: by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

中文:
引理 le_iInf_add_iInf
  条件: {g : κ -> 自然数∞} (h : 对任意 i j, a <= f i + g j)
  证明: by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

Depends on / 依赖: add_iInf, iInf_add, simp_rw
-/
lemma le_iInf_add_iInf {g : κ -> Nat∞} (h : forall i j, a <= f i + g j) :
    a <= iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

/--
lemma `le_iInf₂_add_iInf₂` / 引理 `le_iInf₂_add_iInf₂`

English:
lemma le_iInf₂_add_iInf₂
  statement: {q₁ : ι -> Sort*} {q₂ : κ -> Sort*}
  proof: by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

中文:
引理 le_iInf₂_add_iInf₂
  结论: {q₁ : ι -> 类型层*} {q₂ : κ -> 类型层*}
  证明: by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

Depends on / 依赖: simp_rw
-/
lemma le_iInf₂_add_iInf₂ {q₁ : ι -> Sort*} {q₂ : κ -> Sort*}
    {f : (i : ι) -> q₁ i -> Nat∞} {g : (k : κ) -> q₂ k -> Nat∞}
    (h : forall i pi k qk, a <= f i pi + g k qk) :
    a <= (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

end ENat
