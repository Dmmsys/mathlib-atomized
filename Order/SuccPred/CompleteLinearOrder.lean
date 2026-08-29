/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.SuccPred.Limit

/-!

# Relation between `IsSuccPrelimit` and `iSup` in (conditionally) complete linear orders.

-/

@[expose] public section

open Order Set

variable {ι : Sort*} {α : Type*}

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [Nonempty ι] {f : ι -> α} {s : Set α} {x : α}

@[to_dual]
/--
lemma `csSup_mem_of_not_isSuccLimit` / 引理 `csSup_mem_of_not_isSuccLimit`

English:
lemma csSup_mem_of_not_isSuccLimit
  statement: (hne : s.Nonempty) (hbdd : BddAbove s)
  proof: by
  rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_not] at hlim
  rcases hlim with (hmin | hlim)
  · have ⟨a, has⟩ := hne
    rwa [← hmin.eq_of_le <| le_csSup hbdd has]
  · have ⟨y, hy⟩ := not_forall_not.mp hlim
    have ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
    exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

@[to_dual]

中文:
引理 csSup_mem_of_not_isSuccLimit
  结论: (hne : s.非空) (hbdd : BddAbove s)
  证明: by
  rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_not] at hlim
  rcases hlim with (hmin | hlim)
  · have ⟨a, has⟩ := hne
    rwa [← hmin.eq_of_le <| le_csSup hbdd has]
  · have ⟨y, hy⟩ := not_forall_not.mp hlim
    have ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
    exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

@[to_dual]

Depends on / 依赖: eq_of_le, eq_of_le_of_not_lt, exists_lt_of_lt_csSup, hmin.eq_of_le, hy.lt, isSuccLimit_iff, le_csSup, not_and_or, not_forall_not, not_forall_not.mp, not_not
-/
lemma csSup_mem_of_not_isSuccLimit (hne : s.Nonempty) (hbdd : BddAbove s)
    (hlim : ¬ IsSuccLimit (sSup s)) : sSup s in s := by
  rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_not] at hlim
  rcases hlim with (hmin | hlim)
  · have ⟨a, has⟩ := hne
    rwa [← hmin.eq_of_le <| le_csSup hbdd has]
  · have ⟨y, hy⟩ := not_forall_not.mp hlim
    have ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
    exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

@[to_dual]
/--
lemma `exists_eq_ciSup_of_not_isSuccLimit` / 引理 `exists_eq_ciSup_of_not_isSuccLimit`

English:
lemma exists_eq_ciSup_of_not_isSuccLimit
  statement: (hbdd : BddAbove (range f))
  proof: csSup_mem_of_not_isSuccLimit (range_nonempty f) hbdd hf

@[deprecated csInf_mem_of_not_isPredLimit (since := "2026-04-24")]

中文:
引理 存在_eq_ciSup_of_not_isSuccLimit
  结论: (hbdd : BddAbove (range f))
  证明: csSup_mem_of_not_isSuccLimit (range_nonempty f) hbdd hf

@[deprecated csInf_mem_of_not_isPredLimit (since := "2026-04-24")]

Depends on / 依赖: csSup_mem_of_not_isSuccLimit, range_nonempty
-/
lemma exists_eq_ciSup_of_not_isSuccLimit (hbdd : BddAbove (range f))
    (hf : ¬ IsSuccLimit (⨆ i, f i)) : exists i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccLimit (range_nonempty f) hbdd hf

@[deprecated csInf_mem_of_not_isPredLimit (since := "2026-04-24")]
/--
lemma `csInf_mem_of_not_isPredPrelimit` / 引理 `csInf_mem_of_not_isPredPrelimit`

English:
lemma csInf_mem_of_not_isPredPrelimit
  statement: (hne : s.Nonempty) (hbdd : BddBelow s)
  proof: csInf_mem_of_not_isPredLimit hne hbdd mt IsPredLimit.isPredPrelimit hlim

@[deprecated exists_eq_ciInf_of_not_isPredLimit (since := "2026-04-24")]

中文:
引理 csInf_mem_of_not_isPredPrelimit
  结论: (hne : s.非空) (hbdd : BddBelow s)
  证明: csInf_mem_of_not_isPredLimit hne hbdd mt IsPredLimit.isPredPrelimit hlim

@[deprecated exists_eq_ciInf_of_not_isPredLimit (since := "2026-04-24")]

Depends on / 依赖: IsPredLimit, IsPredLimit.isPredPrelimit, csInf_mem_of_not_isPredLimit, isPredPrelimit
-/
lemma csInf_mem_of_not_isPredPrelimit (hne : s.Nonempty) (hbdd : BddBelow s)
    (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s in s :=
csInf_mem_of_not_isPredLimit hne hbdd mt IsPredLimit.isPredPrelimit hlim

@[deprecated exists_eq_ciInf_of_not_isPredLimit (since := "2026-04-24")]
/--
lemma `exists_eq_ciInf_of_not_isPredPrelimit` / 引理 `exists_eq_ciInf_of_not_isPredPrelimit`

English:
lemma exists_eq_ciInf_of_not_isPredPrelimit
  statement: (hf : BddBelow (range f))
  proof: exists_eq_ciInf_of_not_isPredLimit hf mt IsPredLimit.isPredPrelimit hf'

@[to_dual]

中文:
引理 存在_eq_ciInf_of_not_isPredPrelimit
  结论: (hf : BddBelow (range f))
  证明: exists_eq_ciInf_of_not_isPredLimit hf mt IsPredLimit.isPredPrelimit hf'

@[to_dual]

Depends on / 依赖: IsPredLimit, IsPredLimit.isPredPrelimit, exists_eq_ciInf_of_not_isPredLimit, isPredPrelimit
-/
lemma exists_eq_ciInf_of_not_isPredPrelimit (hf : BddBelow (range f))
    (hf' : ¬ IsPredPrelimit (⨅ i, f i)) : exists i, f i = ⨅ i, f i :=
exists_eq_ciInf_of_not_isPredLimit hf mt IsPredLimit.isPredPrelimit hf'

@[to_dual]
/--
lemma `IsLUB.mem_of_nonempty_of_not_isSuccLimit` / 引理 `IsLUB.mem_of_nonempty_of_not_isSuccLimit`

English:
lemma IsLUB.mem_of_nonempty_of_not_isSuccLimit
  statement: (hs : IsLUB s x) (hne : s.Nonempty)
  proof: hs.csSup_eq hne ▸ csSup_mem_of_not_isSuccLimit hne hs.bddAbove (hs.csSup_eq hne ▸ hx)

@[to_dual]

中文:
引理 IsLUB.mem_of_nonempty_of_not_isSuccLimit
  结论: (hs : IsLUB s x) (hne : s.非空)
  证明: hs.csSup_eq hne ▸ csSup_mem_of_not_isSuccLimit hne hs.bddAbove (hs.csSup_eq hne ▸ hx)

@[to_dual]

Depends on / 依赖: bddAbove, csSup_eq, csSup_mem_of_not_isSuccLimit, hs.bddAbove, hs.csSup_eq
-/
lemma IsLUB.mem_of_nonempty_of_not_isSuccLimit (hs : IsLUB s x) (hne : s.Nonempty)
    (hx : ¬ IsSuccLimit x) : x in s :=
  hs.csSup_eq hne ▸ csSup_mem_of_not_isSuccLimit hne hs.bddAbove (hs.csSup_eq hne ▸ hx)

@[to_dual]
/--
lemma `IsLUB.exists_of_nonempty_of_not_isSuccLimit` / 引理 `IsLUB.exists_of_nonempty_of_not_isSuccLimit`

English:
lemma IsLUB.exists_of_nonempty_of_not_isSuccLimit
  given: (hf : IsLUB (range f) x) (hx : ¬ IsSuccLimit x)
  proof: hf.mem_of_nonempty_of_not_isSuccLimit (range_nonempty f) hx

@[deprecated mem_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]

中文:
引理 IsLUB.存在_of_nonempty_of_not_isSuccLimit
  条件: (hf : IsLUB (range f) x) (hx : ¬ 是SuccLimit x)
  证明: hf.mem_of_nonempty_of_not_isSuccLimit (range_nonempty f) hx

@[deprecated mem_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]

Depends on / 依赖: hf.mem_of_nonempty_of_not_isSuccLimit, mem_of_nonempty_of_not_isSuccLimit, range_nonempty
-/
lemma IsLUB.exists_of_nonempty_of_not_isSuccLimit (hf : IsLUB (range f) x) (hx : ¬ IsSuccLimit x) :
    exists i, f i = x :=
  hf.mem_of_nonempty_of_not_isSuccLimit (range_nonempty f) hx

@[deprecated mem_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]
/--
lemma `IsLUB.mem_of_nonempty_of_not_isSuccPrelimit` / 引理 `IsLUB.mem_of_nonempty_of_not_isSuccPrelimit`

English:
lemma IsLUB.mem_of_nonempty_of_not_isSuccPrelimit
  proof: hs.mem_of_nonempty_of_not_isSuccLimit hne mt IsSuccLimit.isSuccPrelimit hx

@[deprecated mem_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]

中文:
引理 IsLUB.mem_of_nonempty_of_not_isSuccPrelimit
  证明: hs.mem_of_nonempty_of_not_isSuccLimit hne mt IsSuccLimit.isSuccPrelimit hx

@[deprecated mem_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]

Depends on / 依赖: IsSuccLimit, IsSuccLimit.isSuccPrelimit, hs.mem_of_nonempty_of_not_isSuccLimit, isSuccPrelimit, mem_of_nonempty_of_not_isSuccLimit
-/
lemma IsLUB.mem_of_nonempty_of_not_isSuccPrelimit
    (hs : IsLUB s x) (hne : s.Nonempty) (hx : ¬ IsSuccPrelimit x) : x in s :=
hs.mem_of_nonempty_of_not_isSuccLimit hne mt IsSuccLimit.isSuccPrelimit hx

@[deprecated mem_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]
/--
lemma `IsGLB.mem_of_nonempty_of_not_isPredPrelimit` / 引理 `IsGLB.mem_of_nonempty_of_not_isPredPrelimit`

English:
lemma IsGLB.mem_of_nonempty_of_not_isPredPrelimit
  proof: hs.mem_of_nonempty_of_not_isPredLimit hne mt IsPredLimit.isPredPrelimit hx

@[deprecated exists_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]

中文:
引理 IsGLB.mem_of_nonempty_of_not_isPredPrelimit
  证明: hs.mem_of_nonempty_of_not_isPredLimit hne mt IsPredLimit.isPredPrelimit hx

@[deprecated exists_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]

Depends on / 依赖: IsPredLimit, IsPredLimit.isPredPrelimit, hs.mem_of_nonempty_of_not_isPredLimit, isPredPrelimit, mem_of_nonempty_of_not_isPredLimit
-/
lemma IsGLB.mem_of_nonempty_of_not_isPredPrelimit
    (hs : IsGLB s x) (hne : s.Nonempty) (hx : ¬ IsPredPrelimit x) : x in s :=
hs.mem_of_nonempty_of_not_isPredLimit hne mt IsPredLimit.isPredPrelimit hx

@[deprecated exists_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]
/--
lemma `IsLUB.exists_of_nonempty_of_not_isSuccPrelimit` / 引理 `IsLUB.exists_of_nonempty_of_not_isSuccPrelimit`

English:
lemma IsLUB.exists_of_nonempty_of_not_isSuccPrelimit
  proof: hf.exists_of_nonempty_of_not_isSuccLimit mt IsSuccLimit.isSuccPrelimit hx

@[deprecated exists_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]

中文:
引理 IsLUB.存在_of_nonempty_of_not_isSuccPrelimit
  证明: hf.exists_of_nonempty_of_not_isSuccLimit mt IsSuccLimit.isSuccPrelimit hx

@[deprecated exists_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]

Depends on / 依赖: IsSuccLimit, IsSuccLimit.isSuccPrelimit, exists_of_nonempty_of_not_isSuccLimit, hf.exists_of_nonempty_of_not_isSuccLimit, isSuccPrelimit
-/
lemma IsLUB.exists_of_nonempty_of_not_isSuccPrelimit
    (hf : IsLUB (range f) x) (hx : ¬ IsSuccPrelimit x) : exists i, f i = x :=
hf.exists_of_nonempty_of_not_isSuccLimit mt IsSuccLimit.isSuccPrelimit hx

@[deprecated exists_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]
/--
lemma `IsGLB.exists_of_nonempty_of_not_isPredPrelimit` / 引理 `IsGLB.exists_of_nonempty_of_not_isPredPrelimit`

English:
lemma IsGLB.exists_of_nonempty_of_not_isPredPrelimit
  proof: hf.exists_of_nonempty_of_not_isPredLimit mt IsPredLimit.isPredPrelimit hx

中文:
引理 IsGLB.存在_of_nonempty_of_not_isPredPrelimit
  证明: hf.exists_of_nonempty_of_not_isPredLimit mt IsPredLimit.isPredPrelimit hx

Depends on / 依赖: IsPredLimit, IsPredLimit.isPredPrelimit, exists_of_nonempty_of_not_isPredLimit, hf.exists_of_nonempty_of_not_isPredLimit, isPredPrelimit
-/
lemma IsGLB.exists_of_nonempty_of_not_isPredPrelimit
    (hf : IsGLB (range f) x) (hx : ¬ IsPredPrelimit x) : exists i, f i = x :=
hf.exists_of_nonempty_of_not_isPredLimit mt IsPredLimit.isPredPrelimit hx

/-- Every conditionally complete linear order with well-founded `<` is a successor order, by setting
the successor of an element to be the infimum of all larger elements. -/
@[instance_reducible, deprecated SuccOrder.ofLinearWellFoundedLT (since := "2026-04-12")]
/--
Definition of `ConditionallyCompleteLinearOrder.toSuccOrder` / `ConditionallyCompleteLinearOrder.toSuccOrder` 的定义

English:
definition ConditionallyCompleteLinearOrder.toSuccOrder
  signature: [WellFoundedLT α]
  body: .ofLinearWellFoundedLT _

中文:
定义 条件完备线性序.toSuccOrder
  签名: [WellFoundedLT α]
  定义体: .ofLinearWellFoundedLT _

Depends on / 依赖: ofLinearWellFoundedLT
-/
noncomputable def ConditionallyCompleteLinearOrder.toSuccOrder [WellFoundedLT α] :
    SuccOrder α := .ofLinearWellFoundedLT _

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] {f : ι -> α} {s : Set α} {x : α}

/--
lemma `csSup_mem_of_not_isSuccPrelimit` / 引理 `csSup_mem_of_not_isSuccPrelimit`

English:
lemma csSup_mem_of_not_isSuccPrelimit
  given: (hlim : ¬ IsSuccPrelimit (sSup s))
  statement: sSup s in s
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isSuccPrelimit_bot] at hlim
· apply csSup_mem_of_not_isSuccLimit hs _ mt IsSuccLimit.isSuccPrelimit hlim
    contrapose! hlim
    rw [csSup_of_not_bddAbove hlim]; rw [csSup_empty]
    exact isSuccPrelimit_bot

@[deprecated (since := "2026-04-24")]
alias csSup_mem_of_not_isSuccPrelimit' := csSup_mem_of_not_isSuccPrelimit

中文:
引理 csSup_mem_of_not_isSuccPrelimit
  条件: (hlim : ¬ IsSuccPrelimit (sSup s))
  结论: sSup s in s
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isSuccPrelimit_bot] at hlim
· apply csSup_mem_of_not_isSuccLimit hs _ mt IsSuccLimit.isSuccPrelimit hlim
    contrapose! hlim
    rw [csSup_of_not_bddAbove hlim]; rw [csSup_empty]
    exact isSuccPrelimit_bot

@[deprecated (since := "2026-04-24")]
alias csSup_mem_of_not_isSuccPrelimit' := csSup_mem_of_not_isSuccPrelimit

Depends on / 依赖: IsSuccLimit, IsSuccLimit.isSuccPrelimit, contrapose, csSup_empty, csSup_mem_of_not_isSuccLimit, csSup_of_not_bddAbove, eq_empty_or_nonempty, isSuccPrelimit, isSuccPrelimit_bot, s.eq_empty_or_nonempty
-/
lemma csSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s in s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isSuccPrelimit_bot] at hlim
· apply csSup_mem_of_not_isSuccLimit hs _ mt IsSuccLimit.isSuccPrelimit hlim
    contrapose! hlim
    rw [csSup_of_not_bddAbove hlim]; rw [csSup_empty]
    exact isSuccPrelimit_bot

@[deprecated (since := "2026-04-24")]
alias csSup_mem_of_not_isSuccPrelimit' := csSup_mem_of_not_isSuccPrelimit

/--
lemma `exists_eq_ciSup_of_not_isSuccPrelimit` / 引理 `exists_eq_ciSup_of_not_isSuccPrelimit`

English:
lemma exists_eq_ciSup_of_not_isSuccPrelimit
  given: (hf' : ¬ IsSuccPrelimit (⨆ i, f i))
  proof: csSup_mem_of_not_isSuccPrelimit hf'

@[deprecated (since := "2026-04-24")]
alias exists_eq_ciSup_of_not_isSuccPrelimit' := exists_eq_ciSup_of_not_isSuccPrelimit

中文:
引理 存在_eq_ciSup_of_not_isSuccPrelimit
  条件: (hf' : ¬ IsSuccPrelimit (⨆ i, f i))
  证明: csSup_mem_of_not_isSuccPrelimit hf'

@[deprecated (since := "2026-04-24")]
alias exists_eq_ciSup_of_not_isSuccPrelimit' := exists_eq_ciSup_of_not_isSuccPrelimit

Depends on / 依赖: csSup_mem_of_not_isSuccPrelimit
-/
lemma exists_eq_ciSup_of_not_isSuccPrelimit (hf' : ¬ IsSuccPrelimit (⨆ i, f i)) :
    exists i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccPrelimit hf'

@[deprecated (since := "2026-04-24")]
alias exists_eq_ciSup_of_not_isSuccPrelimit' := exists_eq_ciSup_of_not_isSuccPrelimit

/--
theorem `Order.IsSuccPrelimit.sSup_Iio` / 定理 `Order.IsSuccPrelimit.sSup_Iio`

English:
theorem Order.IsSuccPrelimit.sSup_Iio
  given: (h : IsSuccPrelimit x)
  statement: sSup (Iio x) = x
  proof: by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp
  · exact h.isLUB_Iio.csSup_eq ⟨⊥, hx⟩

中文:
定理 Order.IsSuccPrelimit.sSup_Iio
  条件: (h : IsSuccPrelimit x)
  结论: sSup (左无界右开区间 x) = x
  证明: by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp
  · exact h.isLUB_Iio.csSup_eq ⟨⊥, hx⟩

Depends on / 依赖: csSup_eq, eq_bot_or_bot_lt, h.isLUB_Iio.csSup_eq, isLUB_Iio
-/
theorem Order.IsSuccPrelimit.sSup_Iio (h : IsSuccPrelimit x) : sSup (Iio x) = x := by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp
  · exact h.isLUB_Iio.csSup_eq ⟨⊥, hx⟩

/--
theorem `Order.IsSuccPrelimit.iSup_Iio` / 定理 `Order.IsSuccPrelimit.iSup_Iio`

English:
theorem Order.IsSuccPrelimit.iSup_Iio
  given: (h : IsSuccPrelimit x)
  statement: ⨆ a : Iio x, a.1 = x
  proof: by
  rw [← sSup_eq_iSup']; rw [h.sSup_Iio]

中文:
定理 Order.IsSuccPrelimit.iSup_Iio
  条件: (h : IsSuccPrelimit x)
  结论: ⨆ a : 左无界右开区间 x, a.1 = x
  证明: by
  rw [← sSup_eq_iSup']; rw [h.sSup_Iio]

Depends on / 依赖: h.sSup_Iio, sSup_Iio, sSup_eq_iSup
-/
theorem Order.IsSuccPrelimit.iSup_Iio (h : IsSuccPrelimit x) : ⨆ a : Iio x, a.1 = x := by
  rw [← sSup_eq_iSup']; rw [h.sSup_Iio]

/--
theorem `Order.IsSuccLimit.sSup_Iio` / 定理 `Order.IsSuccLimit.sSup_Iio`

English:
theorem Order.IsSuccLimit.sSup_Iio
  given: (h : IsSuccLimit x)
  statement: sSup (Iio x) = x
  proof: h.isSuccPrelimit.sSup_Iio

中文:
定理 Order.是SuccLimit.sSup_Iio
  条件: (h : 是SuccLimit x)
  结论: sSup (左无界右开区间 x) = x
  证明: h.isSuccPrelimit.sSup_Iio

Depends on / 依赖: h.isSuccPrelimit.sSup_Iio, isSuccPrelimit, sSup_Iio
-/
theorem Order.IsSuccLimit.sSup_Iio (h : IsSuccLimit x) : sSup (Iio x) = x :=
  h.isSuccPrelimit.sSup_Iio

/--
theorem `Order.IsSuccLimit.iSup_Iio` / 定理 `Order.IsSuccLimit.iSup_Iio`

English:
theorem Order.IsSuccLimit.iSup_Iio
  given: (h : IsSuccLimit x)
  statement: ⨆ a : Iio x, a.1 = x
  proof: h.isSuccPrelimit.iSup_Iio

中文:
定理 Order.是SuccLimit.iSup_Iio
  条件: (h : 是SuccLimit x)
  结论: ⨆ a : 左无界右开区间 x, a.1 = x
  证明: h.isSuccPrelimit.iSup_Iio

Depends on / 依赖: h.isSuccPrelimit.iSup_Iio, iSup_Iio, isSuccPrelimit
-/
theorem Order.IsSuccLimit.iSup_Iio (h : IsSuccLimit x) : ⨆ a : Iio x, a.1 = x :=
  h.isSuccPrelimit.iSup_Iio

/--
theorem `sSup_Iio_eq_self_iff_isSuccPrelimit` / 定理 `sSup_Iio_eq_self_iff_isSuccPrelimit`

English:
theorem sSup_Iio_eq_self_iff_isSuccPrelimit
  statement: sSup (Iio x) = x ↔ IsSuccPrelimit x
  proof: by
  refine ⟨fun h => ?_, IsSuccPrelimit.sSup_Iio⟩
  by_contra hx
  rw [← h] at hx
  simpa [h] using csSup_mem_of_not_isSuccPrelimit hx

中文:
定理 sSup_Iio_eq_self_iff_isSuccPrelimit
  结论: sSup (左无界右开区间 x) = x ↔ IsSuccPrelimit x
  证明: by
  refine ⟨fun h => ?_, IsSuccPrelimit.sSup_Iio⟩
  by_contra hx
  rw [← h] at hx
  simpa [h] using csSup_mem_of_not_isSuccPrelimit hx

Depends on / 依赖: IsSuccPrelimit, IsSuccPrelimit.sSup_Iio, csSup_mem_of_not_isSuccPrelimit, sSup_Iio
-/
theorem sSup_Iio_eq_self_iff_isSuccPrelimit : sSup (Iio x) = x ↔ IsSuccPrelimit x := by
  refine ⟨fun h => ?_, IsSuccPrelimit.sSup_Iio⟩
  by_contra hx
  rw [← h] at hx
  simpa [h] using csSup_mem_of_not_isSuccPrelimit hx

/--
theorem `iSup_Iio_eq_self_iff_isSuccPrelimit` / 定理 `iSup_Iio_eq_self_iff_isSuccPrelimit`

English:
theorem iSup_Iio_eq_self_iff_isSuccPrelimit
  statement: ⨆ a : Iio x, a.1 = x ↔ IsSuccPrelimit x
  proof: by
  rw [← sSup_eq_iSup']; rw [sSup_Iio_eq_self_iff_isSuccPrelimit]

中文:
定理 iSup_Iio_eq_self_iff_isSuccPrelimit
  结论: ⨆ a : 左无界右开区间 x, a.1 = x ↔ IsSuccPrelimit x
  证明: by
  rw [← sSup_eq_iSup']; rw [sSup_Iio_eq_self_iff_isSuccPrelimit]

Depends on / 依赖: sSup_Iio_eq_self_iff_isSuccPrelimit, sSup_eq_iSup
-/
theorem iSup_Iio_eq_self_iff_isSuccPrelimit : ⨆ a : Iio x, a.1 = x ↔ IsSuccPrelimit x := by
  rw [← sSup_eq_iSup']; rw [sSup_Iio_eq_self_iff_isSuccPrelimit]

/--
theorem `iSup_succ` / 定理 `iSup_succ`

English:
theorem iSup_succ
  given: [SuccOrder α] (x : α)
  statement: ⨆ a : Iio x, succ a.1 = x
  proof: by
  have H : BddAbove (range fun a : Iio x => succ a.1) :=
    ⟨succ x, by simp +contextual [upperBounds, succ_le_succ, le_of_lt]⟩
  apply le_antisymm _ (le_of_forall_lt fun y hy => ?_)
  · rw [ciSup_le_iff' H]
    exact fun a => succ_le_of_lt a.2
  · rw [lt_ciSup_iff' H]
    exact ⟨⟨y, hy⟩, lt_succ_of_not_isMax hy.not_isMax⟩

中文:
定理 iSup_succ
  条件: [Succ序 α] (x : α)
  结论: ⨆ a : 左无界右开区间 x, succ a.1 = x
  证明: by
  have H : BddAbove (range fun a : Iio x => succ a.1) :=
    ⟨succ x, by simp +contextual [upperBounds, succ_le_succ, le_of_lt]⟩
  apply le_antisymm _ (le_of_forall_lt fun y hy => ?_)
  · rw [ciSup_le_iff' H]
    exact fun a => succ_le_of_lt a.2
  · rw [lt_ciSup_iff' H]
    exact ⟨⟨y, hy⟩, lt_succ_of_not_isMax hy.not_isMax⟩

Depends on / 依赖: BddAbove, ciSup_le_iff, contextual, hy.not_isMax, le_antisymm, le_of_forall_lt, le_of_lt, lt_ciSup_iff, lt_succ_of_not_isMax, not_isMax, succ_le_of_lt, succ_le_succ, upperBounds
-/
theorem iSup_succ [SuccOrder α] (x : α) : ⨆ a : Iio x, succ a.1 = x := by
  have H : BddAbove (range fun a : Iio x => succ a.1) :=
    ⟨succ x, by simp +contextual [upperBounds, succ_le_succ, le_of_lt]⟩
  apply le_antisymm _ (le_of_forall_lt fun y hy => ?_)
  · rw [ciSup_le_iff' H]
    exact fun a => succ_le_of_lt a.2
  · rw [lt_ciSup_iff' H]
    exact ⟨⟨y, hy⟩, lt_succ_of_not_isMax hy.not_isMax⟩

end ConditionallyCompleteLinearOrderBot

section CompleteLinearOrder
variable [CompleteLinearOrder α] {s : Set α} {f : ι -> α} {x : α}

/--
lemma `sSup_mem_of_not_isSuccPrelimit` / 引理 `sSup_mem_of_not_isSuccPrelimit`

English:
lemma sSup_mem_of_not_isSuccPrelimit
  given: (hlim : ¬ IsSuccPrelimit (sSup s))
  statement: sSup s in s
  proof: by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := lt_sSup_iff.mp hy.lt
  exact eq_of_le_of_not_lt (le_sSup his) (hy.2 hi) ▸ his

中文:
引理 sSup_mem_of_not_isSuccPrelimit
  条件: (hlim : ¬ IsSuccPrelimit (sSup s))
  结论: sSup s in s
  证明: by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := lt_sSup_iff.mp hy.lt
  exact eq_of_le_of_not_lt (le_sSup his) (hy.2 hi) ▸ his

Depends on / 依赖: eq_of_le_of_not_lt, hy.lt, le_sSup, lt_sSup_iff, lt_sSup_iff.mp, not_forall_not, not_forall_not.mp
-/
lemma sSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s in s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := lt_sSup_iff.mp hy.lt
  exact eq_of_le_of_not_lt (le_sSup his) (hy.2 hi) ▸ his

/--
lemma `sInf_mem_of_not_isPredPrelimit` / 引理 `sInf_mem_of_not_isPredPrelimit`

English:
lemma sInf_mem_of_not_isPredPrelimit
  given: (hlim : ¬ IsPredPrelimit (sInf s))
  statement: sInf s in s
  proof: by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his

中文:
引理 sInf_mem_of_not_isPredPrelimit
  条件: (hlim : ¬ IsPredPrelimit (sInf s))
  结论: sInf s in s
  证明: by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his

Depends on / 依赖: eq_of_le_of_not_lt, hy.lt, not_forall_not, not_forall_not.mp, sInf_le, sInf_lt_iff, sInf_lt_iff.mp
-/
lemma sInf_mem_of_not_isPredPrelimit (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s in s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his

/--
lemma `exists_eq_iSup_of_not_isSuccPrelimit` / 引理 `exists_eq_iSup_of_not_isSuccPrelimit`

English:
lemma exists_eq_iSup_of_not_isSuccPrelimit
  given: (hf : ¬ IsSuccPrelimit (⨆ i, f i))
  proof: sSup_mem_of_not_isSuccPrelimit hf

中文:
引理 存在_eq_iSup_of_not_isSuccPrelimit
  条件: (hf : ¬ IsSuccPrelimit (⨆ i, f i))
  证明: sSup_mem_of_not_isSuccPrelimit hf

Depends on / 依赖: sSup_mem_of_not_isSuccPrelimit
-/
lemma exists_eq_iSup_of_not_isSuccPrelimit (hf : ¬ IsSuccPrelimit (⨆ i, f i)) :
    exists i, f i = ⨆ i, f i :=
  sSup_mem_of_not_isSuccPrelimit hf

/--
lemma `exists_eq_iInf_of_not_isPredPrelimit` / 引理 `exists_eq_iInf_of_not_isPredPrelimit`

English:
lemma exists_eq_iInf_of_not_isPredPrelimit
  given: (hf : ¬ IsPredPrelimit (⨅ i, f i))
  proof: sInf_mem_of_not_isPredPrelimit hf

中文:
引理 存在_eq_iInf_of_not_isPredPrelimit
  条件: (hf : ¬ IsPredPrelimit (⨅ i, f i))
  证明: sInf_mem_of_not_isPredPrelimit hf

Depends on / 依赖: sInf_mem_of_not_isPredPrelimit
-/
lemma exists_eq_iInf_of_not_isPredPrelimit (hf : ¬ IsPredPrelimit (⨅ i, f i)) :
    exists i, f i = ⨅ i, f i :=
  sInf_mem_of_not_isPredPrelimit hf

end CompleteLinearOrder
