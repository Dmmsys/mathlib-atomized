/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.ENNReal.Action
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Induced Outer Measure

We can extend a function defined on a subset of `Set α` to an outer measure.
The underlying function is called `extend`, and the measure it induces is called
`inducedOuterMeasure`.

Some lemmas below are proven twice, once in the general case, and once where the function `m`
is only defined on measurable sets (i.e. when `P = MeasurableSet`). In the latter cases, we can
remove some hypotheses in the statement. The general version has the same name, but with a prime
at the end.

## Tags

outer measure

-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory

open OuterMeasure


section Extend

variable {R α : Type*} {P : α -> Prop}
variable (m : forall s : α, P s -> Real>=0∞)

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (s : α)
  body: ⨅ h : P s, m s h

中文:
定义 extend
  签名: (s : α)
  定义体: ⨅ h : P s, m s h
-/
def extend (s : α) : Real>=0∞ :=
  ⨅ h : P s, m s h

/--
theorem `extend_eq` / 定理 `extend_eq`

English:
theorem extend_eq
  given: {s : α} (h : P s)
  statement: extend m s = m s h
  proof: by simp [extend, h]

中文:
定理 extend_eq
  条件: {s : α} (h : P s)
  结论: extend m s = m s h
  证明: by simp [extend, h]

Depends on / 依赖: extend
-/
theorem extend_eq {s : α} (h : P s) : extend m s = m s h := by simp [extend, h]

/--
theorem `extend_eq_top` / 定理 `extend_eq_top`

English:
theorem extend_eq_top
  given: {s : α} (h : ¬P s)
  statement: extend m s = ∞
  proof: by simp [extend, h]

中文:
定理 extend_eq_top
  条件: {s : α} (h : ¬P s)
  结论: extend m s = ∞
  证明: by simp [extend, h]

Depends on / 依赖: extend
-/
theorem extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ := by simp [extend, h]

/--
theorem `smul_extend` / 定理 `smul_extend`

English:
theorem smul_extend
  statement: [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  classical
  ext s; by_cases h : P s <;> simp [extend, ENNReal.smul_top, *]

中文:
定理 smul_extend
  结论: [半环 R] [是整环 R] [模 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: by
  classical
  ext s; by_cases h : P s <;> simp [extend, ENNReal.smul_top, *]

Depends on / 依赖: ENNReal, ENNReal.smul_top, classical, extend, smul_top
-/
theorem smul_extend [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    [Module.IsTorsionFree R Real>=0∞] {c : R} (hc : c != 0) :
    c • extend m = extend fun s h => c • m s h := by
  classical
  ext s; by_cases h : P s <;> simp [extend, ENNReal.smul_top, *]

/--
lemma `ennreal_smul_extend` / 引理 `ennreal_smul_extend`

English:
lemma ennreal_smul_extend
  given: {c : Real>=0∞} (hc : c != 0)
  statement: c • extend m = extend fun s h => c • m s h
  proof: by
  ext s; by_cases h : P s <;> simp [extend, *]

中文:
引理 ennreal_smul_extend
  条件: {c : 实数>=0∞} (hc : c != 0)
  结论: c • extend m = extend fun s h => c • m s h
  证明: by
  ext s; by_cases h : P s <;> simp [extend, *]

Depends on / 依赖: extend
-/
lemma ennreal_smul_extend {c : Real>=0∞} (hc : c != 0) : c • extend m = extend fun s h => c • m s h := by
  ext s; by_cases h : P s <;> simp [extend, *]

/--
theorem `le_extend` / 定理 `le_extend`

English:
theorem le_extend
  given: {s : α} (h : P s)
  statement: m s h <= extend m s
  proof: by
  simp only [extend, le_iInf_iff]
  intro
  rfl

中文:
定理 le_extend
  条件: {s : α} (h : P s)
  结论: m s h <= extend m s
  证明: by
  simp only [extend, le_iInf_iff]
  intro
  rfl

Depends on / 依赖: extend, le_iInf_iff
-/
theorem le_extend {s : α} (h : P s) : m s h <= extend m s := by
  simp only [extend, le_iInf_iff]
  intro
  rfl

-- TODO: why this is a bad `congr` lemma?
/--
theorem `extend_congr` / 定理 `extend_congr`

English:
theorem extend_congr
  statement: {β : Type*} {Pb : β -> Prop} {mb : forall s : β, Pb s -> Real>=0∞} {sa : α} {sb : β}
  proof: iInf_congr_Prop hP fun _h => hm _ _

@[simp]

中文:
定理 extend_congr
  结论: {β : 类型} {Pb : β -> 命题} {mb : 对任意 s : β, Pb s -> 实数>=0∞} {sa : α} {sb : β}
  证明: iInf_congr_Prop hP fun _h => hm _ _

@[simp]

Depends on / 依赖: iInf_congr_Prop
-/
theorem extend_congr {β : Type*} {Pb : β -> Prop} {mb : forall s : β, Pb s -> Real>=0∞} {sa : α} {sb : β}
    (hP : P sa ↔ Pb sb) (hm : forall (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb) :
    extend m sa = extend mb sb :=
  iInf_congr_Prop hP fun _h => hm _ _

@[simp]
/--
theorem `extend_top` / 定理 `extend_top`

English:
theorem extend_top
  given: {α : Type*} {P : α -> Prop}
  statement: extend (fun _ _ => ∞ : forall s : α, P s -> Real>=0∞) = ⊤
  proof: funext fun _ => iInf_eq_top.mpr fun _ => rfl

中文:
定理 extend_top
  条件: {α : 类型} {P : α -> 命题}
  结论: extend (fun _ _ => ∞ : 对任意 s : α, P s -> 实数>=0∞) = ⊤
  证明: funext fun _ => iInf_eq_top.mpr fun _ => rfl

Depends on / 依赖: iInf_eq_top, iInf_eq_top.mpr
-/
theorem extend_top {α : Type*} {P : α -> Prop} : extend (fun _ _ => ∞ : forall s : α, P s -> Real>=0∞) = ⊤ :=
  funext fun _ => iInf_eq_top.mpr fun _ => rfl

end Extend

section ExtendSet

variable {α : Type*} {P : Set α -> Prop}
variable {m : forall s : Set α, P s -> Real>=0∞}
variable (P0 : P ∅) (m0 : m ∅ P0 = 0)
variable (PU : forall ⦃f : Nat -> Set α⦄ (_hm : forall i, P (f i)), P (⋃ i, f i))
variable
  (mU :
    forall ⦃f : Nat -> Set α⦄ (hm : forall i, P (f i)),
      Pairwise (Disjoint on f) -> m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i))

variable (msU : forall ⦃f : Nat -> Set α⦄ (hm : forall i, P (f i)), m (⋃ i, f i) (PU hm) <= ∑' i, m (f i) (hm i))
variable (m_mono : forall ⦃s₁ s₂ : Set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ subseteq s₂ -> m s₁ hs₁ <= m s₂ hs₂)

/--
theorem `extend_iUnion_nat` / 定理 `extend_iUnion_nat`

English:
theorem extend_iUnion_nat
  statement: {f : Nat -> Set α} (hm : forall i, P (f i))
  proof: (extend_eq _ _).trans
mU.trans by
      congr with i
      rw [extend_eq]

include P0 m0 in

中文:
定理 extend_iUnion_nat
  结论: {f : 自然数 -> 集合 α} (hm : 对任意 i, P (f i))
  证明: (extend_eq _ _).trans
mU.trans by
      congr with i
      rw [extend_eq]

include P0 m0 in

Depends on / 依赖: extend_eq, mU.trans
-/
theorem extend_iUnion_nat {f : Nat -> Set α} (hm : forall i, P (f i))
    (mU : m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i)) :
    extend m (⋃ i, f i) = ∑' i, extend m (f i) :=
(extend_eq _ _).trans
mU.trans by
      congr with i
      rw [extend_eq]

include P0 m0 in
/--
theorem `extend_empty` / 定理 `extend_empty`

English:
theorem extend_empty
  statement: extend m ∅ = 0
  proof: (extend_eq _ P0).trans m0

中文:
定理 extend_empty
  结论: extend m ∅ = 0
  证明: (extend_eq _ P0).trans m0

Depends on / 依赖: extend_eq
-/
theorem extend_empty : extend m ∅ = 0 :=
  (extend_eq _ P0).trans m0

section Subadditive

include PU msU in
/--
theorem `extend_iUnion_le_tsum_nat'` / 定理 `extend_iUnion_le_tsum_nat'`

English:
theorem extend_iUnion_le_tsum_nat'
  given: (s : Nat -> Set α)
  proof: by
  by_cases! h : forall i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i
    apply extend_eq _ (h i)
  · obtain ⟨i, hi⟩ := h
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)

中文:
定理 extend_iUnion_le_tsum_nat'
  条件: (s : 自然数 -> 集合 α)
  证明: by
  by_cases! h : forall i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i
    apply extend_eq _ (h i)
  · obtain ⟨i, hi⟩ := h
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)

Depends on / 依赖: ENNReal, ENNReal.le_tsum, congr_arg, extend_eq, hi.elim, le_iInf, le_trans, le_tsum
-/
theorem extend_iUnion_le_tsum_nat' (s : Nat -> Set α) :
    extend m (⋃ i, s i) <= ∑' i, extend m (s i) := by
  by_cases! h : forall i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i
    apply extend_eq _ (h i)
  · obtain ⟨i, hi⟩ := h
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)

end Subadditive

section Mono

include m_mono in
/--
theorem `extend_mono'` / 定理 `extend_mono'`

English:
theorem extend_mono'
  given: ⦃s₁ s₂
  statement: Set α⦄ (h₁ : P s₁) (hs : s₁ subseteq s₂) : extend m s₁ <= extend m s₂
  proof: by
  refine le_iInf ?_
  intro h₂
  rw [extend_eq m h₁]
  exact m_mono h₁ h₂ hs

中文:
定理 extend_mono'
  条件: ⦃s₁ s₂
  结论: 集合 α⦄ (h₁ : P s₁) (hs : s₁ subseteq s₂) : extend m s₁ <= extend m s₂
  证明: by
  refine le_iInf ?_
  intro h₂
  rw [extend_eq m h₁]
  exact m_mono h₁ h₂ hs

Depends on / 依赖: extend_eq, le_iInf, m_mono
-/
theorem extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs : s₁ subseteq s₂) : extend m s₁ <= extend m s₂ := by
  refine le_iInf ?_
  intro h₂
  rw [extend_eq m h₁]
  exact m_mono h₁ h₂ hs

end Mono

section Unions

include P0 m0 PU mU in
/--
theorem `extend_iUnion` / 定理 `extend_iUnion`

English:
theorem extend_iUnion
  statement: {β} [Countable β] {f : β -> Set α} (hd : Pairwise (Disjoint on f))
  proof: by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]; rw [← tsum_iUnion_decode₂]
  · exact
      extend_iUnion_nat PU (fun n => Encodable.iUnion_decode₂_cases P0 hm)
        (mU _ (Encodable.iUnion_decode₂_disjoint_on hd))
  · exact extend_empty P0 m0

include P0 m0 PU mU in

中文:
定理 extend_iUnion
  结论: {β} [可数 β] {f : β -> 集合 α} (hd : 两两 (Disjoint on f))
  证明: by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]; rw [← tsum_iUnion_decode₂]
  · exact
      extend_iUnion_nat PU (fun n => Encodable.iUnion_decode₂_cases P0 hm)
        (mU _ (Encodable.iUnion_decode₂_disjoint_on hd))
  · exact extend_empty P0 m0

include P0 m0 PU mU in

Depends on / 依赖: Encodable, Encodable.iUnion_decode, extend_empty, extend_iUnion_nat, nonempty_encodable
-/
theorem extend_iUnion {β} [Countable β] {f : β -> Set α} (hd : Pairwise (Disjoint on f))
    (hm : forall i, P (f i)) : extend m (⋃ i, f i) = ∑' i, extend m (f i) := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]; rw [← tsum_iUnion_decode₂]
  · exact
      extend_iUnion_nat PU (fun n => Encodable.iUnion_decode₂_cases P0 hm)
        (mU _ (Encodable.iUnion_decode₂_disjoint_on hd))
  · exact extend_empty P0 m0

include P0 m0 PU mU in
/--
theorem `extend_union` / 定理 `extend_union`

English:
theorem extend_union
  given: {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂)
  proof: by
  rw [union_eq_iUnion]; rw [extend_iUnion P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂]; rw [h₁⟩)]; rw [tsum_fintype]
  simp

中文:
定理 extend_union
  条件: {s₁ s₂ : 集合 α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂)
  证明: by
  rw [union_eq_iUnion]; rw [extend_iUnion P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂]; rw [h₁⟩)]; rw [tsum_fintype]
  simp

Depends on / 依赖: Bool.forall_bool, extend_iUnion, forall_bool, pairwise_disjoint_on_bool, tsum_fintype, union_eq_iUnion
-/
theorem extend_union {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
    extend m (s₁ union s₂) = extend m s₁ + extend m s₂ := by
  rw [union_eq_iUnion]; rw [extend_iUnion P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂]; rw [h₁⟩)]; rw [tsum_fintype]
  simp

end Unions

variable (m)

/--
Definition of `inducedOuterMeasure` / `inducedOuterMeasure` 的定义

English:
definition inducedOuterMeasure
  signature: : OuterMeasure α
  body: OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)

中文:
定义 inducedOuterMeasure
  签名: : 外测度 α
  定义体: OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)

Depends on / 依赖: OuterMeasure, OuterMeasure.ofFunction, extend, extend_empty, ofFunction
-/
def inducedOuterMeasure : OuterMeasure α :=
  OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)

variable {m P0 m0}

/--
theorem `le_inducedOuterMeasure` / 定理 `le_inducedOuterMeasure`

English:
theorem le_inducedOuterMeasure
  given: {μ : OuterMeasure α}
  proof: le_ofFunction.trans forall_congr' fun _s => le_iInf_iff

中文:
定理 le_inducedOuterMeasure
  条件: {μ : 外测度 α}
  证明: le_ofFunction.trans forall_congr' fun _s => le_iInf_iff

Depends on / 依赖: forall_congr, le_iInf_iff, le_ofFunction, le_ofFunction.trans
-/
theorem le_inducedOuterMeasure {μ : OuterMeasure α} :
    μ <= inducedOuterMeasure m P0 m0 ↔ forall (s) (hs : P s), μ s <= m s hs :=
le_ofFunction.trans forall_congr' fun _s => le_iInf_iff

/--
theorem `inducedOuterMeasure_union_of_false_of_nonempty_inter` / 定理 `inducedOuterMeasure_union_of_false_of_nonempty_inter`

English:
theorem inducedOuterMeasure_union_of_false_of_nonempty_inter
  statement: {s t : Set α}
  proof: ofFunction_union_of_top_of_nonempty_inter fun u hsu htu => @iInf_of_empty _ _ _ ⟨h u hsu htu⟩ _

include PU msU m_mono

中文:
定理 inducedOuterMeasure_union_of_false_of_nonempty_inter
  结论: {s t : 集合 α}
  证明: ofFunction_union_of_top_of_nonempty_inter fun u hsu htu => @iInf_of_empty _ _ _ ⟨h u hsu htu⟩ _

include PU msU m_mono

Depends on / 依赖: iInf_of_empty, ofFunction_union_of_top_of_nonempty_inter
-/
theorem inducedOuterMeasure_union_of_false_of_nonempty_inter {s t : Set α}
    (h : forall u, (s inter u).Nonempty -> (t inter u).Nonempty -> ¬P u) :
    inducedOuterMeasure m P0 m0 (s union t) =
      inducedOuterMeasure m P0 m0 s + inducedOuterMeasure m P0 m0 t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hsu htu => @iInf_of_empty _ _ _ ⟨h u hsu htu⟩ _

include PU msU m_mono

/--
theorem `inducedOuterMeasure_eq_extend'` / 定理 `inducedOuterMeasure_eq_extend'`

English:
theorem inducedOuterMeasure_eq_extend'
  given: {s : Set α} (hs : P s)
  proof: ofFunction_eq s (fun _t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)

中文:
定理 inducedOuterMeasure_eq_extend'
  条件: {s : 集合 α} (hs : P s)
  证明: ofFunction_eq s (fun _t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)

Depends on / 依赖: better_inf, extend_iUnion_le_tsum_nat, extend_mono, m_mono, ofFunction_eq
-/
theorem inducedOuterMeasure_eq_extend' {s : Set α} (hs : P s) :
    inducedOuterMeasure m P0 m0 s = extend m s :=
  ofFunction_eq s (fun _t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)

/--
theorem `inducedOuterMeasure_eq'` / 定理 `inducedOuterMeasure_eq'`

English:
theorem inducedOuterMeasure_eq'
  given: {s : Set α} (hs : P s)
  statement: inducedOuterMeasure m P0 m0 s = m s hs
  proof: (inducedOuterMeasure_eq_extend' PU msU m_mono hs).trans extend_eq _ _

中文:
定理 inducedOuterMeasure_eq'
  条件: {s : 集合 α} (hs : P s)
  结论: inducedOuterMeasure m P0 m0 s = m s hs
  证明: (inducedOuterMeasure_eq_extend' PU msU m_mono hs).trans extend_eq _ _

Depends on / 依赖: better_inf, extend_eq, inducedOuterMeasure_eq_extend, inf_le_left, inf_le_right, le_inf, m_mono
-/
theorem inducedOuterMeasure_eq' {s : Set α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs :=
(inducedOuterMeasure_eq_extend' PU msU m_mono hs).trans extend_eq _ _

/--
theorem `inducedOuterMeasure_eq_iInf` / 定理 `inducedOuterMeasure_eq_iInf`

English:
theorem inducedOuterMeasure_eq_iInf
  given: (s : Set α)
  proof: by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro t ht hs
    grw [hs]
    exact le_of_eq (inducedOuterMeasure_eq' _ msU m_mono _)
  · refine le_iInf ?_
    intro f
    refine le_iInf ?_
    intro hf
    refine le_trans ?_ (extend_iUnion_le_tsum_nat' _ msU _)
    refine le_iInf ?_
    int

中文:
定理 inducedOuterMeasure_eq_iInf
  条件: (s : 集合 α)
  证明: by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro t ht hs
    grw [hs]
    exact le_of_eq (inducedOuterMeasure_eq' _ msU m_mono _)
  · refine le_iInf ?_
    intro f
    refine le_iInf ?_
    intro hf
    refine le_trans ?_ (extend_iUnion_le_tsum_nat' _ msU _)
    refine le_iInf ?_
    int

Depends on / 依赖: extend_iUnion_le_tsum_nat, iInf_le, iInf_le_of_le, inducedOuterMeasure_eq, le_antisymm, le_iInf, le_iInf_iff, le_of_eq, le_trans, m_mono
-/
theorem inducedOuterMeasure_eq_iInf (s : Set α) :
    inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s subseteq t), m t ht := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro t ht hs
    grw [hs]
    exact le_of_eq (inducedOuterMeasure_eq' _ msU m_mono _)
  · refine le_iInf ?_
    intro f
    refine le_iInf ?_
    intro hf
    refine le_trans ?_ (extend_iUnion_le_tsum_nat' _ msU _)
    refine le_iInf ?_
    intro h2f
    exact iInf_le_of_le _ (iInf_le_of_le h2f <| iInf_le _ hf)

omit msU m_mono in
/--
theorem `inducedOuterMeasure_zero` / 定理 `inducedOuterMeasure_zero`

English:
theorem inducedOuterMeasure_zero
  given: (Pu : P univ)
  proof: by
  ext s
  rw [inducedOuterMeasure_eq_iInf PU (fun _ _ => by simp) (fun _ _ => by simp)]
  exact le_antisymm (iInf₂_le_of_le univ Pu (by simp)) zero_le

中文:
定理 inducedOuterMeasure_zero
  条件: (Pu : P univ)
  证明: by
  ext s
  rw [inducedOuterMeasure_eq_iInf PU (fun _ _ => by simp) (fun _ _ => by simp)]
  exact le_antisymm (iInf₂_le_of_le univ Pu (by simp)) zero_le

Depends on / 依赖: inducedOuterMeasure_eq_iInf, le_antisymm, zero_le
-/
theorem inducedOuterMeasure_zero (Pu : P univ) :
    inducedOuterMeasure (fun _ _ => 0) P0 (by simp) = 0 := by
  ext s
  rw [inducedOuterMeasure_eq_iInf PU (fun _ _ => by simp) (fun _ _ => by simp)]
  exact le_antisymm (iInf₂_le_of_le univ Pu (by simp)) zero_le

/--
theorem `inducedOuterMeasure_preimage` / 定理 `inducedOuterMeasure_preimage`

English:
theorem inducedOuterMeasure_preimage
  statement: (f : α ≃ α) (Pm : forall s : Set α, P (f ⁻¹' s) ↔ P s)
  proof: by
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]; rw [inducedOuterMeasure_eq_iInf _ msU m_mono]; symm
    refine f.injective.preimage_surjective.iInf_congr (preimage f) fun s => ?_
    refine iInf_congr_Prop (Pm s) ?_; intro hs
    refine iInf_congr_Prop f.surjective.preimage_subset_preimage_iff

中文:
定理 inducedOuterMeasure_preimage
  结论: (f : α ≃ α) (Pm : 对任意 s : 集合 α, P (f ⁻¹' s) ↔ P s)
  证明: by
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]; rw [inducedOuterMeasure_eq_iInf _ msU m_mono]; symm
    refine f.injective.preimage_surjective.iInf_congr (preimage f) fun s => ?_
    refine iInf_congr_Prop (Pm s) ?_; intro hs
    refine iInf_congr_Prop f.surjective.preimage_subset_preimage_iff

Depends on / 依赖: f.injective.preimage_surjective.iInf_congr, f.surjective.preimage_subset_preimage_iff, iInf_congr, iInf_congr_Prop, inducedOuterMeasure_eq_iInf, injective, m_mono, preimage, preimage_subset_preimage_iff, preimage_surjective, surjective
-/
theorem inducedOuterMeasure_preimage (f : α ≃ α) (Pm : forall s : Set α, P (f ⁻¹' s) ↔ P s)
    (mm : forall (s : Set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs) {A : Set α} :
    inducedOuterMeasure m P0 m0 (f ⁻¹' A) = inducedOuterMeasure m P0 m0 A := by
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]; rw [inducedOuterMeasure_eq_iInf _ msU m_mono]; symm
    refine f.injective.preimage_surjective.iInf_congr (preimage f) fun s => ?_
    refine iInf_congr_Prop (Pm s) ?_; intro hs
    refine iInf_congr_Prop f.surjective.preimage_subset_preimage_iff ?_
    intro _; exact mm s hs

/--
theorem `inducedOuterMeasure_exists_set` / 定理 `inducedOuterMeasure_exists_set`

English:
theorem inducedOuterMeasure_exists_set
  statement: {s : Set α} (hs : inducedOuterMeasure m P0 m0 s != ∞)
  proof: by
  have h := ENNReal.lt_add_right hs hε
  conv at h =>
    lhs
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
  simp only [iInf_lt_iff] at h
  rcases h with ⟨t, h1t, h2t, h3t⟩
  exact
    ⟨t, h1t, h2t, le_trans (le_of_eq <| inducedOuterMeasure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩

中文:
定理 inducedOuterMeasure_存在_set
  结论: {s : 集合 α} (hs : inducedOuterMeasure m P0 m0 s != ∞)
  证明: by
  have h := ENNReal.lt_add_right hs hε
  conv at h =>
    lhs
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
  simp only [iInf_lt_iff] at h
  rcases h with ⟨t, h1t, h2t, h3t⟩
  exact
    ⟨t, h1t, h2t, le_trans (le_of_eq <| inducedOuterMeasure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩

Depends on / 依赖: ENNReal, ENNReal.lt_add_right, iInf_lt_iff, inducedOuterMeasure_eq, inducedOuterMeasure_eq_iInf, le_of_eq, le_of_lt, le_trans, lt_add_right, m_mono
-/
theorem inducedOuterMeasure_exists_set {s : Set α} (hs : inducedOuterMeasure m P0 m0 s != ∞)
    {ε : Real>=0∞} (hε : ε != 0) :
    exists t : Set α,
      P t ∧ s subseteq t ∧ inducedOuterMeasure m P0 m0 t <= inducedOuterMeasure m P0 m0 s + ε := by
  have h := ENNReal.lt_add_right hs hε
  conv at h =>
    lhs
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
  simp only [iInf_lt_iff] at h
  rcases h with ⟨t, h1t, h2t, h3t⟩
  exact
    ⟨t, h1t, h2t, le_trans (le_of_eq <| inducedOuterMeasure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩

/--
theorem `inducedOuterMeasure_caratheodory` / 定理 `inducedOuterMeasure_caratheodory`

English:
theorem inducedOuterMeasure_caratheodory
  given: (s : Set α)
  proof: by
  rw [isCaratheodory_iff_le]
  constructor
  · intro h t _ht
    exact h t
  · intro h u
    conv_rhs => rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
    refine le_iInf ?_
    intro t
    refine le_iInf ?_
    intro ht
    refine le_iInf ?_
    intro h2t
    refine le_trans ?_ ((h t ht).trans_eq

中文:
定理 inducedOuterMeasure_caratheodory
  条件: (s : 集合 α)
  证明: by
  rw [isCaratheodory_iff_le]
  constructor
  · intro h t _ht
    exact h t
  · intro h u
    conv_rhs => rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
    refine le_iInf ?_
    intro t
    refine le_iInf ?_
    intro ht
    refine le_iInf ?_
    intro h2t
    refine le_trans ?_ ((h t ht).trans_eq

Depends on / 依赖: conv_rhs, inducedOuterMeasure_eq, inducedOuterMeasure_eq_iInf, isCaratheodory_iff_le, le_iInf, le_trans, m_mono, trans_eq
-/
theorem inducedOuterMeasure_caratheodory (s : Set α) :
    MeasurableSet[(inducedOuterMeasure m P0 m0).caratheodory] s ↔
      forall t : Set α,
        P t ->
          inducedOuterMeasure m P0 m0 (t inter s) + inducedOuterMeasure m P0 m0 (t \ s) <=
            inducedOuterMeasure m P0 m0 t := by
  rw [isCaratheodory_iff_le]
  constructor
  · intro h t _ht
    exact h t
  · intro h u
    conv_rhs => rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
    refine le_iInf ?_
    intro t
    refine le_iInf ?_
    intro ht
    refine le_iInf ?_
    intro h2t
    refine le_trans ?_ ((h t ht).trans_eq <| inducedOuterMeasure_eq' _ msU m_mono ht)
    gcongr

end ExtendSet

/-! If `P` is `MeasurableSet` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/


section MeasurableSpace

variable {α : Type*} [MeasurableSpace α]
variable {m : forall s : Set α, MeasurableSet s -> Real>=0∞}
variable (m0 : m ∅ MeasurableSet.empty = 0)
variable
  (mU :
    forall ⦃f : Nat -> Set α⦄ (hm : forall i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) -> m (⋃ i, f i) (MeasurableSet.iUnion hm) = ∑' i, m (f i) (hm i))
include m0 mU

/--
theorem `extend_mono` / 定理 `extend_mono`

English:
theorem extend_mono
  given: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (hs : s₁ subseteq s₂)
  proof: by
  refine le_iInf ?_; intro h₂
  have :=
    extend_union MeasurableSet.empty m0 MeasurableSet.iUnion mU disjoint_sdiff_self_right h₁
      (h₂.diff h₁)
  rw [union_sdiff_cancel hs] at this
  rw [← extend_eq m]
  exact le_iff_exists_add.2 ⟨_, this⟩

中文:
定理 extend_mono
  条件: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁) (hs : s₁ subseteq s₂)
  证明: by
  refine le_iInf ?_; intro h₂
  have :=
    extend_union MeasurableSet.empty m0 MeasurableSet.iUnion mU disjoint_sdiff_self_right h₁
      (h₂.diff h₁)
  rw [union_sdiff_cancel hs] at this
  rw [← extend_eq m]
  exact le_iff_exists_add.2 ⟨_, this⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, MeasurableSet.iUnion, disjoint_sdiff_self_right, extend_eq, extend_union, iUnion, le_iInf, le_iff_exists_add, union_sdiff_cancel
-/
theorem extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (hs : s₁ subseteq s₂) :
    extend m s₁ <= extend m s₂ := by
  refine le_iInf ?_; intro h₂
  have :=
    extend_union MeasurableSet.empty m0 MeasurableSet.iUnion mU disjoint_sdiff_self_right h₁
      (h₂.diff h₁)
  rw [union_sdiff_cancel hs] at this
  rw [← extend_eq m]
  exact le_iff_exists_add.2 ⟨_, this⟩

/--
theorem `extend_iUnion_le_tsum_nat` / 定理 `extend_iUnion_le_tsum_nat`

English:
theorem extend_iUnion_le_tsum_nat
  statement: forall s : Nat -> Set α,
  proof: by
  refine extend_iUnion_le_tsum_nat' MeasurableSet.iUnion ?_; intro f h
  simp +singlePass only [iUnion_disjointed.symm]
  rw [mU (MeasurableSet.disjointed h) (disjoint_disjointed _)]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← extend_eq m]; rw [← extend_eq m]
  exact extend_mono m0 mU (Meas

中文:
定理 extend_iUnion_le_tsum_nat
  结论: 对任意 s : 自然数 -> 集合 α,
  证明: by
  refine extend_iUnion_le_tsum_nat' MeasurableSet.iUnion ?_; intro f h
  simp +singlePass only [iUnion_disjointed.symm]
  rw [mU (MeasurableSet.disjointed h) (disjoint_disjointed _)]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← extend_eq m]; rw [← extend_eq m]
  exact extend_mono m0 mU (Meas

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, MeasurableSet, MeasurableSet.disjointed, MeasurableSet.iUnion, disjoint_disjointed, disjointed, disjointed_le, extend_eq, extend_iUnion_le_tsum_nat, extend_mono, iUnion, iUnion_disjointed, iUnion_disjointed.symm, singlePass, tsum_le_tsum
-/
theorem extend_iUnion_le_tsum_nat : forall s : Nat -> Set α,
    extend m (⋃ i, s i) <= ∑' i, extend m (s i) := by
  refine extend_iUnion_le_tsum_nat' MeasurableSet.iUnion ?_; intro f h
  simp +singlePass only [iUnion_disjointed.symm]
  rw [mU (MeasurableSet.disjointed h) (disjoint_disjointed _)]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← extend_eq m]; rw [← extend_eq m]
  exact extend_mono m0 mU (MeasurableSet.disjointed h _) (disjointed_le f _)

/--
theorem `inducedOuterMeasure_eq_extend` / 定理 `inducedOuterMeasure_eq_extend`

English:
theorem inducedOuterMeasure_eq_extend
  given: {s : Set α} (hs : MeasurableSet s)
  proof: ofFunction_eq s (fun _t => extend_mono m0 mU hs) (extend_iUnion_le_tsum_nat m0 mU)

中文:
定理 inducedOuterMeasure_eq_extend
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: ofFunction_eq s (fun _t => extend_mono m0 mU hs) (extend_iUnion_le_tsum_nat m0 mU)

Depends on / 依赖: extend_iUnion_le_tsum_nat, extend_mono, ofFunction_eq
-/
theorem inducedOuterMeasure_eq_extend {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = extend m s :=
  ofFunction_eq s (fun _t => extend_mono m0 mU hs) (extend_iUnion_le_tsum_nat m0 mU)

/--
theorem `inducedOuterMeasure_eq` / 定理 `inducedOuterMeasure_eq`

English:
theorem inducedOuterMeasure_eq
  given: {s : Set α} (hs : MeasurableSet s)
  proof: (inducedOuterMeasure_eq_extend m0 mU hs).trans extend_eq _ _

中文:
定理 inducedOuterMeasure_eq
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: (inducedOuterMeasure_eq_extend m0 mU hs).trans extend_eq _ _

Depends on / 依赖: extend_eq, inducedOuterMeasure_eq_extend
-/
theorem inducedOuterMeasure_eq {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = m s hs :=
(inducedOuterMeasure_eq_extend m0 mU hs).trans extend_eq _ _

end MeasurableSpace

namespace OuterMeasure

variable {α : Type*} [MeasurableSpace α] (m : OuterMeasure α)

/--
Definition of `trim` / `trim` 的定义

English:
definition trim
  signature: : OuterMeasure α
  body: inducedOuterMeasure (P := MeasurableSet) (fun s _ => m s) .empty m.empty

中文:
定义 trim
  签名: : 外测度 α
  定义体: inducedOuterMeasure (P := MeasurableSet) (fun s _ => m s) .empty m.empty

Depends on / 依赖: MeasurableSet, inducedOuterMeasure, m.empty
-/
def trim : OuterMeasure α :=
  inducedOuterMeasure (P := MeasurableSet) (fun s _ => m s) .empty m.empty

/--
theorem `le_trim_iff` / 定理 `le_trim_iff`

English:
theorem le_trim_iff
  given: {m₁ m₂ : OuterMeasure α}
  proof: le_inducedOuterMeasure

中文:
定理 le_trim_iff
  条件: {m₁ m₂ : 外测度 α}
  证明: le_inducedOuterMeasure

Depends on / 依赖: le_inducedOuterMeasure
-/
theorem le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁ <= m₂.trim ↔ forall s, MeasurableSet s -> m₁ s <= m₂ s :=
  le_inducedOuterMeasure

/--
theorem `le_trim` / 定理 `le_trim`

English:
theorem le_trim
  statement: m <= m.trim
  proof: le_trim_iff.2 fun _ _ => le_rfl

中文:
定理 le_trim
  结论: m <= m.trim
  证明: le_trim_iff.2 fun _ _ => le_rfl

Depends on / 依赖: le_rfl, le_trim_iff
-/
theorem le_trim : m <= m.trim := le_trim_iff.2 fun _ _ => le_rfl

/--
lemma `null_of_trim_null` / 引理 `null_of_trim_null`

English:
lemma null_of_trim_null
  given: {s : Set α} (h : m.trim s = 0)
  statement: m s = 0
  proof: nonpos_iff_eq_zero.1 (le_trim m s).trans_eq h

@[simp]

中文:
引理 null_of_trim_null
  条件: {s : 集合 α} (h : m.trim s = 0)
  结论: m s = 0
  证明: nonpos_iff_eq_zero.1 (le_trim m s).trans_eq h

@[simp]

Depends on / 依赖: le_trim, nonpos_iff_eq_zero, trans_eq
-/
lemma null_of_trim_null {s : Set α} (h : m.trim s = 0) : m s = 0 :=
nonpos_iff_eq_zero.1 (le_trim m s).trans_eq h

@[simp]
/--
theorem `trim_eq` / 定理 `trim_eq`

English:
theorem trim_eq
  given: {s : Set α} (hs : MeasurableSet s)
  statement: m.trim s = m s
  proof: inducedOuterMeasure_eq' MeasurableSet.iUnion (fun f _hf => measure_iUnion_le f)
    (fun _ _ _ _ h => measure_mono h) hs

中文:
定理 trim_eq
  条件: {s : 集合 α} (hs : 可测集 s)
  结论: m.trim s = m s
  证明: inducedOuterMeasure_eq' MeasurableSet.iUnion (fun f _hf => measure_iUnion_le f)
    (fun _ _ _ _ h => measure_mono h) hs

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, inducedOuterMeasure_eq, measure_iUnion_le, measure_mono
-/
theorem trim_eq {s : Set α} (hs : MeasurableSet s) : m.trim s = m s :=
  inducedOuterMeasure_eq' MeasurableSet.iUnion (fun f _hf => measure_iUnion_le f)
    (fun _ _ _ _ h => measure_mono h) hs

/--
theorem `trim_congr` / 定理 `trim_congr`

English:
theorem trim_congr
  given: {m₁ m₂ : OuterMeasure α} (H : forall {s : Set α}, MeasurableSet s -> m₁ s = m₂ s)
  proof: by
  simp +contextual only [trim, H]

@[gcongr, mono]

中文:
定理 trim_congr
  条件: {m₁ m₂ : 外测度 α} (H : 对任意 {s : 集合 α}, 可测集 s -> m₁ s = m₂ s)
  证明: by
  simp +contextual only [trim, H]

@[gcongr, mono]

Depends on / 依赖: contextual
-/
theorem trim_congr {m₁ m₂ : OuterMeasure α} (H : forall {s : Set α}, MeasurableSet s -> m₁ s = m₂ s) :
    m₁.trim = m₂.trim := by
  simp +contextual only [trim, H]

@[gcongr, mono]
/--
theorem `trim_mono` / 定理 `trim_mono`

English:
theorem trim_mono
  statement: Monotone (trim : OuterMeasure α -> OuterMeasure α)
  proof: fun _m₁ _m₂ H _s =>
  iInf₂_mono fun _f _hs => ENNReal.tsum_le_tsum fun _b => iInf_mono fun _hf => H _

中文:
定理 trim_mono
  结论: 递增 (trim : 外测度 α -> 外测度 α)
  证明: fun _m₁ _m₂ H _s =>
  iInf₂_mono fun _f _hs => ENNReal.tsum_le_tsum fun _b => iInf_mono fun _hf => H _
-/
theorem trim_mono : Monotone (trim : OuterMeasure α -> OuterMeasure α) := fun _m₁ _m₂ H _s =>
  iInf₂_mono fun _f _hs => ENNReal.tsum_le_tsum fun _b => iInf_mono fun _hf => H _

/--
theorem `trim_anti_measurableSpace` / 定理 `trim_anti_measurableSpace`

English:
theorem trim_anti_measurableSpace
  statement: {α} (m : OuterMeasure α) {m0 m1 : MeasurableSpace α}
  proof: by
  simp only [le_trim_iff]
  intro s hs
  rw [trim_eq _ (h s hs)]

中文:
定理 trim_anti_measurableSpace
  结论: {α} (m : 外测度 α) {m0 m1 : 可测空间 α}
  证明: by
  simp only [le_trim_iff]
  intro s hs
  rw [trim_eq _ (h s hs)]

Depends on / 依赖: le_trim_iff, trim_eq
-/
theorem trim_anti_measurableSpace {α} (m : OuterMeasure α) {m0 m1 : MeasurableSpace α}
    (h : m0 <= m1) : @trim _ m1 m <= @trim _ m0 m := by
  simp only [le_trim_iff]
  intro s hs
  rw [trim_eq _ (h s hs)]

/--
theorem `trim_le_trim_iff` / 定理 `trim_le_trim_iff`

English:
theorem trim_le_trim_iff
  given: {m₁ m₂ : OuterMeasure α}
  proof: le_trim_iff.trans forall₂_congr fun s hs => by rw [trim_eq _ hs]

中文:
定理 trim_le_trim_iff
  条件: {m₁ m₂ : 外测度 α}
  证明: le_trim_iff.trans forall₂_congr fun s hs => by rw [trim_eq _ hs]

Depends on / 依赖: le_trim_iff, le_trim_iff.trans, trim_eq
-/
theorem trim_le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim <= m₂.trim ↔ forall s, MeasurableSet s -> m₁ s <= m₂ s :=
le_trim_iff.trans forall₂_congr fun s hs => by rw [trim_eq _ hs]

/--
theorem `trim_eq_trim_iff` / 定理 `trim_eq_trim_iff`

English:
theorem trim_eq_trim_iff
  given: {m₁ m₂ : OuterMeasure α}
  proof: by
  simp only [le_antisymm_iff, trim_le_trim_iff, forall_and]

中文:
定理 trim_eq_trim_iff
  条件: {m₁ m₂ : 外测度 α}
  证明: by
  simp only [le_antisymm_iff, trim_le_trim_iff, forall_and]

Depends on / 依赖: forall_and, le_antisymm_iff, trim_le_trim_iff
-/
theorem trim_eq_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim = m₂.trim ↔ forall s, MeasurableSet s -> m₁ s = m₂ s := by
  simp only [le_antisymm_iff, trim_le_trim_iff, forall_and]

/--
theorem `trim_eq_iInf` / 定理 `trim_eq_iInf`

English:
theorem trim_eq_iInf
  given: (s : Set α)
  statement: m.trim s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t
  proof: by
  simp +singlePass only [iInf_comm]
  exact
    inducedOuterMeasure_eq_iInf MeasurableSet.iUnion (fun f _ => measure_iUnion_le f)
      (fun _ _ _ _ h => measure_mono h) s

中文:
定理 trim_eq_iInf
  条件: (s : 集合 α)
  结论: m.trim s = ⨅ (t) (_ : s subseteq t) (_ : 可测集 t), m t
  证明: by
  simp +singlePass only [iInf_comm]
  exact
    inducedOuterMeasure_eq_iInf MeasurableSet.iUnion (fun f _ => measure_iUnion_le f)
      (fun _ _ _ _ h => measure_mono h) s

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iInf_comm, iUnion, inducedOuterMeasure_eq_iInf, measure_iUnion_le, measure_mono, singlePass
-/
theorem trim_eq_iInf (s : Set α) : m.trim s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t := by
  simp +singlePass only [iInf_comm]
  exact
    inducedOuterMeasure_eq_iInf MeasurableSet.iUnion (fun f _ => measure_iUnion_le f)
      (fun _ _ _ _ h => measure_mono h) s

/--
theorem `trim_eq_iInf'` / 定理 `trim_eq_iInf'`

English:
theorem trim_eq_iInf'
  given: (s : Set α)
  statement: m.trim s = ⨅ t : { t // s subseteq t ∧ MeasurableSet t }, m t
  proof: by
  simp [iInf_subtype, iInf_and, trim_eq_iInf]

中文:
定理 trim_eq_iInf'
  条件: (s : 集合 α)
  结论: m.trim s = ⨅ t : { t // s subseteq t ∧ 可测集 t }, m t
  证明: by
  simp [iInf_subtype, iInf_and, trim_eq_iInf]

Depends on / 依赖: iInf_and, iInf_subtype, trim_eq_iInf
-/
theorem trim_eq_iInf' (s : Set α) : m.trim s = ⨅ t : { t // s subseteq t ∧ MeasurableSet t }, m t := by
  simp [iInf_subtype, iInf_and, trim_eq_iInf]

/--
theorem `trim_trim` / 定理 `trim_trim`

English:
theorem trim_trim
  given: (m : OuterMeasure α)
  statement: m.trim.trim = m.trim
  proof: trim_eq_trim_iff.2 fun _s => m.trim_eq

@[simp]

中文:
定理 trim_trim
  条件: (m : 外测度 α)
  结论: m.trim.trim = m.trim
  证明: trim_eq_trim_iff.2 fun _s => m.trim_eq

@[simp]

Depends on / 依赖: m.trim_eq, trim_eq, trim_eq_trim_iff
-/
theorem trim_trim (m : OuterMeasure α) : m.trim.trim = m.trim :=
  trim_eq_trim_iff.2 fun _s => m.trim_eq

@[simp]
/--
theorem `trim_top` / 定理 `trim_top`

English:
theorem trim_top
  statement: (⊤ : OuterMeasure α).trim = ⊤
  proof: top_unique le_trim _

@[simp]

中文:
定理 trim_top
  结论: (⊤ : 外测度 α).trim = ⊤
  证明: top_unique le_trim _

@[simp]

Depends on / 依赖: le_trim, top_unique
-/
theorem trim_top : (⊤ : OuterMeasure α).trim = ⊤ :=
top_unique le_trim _

@[simp]
/--
theorem `trim_zero` / 定理 `trim_zero`

English:
theorem trim_zero
  statement: (0 : OuterMeasure α).trim = 0
  proof: by
  ext s
exact nonpos_iff_eq_zero.1 (measure_mono (subset_univ s)).trans_eq trim_eq _ .univ

中文:
定理 trim_zero
  结论: (0 : 外测度 α).trim = 0
  证明: by
  ext s
exact nonpos_iff_eq_zero.1 (measure_mono (subset_univ s)).trans_eq trim_eq _ .univ

Depends on / 依赖: measure_mono, nonpos_iff_eq_zero, subset_univ, trans_eq, trim_eq
-/
theorem trim_zero : (0 : OuterMeasure α).trim = 0 := by
  ext s
exact nonpos_iff_eq_zero.1 (measure_mono (subset_univ s)).trans_eq trim_eq _ .univ

/--
theorem `trim_sum_ge` / 定理 `trim_sum_ge`

English:
theorem trim_sum_ge
  given: {ι} (m : ι -> OuterMeasure α)
  statement: (sum fun i => (m i).trim) <= (sum m).trim
  proof: fun s => by
  simp only [sum_apply, trim_eq_iInf, le_iInf_iff]
  exact fun t st ht =>
ENNReal.tsum_le_tsum fun i => iInf_le_of_le t iInf_le_of_le st iInf_le _ ht

中文:
定理 trim_sum_ge
  条件: {ι} (m : ι -> 外测度 α)
  结论: (求和 fun i => (m i).trim) <= (求和 m).trim
  证明: fun s => by
  simp only [sum_apply, trim_eq_iInf, le_iInf_iff]
  exact fun t st ht =>
ENNReal.tsum_le_tsum fun i => iInf_le_of_le t iInf_le_of_le st iInf_le _ ht

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, iInf_le, iInf_le_of_le, le_iInf_iff, sum_apply, trim_eq_iInf, tsum_le_tsum
-/
theorem trim_sum_ge {ι} (m : ι -> OuterMeasure α) : (sum fun i => (m i).trim) <= (sum m).trim :=
  fun s => by
  simp only [sum_apply, trim_eq_iInf, le_iInf_iff]
  exact fun t st ht =>
ENNReal.tsum_le_tsum fun i => iInf_le_of_le t iInf_le_of_le st iInf_le _ ht

/--
theorem `exists_measurable_superset_eq_trim` / 定理 `exists_measurable_superset_eq_trim`

English:
theorem exists_measurable_superset_eq_trim
  given: (m : OuterMeasure α) (s : Set α)
  proof: by
  simp only [trim_eq_iInf]; set ms := ⨅ (t : Set α) (_ : s subseteq t) (_ : MeasurableSet t), m t
  by_cases hs : ms = ∞
  · simp only [hs]
    simp only [iInf_eq_top, ms] at hs
    exact ⟨univ, subset_univ s, MeasurableSet.univ, hs _ (subset_univ s) MeasurableSet.univ⟩
  · have : forall r > ms, 

中文:
定理 存在_measurable_superset_eq_trim
  条件: (m : 外测度 α) (s : 集合 α)
  证明: by
  simp only [trim_eq_iInf]; set ms := ⨅ (t : Set α) (_ : s subseteq t) (_ : MeasurableSet t), m t
  by_cases hs : ms = ∞
  · simp only [hs]
    simp only [iInf_eq_top, ms] at hs
    exact ⟨univ, subset_univ s, MeasurableSet.univ, hs _ (subset_univ s) MeasurableSet.univ⟩
  · have : forall r > ms, 

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, iInf_eq_top, iInf_lt_iff, subset_univ, subseteq, trim_eq_iInf
-/
theorem exists_measurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) :
    exists t, s subseteq t ∧ MeasurableSet t ∧ m t = m.trim s := by
  simp only [trim_eq_iInf]; set ms := ⨅ (t : Set α) (_ : s subseteq t) (_ : MeasurableSet t), m t
  by_cases hs : ms = ∞
  · simp only [hs]
    simp only [iInf_eq_top, ms] at hs
    exact ⟨univ, subset_univ s, MeasurableSet.univ, hs _ (subset_univ s) MeasurableSet.univ⟩
  · have : forall r > ms, exists t, s subseteq t ∧ MeasurableSet t ∧ m t < r := by
      intro r hs
      have : exists t, MeasurableSet t ∧ s subseteq t ∧ m t < r := by simpa [ms, iInf_lt_iff] using hs
      rcases this with ⟨t, hmt, hin, hlt⟩
      exists t
    have : forall n : Nat, exists t, s subseteq t ∧ MeasurableSet t ∧ m t < ms + (n : Real>=0∞)⁻¹ := by
      intro n
      refine this _ (ENNReal.lt_add_right hs ?_)
      simp
    choose t hsub hm hm' using this
    refine ⟨⋂ n, t n, subset_iInter hsub, MeasurableSet.iInter hm, ?_⟩
    have : Tendsto (fun n : Nat => ms + (n : Real>=0∞)⁻¹) atTop (𝓝 (ms + 0)) :=
      tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    rw [add_zero] at this
    refine le_antisymm (ge_of_tendsto' this fun n => ?_) ?_
    · exact le_trans (measure_mono <| iInter_subset t n) (hm' n).le
    · refine iInf_le_of_le (⋂ n, t n) ?_
      refine iInf_le_of_le (subset_iInter hsub) ?_
      exact iInf_le _ (MeasurableSet.iInter hm)

/--
theorem `exists_measurable_superset_of_trim_eq_zero` / 定理 `exists_measurable_superset_of_trim_eq_zero`

English:
theorem exists_measurable_superset_of_trim_eq_zero
  statement: {m : OuterMeasure α} {s : Set α}
  proof: by
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
  exact ⟨t, hst, ht, h ▸ hm⟩

中文:
定理 存在_measurable_superset_of_trim_eq_zero
  结论: {m : 外测度 α} {s : 集合 α}
  证明: by
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
  exact ⟨t, hst, ht, h ▸ hm⟩

Depends on / 依赖: exists_measurable_superset_eq_trim
-/
theorem exists_measurable_superset_of_trim_eq_zero {m : OuterMeasure α} {s : Set α}
    (h : m.trim s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ m t = 0 := by
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
  exact ⟨t, hst, ht, h ▸ hm⟩

/--
theorem `exists_measurable_superset_forall_eq_trim` / 定理 `exists_measurable_superset_forall_eq_trim`

English:
theorem exists_measurable_superset_forall_eq_trim
  statement: {ι} [Countable ι] (μ : ι -> OuterMeasure α)
  proof: by
  choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s
  replace hst := subset_iInter hst
  replace ht := MeasurableSet.iInter ht
  refine ⟨⋂ i, t i, hst, ht, fun i => le_antisymm ?_ ?_⟩
  exacts [hμt i ▸ (μ i).mono (iInter_subset _ _), (measure_mono hst).trans_eq ((μ i).

中文:
定理 存在_measurable_superset_对任意_eq_trim
  结论: {ι} [可数 ι] (μ : ι -> 外测度 α)
  证明: by
  choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s
  replace hst := subset_iInter hst
  replace ht := MeasurableSet.iInter ht
  refine ⟨⋂ i, t i, hst, ht, fun i => le_antisymm ?_ ?_⟩
  exacts [hμt i ▸ (μ i).mono (iInter_subset _ _), (measure_mono hst).trans_eq ((μ i).

Depends on / 依赖: MeasurableSet, MeasurableSet.iInter, exacts, exists_measurable_superset_eq_trim, iInter, iInter_subset, le_antisymm, measure_mono, replace, subset_iInter, trans_eq, trim_eq
-/
theorem exists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι -> OuterMeasure α)
    (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ forall i, μ i t = (μ i).trim s := by
  choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s
  replace hst := subset_iInter hst
  replace ht := MeasurableSet.iInter ht
  refine ⟨⋂ i, t i, hst, ht, fun i => le_antisymm ?_ ?_⟩
  exacts [hμt i ▸ (μ i).mono (iInter_subset _ _), (measure_mono hst).trans_eq ((μ i).trim_eq ht)]

/--
theorem `trim_binop` / 定理 `trim_binop`

English:
theorem trim_binop
  statement: {m₁ m₂ m₃ : OuterMeasure α} {op : Real>=0∞ -> Real>=0∞ -> Real>=0∞}
  proof: by
  rcases exists_measurable_superset_forall_eq_trim ![m₁, m₂, m₃] s with ⟨t, _hst, _ht, htm⟩
  simp only [Fin.forall_iff_succ, Matrix.cons_val_zero, Matrix.cons_val_succ] at htm
  rw [← htm.1]; rw [← htm.2.1]; rw [← htm.2.2.1]; rw [h]

中文:
定理 trim_binop
  结论: {m₁ m₂ m₃ : 外测度 α} {op : 实数>=0∞ -> 实数>=0∞ -> 实数>=0∞}
  证明: by
  rcases exists_measurable_superset_forall_eq_trim ![m₁, m₂, m₃] s with ⟨t, _hst, _ht, htm⟩
  simp only [Fin.forall_iff_succ, Matrix.cons_val_zero, Matrix.cons_val_succ] at htm
  rw [← htm.1]; rw [← htm.2.1]; rw [← htm.2.2.1]; rw [h]

Depends on / 依赖: Fin.forall_iff_succ, Matrix, Matrix.cons_val_succ, Matrix.cons_val_zero, _hst, cons_val_succ, cons_val_zero, exists_measurable_superset_forall_eq_trim, forall_iff_succ
-/
theorem trim_binop {m₁ m₂ m₃ : OuterMeasure α} {op : Real>=0∞ -> Real>=0∞ -> Real>=0∞}
    (h : forall s, m₁ s = op (m₂ s) (m₃ s)) (s : Set α) : m₁.trim s = op (m₂.trim s) (m₃.trim s) := by
  rcases exists_measurable_superset_forall_eq_trim ![m₁, m₂, m₃] s with ⟨t, _hst, _ht, htm⟩
  simp only [Fin.forall_iff_succ, Matrix.cons_val_zero, Matrix.cons_val_succ] at htm
  rw [← htm.1]; rw [← htm.2.1]; rw [← htm.2.2.1]; rw [h]

/--
theorem `trim_op` / 定理 `trim_op`

English:
theorem trim_op
  statement: {m₁ m₂ : OuterMeasure α} {op : Real>=0∞ -> Real>=0∞} (h : forall s, m₁ s = op (m₂ s))
  proof: @trim_binop α _ m₁ m₂ 0 (fun a _b => op a) h s

中文:
定理 trim_op
  结论: {m₁ m₂ : 外测度 α} {op : 实数>=0∞ -> 实数>=0∞} (h : 对任意 s, m₁ s = op (m₂ s))
  证明: @trim_binop α _ m₁ m₂ 0 (fun a _b => op a) h s

Depends on / 依赖: trim_binop
-/
theorem trim_op {m₁ m₂ : OuterMeasure α} {op : Real>=0∞ -> Real>=0∞} (h : forall s, m₁ s = op (m₂ s))
    (s : Set α) : m₁.trim s = op (m₂.trim s) :=
  @trim_binop α _ m₁ m₂ 0 (fun a _b => op a) h s

/--
theorem `trim_add` / 定理 `trim_add`

English:
theorem trim_add
  given: (m₁ m₂ : OuterMeasure α)
  statement: (m₁ + m₂).trim = m₁.trim + m₂.trim
  proof: ext trim_binop (add_apply m₁ m₂)

中文:
定理 trim_add
  条件: (m₁ m₂ : 外测度 α)
  结论: (m₁ + m₂).trim = m₁.trim + m₂.trim
  证明: ext trim_binop (add_apply m₁ m₂)

Depends on / 依赖: add_apply, trim_binop
-/
theorem trim_add (m₁ m₂ : OuterMeasure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
ext trim_binop (add_apply m₁ m₂)

/--
theorem `trim_smul` / 定理 `trim_smul`

English:
theorem trim_smul
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R)
  proof: ext trim_op (smul_apply m c)

中文:
定理 trim_smul
  结论: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (c : R)
  证明: ext trim_op (smul_apply m c)

Depends on / 依赖: smul_apply, trim_op
-/
theorem trim_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R)
    (m : OuterMeasure α) : (c • m).trim = c • m.trim :=
ext trim_op (smul_apply m c)

/--
theorem `trim_sup` / 定理 `trim_sup`

English:
theorem trim_sup
  given: (m₁ m₂ : OuterMeasure α)
  statement: (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim
  proof: ext fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm

中文:
定理 trim_sup
  条件: (m₁ m₂ : 外测度 α)
  结论: (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim
  证明: ext fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm

Depends on / 依赖: sup_apply, trim_binop
-/
theorem trim_sup (m₁ m₂ : OuterMeasure α) : (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim :=
  ext fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm

/--
theorem `trim_iSup` / 定理 `trim_iSup`

English:
theorem trim_iSup
  given: {ι} [Countable ι] (μ : ι -> OuterMeasure α)
  proof: by
  simp_rw [← @iSup_plift_down _ ι]
  ext1 s
  obtain ⟨t, _, _, hμt⟩ :=
    exists_measurable_superset_forall_eq_trim
      (Option.elim' (⨆ i, μ (PLift.down i)) (μ ∘ PLift.down)) s
  simp only [Option.forall, Option.elim'] at hμt
  simp only [iSup_apply, ← hμt.1]
  exact iSup_congr hμt.2

中文:
定理 trim_iSup
  条件: {ι} [可数 ι] (μ : ι -> 外测度 α)
  证明: by
  simp_rw [← @iSup_plift_down _ ι]
  ext1 s
  obtain ⟨t, _, _, hμt⟩ :=
    exists_measurable_superset_forall_eq_trim
      (Option.elim' (⨆ i, μ (PLift.down i)) (μ ∘ PLift.down)) s
  simp only [Option.forall, Option.elim'] at hμt
  simp only [iSup_apply, ← hμt.1]
  exact iSup_congr hμt.2

Depends on / 依赖: Option.elim, Option.forall, PLift.down, exists_measurable_superset_forall_eq_trim, iSup_apply, iSup_congr, iSup_plift_down, simp_rw
-/
theorem trim_iSup {ι} [Countable ι] (μ : ι -> OuterMeasure α) :
    trim (⨆ i, μ i) = ⨆ i, trim (μ i) := by
  simp_rw [← @iSup_plift_down _ ι]
  ext1 s
  obtain ⟨t, _, _, hμt⟩ :=
    exists_measurable_superset_forall_eq_trim
      (Option.elim' (⨆ i, μ (PLift.down i)) (μ ∘ PLift.down)) s
  simp only [Option.forall, Option.elim'] at hμt
  simp only [iSup_apply, ← hμt.1]
  exact iSup_congr hμt.2

/--
theorem `restrict_trim` / 定理 `restrict_trim`

English:
theorem restrict_trim
  given: {μ : OuterMeasure α} {s : Set α} (hs : MeasurableSet s)
  proof: by
  refine le_antisymm (fun t => ?_) (le_trim_iff.2 fun t ht => ?_)
  · rw [restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (t inter s) with ⟨t', htt', ht', hμt'⟩
    rw [← hμt']
    rw [inter_subset] at htt'
    refine (measure_mono htt').trans ?_
    rw [trim_eq _ (hs.compl.union 

中文:
定理 restrict_trim
  条件: {μ : 外测度 α} {s : 集合 α} (hs : 可测集 s)
  证明: by
  refine le_antisymm (fun t => ?_) (le_trim_iff.2 fun t ht => ?_)
  · rw [restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (t inter s) with ⟨t', htt', ht', hμt'⟩
    rw [← hμt']
    rw [inter_subset] at htt'
    refine (measure_mono htt').trans ?_
    rw [trim_eq _ (hs.compl.union 

Depends on / 依赖: Set.empty_union, compl_inter_self, empty_union, exists_measurable_superset_eq_trim, hs.compl.union, ht.inter, inter_subset, inter_subset_left, le_antisymm, le_trim_iff, measure_mono, restrict_apply, trim_eq, union_inter_distrib_right
-/
theorem restrict_trim {μ : OuterMeasure α} {s : Set α} (hs : MeasurableSet s) :
    (restrict s μ).trim = restrict s μ.trim := by
  refine le_antisymm (fun t => ?_) (le_trim_iff.2 fun t ht => ?_)
  · rw [restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (t inter s) with ⟨t', htt', ht', hμt'⟩
    rw [← hμt']
    rw [inter_subset] at htt'
    refine (measure_mono htt').trans ?_
    rw [trim_eq _ (hs.compl.union ht')]; rw [restrict_apply]; rw [union_inter_distrib_right]; rw [compl_inter_self]; rw [Set.empty_union]
    exact measure_mono inter_subset_left
  · rw [restrict_apply, trim_eq _ (ht.inter hs), restrict_apply]

end OuterMeasure

end MeasureTheory
