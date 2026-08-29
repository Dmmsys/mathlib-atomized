/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Sets.Compacts

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the compact subsets) to `ℝ≥0` that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, let us define a function `λ*` on open sets, by letting
  `λ* U` be the supremum of `λ K` for `K` included in `U`. This is a countably subadditive map that
  vanishes at `∅`. In Halmos (1950) this is called the *inner content* `λ*` of `λ`, and formalized
  as `innerContent`.
* Given an inner content, we define an outer measure `μ*`, by letting `μ* E` be the infimum of
  `λ* U` over the open sets `U` containing `E`. This is indeed an outer measure. It is formalized
  as `outerMeasure`.
* Restricting this outer measure to Borel sets gives a regular measure `μ`.

We define bundled contents as `Content`.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions

For `μ : Content G`, we define
* `μ.innerContent` : the inner content associated to `μ`.
* `μ.outerMeasure` : the outer measure associated to `μ`.
* `μ.measure` : the Borel measure associated to `μ`.

These definitions are given for spaces which are R₁.
The resulting measure `μ.measure` is always outer regular by design.
When the space is locally compact, `μ.measure` is also regular.

## References

* Paul Halmos (1950), Measure Theory, §53
* <https://en.wikipedia.org/wiki/Content_(measure_theory)>
-/

@[expose] public section


universe u v w

noncomputable section

open Set TopologicalSpace

open NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {G : Type w} [TopologicalSpace G]

/--
Definition of `Content` / `Content` 的定义

English:
structure Content
  parameters: (G : Type w) [TopologicalSpace G]
  axioms and operations (4):
    - toFun : Compacts G -> Real>=0
    - mono' : forall K₁ K₂ : Compacts G, (K₁ : Set G) subseteq K₂ -> toFun K₁ <= toFun K₂
    - sup_disjoint' : forall K₁ K₂ : Compacts G, Disjoint (K₁ : Set G) K₂ -> IsClosed (K₁ : Set G) -> IsClosed (K₂ : Set G) -> toFun (K₁ ⊔ K₂) = toFun K₁ + toFun K₂
    - sup_le' : forall K₁ K₂ : Compacts G, toFun (K₁ ⊔ K₂) <= toFun K₁ + toFun K₂

中文:
结构 内容
  参数: (G : 类型 w) [拓扑空间 G]
  公理与运算 (4 个):
    - toFun : 余mpacts G -> 实数>=0
    - mono' : 对任意 K₁ K₂ : 余mpacts G, (K₁ : 集合 G) subseteq K₂ -> toFun K₁ <= toFun K₂
    - sup_disjoint' : 对任意 K₁ K₂ : 余mpacts G, Disjoint (K₁ : 集合 G) K₂ -> 是闭集 (K₁ : 集合 G) -> 是闭集 (K₂ : 集合 G) -> toFun (K₁ ⊔ K₂) = toFun K₁ + toFun K₂
    - sup_le' : 对任意 K₁ K₂ : 余mpacts G, toFun (K₁ ⊔ K₂) <= toFun K₁ + toFun K₂
-/
structure Content (G : Type w) [TopologicalSpace G] where
  /-- The underlying additive function -/
  toFun : Compacts G -> Real>=0
  mono' : forall K₁ K₂ : Compacts G, (K₁ : Set G) subseteq K₂ -> toFun K₁ <= toFun K₂
  sup_disjoint' :
    forall K₁ K₂ : Compacts G, Disjoint (K₁ : Set G) K₂ -> IsClosed (K₁ : Set G) -> IsClosed (K₂ : Set G)
      -> toFun (K₁ ⊔ K₂) = toFun K₁ + toFun K₂
  sup_le' : forall K₁ K₂ : Compacts G, toFun (K₁ ⊔ K₂) <= toFun K₁ + toFun K₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Content G)
  body: ⟨{ toFun := fun _ => 0
      mono' := by simp
      sup_disjoint' := by simp
      sup_le' := by simp }⟩

中文:
实例 :
  签名: 可居 (内容 G)
  定义体: ⟨{ toFun := fun _ => 0
      mono' := by simp
      sup_disjoint' := by simp
      sup_le' := by simp }⟩

Depends on / 依赖: sup_disjoint, sup_le
-/
instance : Inhabited (Content G) :=
  ⟨{ toFun := fun _ => 0
      mono' := by simp
      sup_disjoint' := by simp
      sup_le' := by simp }⟩

namespace Content

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Content G) (Compacts G) Real>=0∞
  body: μ.toFun s
  coe_injective := by
rintro ⟨μ, _, _⟩ ⟨v, _, _⟩ h; congr!; ext s : 1; exact ENNReal.coe_injective congr_fun h s

中文:
实例 :
  签名: 函数状 (内容 G) (余mpacts G) 实数>=0∞
  定义体: μ.toFun s
  coe_injective := by
rintro ⟨μ, _, _⟩ ⟨v, _, _⟩ h; congr!; ext s : 1; exact ENNReal.coe_injective congr_fun h s
-/
instance : FunLike (Content G) (Compacts G) Real>=0∞ where
  coe μ s := μ.toFun s
  coe_injective := by
rintro ⟨μ, _, _⟩ ⟨v, _, _⟩ h; congr!; ext s : 1; exact ENNReal.coe_injective congr_fun h s

variable (μ : Content G)

/--
lemma `toFun_eq_toNNReal_apply` / 引理 `toFun_eq_toNNReal_apply`

English:
lemma toFun_eq_toNNReal_apply
  given: (K : Compacts G)
  statement: μ.toFun K = (μ K).toNNReal
  proof: rfl

@[simp]

中文:
引理 toFun_eq_toNN实数_apply
  条件: (K : 余mpacts G)
  结论: μ.toFun K = (μ K).toNN实数
  证明: rfl

@[simp]
-/
@[simp] lemma toFun_eq_toNNReal_apply (K : Compacts G) : μ.toFun K = (μ K).toNNReal := rfl

@[simp]
/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: (toFun : Compacts G -> Real>=0) (mono' sup_disjoint' sup_le') (K : Compacts G)
  proof: rfl

中文:
引理 mk_apply
  条件: (toFun : 余mpacts G -> 实数>=0) (mono' sup_disjoint' sup_le') (K : 余mpacts G)
  证明: rfl
-/
lemma mk_apply (toFun : Compacts G -> Real>=0) (mono' sup_disjoint' sup_le') (K : Compacts G) :
    mk toFun mono' sup_disjoint' sup_le' K = toFun K := rfl

/--
lemma `apply_ne_top` / 引理 `apply_ne_top`

English:
lemma apply_ne_top
  given: {K : Compacts G}
  statement: μ K != ∞
  proof: coe_ne_top

中文:
引理 apply_ne_top
  条件: {K : 余mpacts G}
  结论: μ K != ∞
  证明: coe_ne_top
-/
@[simp] lemma apply_ne_top {K : Compacts G} : μ K != ∞ := coe_ne_top

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (K₁ K₂ : Compacts G) (h : (K₁ : Set G) subseteq K₂)
  statement: μ K₁ <= μ K₂
  proof: by
  simpa using μ.mono' _ _ h

中文:
定理 mono
  条件: (K₁ K₂ : 余mpacts G) (h : (K₁ : 集合 G) subseteq K₂)
  结论: μ K₁ <= μ K₂
  证明: by
  simpa using μ.mono' _ _ h
-/
theorem mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) subseteq K₂) : μ K₁ <= μ K₂ := by
  simpa using μ.mono' _ _ h

/--
theorem `sup_disjoint` / 定理 `sup_disjoint`

English:
theorem sup_disjoint
  statement: (K₁ K₂ : Compacts G) (h : Disjoint (K₁ : Set G) K₂)
  proof: by
  simpa [toNNReal_eq_toNNReal_iff, ← toNNReal_add] using μ.sup_disjoint' _ _ h h₁ h₂

中文:
定理 sup_disjoint
  结论: (K₁ K₂ : 余mpacts G) (h : Disjoint (K₁ : 集合 G) K₂)
  证明: by
  simpa [toNNReal_eq_toNNReal_iff, ← toNNReal_add] using μ.sup_disjoint' _ _ h h₁ h₂

Depends on / 依赖: sup_disjoint, toNNReal_add, toNNReal_eq_toNNReal_iff
-/
theorem sup_disjoint (K₁ K₂ : Compacts G) (h : Disjoint (K₁ : Set G) K₂)
    (h₁ : IsClosed (K₁ : Set G)) (h₂ : IsClosed (K₂ : Set G)) :
    μ (K₁ ⊔ K₂) = μ K₁ + μ K₂ := by
  simpa [toNNReal_eq_toNNReal_iff, ← toNNReal_add] using μ.sup_disjoint' _ _ h h₁ h₂

/--
theorem `sup_le` / 定理 `sup_le`

English:
theorem sup_le
  given: (K₁ K₂ : Compacts G)
  statement: μ (K₁ ⊔ K₂) <= μ K₁ + μ K₂
  proof: by
  simpa [← toNNReal_add] using μ.sup_le' _ _

中文:
定理 sup_le
  条件: (K₁ K₂ : 余mpacts G)
  结论: μ (K₁ ⊔ K₂) <= μ K₁ + μ K₂
  证明: by
  simpa [← toNNReal_add] using μ.sup_le' _ _

Depends on / 依赖: sup_le, toNNReal_add
-/
theorem sup_le (K₁ K₂ : Compacts G) : μ (K₁ ⊔ K₂) <= μ K₁ + μ K₂ := by
  simpa [← toNNReal_add] using μ.sup_le' _ _

/--
theorem `lt_top` / 定理 `lt_top`

English:
theorem lt_top
  given: (K : Compacts G)
  statement: μ K < ∞
  proof: ENNReal.coe_lt_top

中文:
定理 lt_top
  条件: (K : 余mpacts G)
  结论: μ K < ∞
  证明: ENNReal.coe_lt_top

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, coe_lt_top
-/
theorem lt_top (K : Compacts G) : μ K < ∞ :=
  ENNReal.coe_lt_top

/--
theorem `empty` / 定理 `empty`

English:
theorem empty
  statement: μ ⊥ = 0
  proof: by simpa [toNNReal_eq_zero_iff] using μ.sup_disjoint' ⊥ ⊥

中文:
定理 empty
  结论: μ ⊥ = 0
  证明: by simpa [toNNReal_eq_zero_iff] using μ.sup_disjoint' ⊥ ⊥

Depends on / 依赖: sup_disjoint, toNNReal_eq_zero_iff
-/
theorem empty : μ ⊥ = 0 := by simpa [toNNReal_eq_zero_iff] using μ.sup_disjoint' ⊥ ⊥

/--
Definition of `innerContent` / `innerContent` 的定义

English:
definition innerContent
  signature: (U : Opens G)
  body: ⨆ (K : Compacts G) (_ : (K : Set G) subseteq U), μ K

中文:
定义 innerContent
  签名: (U : Opens G)
  定义体: ⨆ (K : Compacts G) (_ : (K : Set G) subseteq U), μ K

Depends on / 依赖: Compacts, subseteq
-/
def innerContent (U : Opens G) : Real>=0∞ :=
  ⨆ (K : Compacts G) (_ : (K : Set G) subseteq U), μ K

/--
theorem `le_innerContent` / 定理 `le_innerContent`

English:
theorem le_innerContent
  given: (K : Compacts G) (U : Opens G) (h2 : (K : Set G) subseteq U)
  proof: le_iSup_of_le K le_iSup (fun _ => (μ.toFun K : Real>=0∞)) h2

中文:
定理 le_innerContent
  条件: (K : 余mpacts G) (U : Opens G) (h2 : (K : 集合 G) subseteq U)
  证明: le_iSup_of_le K le_iSup (fun _ => (μ.toFun K : Real>=0∞)) h2

Depends on / 依赖: le_iSup, le_iSup_of_le
-/
theorem le_innerContent (K : Compacts G) (U : Opens G) (h2 : (K : Set G) subseteq U) :
    μ K <= μ.innerContent U :=
le_iSup_of_le K le_iSup (fun _ => (μ.toFun K : Real>=0∞)) h2

/--
theorem `innerContent_le` / 定理 `innerContent_le`

English:
theorem innerContent_le
  given: (U : Opens G) (K : Compacts G) (h2 : (U : Set G) subseteq K)
  proof: iSup₂_le fun _ hK' => μ.mono _ _ (Subset.trans hK' h2)

中文:
定理 innerContent_le
  条件: (U : Opens G) (K : 余mpacts G) (h2 : (U : 集合 G) subseteq K)
  证明: iSup₂_le fun _ hK' => μ.mono _ _ (Subset.trans hK' h2)

Depends on / 依赖: Subset, Subset.trans
-/
theorem innerContent_le (U : Opens G) (K : Compacts G) (h2 : (U : Set G) subseteq K) :
    μ.innerContent U <= μ K :=
  iSup₂_le fun _ hK' => μ.mono _ _ (Subset.trans hK' h2)

/--
theorem `innerContent_of_isCompact` / 定理 `innerContent_of_isCompact`

English:
theorem innerContent_of_isCompact
  given: {K : Set G} (h1K : IsCompact K) (h2K : IsOpen K)
  proof: le_antisymm (iSup₂_le fun _ hK' => μ.mono _ ⟨K, h1K⟩ hK') (μ.le_innerContent _ _ Subset.rfl)

中文:
定理 innerContent_of_isCompact
  条件: {K : 集合 G} (h1K : 是紧集 K) (h2K : 是开集 K)
  证明: le_antisymm (iSup₂_le fun _ hK' => μ.mono _ ⟨K, h1K⟩ hK') (μ.le_innerContent _ _ Subset.rfl)

Depends on / 依赖: Subset, Subset.rfl, le_antisymm, le_innerContent
-/
theorem innerContent_of_isCompact {K : Set G} (h1K : IsCompact K) (h2K : IsOpen K) :
    μ.innerContent ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
  le_antisymm (iSup₂_le fun _ hK' => μ.mono _ ⟨K, h1K⟩ hK') (μ.le_innerContent _ _ Subset.rfl)

/--
theorem `innerContent_bot` / 定理 `innerContent_bot`

English:
theorem innerContent_bot
  statement: μ.innerContent ⊥ = 0
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [← μ.empty]
  refine iSup₂_le fun K hK => ?_
  have : K = ⊥ := by
    ext1
    rw [subset_empty_iff.mp hK]; rw [Compacts.coe_bot]
  rw [this]

中文:
定理 innerContent_bot
  结论: μ.innerContent ⊥ = 0
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [← μ.empty]
  refine iSup₂_le fun K hK => ?_
  have : K = ⊥ := by
    ext1
    rw [subset_empty_iff.mp hK]; rw [Compacts.coe_bot]
  rw [this]

Depends on / 依赖: Compacts, Compacts.coe_bot, coe_bot, nonpos_iff_eq_zero, subset_empty_iff, subset_empty_iff.mp
-/
theorem innerContent_bot : μ.innerContent ⊥ = 0 := by
  rw [← nonpos_iff_eq_zero]; rw [← μ.empty]
  refine iSup₂_le fun K hK => ?_
  have : K = ⊥ := by
    ext1
    rw [subset_empty_iff.mp hK]; rw [Compacts.coe_bot]
  rw [this]

/--
theorem `innerContent_mono` / 定理 `innerContent_mono`

English:
theorem innerContent_mono
  given: ⦃U V
  statement: Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) :
  proof: biSup_mono fun _ hK => hK.trans h2

中文:
定理 innerContent_mono
  条件: ⦃U V
  结论: 集合 G⦄ (hU : 是开集 U) (hV : 是开集 V) (h2 : U subseteq V) :
  证明: biSup_mono fun _ hK => hK.trans h2

Depends on / 依赖: biSup_mono, hK.trans
-/
theorem innerContent_mono ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) :
    μ.innerContent ⟨U, hU⟩ <= μ.innerContent ⟨V, hV⟩ :=
  biSup_mono fun _ hK => hK.trans h2

/--
theorem `innerContent_exists_compact` / 定理 `innerContent_exists_compact`

English:
theorem innerContent_exists_compact
  statement: {U : Opens G} (hU : μ.innerContent U != ∞) {ε : Real>=0}
  proof: by
  have h'ε := ENNReal.coe_ne_zero.2 hε
  rcases le_or_gt (μ.innerContent U) ε with h | h
  · exact ⟨⊥, empty_subset _, le_add_left h⟩
  have h₂ := ENNReal.sub_lt_self hU h.ne_bot h'ε
  conv at h₂ => rhs; rw [innerContent]
  simp only [lt_iSup_iff] at h₂
  rcases h₂ with ⟨U, h1U, h2U⟩; refine ⟨U, 

中文:
定理 innerContent_存在_compact
  结论: {U : Opens G} (hU : μ.innerContent U != ∞) {ε : 实数>=0}
  证明: by
  have h'ε := ENNReal.coe_ne_zero.2 hε
  rcases le_or_gt (μ.innerContent U) ε with h | h
  · exact ⟨⊥, empty_subset _, le_add_left h⟩
  have h₂ := ENNReal.sub_lt_self hU h.ne_bot h'ε
  conv at h₂ => rhs; rw [innerContent]
  simp only [lt_iSup_iff] at h₂
  rcases h₂ with ⟨U, h1U, h2U⟩; refine ⟨U, 

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero, ENNReal.sub_lt_self, coe_ne_zero, empty_subset, h.ne_bot, innerContent, le_add_left, le_of_lt, le_or_gt, lt_iSup_iff, ne_bot, sub_lt_self, tsub_le_iff_right
-/
theorem innerContent_exists_compact {U : Opens G} (hU : μ.innerContent U != ∞) {ε : Real>=0}
    (hε : ε != 0) : exists K : Compacts G, (K : Set G) subseteq U ∧ μ.innerContent U <= μ K + ε := by
  have h'ε := ENNReal.coe_ne_zero.2 hε
  rcases le_or_gt (μ.innerContent U) ε with h | h
  · exact ⟨⊥, empty_subset _, le_add_left h⟩
  have h₂ := ENNReal.sub_lt_self hU h.ne_bot h'ε
  conv at h₂ => rhs; rw [innerContent]
  simp only [lt_iSup_iff] at h₂
  rcases h₂ with ⟨U, h1U, h2U⟩; refine ⟨U, h1U, ?_⟩
  rw [← tsub_le_iff_right]; exact le_of_lt h2U

/--
theorem `innerContent_iSup_nat` / 定理 `innerContent_iSup_nat`

English:
theorem innerContent_iSup_nat
  given: [R1Space G] (U : Nat -> Opens G)
  proof: by
  have h3 : forall (t : Finset Nat) (K : Nat -> Compacts G), μ (t.sup K) <= t.sum fun i => μ (K i) := by
    intro t K
    refine Finset.induction_on t ?_ ?_
    · simp only [μ.empty, nonpos_iff_eq_zero, Finset.sum_empty, Finset.sup_empty]
    · intro n s hn ih
      grw [Finset.sup_insert, Finse

中文:
定理 innerContent_iSup_nat
  条件: [R1空间 G] (U : 自然数 -> Opens G)
  证明: by
  have h3 : forall (t : Finset Nat) (K : Nat -> Compacts G), μ (t.sup K) <= t.sum fun i => μ (K i) := by
    intro t K
    refine Finset.induction_on t ?_ ?_
    · simp only [μ.empty, nonpos_iff_eq_zero, Finset.sum_empty, Finset.sup_empty]
    · intro n s hn ih
      grw [Finset.sup_insert, Finse

Depends on / 依赖: Compacts, Finset, Finset.induction_on, Finset.sum_empty, Finset.sum_insert, Finset.sup_empty, Finset.sup_insert, K.isCompact.elim_finite_subcover, K.isCompact.finite_compact_cover, Opens.coe_iSup, SetLike, SetLike.coe, coe_iSup, elim_finite_subcover, finite_compact_cover, induction_on, isCompact, isOpen, nonpos_iff_eq_zero, sum_empty
-/
theorem innerContent_iSup_nat [R1Space G] (U : Nat -> Opens G) :
    μ.innerContent (⨆ i : Nat, U i) <= ∑' i : Nat, μ.innerContent (U i) := by
  have h3 : forall (t : Finset Nat) (K : Nat -> Compacts G), μ (t.sup K) <= t.sum fun i => μ (K i) := by
    intro t K
    refine Finset.induction_on t ?_ ?_
    · simp only [μ.empty, nonpos_iff_eq_zero, Finset.sum_empty, Finset.sup_empty]
    · intro n s hn ih
      grw [Finset.sup_insert, Finset.sum_insert hn, μ.sup_le, ih]
  refine iSup₂_le fun K hK => ?_
  obtain ⟨t, ht⟩ :=
    K.isCompact.elim_finite_subcover _ (fun i => (U i).isOpen) (by rwa [← Opens.coe_iSup])
  rcases K.isCompact.finite_compact_cover t (SetLike.coe ∘ U) (fun i _ => (U i).isOpen) ht with
    ⟨K', h1K', h2K', h3K'⟩
  let L : Nat -> Compacts G := fun n => ⟨K' n, h1K' n⟩
  convert! le_trans (h3 t L) _
  · ext1
    rw [Compacts.coe_finset_sup]; rw [Finset.sup_eq_iSup]
    exact h3K'
  refine le_trans (Finset.sum_le_sum ?_) (ENNReal.sum_le_tsum t)
  intro i _
  refine le_trans ?_ (le_iSup _ (L i))
  refine le_trans ?_ (le_iSup _ (h2K' i))
  rfl

/--
theorem `innerContent_iUnion_nat` / 定理 `innerContent_iUnion_nat`

English:
theorem innerContent_iUnion_nat
  given: [R1Space G] ⦃U
  statement: Nat -> Set G⦄
  proof: by
  have := μ.innerContent_iSup_nat fun i => ⟨U i, hU i⟩
  rwa [Opens.iSup_def] at this

中文:
定理 innerContent_iUnion_nat
  条件: [R1空间 G] ⦃U
  结论: 自然数 -> 集合 G⦄
  证明: by
  have := μ.innerContent_iSup_nat fun i => ⟨U i, hU i⟩
  rwa [Opens.iSup_def] at this

Depends on / 依赖: Opens.iSup_def, iSup_def, innerContent_iSup_nat
-/
theorem innerContent_iUnion_nat [R1Space G] ⦃U : Nat -> Set G⦄
    (hU : forall i : Nat, IsOpen (U i)) :
    μ.innerContent ⟨⋃ i : Nat, U i, isOpen_iUnion hU⟩ <= ∑' i : Nat, μ.innerContent ⟨U i, hU i⟩ := by
  have := μ.innerContent_iSup_nat fun i => ⟨U i, hU i⟩
  rwa [Opens.iSup_def] at this

/--
theorem `innerContent_comap` / 定理 `innerContent_comap`

English:
theorem innerContent_comap
  statement: (f : G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
  proof: by
  refine (Compacts.equiv f).surjective.iSup_congr _ fun K => iSup_congr_Prop image_subset_iff ?_
  intro hK
  simp only [Compacts.equiv]
  apply h

@[to_additive]

中文:
定理 innerContent_comap
  结论: (f : G ≃ₜ G) (h : 对任意 ⦃K : 余mpacts G⦄, μ (K.map f f.continuous) = μ K)
  证明: by
  refine (Compacts.equiv f).surjective.iSup_congr _ fun K => iSup_congr_Prop image_subset_iff ?_
  intro hK
  simp only [Compacts.equiv]
  apply h

@[to_additive]

Depends on / 依赖: Compacts, Compacts.equiv, iSup_congr, iSup_congr_Prop, image_subset_iff, surjective, surjective.iSup_congr
-/
theorem innerContent_comap (f : G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
    (U : Opens G) : μ.innerContent (Opens.comap f U) = μ.innerContent U := by
  refine (Compacts.equiv f).surjective.iSup_congr _ fun K => iSup_congr_Prop image_subset_iff ?_
  intro hK
  simp only [Compacts.equiv]
  apply h

@[to_additive]
/--
theorem `is_mul_left_invariant_innerContent` / 定理 `is_mul_left_invariant_innerContent`

English:
theorem is_mul_left_invariant_innerContent
  statement: [Group G] [SeparatelyContinuousMul G]
  proof: by
  convert! μ.innerContent_comap (Homeomorph.mulLeft g) (fun K => h g) U

@[to_additive]

中文:
定理 is_mul_left_invariant_innerContent
  结论: [群 G] [SeparatelyContinuousMul G]
  证明: by
  convert! μ.innerContent_comap (Homeomorph.mulLeft g) (fun K => h g) U

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, convert, innerContent_comap, mulLeft
-/
theorem is_mul_left_invariant_innerContent [Group G] [SeparatelyContinuousMul G]
    (h : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (g : G)
    (U : Opens G) :
    μ.innerContent (Opens.comap (Homeomorph.mulLeft g) U) = μ.innerContent U := by
  convert! μ.innerContent_comap (Homeomorph.mulLeft g) (fun K => h g) U

@[to_additive]
/--
theorem `innerContent_pos_of_is_mul_left_invariant` / 定理 `innerContent_pos_of_is_mul_left_invariant`

English:
theorem innerContent_pos_of_is_mul_left_invariant
  statement: [Group G] [IsTopologicalGroup G]
  proof: by
  have : (interior (U : Set G)).Nonempty := by rwa [U.isOpen.interior_eq]
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩
  suffices μ K <= s.card * μ.innerContent U by
    exact (ENNReal.mul_pos_iff.mp <| hK.bot_lt.trans_le this).2
  have : (K : Set G) subseteq ↑(⨆ g in s, 

中文:
定理 innerContent_pos_of_is_mul_left_invariant
  结论: [群 G] [是拓扑群 G]
  证明: by
  have : (interior (U : Set G)).Nonempty := by rwa [U.isOpen.interior_eq]
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩
  suffices μ K <= s.card * μ.innerContent U by
    exact (ENNReal.mul_pos_iff.mp <| hK.bot_lt.trans_le this).2
  have : (K : Set G) subseteq ↑(⨆ g in s, 

Depends on / 依赖: ENNReal, ENNReal.mul_pos_iff.mp, Homeomorph, Homeomorph.mulLeft, Nonempty, Opens.coe_comap, Opens.comap, Opens.iSup_def, Subtype, Subtype.coe_mk, U.isOpen.interior_eq, bot_lt, coe_comap, coe_mk, compact_covered_by_mul_left_translates, hK.bot_lt.trans_le, iSup_def, innerContent, innerContent_b, interior
-/
theorem innerContent_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G]
    (h3 : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (K : Compacts G)
    (hK : μ K != 0) (U : Opens G) (hU : (U : Set G).Nonempty) : 0 < μ.innerContent U := by
  have : (interior (U : Set G)).Nonempty := by rwa [U.isOpen.interior_eq]
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩
  suffices μ K <= s.card * μ.innerContent U by
    exact (ENNReal.mul_pos_iff.mp <| hK.bot_lt.trans_le this).2
  have : (K : Set G) subseteq ↑(⨆ g in s, Opens.comap (Homeomorph.mulLeft g : C(G, G)) U) := by
    simpa only [Opens.iSup_def, Opens.coe_comap, Subtype.coe_mk]
  refine (μ.le_innerContent _ _ this).trans ?_
  refine
    (rel_iSup_sum μ.innerContent μ.innerContent_bot (· <= ·) μ.innerContent_iSup_nat _ _).trans ?_
  simp only [μ.is_mul_left_invariant_innerContent h3, Finset.sum_const, nsmul_eq_mul, le_refl]

/--
theorem `innerContent_mono'` / 定理 `innerContent_mono'`

English:
theorem innerContent_mono'
  given: ⦃U V
  statement: Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) :
  proof: biSup_mono fun _ hK => hK.trans h2

中文:
定理 innerContent_mono'
  条件: ⦃U V
  结论: 集合 G⦄ (hU : 是开集 U) (hV : 是开集 V) (h2 : U subseteq V) :
  证明: biSup_mono fun _ hK => hK.trans h2

Depends on / 依赖: biSup_mono, hK.trans
-/
theorem innerContent_mono' ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) :
    μ.innerContent ⟨U, hU⟩ <= μ.innerContent ⟨V, hV⟩ :=
  biSup_mono fun _ hK => hK.trans h2

section OuterMeasure

/--
Definition of `outerMeasure` / `outerMeasure` 的定义

English:
definition outerMeasure
  signature: : OuterMeasure G
  body: inducedOuterMeasure (fun U hU => μ.innerContent ⟨U, hU⟩) isOpen_empty μ.innerContent_bot

中文:
定义 outerMeasure
  签名: : 外测度 G
  定义体: inducedOuterMeasure (fun U hU => μ.innerContent ⟨U, hU⟩) isOpen_empty μ.innerContent_bot
-/
protected def outerMeasure : OuterMeasure G :=
  inducedOuterMeasure (fun U hU => μ.innerContent ⟨U, hU⟩) isOpen_empty μ.innerContent_bot

variable [R1Space G]

/--
theorem `outerMeasure_opens` / 定理 `outerMeasure_opens`

English:
theorem outerMeasure_opens
  given: (U : Opens G)
  statement: μ.outerMeasure U = μ.innerContent U
  proof: inducedOuterMeasure_eq' (fun _ => isOpen_iUnion) μ.innerContent_iUnion_nat μ.innerContent_mono U.2

中文:
定理 outerMeasure_opens
  条件: (U : Opens G)
  结论: μ.outerMeasure U = μ.innerContent U
  证明: inducedOuterMeasure_eq' (fun _ => isOpen_iUnion) μ.innerContent_iUnion_nat μ.innerContent_mono U.2

Depends on / 依赖: inducedOuterMeasure_eq, innerContent_iUnion_nat, innerContent_mono, isOpen_iUnion
-/
theorem outerMeasure_opens (U : Opens G) : μ.outerMeasure U = μ.innerContent U :=
  inducedOuterMeasure_eq' (fun _ => isOpen_iUnion) μ.innerContent_iUnion_nat μ.innerContent_mono U.2

/--
theorem `outerMeasure_of_isOpen` / 定理 `outerMeasure_of_isOpen`

English:
theorem outerMeasure_of_isOpen
  given: (U : Set G) (hU : IsOpen U)
  proof: μ.outerMeasure_opens ⟨U, hU⟩

中文:
定理 outerMeasure_of_isOpen
  条件: (U : 集合 G) (hU : 是开集 U)
  证明: μ.outerMeasure_opens ⟨U, hU⟩

Depends on / 依赖: outerMeasure_opens
-/
theorem outerMeasure_of_isOpen (U : Set G) (hU : IsOpen U) :
    μ.outerMeasure U = μ.innerContent ⟨U, hU⟩ :=
  μ.outerMeasure_opens ⟨U, hU⟩

/--
theorem `outerMeasure_le` / 定理 `outerMeasure_le`

English:
theorem outerMeasure_le
  given: (U : Opens G) (K : Compacts G) (hUK : (U : Set G) subseteq K)
  proof: (μ.outerMeasure_opens U).le.trans μ.innerContent_le U K hUK

中文:
定理 outerMeasure_le
  条件: (U : Opens G) (K : 余mpacts G) (hUK : (U : 集合 G) subseteq K)
  证明: (μ.outerMeasure_opens U).le.trans μ.innerContent_le U K hUK

Depends on / 依赖: innerContent_le, le.trans, outerMeasure_opens
-/
theorem outerMeasure_le (U : Opens G) (K : Compacts G) (hUK : (U : Set G) subseteq K) :
    μ.outerMeasure U <= μ K :=
(μ.outerMeasure_opens U).le.trans μ.innerContent_le U K hUK

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_outerMeasure_compacts` / 定理 `le_outerMeasure_compacts`

English:
theorem le_outerMeasure_compacts
  given: (K : Compacts G)
  statement: μ K <= μ.outerMeasure K
  proof: by
  rw [Content.outerMeasure]; rw [inducedOuterMeasure_eq_iInf]
· exact le_iInf fun U => le_iInf fun hU => le_iInf μ.le_innerContent K ⟨U, hU⟩
  · exact fun U hU => isOpen_iUnion hU
  · exact μ.innerContent_iUnion_nat
  · exact μ.innerContent_mono

中文:
定理 le_outerMeasure_compacts
  条件: (K : 余mpacts G)
  结论: μ K <= μ.outerMeasure K
  证明: by
  rw [Content.outerMeasure]; rw [inducedOuterMeasure_eq_iInf]
· exact le_iInf fun U => le_iInf fun hU => le_iInf μ.le_innerContent K ⟨U, hU⟩
  · exact fun U hU => isOpen_iUnion hU
  · exact μ.innerContent_iUnion_nat
  · exact μ.innerContent_mono

Depends on / 依赖: Content, Content.outerMeasure, inducedOuterMeasure_eq_iInf, innerContent_iUnion_nat, innerContent_mono, isOpen_iUnion, le_iInf, le_innerContent, outerMeasure
-/
theorem le_outerMeasure_compacts (K : Compacts G) : μ K <= μ.outerMeasure K := by
  rw [Content.outerMeasure]; rw [inducedOuterMeasure_eq_iInf]
· exact le_iInf fun U => le_iInf fun hU => le_iInf μ.le_innerContent K ⟨U, hU⟩
  · exact fun U hU => isOpen_iUnion hU
  · exact μ.innerContent_iUnion_nat
  · exact μ.innerContent_mono

/--
theorem `outerMeasure_eq_iInf` / 定理 `outerMeasure_eq_iInf`

English:
theorem outerMeasure_eq_iInf
  given: (A : Set G)
  proof: inducedOuterMeasure_eq_iInf _ μ.innerContent_iUnion_nat μ.innerContent_mono A

中文:
定理 outerMeasure_eq_iInf
  条件: (A : 集合 G)
  证明: inducedOuterMeasure_eq_iInf _ μ.innerContent_iUnion_nat μ.innerContent_mono A

Depends on / 依赖: inducedOuterMeasure_eq_iInf, innerContent_iUnion_nat, innerContent_mono
-/
theorem outerMeasure_eq_iInf (A : Set G) :
    μ.outerMeasure A = ⨅ (U : Set G) (hU : IsOpen U) (_ : A subseteq U), μ.innerContent ⟨U, hU⟩ :=
  inducedOuterMeasure_eq_iInf _ μ.innerContent_iUnion_nat μ.innerContent_mono A

/--
theorem `outerMeasure_interior_compacts` / 定理 `outerMeasure_interior_compacts`

English:
theorem outerMeasure_interior_compacts
  given: (K : Compacts G)
  statement: μ.outerMeasure (interior K) <= μ K
  proof: (μ.outerMeasure_opens <| Opens.interior K).le.trans μ.innerContent_le _ _ interior_subset

中文:
定理 outerMeasure_interior_compacts
  条件: (K : 余mpacts G)
  结论: μ.outerMeasure (interior K) <= μ K
  证明: (μ.outerMeasure_opens <| Opens.interior K).le.trans μ.innerContent_le _ _ interior_subset

Depends on / 依赖: Opens.interior, innerContent_le, interior, interior_subset, le.trans, outerMeasure_opens
-/
theorem outerMeasure_interior_compacts (K : Compacts G) : μ.outerMeasure (interior K) <= μ K :=
(μ.outerMeasure_opens <| Opens.interior K).le.trans μ.innerContent_le _ _ interior_subset

/--
theorem `outerMeasure_exists_compact` / 定理 `outerMeasure_exists_compact`

English:
theorem outerMeasure_exists_compact
  statement: {U : Opens G} (hU : μ.outerMeasure U != ∞) {ε : Real>=0}
  proof: by
  rw [μ.outerMeasure_opens] at hU ⊢
  rcases μ.innerContent_exists_compact hU hε with ⟨K, h1K, h2K⟩
  exact ⟨K, h1K, by grw [h2K, μ.le_outerMeasure_compacts K]⟩

中文:
定理 outerMeasure_存在_compact
  结论: {U : Opens G} (hU : μ.outerMeasure U != ∞) {ε : 实数>=0}
  证明: by
  rw [μ.outerMeasure_opens] at hU ⊢
  rcases μ.innerContent_exists_compact hU hε with ⟨K, h1K, h2K⟩
  exact ⟨K, h1K, by grw [h2K, μ.le_outerMeasure_compacts K]⟩

Depends on / 依赖: innerContent_exists_compact, le_outerMeasure_compacts, outerMeasure_opens
-/
theorem outerMeasure_exists_compact {U : Opens G} (hU : μ.outerMeasure U != ∞) {ε : Real>=0}
    (hε : ε != 0) : exists K : Compacts G, (K : Set G) subseteq U ∧ μ.outerMeasure U <= μ.outerMeasure K + ε := by
  rw [μ.outerMeasure_opens] at hU ⊢
  rcases μ.innerContent_exists_compact hU hε with ⟨K, h1K, h2K⟩
  exact ⟨K, h1K, by grw [h2K, μ.le_outerMeasure_compacts K]⟩

/--
theorem `outerMeasure_exists_open` / 定理 `outerMeasure_exists_open`

English:
theorem outerMeasure_exists_open
  given: {A : Set G} (hA : μ.outerMeasure A != ∞) {ε : Real>=0} (hε : ε != 0)
  proof: by
  rcases inducedOuterMeasure_exists_set _ μ.innerContent_iUnion_nat μ.innerContent_mono hA
      (ENNReal.coe_ne_zero.2 hε) with
    ⟨U, hU, h2U, h3U⟩
  exact ⟨⟨U, hU⟩, h2U, h3U⟩

中文:
定理 outerMeasure_存在_open
  条件: {A : 集合 G} (hA : μ.outerMeasure A != ∞) {ε : 实数>=0} (hε : ε != 0)
  证明: by
  rcases inducedOuterMeasure_exists_set _ μ.innerContent_iUnion_nat μ.innerContent_mono hA
      (ENNReal.coe_ne_zero.2 hε) with
    ⟨U, hU, h2U, h3U⟩
  exact ⟨⟨U, hU⟩, h2U, h3U⟩

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero, coe_ne_zero, inducedOuterMeasure_exists_set, innerContent_iUnion_nat, innerContent_mono
-/
theorem outerMeasure_exists_open {A : Set G} (hA : μ.outerMeasure A != ∞) {ε : Real>=0} (hε : ε != 0) :
    exists U : Opens G, A subseteq U ∧ μ.outerMeasure U <= μ.outerMeasure A + ε := by
  rcases inducedOuterMeasure_exists_set _ μ.innerContent_iUnion_nat μ.innerContent_mono hA
      (ENNReal.coe_ne_zero.2 hε) with
    ⟨U, hU, h2U, h3U⟩
  exact ⟨⟨U, hU⟩, h2U, h3U⟩

/--
theorem `outerMeasure_preimage` / 定理 `outerMeasure_preimage`

English:
theorem outerMeasure_preimage
  statement: (f : G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
  proof: by
  refine inducedOuterMeasure_preimage _ μ.innerContent_iUnion_nat μ.innerContent_mono _
    (fun _ => f.isOpen_preimage) ?_
  intro s hs
  convert! μ.innerContent_comap f h ⟨s, hs⟩

中文:
定理 outerMeasure_preimage
  结论: (f : G ≃ₜ G) (h : 对任意 ⦃K : 余mpacts G⦄, μ (K.map f f.continuous) = μ K)
  证明: by
  refine inducedOuterMeasure_preimage _ μ.innerContent_iUnion_nat μ.innerContent_mono _
    (fun _ => f.isOpen_preimage) ?_
  intro s hs
  convert! μ.innerContent_comap f h ⟨s, hs⟩

Depends on / 依赖: convert, f.isOpen_preimage, inducedOuterMeasure_preimage, innerContent_comap, innerContent_iUnion_nat, innerContent_mono, isOpen_preimage
-/
theorem outerMeasure_preimage (f : G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
    (A : Set G) : μ.outerMeasure (f ⁻¹' A) = μ.outerMeasure A := by
  refine inducedOuterMeasure_preimage _ μ.innerContent_iUnion_nat μ.innerContent_mono _
    (fun _ => f.isOpen_preimage) ?_
  intro s hs
  convert! μ.innerContent_comap f h ⟨s, hs⟩

/--
theorem `outerMeasure_lt_top_of_isCompact` / 定理 `outerMeasure_lt_top_of_isCompact`

English:
theorem outerMeasure_lt_top_of_isCompact
  statement: [WeaklyLocallyCompactSpace G]
  proof: by
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩
  calc
    μ.outerMeasure K <= μ.outerMeasure (interior F) := measure_mono h2F
    _ <= μ ⟨F, h1F⟩ := by
      apply μ.outerMeasure_le ⟨interior F, isOpen_interior⟩ ⟨F, h1F⟩ interior_subset
    _ < ⊤ := μ.lt_top _

@[to_additive]

中文:
定理 outerMeasure_lt_top_of_isCompact
  结论: [WeaklyLocallyCompact空间 G]
  证明: by
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩
  calc
    μ.outerMeasure K <= μ.outerMeasure (interior F) := measure_mono h2F
    _ <= μ ⟨F, h1F⟩ := by
      apply μ.outerMeasure_le ⟨interior F, isOpen_interior⟩ ⟨F, h1F⟩ interior_subset
    _ < ⊤ := μ.lt_top _

@[to_additive]

Depends on / 依赖: exists_compact_superset, interior, interior_subset, isOpen_interior, lt_top, measure_mono, outerMeasure, outerMeasure_le
-/
theorem outerMeasure_lt_top_of_isCompact [WeaklyLocallyCompactSpace G]
    {K : Set G} (hK : IsCompact K) :
    μ.outerMeasure K < ∞ := by
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩
  calc
    μ.outerMeasure K <= μ.outerMeasure (interior F) := measure_mono h2F
    _ <= μ ⟨F, h1F⟩ := by
      apply μ.outerMeasure_le ⟨interior F, isOpen_interior⟩ ⟨F, h1F⟩ interior_subset
    _ < ⊤ := μ.lt_top _

@[to_additive]
/--
theorem `is_mul_left_invariant_outerMeasure` / 定理 `is_mul_left_invariant_outerMeasure`

English:
theorem is_mul_left_invariant_outerMeasure
  statement: [Group G] [SeparatelyContinuousMul G]
  proof: by
  convert! μ.outerMeasure_preimage (Homeomorph.mulLeft g) (fun K => h g) A

中文:
定理 is_mul_left_invariant_outerMeasure
  结论: [群 G] [SeparatelyContinuousMul G]
  证明: by
  convert! μ.outerMeasure_preimage (Homeomorph.mulLeft g) (fun K => h g) A

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, convert, mulLeft, outerMeasure_preimage
-/
theorem is_mul_left_invariant_outerMeasure [Group G] [SeparatelyContinuousMul G]
    (h : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (g : G)
    (A : Set G) : μ.outerMeasure ((g * ·) ⁻¹' A) = μ.outerMeasure A := by
  convert! μ.outerMeasure_preimage (Homeomorph.mulLeft g) (fun K => h g) A

/--
theorem `outerMeasure_caratheodory` / 定理 `outerMeasure_caratheodory`

English:
theorem outerMeasure_caratheodory
  given: (A : Set G)
  proof: by
  rw [Opens.forall]
  apply inducedOuterMeasure_caratheodory
  · apply innerContent_iUnion_nat
  · apply innerContent_mono'

@[to_additive]

中文:
定理 outerMeasure_caratheodory
  条件: (A : 集合 G)
  证明: by
  rw [Opens.forall]
  apply inducedOuterMeasure_caratheodory
  · apply innerContent_iUnion_nat
  · apply innerContent_mono'

@[to_additive]

Depends on / 依赖: Opens.forall, inducedOuterMeasure_caratheodory, innerContent_iUnion_nat, innerContent_mono
-/
theorem outerMeasure_caratheodory (A : Set G) :
    MeasurableSet[μ.outerMeasure.caratheodory] A ↔
      forall U : Opens G, μ.outerMeasure (U inter A) + μ.outerMeasure (U \ A) <= μ.outerMeasure U := by
  rw [Opens.forall]
  apply inducedOuterMeasure_caratheodory
  · apply innerContent_iUnion_nat
  · apply innerContent_mono'

@[to_additive]
/--
theorem `outerMeasure_pos_of_is_mul_left_invariant` / 定理 `outerMeasure_pos_of_is_mul_left_invariant`

English:
theorem outerMeasure_pos_of_is_mul_left_invariant
  statement: [Group G] [IsTopologicalGroup G]
  proof: by
  convert! μ.innerContent_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U
  exact μ.outerMeasure_opens ⟨U, h1U⟩

中文:
定理 outerMeasure_pos_of_is_mul_left_invariant
  结论: [群 G] [是拓扑群 G]
  证明: by
  convert! μ.innerContent_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U
  exact μ.outerMeasure_opens ⟨U, h1U⟩

Depends on / 依赖: convert, innerContent_pos_of_is_mul_left_invariant, outerMeasure_opens
-/
theorem outerMeasure_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G]
    (h3 : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (K : Compacts G)
    (hK : μ K != 0) {U : Set G} (h1U : IsOpen U) (h2U : U.Nonempty) : 0 < μ.outerMeasure U := by
  convert! μ.innerContent_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U
  exact μ.outerMeasure_opens ⟨U, h1U⟩

variable [S : MeasurableSpace G] [BorelSpace G]

/--
theorem `borel_le_caratheodory` / 定理 `borel_le_caratheodory`

English:
theorem borel_le_caratheodory
  statement: S <= μ.outerMeasure.caratheodory
  proof: by
  rw [BorelSpace.measurable_eq (α := G)]
  refine MeasurableSpace.generateFrom_le ?_
  intro U hU
  rw [μ.outerMeasure_caratheodory]
  intro U'
  rw [μ.outerMeasure_of_isOpen ((U' : Set G) inter U) (U'.isOpen.inter hU)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  have : Nonemp

中文:
定理 borel_le_caratheodory
  结论: S <= μ.outerMeasure.caratheodory
  证明: by
  rw [BorelSpace.measurable_eq (α := G)]
  refine MeasurableSpace.generateFrom_le ?_
  intro U hU
  rw [μ.outerMeasure_caratheodory]
  intro U'
  rw [μ.outerMeasure_of_isOpen ((U' : Set G) inter U) (U'.isOpen.inter hU)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  have : Nonemp

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq, Compacts, ENNReal, ENNReal.iSup_add, L.isCompact.closure, MeasurableSpace, MeasurableSpace.generateFrom_le, Nonempty, Opens.coe_mk, closure, coe_mk, empty_subset, generateFrom_le, iSup_add, iSup_le, iSup_subtype, innerContent, isCompact, isOpen
-/
theorem borel_le_caratheodory : S <= μ.outerMeasure.caratheodory := by
  rw [BorelSpace.measurable_eq (α := G)]
  refine MeasurableSpace.generateFrom_le ?_
  intro U hU
  rw [μ.outerMeasure_caratheodory]
  intro U'
  rw [μ.outerMeasure_of_isOpen ((U' : Set G) inter U) (U'.isOpen.inter hU)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  have : Nonempty { L : Compacts G // (L : Set G) subseteq U' inter U } := ⟨⟨⊥, empty_subset _⟩⟩
  rw [ENNReal.iSup_add]
  refine iSup_le ?_
  rintro ⟨L, hL⟩
  let L' : Compacts G := ⟨closure L, L.isCompact.closure⟩
  dsimp
  grw [show μ L <= μ L' from μ.mono _ _ subset_closure]
  simp only [subset_inter_iff] at hL
  have hL'U : (L' : Set G) subseteq U := IsCompact.closure_subset_of_isOpen L.2 hU hL.2
  have hL'U' : (L' : Set G) subseteq (U' : Set G) := IsCompact.closure_subset_of_isOpen L.2 U'.2 hL.1
  have : ↑U' \ U subseteq U' \ L' := sdiff_subset_sdiff_right hL'U
  grw [this]
  rw [μ.outerMeasure_of_isOpen (↑U' \ L') (IsOpen.sdiff U'.2 isClosed_closure)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  have : Nonempty { M : Compacts G // (M : Set G) subseteq ↑U' \ closure L } := ⟨⟨⊥, empty_subset _⟩⟩
  rw [ENNReal.add_iSup]
  refine iSup_le ?_
  rintro ⟨M, hM⟩
  let M' : Compacts G := ⟨closure M, M.isCompact.closure⟩
  dsimp
  grw [show μ M <= μ M' from μ.mono _ _ subset_closure]
  have hM' : (M' : Set G) subseteq U' \ L' :=
    IsCompact.closure_subset_of_isOpen M.2 (IsOpen.sdiff U'.2 isClosed_closure) hM
  have : (↑(L' ⊔ M') : Set G) subseteq U' := by
    simp only [Compacts.coe_sup, union_subset_iff, hL'U', true_and]
    exact hM'.trans sdiff_subset
  rw [μ.outerMeasure_of_isOpen (↑U') U'.2]
  refine le_trans (ge_of_eq ?_) (μ.le_innerContent _ _ this)
  exact μ.sup_disjoint L' M' (subset_sdiff.1 hM').2.symm isClosed_closure isClosed_closure

/--
Definition of `measure` / `measure` 的定义

English:
definition measure
  signature: : Measure G
  body: μ.outerMeasure.toMeasure μ.borel_le_caratheodory

中文:
定义 measure
  签名: : 测度 G
  定义体: μ.outerMeasure.toMeasure μ.borel_le_caratheodory
-/
protected def measure : Measure G :=
  μ.outerMeasure.toMeasure μ.borel_le_caratheodory

/--
theorem `measure_apply` / 定理 `measure_apply`

English:
theorem measure_apply
  given: {s : Set G} (hs : MeasurableSet s)
  statement: μ.measure s = μ.outerMeasure s
  proof: toMeasure_apply _ _ hs

中文:
定理 measure_apply
  条件: {s : 集合 G} (hs : 可测集 s)
  结论: μ.measure s = μ.outerMeasure s
  证明: toMeasure_apply _ _ hs

Depends on / 依赖: toMeasure_apply
-/
theorem measure_apply {s : Set G} (hs : MeasurableSet s) : μ.measure s = μ.outerMeasure s :=
  toMeasure_apply _ _ hs

/--
Instance `outerRegular` / 实例 `outerRegular`

English:
instance outerRegular
  signature: : μ.measure.OuterRegular
  body: by
  refine ⟨fun A hA r (hr : _ < _) => ?_⟩
  rw [μ.measure_apply hA]; rw [outerMeasure_eq_iInf] at hr
  simp only [iInf_lt_iff] at hr
  rcases hr with ⟨U, hUo, hAU, hr⟩
  rw [← μ.outerMeasure_of_isOpen U hUo]; rw [← μ.measure_apply hUo.measurableSet] at hr
  exact ⟨U, hAU, hUo, hr⟩

中文:
实例 outerRegular
  签名: : μ.measure.外正则
  定义体: by
  refine ⟨fun A hA r (hr : _ < _) => ?_⟩
  rw [μ.measure_apply hA]; rw [outerMeasure_eq_iInf] at hr
  simp only [iInf_lt_iff] at hr
  rcases hr with ⟨U, hUo, hAU, hr⟩
  rw [← μ.outerMeasure_of_isOpen U hUo]; rw [← μ.measure_apply hUo.measurableSet] at hr
  exact ⟨U, hAU, hUo, hr⟩

Depends on / 依赖: hUo.measurableSet, iInf_lt_iff, measurableSet, measure_apply, outerMeasure_eq_iInf, outerMeasure_of_isOpen
-/
instance outerRegular : μ.measure.OuterRegular := by
  refine ⟨fun A hA r (hr : _ < _) => ?_⟩
  rw [μ.measure_apply hA]; rw [outerMeasure_eq_iInf] at hr
  simp only [iInf_lt_iff] at hr
  rcases hr with ⟨U, hUo, hAU, hr⟩
  rw [← μ.outerMeasure_of_isOpen U hUo]; rw [← μ.measure_apply hUo.measurableSet] at hr
  exact ⟨U, hAU, hUo, hr⟩

/--
Instance `regular` / 实例 `regular`

English:
instance regular
  signature: [WeaklyLocallyCompactSpace G]
  body: by
  have : IsFiniteMeasureOnCompacts μ.measure := by
    refine ⟨fun K hK => ?_⟩
    apply (measure_mono subset_closure).trans_lt _
    rw [measure_apply _ isClosed_closure.measurableSet]
    exact μ.outerMeasure_lt_top_of_isCompact hK.closure
  refine ⟨fun U hU r hr => ?_⟩
  rw [measure_apply _ hU

中文:
实例 regular
  签名: [WeaklyLocallyCompact空间 G]
  定义体: by
  have : IsFiniteMeasureOnCompacts μ.measure := by
    refine ⟨fun K hK => ?_⟩
    apply (measure_mono subset_closure).trans_lt _
    rw [measure_apply _ isClosed_closure.measurableSet]
    exact μ.outerMeasure_lt_top_of_isCompact hK.closure
  refine ⟨fun U hU r hr => ?_⟩
  rw [measure_apply _ hU

Depends on / 依赖: IsFiniteMeasureOnCompacts, closure, hK.closure, hU.measurableSet, hr.trans_le, innerContent, isClosed_closure, isClosed_closure.measurableSet, le_outerMeasure_compacts, le_toMeasur, lt_iSup_iff, measurableSet, measure, measure_apply, measure_mono, outerMeasure_lt_top_of_isCompact, outerMeasure_of_isOpen, subset_closure, trans_le, trans_lt
-/
instance regular [WeaklyLocallyCompactSpace G] : μ.measure.Regular := by
  have : IsFiniteMeasureOnCompacts μ.measure := by
    refine ⟨fun K hK => ?_⟩
    apply (measure_mono subset_closure).trans_lt _
    rw [measure_apply _ isClosed_closure.measurableSet]
    exact μ.outerMeasure_lt_top_of_isCompact hK.closure
  refine ⟨fun U hU r hr => ?_⟩
  rw [measure_apply _ hU.measurableSet]; rw [μ.outerMeasure_of_isOpen U hU] at hr
  simp only [innerContent, lt_iSup_iff] at hr
  rcases hr with ⟨K, hKU, hr⟩
  refine ⟨K, hKU, K.2, hr.trans_le ?_⟩
  exact (μ.le_outerMeasure_compacts K).trans (le_toMeasure_apply _ _ _)

end OuterMeasure

section RegularContents

/--
Definition of `ContentRegular` / `ContentRegular` 的定义

English:
definition ContentRegular
  body: forall ⦃K : TopologicalSpace.Compacts G⦄,
    μ K = ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) subseteq interior (K' : Set G)), μ K'

中文:
定义 ContentRegular
  定义体: forall ⦃K : TopologicalSpace.Compacts G⦄,
    μ K = ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) subseteq interior (K' : Set G)), μ K'

Depends on / 依赖: Compacts, TopologicalSpace, TopologicalSpace.Compacts, interior, subseteq
-/
def ContentRegular :=
  forall ⦃K : TopologicalSpace.Compacts G⦄,
    μ K = ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) subseteq interior (K' : Set G)), μ K'

/--
theorem `contentRegular_exists_compact` / 定理 `contentRegular_exists_compact`

English:
theorem contentRegular_exists_compact
  statement: (H : ContentRegular μ) (K : TopologicalSpace.Compacts G)
  proof: by
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have lower_bound_iInf : μ K + ε <=
      ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) subseteq interior (K' : Set G)), μ K' :=
    le_iInf fun K' => le_iInf fun K'_hyp => le_of_lt (hc K' K'_hyp)
  rw [← H] at lower_bound_iI

中文:
定理 contentRegular_存在_compact
  结论: (H : ContentRegular μ) (K : 拓扑空间.余mpacts G)
  证明: by
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have lower_bound_iInf : μ K + ε <=
      ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) subseteq interior (K' : Set G)), μ K' :=
    le_iInf fun K' => le_iInf fun K'_hyp => le_of_lt (hc K' K'_hyp)
  rw [← H] at lower_bound_iI

Depends on / 依赖: Compacts, ENNReal, ENNReal.coe_ne_zero.mpr, ENNReal.lt_add_right, TopologicalSpace, TopologicalSpace.Compacts, _hyp, coe_ne_zero, interior, le_iInf, le_of_lt, lower_bound_iInf, lt_add_right, lt_of_le_of_lt, lt_self_iff_false, lt_top, ne_top_of_lt, not_and, not_exists, not_le
-/
theorem contentRegular_exists_compact (H : ContentRegular μ) (K : TopologicalSpace.Compacts G)
    {ε : NNReal} (hε : ε != 0) :
    exists K' : TopologicalSpace.Compacts G, K.carrier subseteq interior K'.carrier ∧ μ K' <= μ K + ε := by
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have lower_bound_iInf : μ K + ε <=
      ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) subseteq interior (K' : Set G)), μ K' :=
    le_iInf fun K' => le_iInf fun K'_hyp => le_of_lt (hc K' K'_hyp)
  rw [← H] at lower_bound_iInf
  exact (lt_self_iff_false (μ K)).mp (lt_of_le_of_lt' lower_bound_iInf
    (ENNReal.lt_add_right (ne_top_of_lt (μ.lt_top K)) (ENNReal.coe_ne_zero.mpr hε)))

variable [MeasurableSpace G] [R1Space G] [BorelSpace G]

/--
theorem `measure_eq_content_of_regular` / 定理 `measure_eq_content_of_regular`

English:
theorem measure_eq_content_of_regular
  statement: (H : MeasureTheory.Content.ContentRegular μ)
  proof: by
  refine le_antisymm ?_ ?_
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε εpos _
    obtain ⟨K', K'_hyp⟩ := contentRegular_exists_compact μ H K (ne_bot_of_gt εpos)
    calc
      μ.measure ↑K <= μ.measure (interior ↑K') := measure_mono K'_hyp.1
      _ <= μ K' := by
        rw [μ.measure_a

中文:
定理 measure_eq_content_of_regular
  结论: (H : 测度论.内容.ContentRegular μ)
  证明: by
  refine le_antisymm ?_ ?_
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε εpos _
    obtain ⟨K', K'_hyp⟩ := contentRegular_exists_compact μ H K (ne_bot_of_gt εpos)
    calc
      μ.measure ↑K <= μ.measure (interior ↑K') := measure_mono K'_hyp.1
      _ <= μ K' := by
        rw [μ.measure_a

Depends on / 依赖: ENNReal, ENNReal.le_of_forall_pos_le_add, IsOpen, IsOpen.measurableSet, _hyp, _hyp.right, closure, contentRegular_exists_compact, interior, isOpen_interior, le_antisymm, le_of_forall_pos_le_add, measurableSet, measure, measure_app, measure_apply, measure_mono, ne_bot_of_gt, outerMeasure_interior_compacts, subset_closure
-/
theorem measure_eq_content_of_regular (H : MeasureTheory.Content.ContentRegular μ)
    (K : TopologicalSpace.Compacts G) : μ.measure ↑K = μ K := by
  refine le_antisymm ?_ ?_
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε εpos _
    obtain ⟨K', K'_hyp⟩ := contentRegular_exists_compact μ H K (ne_bot_of_gt εpos)
    calc
      μ.measure ↑K <= μ.measure (interior ↑K') := measure_mono K'_hyp.1
      _ <= μ K' := by
        rw [μ.measure_apply (IsOpen.measurableSet isOpen_interior)]
        exact μ.outerMeasure_interior_compacts K'
      _ <= μ K + ε := K'_hyp.right
  · calc
    μ K <= μ ⟨closure K, K.2.closure⟩ := μ.mono _ _ subset_closure
    _ <= μ.measure (closure K) := by
      rw [μ.measure_apply (isClosed_closure.measurableSet)]
      exact μ.le_outerMeasure_compacts _
    _ = μ.measure K := K.2.measure_closure _

end RegularContents

end Content

end MeasureTheory
