/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The successor case in the induction for Nöbeling's theorem

Here we assume that `o` is an ordinal such that `contained C (o+1)` and `o < I`. The element in `I`
corresponding to `o` is called `term I ho`, but in this informal docstring we refer to it simply as
`o`.

This section follows the proof in [scholze2019condensed] quite closely. A translation of the
notation there is as follows:

```
[scholze2019condensed] | This file
`S₀` |`C0`
`S₁` |`C1`
`\overline{S}` |`π C (ord I · < o)
`\overline{S}'` |`C'`
The left map in the exact sequence |`πs`
The right map in the exact sequence |`Linear_CC'`
```

When comparing the proof of the successor case in Theorem 5.4 in [scholze2019condensed] with this
proof, one should read the phrase "is a basis" as "is linearly independent". Also, the short exact
sequence in [scholze2019condensed] is only proved to be left exact here (indeed, that is enough
since we are only proving linear independence).

This section is split into two sections. The first one, `ExactSequence` defines the left exact
sequence mentioned in the previous paragraph (see `succ_mono` and `succ_exact`). It corresponds to
the penultimate paragraph of the proof in [scholze2019condensed]. The second one, `GoodProducts`
corresponds to the last paragraph in the proof in [scholze2019condensed].

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main definitions

The main definitions in the section `ExactSequence` are all just notation explained in the table
above.

The main definitions in the section `GoodProducts` are as follows:

* `MaxProducts`: the set of good products that contain the ordinal `o` (since we have
  `contained C (o+1)`, these all start with `o`).

* `GoodProducts.sum_equiv`: the equivalence between `GoodProducts C` and the disjoint union of
  `MaxProducts C` and `GoodProducts (π C (ord I · < o))`.

## Main results

* The main results in the section `ExactSequence` are `succ_mono` and `succ_exact` which together
  say that the sequence given by `πs` and `Linear_CC'` is left exact:
  ```
                                              f g
  0 --→ LocallyConstant (π C (ord I · < o)) ℤ --→ LocallyConstant C ℤ --→ LocallyConstant C' ℤ
  ```
  where `f` is `πs` and `g` is `Linear_CC'`.

The main results in the section `GoodProducts` are as follows:

* `Products.max_eq_eval` says that the linear map on the right in the exact sequence, i.e.
  `Linear_CC'`, takes the evaluation of a term of `MaxProducts` to the evaluation of the
  corresponding list with the leading `o` removed.

* `GoodProducts.maxTail_isGood` says that removing the leading `o` from a term of `MaxProducts C`
  yields a list which `isGood` with respect to `C'`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I -> Bool)) [LinearOrder I] [WellFoundedLT I]
  {o : Ordinal} (hC : IsClosed C) (hsC : contained C (Order.succ o))
  (ho : o < Ordinal.type (· < · : I -> I -> Prop))

section ExactSequence

/--
Definition of `C0` / `C0` 的定义

English:
definition C0
  body: C inter {f | f (term I ho) = false}

中文:
定义 C0
  定义体: C inter {f | f (term I ho) = false}
-/
def C0 := C inter {f | f (term I ho) = false}

/--
Definition of `C1` / `C1` 的定义

English:
definition C1
  body: C inter {f | f (term I ho) = true}

include hC in

中文:
定义 C1
  定义体: C inter {f | f (term I ho) = true}

include hC in
-/
def C1 := C inter {f | f (term I ho) = true}

include hC in
/--
theorem `isClosed_C0` / 定理 `isClosed_C0`

English:
theorem isClosed_C0
  statement: IsClosed (C0 C ho)
  proof: by
  refine hC.inter ?_
  have h : Continuous (fun (f : I -> Bool) => f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {false}) (isClosed_discrete _)

include hC in

中文:
定理 isClosed_C0
  结论: 是闭集 (C0 C ho)
  证明: by
  refine hC.inter ?_
  have h : Continuous (fun (f : I -> Bool) => f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {false}) (isClosed_discrete _)

include hC in

Depends on / 依赖: Continuous, IsClosed, IsClosed.preimage, continuous_apply, hC.inter, isClosed_discrete, preimage
-/
theorem isClosed_C0 : IsClosed (C0 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I -> Bool) => f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {false}) (isClosed_discrete _)

include hC in
/--
theorem `isClosed_C1` / 定理 `isClosed_C1`

English:
theorem isClosed_C1
  statement: IsClosed (C1 C ho)
  proof: by
  refine hC.inter ?_
  have h : Continuous (fun (f : I -> Bool) => f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {true}) (isClosed_discrete _)

中文:
定理 isClosed_C1
  结论: 是闭集 (C1 C ho)
  证明: by
  refine hC.inter ?_
  have h : Continuous (fun (f : I -> Bool) => f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {true}) (isClosed_discrete _)

Depends on / 依赖: Continuous, IsClosed, IsClosed.preimage, continuous_apply, hC.inter, isClosed_discrete, preimage
-/
theorem isClosed_C1 : IsClosed (C1 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I -> Bool) => f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {true}) (isClosed_discrete _)

/--
theorem `contained_C1` / 定理 `contained_C1`

English:
theorem contained_C1
  statement: contained (π (C1 C ho) (ord I · < o)) o
  proof: contained_proj _ _

中文:
定理 contained_C1
  结论: contained (π (C1 C ho) (ord I · < o)) o
  证明: contained_proj _ _

Depends on / 依赖: contained_proj
-/
theorem contained_C1 : contained (π (C1 C ho) (ord I · < o)) o :=
  contained_proj _ _

/--
theorem `union_C0C1_eq` / 定理 `union_C0C1_eq`

English:
theorem union_C0C1_eq
  statement: (C0 C ho) union (C1 C ho) = C
  proof: by
  ext x
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
    ← and_or_left, and_iff_left_iff_imp, Bool.dichotomy (x (term I ho)), implies_true]

中文:
定理 union_C0C1_eq
  结论: (C0 C ho) union (C1 C ho) = C
  证明: by
  ext x
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
    ← and_or_left, and_iff_left_iff_imp, Bool.dichotomy (x (term I ho)), implies_true]

Depends on / 依赖: Bool.dichotomy, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union, and_iff_left_iff_imp, and_or_left, dichotomy, implies_true, mem_inter_iff, mem_ofPred_eq, mem_union
-/
theorem union_C0C1_eq : (C0 C ho) union (C1 C ho) = C := by
  ext x
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
    ← and_or_left, and_iff_left_iff_imp, Bool.dichotomy (x (term I ho)), implies_true]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `C'` / `C'` 的定义

English:
definition C'
  body: C0 C ho inter π (C1 C ho) (ord I · < o)

include hC in

中文:
定义 C'
  定义体: C0 C ho inter π (C1 C ho) (ord I · < o)

include hC in
-/
noncomputable def C' := C0 C ho inter π (C1 C ho) (ord I · < o)

include hC in
/--
theorem `isClosed_C'` / 定理 `isClosed_C'`

English:
theorem isClosed_C'
  statement: IsClosed (C' C ho)
  proof: IsClosed.inter (isClosed_C0 _ hC _) (isClosed_proj _ _ (isClosed_C1 _ hC _))

中文:
定理 isClosed_C'
  结论: 是闭集 (C' C ho)
  证明: IsClosed.inter (isClosed_C0 _ hC _) (isClosed_proj _ _ (isClosed_C1 _ hC _))

Depends on / 依赖: IsClosed, IsClosed.inter, isClosed_C0, isClosed_C1, isClosed_proj
-/
theorem isClosed_C' : IsClosed (C' C ho) :=
  IsClosed.inter (isClosed_C0 _ hC _) (isClosed_proj _ _ (isClosed_C1 _ hC _))

/--
theorem `contained_C'` / 定理 `contained_C'`

English:
theorem contained_C'
  statement: contained (C' C ho) o
  proof: fun f hf i hi => contained_C1 C ho f hf.2 i hi

中文:
定理 contained_C'
  结论: contained (C' C ho) o
  证明: fun f hf i hi => contained_C1 C ho f hf.2 i hi

Depends on / 依赖: contained_C1
-/
theorem contained_C' : contained (C' C ho) o := fun f hf i hi => contained_C1 C ho f hf.2 i hi

variable (o)

/-- Swapping the `o`-th coordinate to `true`. -/
noncomputable
/--
Definition of `SwapTrue` / `SwapTrue` 的定义

English:
definition SwapTrue
  signature: : (I -> Bool) -> I -> Bool
  body: fun f i => if ord I i = o then true else f i

中文:
定义 SwapTrue
  签名: : (I -> 布尔值) -> I -> 布尔值
  定义体: fun f i => if ord I i = o then true else f i
-/
def SwapTrue : (I -> Bool) -> I -> Bool :=
  fun f i => if ord I i = o then true else f i

/--
theorem `continuous_swapTrue` / 定理 `continuous_swapTrue`

English:
theorem continuous_swapTrue
  statement: Continuous (SwapTrue o : (I -> Bool) -> I -> Bool)
  proof: by
  dsimp +unfoldPartialApp [SwapTrue]
  apply continuous_pi
  intro i
  apply Continuous.comp'
  · apply continuous_bot
  · apply continuous_apply

中文:
定理 continuous_swapTrue
  结论: 连续 (SwapTrue o : (I -> 布尔值) -> I -> 布尔值)
  证明: by
  dsimp +unfoldPartialApp [SwapTrue]
  apply continuous_pi
  intro i
  apply Continuous.comp'
  · apply continuous_bot
  · apply continuous_apply

Depends on / 依赖: Continuous, Continuous.comp, SwapTrue, continuous_apply, continuous_bot, continuous_pi, unfoldPartialApp
-/
theorem continuous_swapTrue : Continuous (SwapTrue o : (I -> Bool) -> I -> Bool) := by
  dsimp +unfoldPartialApp [SwapTrue]
  apply continuous_pi
  intro i
  apply Continuous.comp'
  · apply continuous_bot
  · apply continuous_apply

variable {o}

include hsC in
/--
theorem `swapTrue_mem_C1` / 定理 `swapTrue_mem_C1`

English:
theorem swapTrue_mem_C1
  given: (f : π (C1 C ho) (ord I · < o))
  proof: by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert! hg
  dsimp +unfoldPartialApp [SwapTrue]
  ext i
  split_ifs with h
  · rw [ord_term ho] at h
    simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
 

中文:
定理 swapTrue_mem_C1
  条件: (f : π (C1 C ho) (ord I · < o))
  证明: by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert! hg
  dsimp +unfoldPartialApp [SwapTrue]
  ext i
  split_ifs with h
  · rw [ord_term ho] at h
    simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
 

Depends on / 依赖: Bool.not_eq_true, Order.succ_le_of_lt, SwapTrue, contrapose, convert, eq_comm, ite_eq_left_iff, lt_of_ne, not_eq_true, not_lt, ord_term, specialize, split_ifs, succ_le_of_lt, unfoldPartialApp
-/
theorem swapTrue_mem_C1 (f : π (C1 C ho) (ord I · < o)) :
    SwapTrue o f.val in C1 C ho := by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert! hg
  dsimp +unfoldPartialApp [SwapTrue]
  ext i
  split_ifs with h
  · rw [ord_term ho] at h
    simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
    contrapose! hsC
    exact ⟨hsC, Order.succ_le_of_lt (h'.lt_of_ne' h)⟩

/--
Definition of `CC'₀` / `CC'₀` 的定义

English:
definition CC'₀
  signature: : C' C ho -> C
  body: fun g => ⟨g.val,g.prop.1.1⟩

中文:
定义 CC'₀
  签名: : C' C ho -> C
  定义体: fun g => ⟨g.val,g.prop.1.1⟩

Depends on / 依赖: g.prop, g.val
-/
def CC'₀ : C' C ho -> C := fun g => ⟨g.val,g.prop.1.1⟩

/-- The second way to map `C'` into `C`. -/
noncomputable
/--
Definition of `CC'₁` / `CC'₁` 的定义

English:
definition CC'₁
  signature: : C' C ho -> C
  body: fun g => ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ho ⟨g.val,g.prop.2⟩).1⟩

中文:
定义 CC'₁
  签名: : C' C ho -> C
  定义体: fun g => ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ho ⟨g.val,g.prop.2⟩).1⟩
-/
def CC'₁ : C' C ho -> C :=
  fun g => ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ho ⟨g.val,g.prop.2⟩).1⟩

/--
theorem `continuous_CC'₀` / 定理 `continuous_CC'₀`

English:
theorem continuous_CC'₀
  statement: Continuous (CC'₀ C ho)
  proof: Continuous.subtype_mk continuous_subtype_val _

中文:
定理 continuous_CC'₀
  结论: 连续 (CC'₀ C ho)
  证明: Continuous.subtype_mk continuous_subtype_val _

Depends on / 依赖: Continuous, Continuous.subtype_mk, continuous_subtype_val, subtype_mk
-/
theorem continuous_CC'₀ : Continuous (CC'₀ C ho) := Continuous.subtype_mk continuous_subtype_val _

/--
theorem `continuous_CC'₁` / 定理 `continuous_CC'₁`

English:
theorem continuous_CC'₁
  statement: Continuous (CC'₁ C hsC ho)
  proof: Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

中文:
定理 continuous_CC'₁
  结论: 连续 (CC'₁ C hsC ho)
  证明: Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _
-/
theorem continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
  Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

/-- The `ℤ`-linear map induced by precomposing with `CC'₀` -/
noncomputable
/--
Definition of `Linear_CC'₀` / `Linear_CC'₀` 的定义

English:
definition Linear_CC'₀
  signature: : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int
  body: LocallyConstant.comapₗ Int ⟨(CC'₀ C ho), (continuous_CC'₀ C ho)⟩

中文:
定义 Linear_CC'₀
  签名: : 局部常数 C 整数 ->ₗ[整数] 局部常数 (C' C ho) 整数
  定义体: LocallyConstant.comapₗ Int ⟨(CC'₀ C ho), (continuous_CC'₀ C ho)⟩

Depends on / 依赖: LocallyConstant, LocallyConstant.comap, continuous_CC
-/
def Linear_CC'₀ : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int :=
  LocallyConstant.comapₗ Int ⟨(CC'₀ C ho), (continuous_CC'₀ C ho)⟩

/-- The `ℤ`-linear map induced by precomposing with `CC'₁` -/
noncomputable
/--
Definition of `Linear_CC'₁` / `Linear_CC'₁` 的定义

English:
definition Linear_CC'₁
  signature: : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int
  body: LocallyConstant.comapₗ Int ⟨(CC'₁ C hsC ho), (continuous_CC'₁ C hsC ho)⟩

中文:
定义 Linear_CC'₁
  签名: : 局部常数 C 整数 ->ₗ[整数] 局部常数 (C' C ho) 整数
  定义体: LocallyConstant.comapₗ Int ⟨(CC'₁ C hsC ho), (continuous_CC'₁ C hsC ho)⟩
-/
def Linear_CC'₁ : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int :=
  LocallyConstant.comapₗ Int ⟨(CC'₁ C hsC ho), (continuous_CC'₁ C hsC ho)⟩

/-- The difference between `Linear_CC'₁` and `Linear_CC'₀`. -/
noncomputable
/--
Definition of `Linear_CC'` / `Linear_CC'` 的定义

English:
definition Linear_CC'
  signature: : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int
  body: Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

中文:
定义 Linear_CC'
  签名: : 局部常数 C 整数 ->ₗ[整数] 局部常数 (C' C ho) 整数
  定义体: Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho
-/
def Linear_CC' : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int :=
  Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

set_option backward.defeqAttrib.useBackward true in
/--
theorem `CC_comp_zero` / 定理 `CC_comp_zero`

English:
theorem CC_comp_zero
  statement: forall y, (Linear_CC' C hsC ho) ((πs C o) y) = 0
  proof: by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).

中文:
定理 CC_comp_zero
  结论: 对任意 y, (Linear_CC' C hsC ho) ((πs C o) y) = 0
  证明: by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).

Depends on / 依赖: Iff.rfl, Linear_CC, LocallyConstant, LocallyConstant.sub_apply, ProjRestrict, SwapTrue, if_ctx_congr, ite_eq_right_iff, sub_apply, sub_eq_zero
-/
theorem CC_comp_zero : forall y, (Linear_CC' C hsC ho) ((πs C o) y) = 0 := by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).elim

include hsC in
/--
theorem `C0_projOrd` / 定理 `C0_projOrd`

English:
theorem C0_projOrd
  given: {x : I -> Bool} (hx : x in C0 C ho)
  statement: Proj (ord I · < o) x = x
  proof: by
  ext i
  simp only [Proj, ite_eq_left_iff, not_lt]
  intro hi
  rcases hi.lt_or_eq with hi | hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_ofPre

中文:
定理 C0_projOrd
  条件: {x : I -> 布尔值} (hx : x in C0 C ho)
  结论: Proj (ord I · < o) x = x
  证明: by
  ext i
  simp only [Proj, ite_eq_left_iff, not_lt]
  intro hi
  rcases hi.lt_or_eq with hi | hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_ofPre

Depends on / 依赖: Bool.not_eq_true, Order.succ_le_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, eq_comm, hi.lt_or_eq, ite_eq_left_iff, lt_or_eq, mem_inter_iff, mem_ofPred_eq, not_eq_true, not_imp_not, not_lt, ord_term, specialize, succ_le_iff
-/
theorem C0_projOrd {x : I -> Bool} (hx : x in C0 C ho) : Proj (ord I · < o) x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff, not_lt]
  intro hi
  rcases hi.lt_or_eq with hi | hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    rw [eq_comm]; rw [ord_term ho] at hi
    rw [← hx.2]; rw [hi]

include hsC in
/--
theorem `C1_projOrd` / 定理 `C1_projOrd`

English:
theorem C1_projOrd
  given: {x : I -> Bool} (hx : x in C1 C ho)
  statement: SwapTrue o (Proj (ord I · < o) x) = x
  proof: by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [ord_term ho] at hi
    rw [← hx.2]; rw [hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_tr

中文:
定理 C1_projOrd
  条件: {x : I -> 布尔值} (hx : x in C1 C ho)
  结论: SwapTrue o (Proj (ord I · < o) x) = x
  证明: by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [ord_term ho] at hi
    rw [← hx.2]; rw [hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_tr

Depends on / 依赖: Bool.not_eq_true, Ne.symm, Order.succ_le_iff, SwapTrue, lt_of_le_of_ne, not_eq_true, not_imp_not, not_lt, ord_term, specialize, split_ifs, succ_le_iff
-/
theorem C1_projOrd {x : I -> Bool} (hx : x in C1 C ho) : SwapTrue o (Proj (ord I · < o) x) = x := by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [ord_term ho] at hi
    rw [← hx.2]; rw [hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC h').symm

set_option backward.isDefEq.respectTransparency.types false in
include hC in
/--
theorem `CC_exact` / 定理 `CC_exact`

English:
theorem CC_exact
  given: {f : LocallyConstant C Int} (hf : Linear_CC' C hsC ho f = 0)
  proof: by
  classical
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj] at hf
  let C₀C : C0 C ho -> C := fun x => ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : π (C1 C ho) (ord I · < o) -> 

中文:
定理 CC_exact
  条件: {f : 局部常数 C 整数} (hf : Linear_CC' C hsC ho f = 0)
  证明: by
  classical
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj] at hf
  let C₀C : C0 C ho -> C := fun x => ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : π (C1 C ho) (ord I · < o) -> 

Depends on / 依赖: Continuous, Continuous.subtype_mk, Linear_CC, LocallyConstant, LocallyConstant.coe_inj, LocallyConstant.piecewise, SwapTrue, classical, coe_inj, continuous_induced_dom, continuous_subtype_val, continuous_swapTrue, piecewise, sub_eq_zero, subtype_mk, swapTrue_mem_C1, x.prop, x.val
-/
theorem CC_exact {f : LocallyConstant C Int} (hf : Linear_CC' C hsC ho f = 0) :
    exists y, πs C o y = f := by
  classical
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj] at hf
  let C₀C : C0 C ho -> C := fun x => ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : π (C1 C ho) (ord I · < o) -> C :=
    fun x => ⟨SwapTrue o x.val, (swapTrue_mem_C1 C hsC ho x).1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk
    ((continuous_swapTrue o).comp continuous_subtype_val) _
  refine ⟨LocallyConstant.piecewise' ?_ (isClosed_C0 C hC ho)
      (isClosed_proj _ o (isClosed_C1 C hC ho)) (f.comap ⟨C₀C, h₀⟩) (f.comap ⟨C₁C, h₁⟩) ?_, ?_⟩
  · rintro _ ⟨y, hyC, rfl⟩
    simp only [Set.mem_union]
    rw [← union_C0C1_eq C ho] at hyC
    refine hyC.imp (fun hyC => ?_) (fun hyC => ⟨y, hyC, rfl⟩)
    rwa [C0_projOrd C hsC ho hyC]
  · intro x hx
    simpa only [h₀, h₁, LocallyConstant.coe_comap] using! (congrFun hf ⟨x, hx⟩).symm
  · ext ⟨x, hx⟩
    rw [← union_C0C1_eq C ho] at hx
    rcases hx with hx₀ | hx₁
    · have hx₀' : ProjRestrict C (ord I · < o) ⟨x, hx⟩ = x := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using! C0_projOrd C hsC ho hx₀
      simp only [C₀C, πs_apply_apply, hx₀', hx₀, LocallyConstant.piecewise'_apply_left,
        LocallyConstant.coe_comap, ContinuousMap.coe_mk, Function.comp_apply]
    · have hx₁' : (ProjRestrict C (ord I · < o) ⟨x, hx⟩).val in π (C1 C ho) (ord I · < o) := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using! ⟨x, hx₁, rfl⟩
      simp only [C₁C, πs_apply_apply, LocallyConstant.coe_comap,
        Function.comp_apply, hx₁', LocallyConstant.piecewise'_apply_right]
      congr
      simp only [ContinuousMap.coe_mk, Subtype.mk.injEq]
      exact C1_projOrd C hsC ho hx₁

variable (o) in
/--
theorem `succ_mono` / 定理 `succ_mono`

English:
theorem succ_mono
  statement: CategoryTheory.Mono (ModuleCat.ofHom (πs C o))
  proof: by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

include hC in

中文:
定理 succ_mono
  结论: 范畴论.单态射 (模范畴.ofHom (πs C o))
  证明: by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

include hC in

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, mono_iff_injective
-/
theorem succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (πs C o)) := by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

include hC in
/--
theorem `succ_exact` / 定理 `succ_exact`

English:
theorem succ_exact
  proof: by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f
  exact CC_exact C hC hsC ho

中文:
定理 succ_exact
  证明: by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f
  exact CC_exact C hC hsC ho

Depends on / 依赖: CC_exact, ShortComplex, ShortComplex.moduleCat_exact_iff, moduleCat_exact_iff
-/
theorem succ_exact :
    (ShortComplex.mk (ModuleCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC ho))
    (by ext : 2; apply CC_comp_zero)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f
  exact CC_exact C hC hsC ho

end ExactSequence

namespace GoodProducts

/--
Definition of `MaxProducts` / `MaxProducts` 的定义

English:
definition MaxProducts
  signature: : Set (Products I)
  body: {l | l.isGood C ∧ term I ho in l.val}

include hsC in

中文:
定义 MaxProducts
  签名: : 集合 (Products I)
  定义体: {l | l.isGood C ∧ term I ho in l.val}

include hsC in

Depends on / 依赖: isGood, l.isGood, l.val
-/
def MaxProducts : Set (Products I) := {l | l.isGood C ∧ term I ho in l.val}

include hsC in
/--
theorem `union_succ` / 定理 `union_succ`

English:
theorem union_succ
  statement: GoodProducts C = GoodProducts (π C (ord I · < o)) union MaxProducts C ho
  proof: by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hh : term I ho in l.val
    · exact Or.inr ⟨h, hh⟩
    · left
      intro he
      apply h
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp 

中文:
定理 union_succ
  结论: GoodProducts C = GoodProducts (π C (ord I · < o)) union MaxProducts C ho
  证明: by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hh : term I ho in l.val
    · exact Or.inr ⟨h, hh⟩
    · left
      intro he
      apply h
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp 

Depends on / 依赖: GoodProducts, MaxProducts, Or.inr, Order.lt_succ_iff, Products, Products.eval_, Products.prop_of_isGood_of_contained, Set.mem_ofPred_eq, Set.mem_union, l.val, lt_of_ne, lt_succ_iff, mem_ofPred_eq, mem_union, ne_eq, ord_term, prop_of_isGood_of_contained
-/
theorem union_succ : GoodProducts C = GoodProducts (π C (ord I · < o)) union MaxProducts C ho := by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hh : term I ho in l.val
    · exact Or.inr ⟨h, hh⟩
    · left
      intro he
      apply h
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp only [Order.lt_succ_iff] at h'
      have hh' : forall a in l.val, ord I a < o := by
        intro a ha
        refine (h' a ha).lt_of_ne ?_
        rw [ne_eq]; rw [ord_term ho a]
        rintro rfl
        contradiction
      rwa [Products.eval_πs_image C hh', ← Products.eval_πs C hh',
        Submodule.apply_mem_span_image_iff_mem_span (injective_πs _ _)]
  · refine h.elim (fun hh => ?_) And.left
    have := Products.isGood_mono C (Order.lt_succ o).le hh
    rwa [contained_eq_proj C (Order.succ o) hsC]

/--
Definition of `sum_to` / `sum_to` 的定义

English:
definition sum_to
  signature: : (GoodProducts (π C (ord I · < o))) oplus (MaxProducts C ho) -> Products I
  body: Sum.elim Subtype.val Subtype.val

中文:
定义 sum_to
  签名: : (GoodProducts (π C (ord I · < o))) oplus (MaxProducts C ho) -> Products I
  定义体: Sum.elim Subtype.val Subtype.val

Depends on / 依赖: Subtype, Subtype.val, Sum.elim
-/
def sum_to : (GoodProducts (π C (ord I · < o))) oplus (MaxProducts C ho) -> Products I :=
  Sum.elim Subtype.val Subtype.val

/--
theorem `injective_sum_to` / 定理 `injective_sum_to`

English:
theorem injective_sum_to
  statement: Function.Injective (sum_to C ho)
  proof: by
  refine Function.Injective.sumElim Subtype.val_injective Subtype.val_injective
    (fun ⟨a,ha⟩ ⟨b,hb⟩ => (fun (hab : a = b) => ?_))
  rw [← hab] at hb
  have ha' := Products.prop_of_isGood C _ ha (term I ho) hb.2
  simp only [ord_term_aux, lt_self_iff_false] at ha'

中文:
定理 injective_sum_to
  结论: 函数.单射 (sum_to C ho)
  证明: by
  refine Function.Injective.sumElim Subtype.val_injective Subtype.val_injective
    (fun ⟨a,ha⟩ ⟨b,hb⟩ => (fun (hab : a = b) => ?_))
  rw [← hab] at hb
  have ha' := Products.prop_of_isGood C _ ha (term I ho) hb.2
  simp only [ord_term_aux, lt_self_iff_false] at ha'

Depends on / 依赖: Function, Function.Injective.sumElim, Injective, Products, Products.prop_of_isGood, Subtype, Subtype.val_injective, lt_self_iff_false, ord_term_aux, prop_of_isGood, sumElim, val_injective
-/
theorem injective_sum_to : Function.Injective (sum_to C ho) := by
  refine Function.Injective.sumElim Subtype.val_injective Subtype.val_injective
    (fun ⟨a,ha⟩ ⟨b,hb⟩ => (fun (hab : a = b) => ?_))
  rw [← hab] at hb
  have ha' := Products.prop_of_isGood C _ ha (term I ho) hb.2
  simp only [ord_term_aux, lt_self_iff_false] at ha'

/--
theorem `sum_to_range` / 定理 `sum_to_range`

English:
theorem sum_to_range
  proof: by
  have : Set.range (sum_to C ho) = _ union _ := Set.Sum.elim_range _ _
  simp_all

中文:
定理 sum_to_range
  证明: by
  have : Set.range (sum_to C ho) = _ union _ := Set.Sum.elim_range _ _
  simp_all

Depends on / 依赖: Set.Sum.elim_range, Set.range, elim_range, sum_to
-/
theorem sum_to_range :
    Set.range (sum_to C ho) = GoodProducts (π C (ord I · < o)) union MaxProducts C ho := by
  have : Set.range (sum_to C ho) = _ union _ := Set.Sum.elim_range _ _
  simp_all

/-- The equivalence from the sum of `GoodProducts (π C (ord I · < o))` and
`(MaxProducts C ho)` to `GoodProducts C`. -/
noncomputable
/--
Definition of `sum_equiv` / `sum_equiv` 的定义

English:
definition sum_equiv
  signature: (hsC : contained C (Order.succ o)) (ho : o < Ordinal.type (· < · : I -> I -> Prop))
  body: calc _ ≃ Set.range (sum_to C ho) := Equiv.ofInjective (sum_to C ho) (injective_sum_to C ho)
_ ≃ _ := Equiv.setCongr by rw [sum_to_range C ho, union_succ C hsC ho]

中文:
定义 sum_equiv
  签名: (hsC : contained C (Order.succ o)) (ho : o < 序数.type (· < · : I -> I -> 命题))
  定义体: calc _ ≃ Set.range (sum_to C ho) := Equiv.ofInjective (sum_to C ho) (injective_sum_to C ho)
_ ≃ _ := Equiv.setCongr by rw [sum_to_range C ho, union_succ C hsC ho]

Depends on / 依赖: Equiv.ofInjective, Equiv.setCongr, Set.range, injective_sum_to, ofInjective, setCongr, sum_to, sum_to_range, union_succ
-/
def sum_equiv (hsC : contained C (Order.succ o)) (ho : o < Ordinal.type (· < · : I -> I -> Prop)) :
    GoodProducts (π C (ord I · < o)) oplus (MaxProducts C ho) ≃ GoodProducts C :=
  calc _ ≃ Set.range (sum_to C ho) := Equiv.ofInjective (sum_to C ho) (injective_sum_to C ho)
_ ≃ _ := Equiv.setCongr by rw [sum_to_range C ho, union_succ C hsC ho]

/--
theorem `sum_equiv_comp_eval_eq_elim` / 定理 `sum_equiv_comp_eval_eq_elim`

English:
theorem sum_equiv_comp_eval_eq_elim
  statement: eval C ∘ (sum_equiv C hsC ho).toFun =
  proof: by
  ext ⟨_, _⟩ <;> [rfl; rfl]

中文:
定理 sum_equiv_comp_eval_eq_elim
  结论: eval C ∘ (sum_equiv C hsC ho).toFun =
  证明: by
  ext ⟨_, _⟩ <;> [rfl; rfl]
-/
theorem sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun =
    (Sum.elim (fun (l : GoodProducts (π C (ord I · < o))) => Products.eval C l.1)
    (fun (l : MaxProducts C ho) => Products.eval C l.1)) := by
  ext ⟨_, _⟩ <;> [rfl; rfl]

/--
Definition of `SumEval` / `SumEval` 的定义

English:
definition SumEval
  signature: : GoodProducts (π C (ord I · < o)) oplus MaxProducts C ho ->
  body: Sum.elim (fun l => l.1.eval C) (fun l => l.1.eval C)

中文:
定义 SumEval
  签名: : GoodProducts (π C (ord I · < o)) oplus MaxProducts C ho ->
  定义体: Sum.elim (fun l => l.1.eval C) (fun l => l.1.eval C)

Depends on / 依赖: Sum.elim
-/
def SumEval : GoodProducts (π C (ord I · < o)) oplus MaxProducts C ho ->
    LocallyConstant C Int :=
  Sum.elim (fun l => l.1.eval C) (fun l => l.1.eval C)

set_option backward.isDefEq.respectTransparency false in
include hsC in
/--
theorem `linearIndependent_iff_sum` / 定理 `linearIndependent_iff_sum`

English:
theorem linearIndependent_iff_sum
  proof: by
  rw [← linearIndependent_equiv (sum_equiv C hsC ho)]; rw [SumEval]; rw [← sum_equiv_comp_eval_eq_elim C hsC ho]
  exact Iff.rfl

中文:
定理 linearIndependent_iff_sum
  证明: by
  rw [← linearIndependent_equiv (sum_equiv C hsC ho)]; rw [SumEval]; rw [← sum_equiv_comp_eval_eq_elim C hsC ho]
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, SumEval, linearIndependent_equiv, sum_equiv, sum_equiv_comp_eval_eq_elim
-/
theorem linearIndependent_iff_sum :
    LinearIndependent Int (eval C) ↔ LinearIndependent Int (SumEval C ho) := by
  rw [← linearIndependent_equiv (sum_equiv C hsC ho)]; rw [SumEval]; rw [← sum_equiv_comp_eval_eq_elim C hsC ho]
  exact Iff.rfl

set_option backward.isDefEq.respectTransparency false in
include hsC in
/--
theorem `span_sum` / 定理 `span_sum`

English:
theorem span_sum
  statement: Set.range (eval C) = Set.range (Sum.elim
  proof: by
  rw [← sum_equiv_comp_eval_eq_elim C hsC ho]; rw [Equiv.toFun_as_coe]; rw [EquivLike.range_comp (e := sum_equiv C hsC ho)]

中文:
定理 span_sum
  结论: 集合.range (eval C) = 集合.range (和.elim
  证明: by
  rw [← sum_equiv_comp_eval_eq_elim C hsC ho]; rw [Equiv.toFun_as_coe]; rw [EquivLike.range_comp (e := sum_equiv C hsC ho)]

Depends on / 依赖: Equiv.toFun_as_coe, EquivLike, EquivLike.range_comp, range_comp, sum_equiv, sum_equiv_comp_eval_eq_elim, toFun_as_coe
-/
theorem span_sum : Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (π C (ord I · < o))) => Products.eval C l.1)
    (fun (l : MaxProducts C ho) => Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C hsC ho]; rw [Equiv.toFun_as_coe]; rw [EquivLike.range_comp (e := sum_equiv C hsC ho)]


set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `square_commutes` / 定理 `square_commutes`

English:
theorem square_commutes
  statement: SumEval C ho ∘ Sum.inl =
  proof: by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood _ _ l.prop)]
  simp [eval]

中文:
定理 square_commutes
  结论: SumEval C ho ∘ 和.inl =
  证明: by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood _ _ l.prop)]
  simp [eval]

Depends on / 依赖: Products, Products.eval_, Products.prop_of_isGood, SumEval, l.prop, prop_of_isGood
-/
theorem square_commutes : SumEval C ho ∘ Sum.inl =
    ModuleCat.ofHom (πs C o) ∘ eval (π C (ord I · < o)) := by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood _ _ l.prop)]
  simp [eval]

end GoodProducts

/--
theorem `swapTrue_eq_true` / 定理 `swapTrue_eq_true`

English:
theorem swapTrue_eq_true
  given: (x : I -> Bool)
  statement: SwapTrue o x (term I ho) = true
  proof: by
  simp only [SwapTrue, ord_term_aux, ite_true]

中文:
定理 swapTrue_eq_true
  条件: (x : I -> 布尔值)
  结论: SwapTrue o x (term I ho) = true
  证明: by
  simp only [SwapTrue, ord_term_aux, ite_true]

Depends on / 依赖: SwapTrue, ite_true, ord_term_aux
-/
theorem swapTrue_eq_true (x : I -> Bool) : SwapTrue o x (term I ho) = true := by
  simp only [SwapTrue, ord_term_aux, ite_true]

/--
theorem `mem_C'_eq_false` / 定理 `mem_C'_eq_false`

English:
theorem mem_C'_eq_false
  statement: forall x, x in C' C ho -> x (term I ho) = false
  proof: by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, ord_term_aux, lt_self_iff_false, ite_false]

中文:
定理 mem_C'_eq_false
  结论: 对任意 x, x in C' C ho -> x (term I ho) = false
  证明: by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, ord_term_aux, lt_self_iff_false, ite_false]

Depends on / 依赖: ite_false, lt_self_iff_false, ord_term_aux
-/
theorem mem_C'_eq_false : forall x, x in C' C ho -> x (term I ho) = false := by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, ord_term_aux, lt_self_iff_false, ite_false]

/--
Definition of `Products.Tail` / `Products.Tail` 的定义

English:
definition Products.Tail
  signature: (l : Products I)
  body: ⟨l.val.tail, List.IsChain.tail l.prop⟩

中文:
定义 Products.Tail
  签名: (l : Products I)
  定义体: ⟨l.val.tail, List.IsChain.tail l.prop⟩

Depends on / 依赖: IsChain, List.IsChain.tail, l.prop, l.val.tail
-/
def Products.Tail (l : Products I) : Products I :=
  ⟨l.val.tail, List.IsChain.tail l.prop⟩

/--
theorem `Products.max_eq_o_cons_tail` / 定理 `Products.max_eq_o_cons_tail`

English:
theorem Products.max_eq_o_cons_tail
  statement: [Inhabited I] (l : Products I) (hl : l.val != [])
  proof: by
  rw [← List.cons_head!_tail hl]; rw [hlh]
  simp [Tail]

中文:
定理 Products.max_eq_o_cons_tail
  结论: [可居 I] (l : Products I) (hl : l.val != [])
  证明: by
  rw [← List.cons_head!_tail hl]; rw [hlh]
  simp [Tail]

Depends on / 依赖: List.cons_head, _tail, cons_head
-/
theorem Products.max_eq_o_cons_tail [Inhabited I] (l : Products I) (hl : l.val != [])
    (hlh : l.val.head! = term I ho) : l.val = term I ho :: l.Tail.val := by
  rw [← List.cons_head!_tail hl]; rw [hlh]
  simp [Tail]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Products.max_eq_o_cons_tail'` / 定理 `Products.max_eq_o_cons_tail'`

English:
theorem Products.max_eq_o_cons_tail'
  statement: [Inhabited I] (l : Products I) (hl : l.val != [])
  proof: by
  simp_rw [← max_eq_o_cons_tail ho l hl hlh, Subtype.coe_eta]

include hsC in

中文:
定理 Products.max_eq_o_cons_tail'
  结论: [可居 I] (l : Products I) (hl : l.val != [])
  证明: by
  simp_rw [← max_eq_o_cons_tail ho l hl hlh, Subtype.coe_eta]

include hsC in

Depends on / 依赖: Subtype, Subtype.coe_eta, coe_eta, max_eq_o_cons_tail, simp_rw
-/
theorem Products.max_eq_o_cons_tail' [Inhabited I] (l : Products I) (hl : l.val != [])
    (hlh : l.val.head! = term I ho) (hlc : List.IsChain (· > ·) (term I ho :: l.Tail.val)) :
    l = ⟨term I ho :: l.Tail.val, hlc⟩ := by
  simp_rw [← max_eq_o_cons_tail ho l hl hlh, Subtype.coe_eta]

include hsC in
/--
theorem `GoodProducts.head!_eq_o_of_maxProducts` / 定理 `GoodProducts.head!_eq_o_of_maxProducts`

English:
theorem GoodProducts.head!_eq_o_of_maxProducts
  given: [Inhabited I] (l : ↑(MaxProducts C ho))
  proof: by
  rw [eq_comm]; rw [← ord_term ho]
  have hm := l.prop.2
  have := Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem hm))
  simp only [Order.lt_succ_iff] at this
  refine eq_of_le_of_not_lt this (not_lt.mpr ?_)
  have h : ord I (ter

中文:
定理 GoodProducts.head!_eq_o_of_maxProducts
  条件: [可居 I] (l : ↑(MaxProducts C ho))
  证明: by
  rw [eq_comm]; rw [← ord_term ho]
  have hm := l.prop.2
  have := Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem hm))
  simp only [Order.lt_succ_iff] at this
  refine eq_of_le_of_not_lt this (not_lt.mpr ?_)
  have h : ord I (ter

Depends on / 依赖: List.head, List.ne_nil_of_mem, Order.lt_succ_iff, Ordinal, Ordinal.typein_le_typein, Products, Products.prop_of_isGood_of_contained, Products.rel_head, _mem_self, _of_mem, eq_comm, eq_of_le_of_not_lt, l.prop, l.val.val.head, lt_succ_iff, ne_nil_of_mem, not_lt, not_lt.mpr, ord_term, ord_term_aux
-/
theorem GoodProducts.head!_eq_o_of_maxProducts [Inhabited I] (l : ↑(MaxProducts C ho)) :
    l.val.val.head! = term I ho := by
  rw [eq_comm]; rw [← ord_term ho]
  have hm := l.prop.2
  have := Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem hm))
  simp only [Order.lt_succ_iff] at this
  refine eq_of_le_of_not_lt this (not_lt.mpr ?_)
  have h : ord I (term I ho) <= ord I l.val.val.head! := by
    simp only [ord, Ordinal.typein_le_typein, not_lt]
    exact Products.rel_head!_of_mem hm
  rwa [ord_term_aux] at h

include hsC in
/--
theorem `GoodProducts.max_eq_o_cons_tail` / 定理 `GoodProducts.max_eq_o_cons_tail`

English:
theorem GoodProducts.max_eq_o_cons_tail
  given: (l : MaxProducts C ho)
  proof: have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_o_cons_tail ho l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

中文:
定理 GoodProducts.max_eq_o_cons_tail
  条件: (l : MaxProducts C ho)
  证明: have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_o_cons_tail ho l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

Depends on / 依赖: Inhabited, List.ne_nil_of_mem, Products, Products.max_eq_o_cons_tail, _eq_o_of_maxProducts, l.prop, l.val, max_eq_o_cons_tail, ne_nil_of_mem
-/
theorem GoodProducts.max_eq_o_cons_tail (l : MaxProducts C ho) :
    l.val.val = (term I ho) :: l.val.Tail.val :=
  have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_o_cons_tail ho l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Products.evalCons` / 定理 `Products.evalCons`

English:
theorem Products.evalCons
  statement: {I} [LinearOrder I] {C : Set (I -> Bool)} {l : List I} {a : I}
  proof: by
  simp only [eval.eq_1, List.map, List.prod_cons]

中文:
定理 Products.evalCons
  结论: {I} [线性序 I] {C : 集合 (I -> 布尔值)} {l : 列表 I} {a : I}
  证明: by
  simp only [eval.eq_1, List.map, List.prod_cons]

Depends on / 依赖: List.map, List.prod_cons, eq_1, eval.eq_1, prod_cons
-/
theorem Products.evalCons {I} [LinearOrder I] {C : Set (I -> Bool)} {l : List I} {a : I}
    (hla : (a::l).IsChain (· > ·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.IsChain.sublist hla (List.tail_sublist (a::l))⟩ := by
  simp only [eval.eq_1, List.map, List.prod_cons]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Products.max_eq_eval` / 定理 `Products.max_eq_eval`

English:
theorem Products.max_eq_eval
  statement: [Inhabited I] (l : Products I) (hl : l.val != [])
  proof: by
  have hlc : ((term I ho) :: l.Tail.val).IsChain (· > ·) := by
    rw [← max_eq_o_cons_tail ho l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' ho l hl hlh hlc]; rw [Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₁, LocallyConstant.comapₗ, Linear_CC'₀, Subtype.coe_eta,
    LinearM

中文:
定理 Products.max_eq_eval
  结论: [可居 I] (l : Products I) (hl : l.val != [])
  证明: by
  have hlc : ((term I ho) :: l.Tail.val).IsChain (· > ·) := by
    rw [← max_eq_o_cons_tail ho l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' ho l hl hlh hlc]; rw [Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₁, LocallyConstant.comapₗ, Linear_CC'₀, Subtype.coe_eta,
    LinearM

Depends on / 依赖: AddHom, AddHom.coe_mk, ContinuousMap, ContinuousMap.coe_mk, Function, Function.comp_apply, IsChain, LinearMap, LinearMap.coe_mk, LinearMap.sub_apply, Linear_CC, LocallyConstant, LocallyConstant.coe_comap, LocallyConstant.coe_mul, LocallyConstant.comap, LocallyConstant.sub_apply, Pi.mul_apply, Product, Products, Products.evalCons
-/
theorem Products.max_eq_eval [Inhabited I] (l : Products I) (hl : l.val != [])
    (hlh : l.val.head! = term I ho) :
    Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho) := by
  have hlc : ((term I ho) :: l.Tail.val).IsChain (· > ·) := by
    rw [← max_eq_o_cons_tail ho l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' ho l hl hlh hlc]; rw [Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₁, LocallyConstant.comapₗ, Linear_CC'₀, Subtype.coe_eta,
    LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LocallyConstant.sub_apply,
    LocallyConstant.coe_comap, LocallyConstant.coe_mul, ContinuousMap.coe_mk, Function.comp_apply,
    Pi.mul_apply]
  rw [CC'₁]; rw [CC'₀]; rw [Products.eval_eq]; rw [Products.eval_eq]; rw [Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : forall i, i in l.Tail.val -> (x.val i = SwapTrue o x.val i) := by
    intro i hi
    simp only [SwapTrue, @eq_comm _ (x.val i), ite_eq_right_iff, ord_term ho]
    rintro rfl
    exact ((List.IsChain.rel_cons hlc hi).ne rfl).elim
  have H : (forall i, i in l.Tail.val -> (x.val i = true)) =
      (forall i, i in l.Tail.val -> (SwapTrue o x.val i = true)) := by
    apply forall_congr; intro i; apply forall_congr; intro hi; rw [hi' i hi]
  simp only [H]
  split_ifs with h₁ h₂ h₃ <;> try (dsimp [e])
  · rw [if_pos (swapTrue_eq_true _ _), if_neg]
    · rfl
    · simp [mem_C'_eq_false C ho x x.prop]
  · push Not at h₂; obtain ⟨i, hi⟩ := h₂; exfalso; rw [hi' i hi.1] at hi; exact hi.2 (h₁ i hi.1)
  · push Not at h₁; obtain ⟨i, hi⟩ := h₁; exfalso; rw [← hi' i hi.1] at hi; exact hi.2 (h₃ i hi.1)

namespace GoodProducts

/--
theorem `max_eq_eval` / 定理 `max_eq_eval`

English:
theorem max_eq_eval
  given: (l : MaxProducts C ho)
  proof: have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_eval _ _ _ _ (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

中文:
定理 max_eq_eval
  条件: (l : MaxProducts C ho)
  证明: have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_eval _ _ _ _ (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

Depends on / 依赖: Inhabited, List.ne_nil_of_mem, Products, Products.max_eq_eval, _eq_o_of_maxProducts, l.prop, max_eq_eval, ne_nil_of_mem
-/
theorem max_eq_eval (l : MaxProducts C ho) :
    Linear_CC' C hsC ho (l.val.eval C) = l.val.Tail.eval (C' C ho) :=
  have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_eval _ _ _ _ (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

/--
theorem `max_eq_eval_unapply` / 定理 `max_eq_eval_unapply`

English:
theorem max_eq_eval_unapply
  proof: by
  ext1 l
  exact max_eq_eval _ _ _ _

include hsC in

中文:
定理 max_eq_eval_unapply
  证明: by
  ext1 l
  exact max_eq_eval _ _ _ _

include hsC in

Depends on / 依赖: max_eq_eval
-/
theorem max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : MaxProducts C ho) => Products.eval C l.val) =
    (fun l => l.val.Tail.eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

include hsC in
/--
theorem `isChain_cons_of_lt` / 定理 `isChain_cons_of_lt`

English:
theorem isChain_cons_of_lt
  statement: (l : MaxProducts C ho)
  proof: by
  have : Inhabited I := ⟨term I ho⟩
  rw [List.isChain_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha => lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.isChain_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_me

中文:
定理 isChain_cons_of_lt
  结论: (l : MaxProducts C ho)
  证明: by
  have : Inhabited I := ⟨term I ho⟩
  rw [List.isChain_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha => lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.isChain_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_me

Depends on / 依赖: Inhabited, List.isChain_iff_pairwise, List.isChain_iff_pairwise.mp, List.not_lex_nil, List.pairwise_cons, Products, Products.head, Products.lt_iff_lex_lt, Products.rel_head, _le_of_lt, _of_mem, gt_iff_lt, isChain_iff_pairwise, l.val.Tail.val, l.val.prop, lt_iff_lex_lt, lt_of_le_of_lt, max_eq_o_cons_tail, ne_nil_of_mem, not_lex_nil
-/
theorem isChain_cons_of_lt (l : MaxProducts C ho)
    (q : Products I) (hq : q < l.val.Tail) :
    List.IsChain (fun x x_1 => x > x_1) (term I ho :: q.val) := by
  have : Inhabited I := ⟨term I ho⟩
  rw [List.isChain_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha => lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.isChain_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_mem ha)) ?_
  by_cases hM : l.val.Tail.val = []
  · rw [Products.lt_iff_lex_lt, hM] at hq
    simp only [List.not_lex_nil] at hq
  · have := l.val.prop
    rw [max_eq_o_cons_tail C hsC ho l]; rw [List.isChain_iff_pairwise] at this
    exact List.rel_of_pairwise_cons this (List.head!_mem_self hM)

include hsC in
/--
theorem `good_lt_maxProducts` / 定理 `good_lt_maxProducts`

English:
theorem good_lt_maxProducts
  statement: (q : GoodProducts (π C (ord I · < o)))
  proof: by
  have : Inhabited I := ⟨term I ho⟩
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC ho l]
    apply List.Lex.rel
    rw [← Ordinal.typein_lt_typein (· < ·)]
    simp only [term, Ordinal.typei

中文:
定理 good_lt_maxProducts
  结论: (q : GoodProducts (π C (ord I · < o)))
  证明: by
  have : Inhabited I := ⟨term I ho⟩
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC ho l]
    apply List.Lex.rel
    rw [← Ordinal.typein_lt_typein (· < ·)]
    simp only [term, Ordinal.typei

Depends on / 依赖: Inhabited, List.Lex.nil, List.Lex.rel, List.cons_head, List.head, Ordinal, Ordinal.typein_enum, Ordinal.typein_lt_typein, Products, Products.prop_of_isGood, _mem_self, _tail, cons_head, max_eq_o_cons_tail, prop_of_isGood, q.prop, q.val.val, q.val.val.head, typein_enum, typein_lt_typein
-/
theorem good_lt_maxProducts (q : GoodProducts (π C (ord I · < o)))
    (l : MaxProducts C ho) : List.Lex (· < ·) q.val.val l.val.val := by
  have : Inhabited I := ⟨term I ho⟩
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC ho l]
    apply List.Lex.rel
    rw [← Ordinal.typein_lt_typein (· < ·)]
    simp only [term, Ordinal.typein_enum]
    exact Products.prop_of_isGood C _ q.prop q.val.val.head! (List.head!_mem_self h)

set_option backward.isDefEq.respectTransparency.types false in
include hC hsC in
/--
theorem `maxTail_isGood` / 定理 `maxTail_isGood`

English:
theorem maxTail_isGood
  statement: (l : MaxProducts C ho)
  proof: by
  have : Inhabited I := ⟨term I ho⟩
  -- Write `l.Tail` as a linear combination of smaller products:
  intro h
  rw [Finsupp.mem_span_image_iff_linearCombination]; rw [← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.linearCombination_apply] at hmsum
  -- Write the ima

中文:
定理 maxTail_isGood
  结论: (l : MaxProducts C ho)
  证明: by
  have : Inhabited I := ⟨term I ho⟩
  -- Write `l.Tail` as a linear combination of smaller products:
  intro h
  rw [Finsupp.mem_span_image_iff_linearCombination]; rw [← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.linearCombination_apply] at hmsum
  -- Write the ima

Depends on / 依赖: Inhabited
-/
theorem maxTail_isGood (l : MaxProducts C ho)
    (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))) :
    l.val.Tail.isGood (C' C ho) := by
  have : Inhabited I := ⟨term I ho⟩
  -- Write `l.Tail` as a linear combination of smaller products:
  intro h
  rw [Finsupp.mem_span_image_iff_linearCombination]; rw [← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.linearCombination_apply] at hmsum
  -- Write the image of `l` under `Linear_CC'` as `Linear_CC'` applied to the linear combination
  -- above, with leading `term I ho`'s added to each term:
  have : (Linear_CC' C hsC ho) (l.val.eval C) = (Linear_CC' C hsC ho)
      (Finsupp.sum m fun i a => a • ((term I ho :: i.1).map (e C)).prod) := by
    rw [← hmsum]
    simp only [map_finsuppSum]
    apply Finsupp.sum_congr
    intro q hq
    rw [map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < l.val.Tail := hmmem hq
    have : exists (p : Products I), p.val != [] ∧ p.val.head! = term I ho ∧ q = p.Tail :=
      ⟨⟨term I ho :: q.val, isChain_cons_of_lt C hsC ho l q hx''⟩,
        ⟨List.cons_ne_nil _ _, by simp only [List.head!_cons],
        by simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]⟩⟩
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2]; rw [← Products.max_eq_eval C hsC ho p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail ho p hp.1 hp.2.1]; rw [List.map_cons]; rw [List.prod_cons]
  have hse := succ_exact C hC hsC ho
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hse
  dsimp [ModuleCat.ofHom] at hse
  -- Rewrite `this` using exact sequence manipulations to conclude that a term is in the range of
  -- the linear map `πs`:
  rw [← LinearMap.sub_mem_ker_iff]; rw [← hse] at this
  obtain ⟨(n : LocallyConstant (π C (ord I · < o)) Int), hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' := h₁ (Submodule.mem_top : n in ⊤)
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w, hc⟩ := hn'
  rw [← hc]; rw [map_finsuppSum] at hn
  apply l.prop.1
  rw [← hn]
  -- Now we just need to prove that a sum of two terms belongs to a span:
  apply Submodule.add_mem
  · apply Submodule.finsuppSum_mem
    intro q _
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    dsimp only [eval]
    rw [Products.eval_πs C (Products.prop_of_isGood _ _ q.prop)]
    refine ⟨q.val, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_ofPred_eq]
    exact good_lt_maxProducts C hsC ho q l
  · apply Submodule.finsuppSum_mem
    intro q hq
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finsupp.mem_supported] at hmmem
    rw [← Finsupp.mem_support_iff] at hq
    refine ⟨⟨term I ho :: q.val, isChain_cons_of_lt C hsC ho l q (hmmem hq)⟩, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_ofPred_eq]
    rw [max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.cons ((Products.lt_iff_lex_lt q l.val.Tail).mp (hmmem hq))

/-- Given `l : MaxProducts C ho`, its `Tail` is a `GoodProducts (C' C ho)`. -/
noncomputable
/--
Definition of `MaxToGood` / `MaxToGood` 的定义

English:
definition MaxToGood
  body: fun l => ⟨l.val.Tail, maxTail_isGood C hC hsC ho l h₁⟩

中文:
定义 MaxToGood
  定义体: fun l => ⟨l.val.Tail, maxTail_isGood C hC hsC ho l h₁⟩

Depends on / 依赖: l.val.Tail, maxTail_isGood
-/
def MaxToGood
    (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))) :
    MaxProducts C ho -> GoodProducts (C' C ho) :=
  fun l => ⟨l.val.Tail, maxTail_isGood C hC hsC ho l h₁⟩

/--
theorem `maxToGood_injective` / 定理 `maxToGood_injective`

English:
theorem maxToGood_injective
  proof: by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC ho m]; rw [max_eq_o_cons_tail C hsC ho n]; rw [h]

include hC in

中文:
定理 maxToGood_injective
  证明: by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC ho m]; rw [max_eq_o_cons_tail C hsC ho n]; rw [h]

include hC in

Depends on / 依赖: MaxToGood, Subtype, Subtype.ext, Subtype.ext_iff, ext_iff, max_eq_o_cons_tail
-/
theorem maxToGood_injective
    (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))) :
    (MaxToGood C hC hsC ho h₁).Injective := by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC ho m]; rw [max_eq_o_cons_tail C hsC ho n]; rw [h]

include hC in
/--
theorem `linearIndependent_comp_of_eval` / 定理 `linearIndependent_comp_of_eval`

English:
theorem linearIndependent_comp_of_eval
  proof: by
  dsimp [SumEval, ModuleCat.ofHom]
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := MaxToGood C hC hsC ho h₁
  have hf : f.Injective := maxToGood_injective C hC hsC ho h₁
  have hh : (fun l => Products.eval (C' C ho) l.val.Tail) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

中文:
定理 linearIndependent_comp_of_eval
  证明: by
  dsimp [SumEval, ModuleCat.ofHom]
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := MaxToGood C hC hsC ho h₁
  have hf : f.Injective := maxToGood_injective C hC hsC ho h₁
  have hh : (fun l => Products.eval (C' C ho) l.val.Tail) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

Depends on / 依赖: Injective, MaxToGood, ModuleCat, ModuleCat.ofHom, Products, Products.eval, SumEval, f.Injective, h.comp, l.val.Tail, maxToGood_injective, max_eq_eval_unapply
-/
theorem linearIndependent_comp_of_eval
    (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))) :
    LinearIndependent Int (eval (C' C ho)) ->
    LinearIndependent Int (ModuleCat.ofHom (Linear_CC' C hsC ho) ∘ SumEval C ho ∘ Sum.inr) := by
  dsimp [SumEval, ModuleCat.ofHom]
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := MaxToGood C hC hsC ho h₁
  have hf : f.Injective := maxToGood_injective C hC hsC ho h₁
  have hh : (fun l => Products.eval (C' C ho) l.val.Tail) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

end GoodProducts

end Profinite.NobelingProof
