/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johan Commelin
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.CPolynomialDef
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Composition of analytic functions

In this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.compAlongComposition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : Composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `Composition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `HasFPowerSeriesAt.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `AnalyticAt.comp` states that the composition of analytic functions is analytic.
* `FormalMultilinearSeries.comp_assoc` states that composition is associative on formal
  multilinear series.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.compAlongComposition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `Composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, Composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `Composition`.

The associativity of composition on formal multilinear series is a nontrivial result: it does not
follow from the associativity of composition of analytic functions, as there is no uniqueness for
the formal multilinear series representing a function (and also, it holds even when the radius of
convergence of the series is `0`). Instead, we give a direct proof, which amounts to reordering
double sums in a careful way. The change of variables is a canonical (combinatorial) bijection
`Composition.sigmaEquivSigmaPi` between `(Σ (a : Composition n), Composition a.length)` and
`(Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i))`, and is described
in more details below in the paragraph on associativity.
-/

@[expose] public section


noncomputable section

variable {𝕜 : Type*} {E F G H : Type*}

open Filter List

open scoped Topology NNReal ENNReal

section Topological

variable [CommRing 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

/-! ### Composing formal multilinear series -/


namespace FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-!
In this paragraph, we define the composition of formal multilinear series, by summing over all
possible compositions of `n`.
-/


/--
Definition of `applyComposition` / `applyComposition` 的定义

English:
definition applyComposition
  signature: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Composition n)
  body: fun v i => p (c.blocksFun i) (v ∘ c.embedding i)

中文:
定义 applyComposition
  签名: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数} (c : Composition n)
  定义体: fun v i => p (c.blocksFun i) (v ∘ c.embedding i)

Depends on / 依赖: blocksFun, c.blocksFun, c.embedding, embedding
-/
def applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Composition n) :
    (Fin n -> E) -> Fin c.length -> F := fun v i => p (c.blocksFun i) (v ∘ c.embedding i)

/--
theorem `applyComposition_ones` / 定理 `applyComposition_ones`

English:
theorem applyComposition_ones
  given: (p : FormalMultilinearSeries 𝕜 E F) (n : Nat)
  proof: by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by lia
  refine congr_arg v ?_
  rw [Fin.ext_iff]; rw [Fin.val_castLE]; rw [Composition.ones_embedding]; rw [Fin.val_mk]

中文:
定理 applyComposition_ones
  条件: (p : FormalMultilinearSeries 𝕜 E F) (n : 自然数)
  证明: by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by lia
  refine congr_arg v ?_
  rw [Fin.ext_iff]; rw [Fin.val_castLE]; rw [Composition.ones_embedding]; rw [Fin.val_mk]

Depends on / 依赖: Composition, Composition.ones_blocksFun, Composition.ones_embedding, Fin.ext_iff, Fin.val_castLE, Fin.val_mk, congr_arg, ext_iff, ones_blocksFun, ones_embedding, p.congr, val_castLE, val_mk
-/
theorem applyComposition_ones (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) :
    p.applyComposition (Composition.ones n) = fun v i =>
      p 1 fun _ => v (Fin.castLE (Composition.length_le _) i) := by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by lia
  refine congr_arg v ?_
  rw [Fin.ext_iff]; rw [Fin.val_castLE]; rw [Composition.ones_embedding]; rw [Fin.val_mk]

/--
theorem `applyComposition_single` / 定理 `applyComposition_single`

English:
theorem applyComposition_single
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : 0 < n)
  proof: by
  ext j
  refine p.congr (by simp) fun i hi1 hi2 => ?_
  dsimp
  congr 1
  convert! Composition.single_embedding hn ⟨i, hi2⟩ using 1
  obtain ⟨j_val, j_property⟩ := j
  have : j_val = 0 := le_bot_iff.1 (Nat.lt_succ_iff.1 j_property)
  rw! [this]
  rfl

@[simp]

中文:
定理 applyComposition_single
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数} (hn : 0 < n)
  证明: by
  ext j
  refine p.congr (by simp) fun i hi1 hi2 => ?_
  dsimp
  congr 1
  convert! Composition.single_embedding hn ⟨i, hi2⟩ using 1
  obtain ⟨j_val, j_property⟩ := j
  have : j_val = 0 := le_bot_iff.1 (Nat.lt_succ_iff.1 j_property)
  rw! [this]
  rfl

@[simp]

Depends on / 依赖: Composition, Composition.single_embedding, Nat.lt_succ_iff, convert, j_property, j_val, le_bot_iff, lt_succ_iff, p.congr, single_embedding
-/
theorem applyComposition_single (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : 0 < n)
    (v : Fin n -> E) : p.applyComposition (Composition.single n hn) v = fun _j => p n v := by
  ext j
  refine p.congr (by simp) fun i hi1 hi2 => ?_
  dsimp
  congr 1
  convert! Composition.single_embedding hn ⟨i, hi2⟩ using 1
  obtain ⟨j_val, j_property⟩ := j
  have : j_val = 0 := le_bot_iff.1 (Nat.lt_succ_iff.1 j_property)
  rw! [this]
  rfl

@[simp]
/--
theorem `removeZero_applyComposition` / 定理 `removeZero_applyComposition`

English:
theorem removeZero_applyComposition
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: by
  ext v i
  simp [applyComposition, zero_lt_one.trans_le (c.one_le_blocksFun i), removeZero_of_pos]

中文:
定理 removeZero_applyComposition
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: by
  ext v i
  simp [applyComposition, zero_lt_one.trans_le (c.one_le_blocksFun i), removeZero_of_pos]

Depends on / 依赖: applyComposition, c.one_le_blocksFun, one_le_blocksFun, removeZero_of_pos, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem removeZero_applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (c : Composition n) : p.removeZero.applyComposition c = p.applyComposition c := by
  ext v i
  simp [applyComposition, zero_lt_one.trans_le (c.one_le_blocksFun i), removeZero_of_pos]

/--
theorem `applyComposition_update` / 定理 `applyComposition_update`

English:
theorem applyComposition_update
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Composition n)
  proof: by
  ext k
  by_cases h : k = c.index j
  · rw [h]
    let r : Fin (c.blocksFun (c.index j)) -> Fin n := c.embedding (c.index j)
    simp only [Function.update_self]
    change p (c.blocksFun (c.index j)) (Function.update v j z ∘ r) = _
    let j' := c.invEmbedding j
    suffices B : Function.update

中文:
定理 applyComposition_update
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数} (c : Composition n)
  证明: by
  ext k
  by_cases h : k = c.index j
  · rw [h]
    let r : Fin (c.blocksFun (c.index j)) -> Fin n := c.embedding (c.index j)
    simp only [Function.update_self]
    change p (c.blocksFun (c.index j)) (Function.update v j z ∘ r) = _
    let j' := c.invEmbedding j
    suffices B : Function.update

Depends on / 依赖: Function, Function.update, Function.update_comp_eq_of_injective, Function.update_self, blocksFun, c.blocksFun, c.embedding, c.embedding_comp_inv, c.index, c.invEmbedding, convert, embedding, embedding_comp_inv, invEmbedding, update, update_comp_eq_of_injective, update_self
-/
theorem applyComposition_update (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Composition n)
    (j : Fin n) (v : Fin n -> E) (z : E) :
    p.applyComposition c (Function.update v j z) =
      Function.update (p.applyComposition c v) (c.index j)
        (p (c.blocksFun (c.index j))
          (Function.update (v ∘ c.embedding (c.index j)) (c.invEmbedding j) z)) := by
  ext k
  by_cases h : k = c.index j
  · rw [h]
    let r : Fin (c.blocksFun (c.index j)) -> Fin n := c.embedding (c.index j)
    simp only [Function.update_self]
    change p (c.blocksFun (c.index j)) (Function.update v j z ∘ r) = _
    let j' := c.invEmbedding j
    suffices B : Function.update v j z ∘ r = Function.update (v ∘ r) j' z by rw [B]
    suffices C : Function.update v (r j') z ∘ r = Function.update (v ∘ r) j' z by
      convert! C; exact (c.embedding_comp_inv j).symm
    exact Function.update_comp_eq_of_injective _ (c.embedding _).injective _ _
  · simp only [h, Function.update_of_ne, Ne, not_false_iff]
    let r : Fin (c.blocksFun k) -> Fin n := c.embedding k
    change p (c.blocksFun k) (Function.update v j z ∘ r) = p (c.blocksFun k) (v ∘ r)
    suffices B : Function.update v j z ∘ r = v ∘ r by rw [B]
    apply Function.update_comp_eq_of_notMem_range
    rwa [c.mem_range_embedding_iff']

@[simp]
/--
theorem `compContinuousLinearMap_applyComposition` / 定理 `compContinuousLinearMap_applyComposition`

English:
theorem compContinuousLinearMap_applyComposition
  statement: {n : Nat} (p : FormalMultilinearSeries 𝕜 F G)
  proof: by
  ext
  simp [applyComposition, Function.comp_def]

@[simp]

中文:
定理 compContinuousLinearMap_applyComposition
  结论: {n : 自然数} (p : FormalMultilinearSeries 𝕜 F G)
  证明: by
  ext
  simp [applyComposition, Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, applyComposition, comp_def
-/
theorem compContinuousLinearMap_applyComposition {n : Nat} (p : FormalMultilinearSeries 𝕜 F G)
    (f : E ->L[𝕜] F) (c : Composition n) (v : Fin n -> E) :
    (p.compContinuousLinearMap f).applyComposition c v = p.applyComposition c (f ∘ v) := by
  ext
  simp [applyComposition, Function.comp_def]

@[simp]
/--
theorem `applyComposition_apply_prod` / 定理 `applyComposition_apply_prod`

English:
theorem applyComposition_apply_prod
  statement: {H : Type*} [CommRing H] [Algebra 𝕜 H] [TopologicalSpace H]
  proof: by
  rfl

中文:
定理 applyComposition_apply_prod
  结论: {H : 类型} [CommRing H] [Algebra 𝕜 H] [TopologicalSpace H]
  证明: by
  rfl
-/
theorem applyComposition_apply_prod {H : Type*} [CommRing H] [Algebra 𝕜 H] [TopologicalSpace H]
    [IsTopologicalRing H] [ContinuousConstSMul 𝕜 H] (p : FormalMultilinearSeries 𝕜 E H) {n : Nat}
    (c : Composition n) (v : Fin n -> E) :
    ∏ i, p.applyComposition c v i = ∏ i, p (c.blocksFun i) (v ∘ c.embedding i) := by
  rfl

end FormalMultilinearSeries

namespace ContinuousMultilinearMap

open FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/--
Definition of `compAlongComposition` / `compAlongComposition` 的定义

English:
definition compAlongComposition
  signature: {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
  body: MultilinearMap.mk' (fun v => f (p.applyComposition c v))
      (fun v i x y => by simp only [applyComposition_update, map_update_add])
      (fun v i c x => by simp only [applyComposition_update, map_update_smul])
  cont :=
f.cont.comp
continuous_pi fun _ => (coe_continuous _).comp continuous_pi fun

中文:
定义 compAlongComposition
  签名: {n : 自然数} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
  定义体: MultilinearMap.mk' (fun v => f (p.applyComposition c v))
      (fun v i x y => by simp only [applyComposition_update, map_update_add])
      (fun v i c x => by simp only [applyComposition_update, map_update_smul])
  cont :=
f.cont.comp
continuous_pi fun _ => (coe_continuous _).comp continuous_pi fun

Depends on / 依赖: MultilinearMap, MultilinearMap.mk, applyComposition, applyComposition_update, coe_continuous, continuous_apply, continuous_pi, f.cont.comp, map_update_add, map_update_smul, p.applyComposition
-/
def compAlongComposition {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]->L[𝕜] G) : E [×n]->L[𝕜] G where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v => f (p.applyComposition c v))
      (fun v i x y => by simp only [applyComposition_update, map_update_add])
      (fun v i c x => by simp only [applyComposition_update, map_update_smul])
  cont :=
f.cont.comp
continuous_pi fun _ => (coe_continuous _).comp continuous_pi fun _ => continuous_apply _

@[simp]
/--
theorem `compAlongComposition_apply` / 定理 `compAlongComposition_apply`

English:
theorem compAlongComposition_apply
  statement: {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
  proof: rfl

中文:
定理 compAlongComposition_apply
  结论: {n : 自然数} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
  证明: rfl
-/
theorem compAlongComposition_apply {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]->L[𝕜] G) (v : Fin n -> E) :
    (f.compAlongComposition p c) v = f (p.applyComposition c v) :=
  rfl

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/--
Definition of `compAlongComposition` / `compAlongComposition` 的定义

English:
definition compAlongComposition
  signature: {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  body: (q c.length).compAlongComposition p c

@[simp]

中文:
定义 compAlongComposition
  签名: {n : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  定义体: (q c.length).compAlongComposition p c

@[simp]

Depends on / 依赖: c.length, compAlongComposition, length
-/
def compAlongComposition {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) : (E [×n]->L[𝕜] G) :=
  (q c.length).compAlongComposition p c

@[simp]
/--
theorem `compAlongComposition_apply` / 定理 `compAlongComposition_apply`

English:
theorem compAlongComposition_apply
  statement: {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  proof: rfl

中文:
定理 compAlongComposition_apply
  结论: {n : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  证明: rfl
-/
theorem compAlongComposition_apply {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) (v : Fin n -> E) :
    (q.compAlongComposition p c) v = q c.length (p.applyComposition c v) :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  body: fun n => ∑ c : Composition n, q.compAlongComposition p c

中文:
定义 comp
  签名: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  定义体: fun n => ∑ c : Composition n, q.compAlongComposition p c
-/
protected def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => ∑ c : Composition n, q.compAlongComposition p c

/--
theorem `comp_coeff_zero` / 定理 `comp_coeff_zero`

English:
theorem comp_coeff_zero
  statement: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  let c : Composition 0 := Composition.ones 0
  dsimp [FormalMultilinearSeries.comp]
  have : {c} = (Finset.univ : Finset (Composition 0)) := by
    apply Finset.eq_of_subset_of_card_le <;> simp [Finset.card_univ, composition_card 0]
  rw [← this]; rw [Finset.sum_singleton]; rw [compAlongComposit

中文:
定理 comp_coeff_zero
  结论: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  let c : Composition 0 := Composition.ones 0
  dsimp [FormalMultilinearSeries.comp]
  have : {c} = (Finset.univ : Finset (Composition 0)) := by
    apply Finset.eq_of_subset_of_card_le <;> simp [Finset.card_univ, composition_card 0]
  rw [← this]; rw [Finset.sum_singleton]; rw [compAlongComposit

Depends on / 依赖: Composition, Composition.ones, Finset, Finset.card_univ, Finset.eq_of_subset_of_card_le, Finset.sum_singleton, Finset.univ, FormalMultilinearSeries, FormalMultilinearSeries.comp, card_univ, compAlongComposition_apply, composition_card, eq_of_subset_of_card_le, sum_singleton
-/
theorem comp_coeff_zero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 0 -> E) (v' : Fin 0 -> F) : (q.comp p) 0 v = q 0 v' := by
  let c : Composition 0 := Composition.ones 0
  dsimp [FormalMultilinearSeries.comp]
  have : {c} = (Finset.univ : Finset (Composition 0)) := by
    apply Finset.eq_of_subset_of_card_le <;> simp [Finset.card_univ, composition_card 0]
  rw [← this]; rw [Finset.sum_singleton]; rw [compAlongComposition_apply]
  symm; congr!

@[simp]
/--
theorem `comp_coeff_zero'` / 定理 `comp_coeff_zero'`

English:
theorem comp_coeff_zero'
  statement: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: q.comp_coeff_zero p v _

中文:
定理 comp_coeff_zero'
  结论: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: q.comp_coeff_zero p v _

Depends on / 依赖: comp_coeff_zero, q.comp_coeff_zero
-/
theorem comp_coeff_zero' (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 0 -> E) : (q.comp p) 0 v = q 0 fun _i => 0 :=
  q.comp_coeff_zero p v _

/--
theorem `comp_coeff_zero''` / 定理 `comp_coeff_zero''`

English:
theorem comp_coeff_zero''
  given: (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultilinearSeries 𝕜 E E)
  proof: by ext v; exact q.comp_coeff_zero p _ _

中文:
定理 comp_coeff_zero''
  条件: (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultilinearSeries 𝕜 E E)
  证明: by ext v; exact q.comp_coeff_zero p _ _

Depends on / 依赖: comp_coeff_zero, q.comp_coeff_zero
-/
theorem comp_coeff_zero'' (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultilinearSeries 𝕜 E E) :
    (q.comp p) 0 = q 0 := by ext v; exact q.comp_coeff_zero p _ _

/--
theorem `comp_coeff_one` / 定理 `comp_coeff_one`

English:
theorem comp_coeff_one
  statement: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  have : {Composition.ones 1} = (Finset.univ : Finset (Composition 1)) :=
    Finset.eq_univ_of_card _ (by simp [composition_card])
  simp only [FormalMultilinearSeries.comp, compAlongComposition_apply, ← this,
    Finset.sum_singleton]
  refine q.congr (by simp) fun i hi1 hi2 => ?_
  simp only [

中文:
定理 comp_coeff_one
  结论: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  have : {Composition.ones 1} = (Finset.univ : Finset (Composition 1)) :=
    Finset.eq_univ_of_card _ (by simp [composition_card])
  simp only [FormalMultilinearSeries.comp, compAlongComposition_apply, ← this,
    Finset.sum_singleton]
  refine q.congr (by simp) fun i hi1 hi2 => ?_
  simp only [

Depends on / 依赖: Composition, Composition.ones, Finset, Finset.eq_univ_of_card, Finset.sum_singleton, Finset.univ, FormalMultilinearSeries, FormalMultilinearSeries.comp, _hj1, applyComposition_ones, compAlongComposition_apply, composition_card, eq_univ_of_card, p.congr, q.congr, sum_singleton
-/
theorem comp_coeff_one (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 1 -> E) : (q.comp p) 1 v = q 1 fun _i => p 1 v := by
  have : {Composition.ones 1} = (Finset.univ : Finset (Composition 1)) :=
    Finset.eq_univ_of_card _ (by simp [composition_card])
  simp only [FormalMultilinearSeries.comp, compAlongComposition_apply, ← this,
    Finset.sum_singleton]
  refine q.congr (by simp) fun i hi1 hi2 => ?_
  simp only [applyComposition_ones]
  exact p.congr rfl fun j _hj1 hj2 => by congr!

/--
theorem `removeZero_comp_of_pos` / 定理 `removeZero_comp_of_pos`

English:
theorem removeZero_comp_of_pos
  statement: (q : FormalMultilinearSeries 𝕜 F G)
  proof: by
  ext v
  simp only [FormalMultilinearSeries.comp, compAlongComposition,
    ContinuousMultilinearMap.compAlongComposition_apply, sum_apply]
  refine Finset.sum_congr rfl fun c _hc => ?_
  rw [removeZero_of_pos _ (c.length_pos_of_pos hn)]

@[simp]

中文:
定理 removeZero_comp_of_pos
  结论: (q : FormalMultilinearSeries 𝕜 F G)
  证明: by
  ext v
  simp only [FormalMultilinearSeries.comp, compAlongComposition,
    ContinuousMultilinearMap.compAlongComposition_apply, sum_apply]
  refine Finset.sum_congr rfl fun c _hc => ?_
  rw [removeZero_of_pos _ (c.length_pos_of_pos hn)]

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compAlongComposition_apply, Finset, Finset.sum_congr, FormalMultilinearSeries, FormalMultilinearSeries.comp, c.length_pos_of_pos, compAlongComposition, compAlongComposition_apply, length_pos_of_pos, removeZero_of_pos, sum_apply, sum_congr
-/
theorem removeZero_comp_of_pos (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : 0 < n) :
    q.removeZero.comp p n = q.comp p n := by
  ext v
  simp only [FormalMultilinearSeries.comp, compAlongComposition,
    ContinuousMultilinearMap.compAlongComposition_apply, sum_apply]
  refine Finset.sum_congr rfl fun c _hc => ?_
  rw [removeZero_of_pos _ (c.length_pos_of_pos hn)]

@[simp]
/--
theorem `comp_removeZero` / 定理 `comp_removeZero`

English:
theorem comp_removeZero
  given: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by ext n; simp [FormalMultilinearSeries.comp]

中文:
定理 comp_removeZero
  条件: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by ext n; simp [FormalMultilinearSeries.comp]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.comp
-/
theorem comp_removeZero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    q.comp p.removeZero = q.comp p := by ext n; simp [FormalMultilinearSeries.comp]

end FormalMultilinearSeries

end Topological

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

namespace FormalMultilinearSeries

/--
theorem `compAlongComposition_bound` / 定理 `compAlongComposition_bound`

English:
theorem compAlongComposition_bound
  statement: {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
  proof: calc
    ‖f.compAlongComposition p c v‖ = ‖f (p.applyComposition c v)‖ := rfl
    _ <= ‖f‖ * ∏ i, ‖p.applyComposition c v i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ <= ‖f‖ * ∏ i, ‖p (c.blocksFun i)‖ * ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      gcongr with i
      apply Co

中文:
定理 compAlongComposition_bound
  结论: {n : 自然数} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
  证明: calc
    ‖f.compAlongComposition p c v‖ = ‖f (p.applyComposition c v)‖ := rfl
    _ <= ‖f‖ * ∏ i, ‖p.applyComposition c v i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ <= ‖f‖ * ∏ i, ‖p (c.blocksFun i)‖ * ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      gcongr with i
      apply Co

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.le_opNorm, Finset, Finset.prod_mul_distrib, applyComposition, blocksFun, c.blocksFun, c.embedding, compAlongComposition, embedding, f.compAlongComposition, le_opNorm, mul_assoc, p.applyComposition, prod_mul_distrib
-/
theorem compAlongComposition_bound {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]->L[𝕜] G) (v : Fin n -> E) :
    ‖f.compAlongComposition p c v‖ <= (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖ :=
  calc
    ‖f.compAlongComposition p c v‖ = ‖f (p.applyComposition c v)‖ := rfl
    _ <= ‖f‖ * ∏ i, ‖p.applyComposition c v i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ <= ‖f‖ * ∏ i, ‖p (c.blocksFun i)‖ * ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      gcongr with i
      apply ContinuousMultilinearMap.le_opNorm
    _ = (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) *
        ∏ i, ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      rw [Finset.prod_mul_distrib]; rw [mul_assoc]
    _ = (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖ := by
      rw [← c.blocksFinEquiv.prod_comp]; rw [← Finset.univ_sigma_univ]; rw [Finset.prod_sigma]
      congr

/--
theorem `compAlongComposition_norm` / 定理 `compAlongComposition_norm`

English:
theorem compAlongComposition_norm
  statement: {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  proof: ContinuousMultilinearMap.opNorm_le_bound (by positivity) (compAlongComposition_bound _ _ _)

中文:
定理 compAlongComposition_norm
  结论: {n : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  证明: ContinuousMultilinearMap.opNorm_le_bound (by positivity) (compAlongComposition_bound _ _ _)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, compAlongComposition_bound, opNorm_le_bound
-/
theorem compAlongComposition_norm {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ‖q.compAlongComposition p c‖ <= ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity) (compAlongComposition_bound _ _ _)

/--
theorem `compAlongComposition_nnnorm` / 定理 `compAlongComposition_nnnorm`

English:
theorem compAlongComposition_nnnorm
  statement: {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  proof: by
  rw [← NNReal.coe_le_coe]; push_cast; exact q.compAlongComposition_norm p c

中文:
定理 compAlongComposition_nnnorm
  结论: {n : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  证明: by
  rw [← NNReal.coe_le_coe]; push_cast; exact q.compAlongComposition_norm p c

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, compAlongComposition_norm, q.compAlongComposition_norm
-/
theorem compAlongComposition_nnnorm {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ‖q.compAlongComposition p c‖₊ <= ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊ := by
  rw [← NNReal.coe_le_coe]; push_cast; exact q.compAlongComposition_norm p c

/-!
### The identity formal power series

We will now define the identity power series, and show that it is a neutral element for left and
right composition.
-/


section

variable (𝕜 E)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (x : E)

中文:
定义 id
  签名: (x : E)
-/
def id (x : E) : FormalMultilinearSeries 𝕜 E E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 E E).symm (ContinuousLinearMap.id 𝕜 E)
  | _ => 0

/--
theorem `id_apply_zero` / 定理 `id_apply_zero`

English:
theorem id_apply_zero
  given: (x : E) (v : Fin 0 -> E)
  proof: rfl

中文:
定理 id_apply_zero
  条件: (x : E) (v : Fin 0 -> E)
  证明: rfl
-/
@[simp] theorem id_apply_zero (x : E) (v : Fin 0 -> E) :
    (FormalMultilinearSeries.id 𝕜 E x) 0 v = x := rfl

/-- The first coefficient of `id 𝕜 E` is the identity. -/
@[simp]
/--
theorem `id_apply_one` / 定理 `id_apply_one`

English:
theorem id_apply_one
  given: (x : E) (v : Fin 1 -> E)
  statement: (FormalMultilinearSeries.id 𝕜 E x) 1 v = v 0
  proof: rfl

中文:
定理 id_apply_one
  条件: (x : E) (v : Fin 1 -> E)
  结论: (FormalMultilinearSeries.id 𝕜 E x) 1 v = v 0
  证明: rfl
-/
theorem id_apply_one (x : E) (v : Fin 1 -> E) : (FormalMultilinearSeries.id 𝕜 E x) 1 v = v 0 :=
  rfl

/--
theorem `id_apply_one'` / 定理 `id_apply_one'`

English:
theorem id_apply_one'
  given: (x : E) {n : Nat} (h : n = 1) (v : Fin n -> E)
  proof: by
  subst n
  apply id_apply_one

中文:
定理 id_apply_one'
  条件: (x : E) {n : 自然数} (h : n = 1) (v : Fin n -> E)
  证明: by
  subst n
  apply id_apply_one

Depends on / 依赖: id_apply_one
-/
theorem id_apply_one' (x : E) {n : Nat} (h : n = 1) (v : Fin n -> E) :
    (id 𝕜 E x) n v = v ⟨0, h.symm ▸ zero_lt_one⟩ := by
  subst n
  apply id_apply_one

/-- For `n ≠ 1`, the `n`-th coefficient of `id 𝕜 E` is zero, by definition. -/
@[simp]
/--
theorem `id_apply_of_one_lt` / 定理 `id_apply_of_one_lt`

English:
theorem id_apply_of_one_lt
  given: (x : E) {n : Nat} (h : 1 < n)
  proof: by
  match n with
    | 0 => contradiction
    | 1 => contradiction
    | n + 2 => rfl

中文:
定理 id_apply_of_one_lt
  条件: (x : E) {n : 自然数} (h : 1 < n)
  证明: by
  match n with
    | 0 => contradiction
    | 1 => contradiction
    | n + 2 => rfl
-/
theorem id_apply_of_one_lt (x : E) {n : Nat} (h : 1 < n) :
    (FormalMultilinearSeries.id 𝕜 E x) n = 0 := by
  match n with
    | 0 => contradiction
    | 1 => contradiction
    | n + 2 => rfl

end

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  statement: p.comp (id 𝕜 E x) = p
  proof: by
  ext1 n
  dsimp [FormalMultilinearSeries.comp]
  rw [Finset.sum_eq_single (Composition.ones n)]
  · show compAlongComposition p (id 𝕜 E x) (Composition.ones n) = p n
    ext v
    rw [compAlongComposition_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComposition_on

中文:
定理 comp_id
  条件: (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  结论: p.comp (id 𝕜 E x) = p
  证明: by
  ext1 n
  dsimp [FormalMultilinearSeries.comp]
  rw [Finset.sum_eq_single (Composition.ones n)]
  · show compAlongComposition p (id 𝕜 E x) (Composition.ones n) = p n
    ext v
    rw [compAlongComposition_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComposition_on

Depends on / 依赖: Composition, Composition.ones, Composition.ones_length, Fin.ext_iff, Fin.val_castLE, Fin.val_mk, Finset, Finset.sum_eq_single, Finset.univ, FormalMultilinearSeries, FormalMultilinearSeries.comp, applyComposition_ones, compAlongComposition, compAlongComposition_apply, congr_arg, ext_iff, intros, ones_length, p.congr, sum_eq_single
-/
theorem comp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) : p.comp (id 𝕜 E x) = p := by
  ext1 n
  dsimp [FormalMultilinearSeries.comp]
  rw [Finset.sum_eq_single (Composition.ones n)]
  · show compAlongComposition p (id 𝕜 E x) (Composition.ones n) = p n
    ext v
    rw [compAlongComposition_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComposition_ones]
    refine congr_arg v ?_
    rw [Fin.ext_iff]; rw [Fin.val_castLE]; rw [Fin.val_mk]
  · change
    forall b : Composition n,
      b in Finset.univ -> b != Composition.ones n -> compAlongComposition p (id 𝕜 E x) b = 0
    intro b _ hb
    obtain ⟨k, hk, lt_k⟩ : exists (k : Nat), k in Composition.blocks b ∧ 1 < k :=
      Composition.ne_ones_iff.1 hb
    obtain ⟨i, hi⟩ : exists (i : Fin b.blocks.length), b.blocks[i] = k :=
      List.get_of_mem hk
    let j : Fin b.length := ⟨i.val, b.blocks_length ▸ i.prop⟩
    have A : 1 < b.blocksFun j := by convert! lt_k
    ext v
    rw [compAlongComposition_apply]; rw [_root_.zero_apply]
    apply ContinuousMultilinearMap.map_coord_zero _ j
    dsimp [applyComposition]
    rw [id_apply_of_one_lt _ _ _ A]; rw [_root_.zero_apply]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (p : FormalMultilinearSeries 𝕜 E F) (v0 : Fin 0 -> E)
  proof: by
  ext1 n
  obtain rfl | n_pos := n.eq_zero_or_pos
  · ext v
    simp only [comp_coeff_zero', id_apply_zero]
    congr with i
    exact i.elim0
  · dsimp [FormalMultilinearSeries.comp]
    rw [Finset.sum_eq_single (Composition.single n n_pos)]
    · show compAlongComposition (id 𝕜 F (p 0 v0)) p (C

中文:
定理 id_comp
  条件: (p : FormalMultilinearSeries 𝕜 E F) (v0 : Fin 0 -> E)
  证明: by
  ext1 n
  obtain rfl | n_pos := n.eq_zero_or_pos
  · ext v
    simp only [comp_coeff_zero', id_apply_zero]
    congr with i
    exact i.elim0
  · dsimp [FormalMultilinearSeries.comp]
    rw [Finset.sum_eq_single (Composition.single n n_pos)]
    · show compAlongComposition (id 𝕜 F (p 0 v0)) p (C

Depends on / 依赖: Composition, Composition.single, Composition.single_length, Finset, Finset.sum_eq_single, FormalMultilinearSeries, FormalMultilinearSeries.comp, applyComposition, compAlongComposition, compAlongComposition_apply, comp_coeff_zero, congr_arg, eq_zero_or_pos, i.elim0, id_apply_one, id_apply_zero, n.eq_zero_or_pos, n_pos, p.congr, single
-/
theorem id_comp (p : FormalMultilinearSeries 𝕜 E F) (v0 : Fin 0 -> E) :
    (id 𝕜 F (p 0 v0)).comp p = p := by
  ext1 n
  obtain rfl | n_pos := n.eq_zero_or_pos
  · ext v
    simp only [comp_coeff_zero', id_apply_zero]
    congr with i
    exact i.elim0
  · dsimp [FormalMultilinearSeries.comp]
    rw [Finset.sum_eq_single (Composition.single n n_pos)]
    · show compAlongComposition (id 𝕜 F (p 0 v0)) p (Composition.single n n_pos) = p n
      ext v
      rw [compAlongComposition_apply]; rw [id_apply_one' _ _ _ (Composition.single_length n_pos)]
      dsimp [applyComposition]
refine p.congr rfl fun i him hin => congr_arg v ?_
      ext; simp
    · change
      forall b : Composition n, b in Finset.univ -> b != Composition.single n n_pos ->
        compAlongComposition (id 𝕜 F (p 0 v0)) p b = 0
      intro b _ hb
      have A : 1 < b.length := by
        have : b.length != 1 := by simpa [Composition.eq_single_iff_length] using hb
        have : 0 < b.length := Composition.length_pos_of_pos b n_pos
        lia
      ext v
      rw [compAlongComposition_apply]; rw [id_apply_of_one_lt _ _ _ A]; rw [_root_.zero_apply]; rw [_root_.zero_apply]
    · simp

/--
theorem `id_comp'` / 定理 `id_comp'`

English:
theorem id_comp'
  given: (p : FormalMultilinearSeries 𝕜 E F) (x : F) (v0 : Fin 0 -> E) (h : x = p 0 v0)
  proof: by
  simp [h]

中文:
定理 id_comp'
  条件: (p : FormalMultilinearSeries 𝕜 E F) (x : F) (v0 : Fin 0 -> E) (h : x = p 0 v0)
  证明: by
  simp [h]
-/
theorem id_comp' (p : FormalMultilinearSeries 𝕜 E F) (x : F) (v0 : Fin 0 -> E) (h : x = p 0 v0) :
    (id 𝕜 F x).comp p = p := by
  simp [h]

/-! ### Summability properties of the composition of formal power series -/


section

/--
theorem `comp_summable_nnreal` / 定理 `comp_summable_nnreal`

English:
theorem comp_summable_nnreal
  statement: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  /- This follows from the fact that the growth rate of `‖qₙ‖` and `‖pₙ‖` is at most geometric,
    giving a geometric bound on each `‖q.compAlongComposition p op‖`, together with the
    fact that there are `2^(n-1)` compositions of `n`, giving at most a geometric loss. -/
  rcases ENNReal.lt_if

中文:
定理 comp_summable_nnreal
  结论: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  /- This follows from the fact that the growth rate of `‖qₙ‖` and `‖pₙ‖` is at most geometric,
    giving a geometric bound on each `‖q.compAlongComposition p op‖`, together with the
    fact that there are `2^(n-1)` compositions of `n`, giving at most a geometric loss. -/
  rcases ENNReal.lt_if
-/
theorem comp_summable_nnreal (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (hq : 0 < q.radius) (hp : 0 < p.radius) :
    exists r > (0 : Real>=0),
      Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 := by
  /- This follows from the fact that the growth rate of `‖qₙ‖` and `‖pₙ‖` is at most geometric,
    giving a geometric bound on each `‖q.compAlongComposition p op‖`, together with the
    fact that there are `2^(n-1)` compositions of `n`, giving at most a geometric loss. -/
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hq) with ⟨rq, rq_pos, hrq⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hp) with ⟨rp, rp_pos, hrp⟩
  simp only [lt_min_iff, ENNReal.coe_lt_one_iff, ENNReal.coe_pos] at hrp hrq rp_pos rq_pos
  obtain ⟨Cq, _hCq0, hCq⟩ : exists Cq > 0, forall n, ‖q n‖₊ * rq ^ n <= Cq :=
    q.nnnorm_mul_pow_le_of_lt_radius hrq.2
  obtain ⟨Cp, hCp1, hCp⟩ : exists Cp >= 1, forall n, ‖p n‖₊ * rp ^ n <= Cp := by
    rcases p.nnnorm_mul_pow_le_of_lt_radius hrp.2 with ⟨Cp, -, hCp⟩
    exact ⟨max Cp 1, le_max_right _ _, fun n => (hCp n).trans (le_max_left _ _)⟩
  let r0 : Real>=0 := (4 * Cp)⁻¹
  have r0_pos : 0 < r0 := inv_pos.2 (mul_pos zero_lt_four (zero_lt_one.trans_le hCp1))
  set r : Real>=0 := rp * rq * r0
  have r_pos : 0 < r := mul_pos (mul_pos rp_pos rq_pos) r0_pos
  have I :
    forall i : Σ n : Nat, Composition n, ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 <= Cq / 4 ^ i.1 := by
    rintro ⟨n, c⟩
    have A := calc
      ‖q c.length‖₊ * rq ^ n <= ‖q c.length‖₊ * rq ^ c.length :=
        mul_le_mul' le_rfl (pow_le_pow_of_le_one rq.2 hrq.1.le c.length_le)
      _ <= Cq := hCq _
    have B := calc
      (∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n = ∏ i, ‖p (c.blocksFun i)‖₊ * rp ^ c.blocksFun i := by
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
      _ <= ∏ _i : Fin c.length, Cp := Finset.prod_le_prod' fun i _ => hCp _
      _ = Cp ^ c.length := by simp
      _ <= Cp ^ n := pow_right_mono₀ hCp1 c.length_le
    calc
      ‖q.compAlongComposition p c‖₊ * r ^ n <=
          (‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊) * r ^ n := by
        grw [q.compAlongComposition_nnnorm p c]
      _ = ‖q c.length‖₊ * rq ^ n * ((∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n) * r0 ^ n := by
        ring
      _ <= Cq * Cp ^ n * r0 ^ n := mul_le_mul' (mul_le_mul' A B) le_rfl
      _ = Cq / 4 ^ n := by
        simp only [r0]
        simp [field, mul_pow]
  refine ⟨r, r_pos, NNReal.summable_of_le I ?_⟩
  simp_rw [div_eq_mul_inv]
  refine Summable.mul_left _ ?_
  have : forall n : Nat, HasSum (fun c : Composition n => (4 ^ n : Real>=0)⁻¹) (2 ^ (n - 1) / 4 ^ n) := by
    intro n
    convert! hasSum_fintype fun c : Composition n => (4 ^ n : Real>=0)⁻¹
    simp [Finset.card_univ, composition_card, div_eq_mul_inv]
  refine NNReal.summable_sigma.2 ⟨fun n => (this n).summable, (NNReal.summable_nat_add_iff 1).1 ?_⟩
  convert! (NNReal.summable_geometric (NNReal.div_lt_one_of_lt one_lt_two)).mul_left (1 / 4) using 1
  ext1 n
  rw [(this _).tsum_eq]; rw [add_tsub_cancel_right]
  simp [field, pow_succ, mul_pow, show (4 : Real>=0) = 2 * 2 by norm_num]

end

/--
theorem `le_comp_radius_of_summable` / 定理 `le_comp_radius_of_summable`

English:
theorem le_comp_radius_of_summable
  statement: (q : FormalMultilinearSeries 𝕜 F G)
  proof: by
  refine
    le_radius_of_bound_nnreal _
      (∑' i : Σ n, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst) fun n => ?_
  calc
    ‖FormalMultilinearSeries.comp q p n‖₊ * r ^ n <=
        ∑' c : Composition n, ‖compAlongComposition q p c‖₊ * r ^ n := by
      rw [tsum_fintype]; rw [

中文:
定理 le_comp_radius_of_summable
  结论: (q : FormalMultilinearSeries 𝕜 F G)
  证明: by
  refine
    le_radius_of_bound_nnreal _
      (∑' i : Σ n, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst) fun n => ?_
  calc
    ‖FormalMultilinearSeries.comp q p n‖₊ * r ^ n <=
        ∑' c : Composition n, ‖compAlongComposition q p c‖₊ * r ^ n := by
      rw [tsum_fintype]; rw [

Depends on / 依赖: Composition, Finset, Finset.sum_mul, FormalMultilinearSeries, FormalMultilinearSeries.comp, NNReal, NNReal.tsum_comp_le_tsum_of_inj, compAlongComposition, i.fst, i.snd, le_radius_of_bound_nnreal, le_rfl, mul_le_mul, nnnorm_sum_le, sigma_mk_injective, sum_mul, tsum_comp_le_tsum_of_inj, tsum_fintype
-/
theorem le_comp_radius_of_summable (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (r : Real>=0)
    (hr : Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1) :
    (r : Real>=0∞) <= (q.comp p).radius := by
  refine
    le_radius_of_bound_nnreal _
      (∑' i : Σ n, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst) fun n => ?_
  calc
    ‖FormalMultilinearSeries.comp q p n‖₊ * r ^ n <=
        ∑' c : Composition n, ‖compAlongComposition q p c‖₊ * r ^ n := by
      rw [tsum_fintype]; rw [← Finset.sum_mul]
      exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl
    _ <= ∑' i : Σ n : Nat, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst :=
      NNReal.tsum_comp_le_tsum_of_inj hr sigma_mk_injective

/-!
### Composing analytic functions

Now, we will prove that the composition of the partial sums of `q` and `p` up to order `N` is
given by a sum over some large subset of `Σ n, Composition n` of `q.compAlongComposition p`, to
deduce that the series for `q.comp p` indeed converges to `g ∘ f` when `q` is a power series for
`g` and `p` is a power series for `f`.

This proof is a big reindexing argument of a sum. Since it is a bit involved, we define first
the source of the change of variables (`compPartialSumSource`), its target
(`compPartialSumTarget`) and the change of variables itself (`compChangeOfVariables`) before
giving the main statement in `comp_partialSum`. -/


/--
Definition of `compPartialSumSource` / `compPartialSumSource` 的定义

English:
definition compPartialSumSource
  signature: (m M N : Nat)
  body: Finset.sigma (Finset.Ico m M) (fun n : Nat => Fintype.piFinset fun _i : Fin n => Finset.Ico 1 N :)

@[simp]

中文:
定义 compPartialSumSource
  签名: (m M N : 自然数)
  定义体: Finset.sigma (Finset.Ico m M) (fun n : Nat => Fintype.piFinset fun _i : Fin n => Finset.Ico 1 N :)

@[simp]

Depends on / 依赖: Finset, Finset.Ico, Finset.sigma, Fintype, Fintype.piFinset, piFinset
-/
def compPartialSumSource (m M N : Nat) : Finset (Σ n, Fin n -> Nat) :=
  Finset.sigma (Finset.Ico m M) (fun n : Nat => Fintype.piFinset fun _i : Fin n => Finset.Ico 1 N :)

@[simp]
/--
theorem `mem_compPartialSumSource_iff` / 定理 `mem_compPartialSumSource_iff`

English:
theorem mem_compPartialSumSource_iff
  given: (m M N : Nat) (i : Σ n, Fin n -> Nat)
  proof: by
  simp only [compPartialSumSource, Finset.mem_Ico, Fintype.mem_piFinset, Finset.mem_sigma]

中文:
定理 mem_compPartialSumSource_iff
  条件: (m M N : 自然数) (i : Σ n, Fin n -> 自然数)
  证明: by
  simp only [compPartialSumSource, Finset.mem_Ico, Fintype.mem_piFinset, Finset.mem_sigma]

Depends on / 依赖: Finset, Finset.mem_Ico, Finset.mem_sigma, Fintype, Fintype.mem_piFinset, compPartialSumSource, mem_Ico, mem_piFinset, mem_sigma
-/
theorem mem_compPartialSumSource_iff (m M N : Nat) (i : Σ n, Fin n -> Nat) :
    i in compPartialSumSource m M N ↔
      (m <= i.1 ∧ i.1 < M) ∧ forall a : Fin i.1, 1 <= i.2 a ∧ i.2 a < N := by
  simp only [compPartialSumSource, Finset.mem_Ico, Fintype.mem_piFinset, Finset.mem_sigma]

/--
Definition of `compChangeOfVariables` / `compChangeOfVariables` 的定义

English:
definition compChangeOfVariables
  signature: (m M N : Nat) (i : Σ n, Fin n -> Nat) (hi : i in compPartialSumSource m M N)
  body: by
  rcases i with ⟨n, f⟩
  rw [mem_compPartialSumSource_iff] at hi
  refine ⟨∑ j, f j, ofFn fun a => f a, fun {i} hi' => ?_, by simp [sum_ofFn]⟩
  obtain ⟨j, rfl⟩ : exists j : Fin n, f j = i := by rwa [mem_ofFn', Set.mem_range] at hi'
  exact (hi.2 j).1

@[simp]

中文:
定义 compChangeOfVariables
  签名: (m M N : 自然数) (i : Σ n, Fin n -> 自然数) (hi : i in compPartialSumSource m M N)
  定义体: by
  rcases i with ⟨n, f⟩
  rw [mem_compPartialSumSource_iff] at hi
  refine ⟨∑ j, f j, ofFn fun a => f a, fun {i} hi' => ?_, by simp [sum_ofFn]⟩
  obtain ⟨j, rfl⟩ : exists j : Fin n, f j = i := by rwa [mem_ofFn', Set.mem_range] at hi'
  exact (hi.2 j).1

@[simp]

Depends on / 依赖: Set.mem_range, mem_compPartialSumSource_iff, mem_ofFn, mem_range, sum_ofFn
-/
def compChangeOfVariables (m M N : Nat) (i : Σ n, Fin n -> Nat) (hi : i in compPartialSumSource m M N) :
    Σ n, Composition n := by
  rcases i with ⟨n, f⟩
  rw [mem_compPartialSumSource_iff] at hi
  refine ⟨∑ j, f j, ofFn fun a => f a, fun {i} hi' => ?_, by simp [sum_ofFn]⟩
  obtain ⟨j, rfl⟩ : exists j : Fin n, f j = i := by rwa [mem_ofFn', Set.mem_range] at hi'
  exact (hi.2 j).1

@[simp]
/--
theorem `compChangeOfVariables_length` / 定理 `compChangeOfVariables_length`

English:
theorem compChangeOfVariables_length
  statement: (m M N : Nat) {i : Σ n, Fin n -> Nat}
  proof: by
  rcases i with ⟨k, blocks_fun⟩
  dsimp [compChangeOfVariables]
  simp only [Composition.length, length_ofFn]

中文:
定理 compChangeOfVariables_length
  结论: (m M N : 自然数) {i : Σ n, Fin n -> 自然数}
  证明: by
  rcases i with ⟨k, blocks_fun⟩
  dsimp [compChangeOfVariables]
  simp only [Composition.length, length_ofFn]

Depends on / 依赖: Composition, Composition.length, blocks_fun, compChangeOfVariables, length, length_ofFn
-/
theorem compChangeOfVariables_length (m M N : Nat) {i : Σ n, Fin n -> Nat}
    (hi : i in compPartialSumSource m M N) :
    Composition.length (compChangeOfVariables m M N i hi).2 = i.1 := by
  rcases i with ⟨k, blocks_fun⟩
  dsimp [compChangeOfVariables]
  simp only [Composition.length, length_ofFn]

/--
theorem `compChangeOfVariables_blocksFun` / 定理 `compChangeOfVariables_blocksFun`

English:
theorem compChangeOfVariables_blocksFun
  statement: (m M N : Nat) {i : Σ n, Fin n -> Nat}
  proof: by
  rcases i with ⟨n, f⟩
  dsimp [Composition.blocksFun, Composition.blocks, compChangeOfVariables]
  simp only [List.getElem_ofFn]

中文:
定理 compChangeOfVariables_blocksFun
  结论: (m M N : 自然数) {i : Σ n, Fin n -> 自然数}
  证明: by
  rcases i with ⟨n, f⟩
  dsimp [Composition.blocksFun, Composition.blocks, compChangeOfVariables]
  simp only [List.getElem_ofFn]

Depends on / 依赖: Composition, Composition.blocks, Composition.blocksFun, List.getElem_ofFn, blocks, blocksFun, compChangeOfVariables, getElem_ofFn
-/
theorem compChangeOfVariables_blocksFun (m M N : Nat) {i : Σ n, Fin n -> Nat}
    (hi : i in compPartialSumSource m M N) (j : Fin i.1) :
    (compChangeOfVariables m M N i hi).2.blocksFun
        ⟨j, (compChangeOfVariables_length m M N hi).symm ▸ j.2⟩ =
      i.2 j := by
  rcases i with ⟨n, f⟩
  dsimp [Composition.blocksFun, Composition.blocks, compChangeOfVariables]
  simp only [List.getElem_ofFn]

/--
Definition of `compPartialSumTargetSet` / `compPartialSumTargetSet` 的定义

English:
definition compPartialSumTargetSet
  signature: (m M N : Nat)
  body: {i | m <= i.2.length ∧ i.2.length < M ∧ forall j : Fin i.2.length, i.2.blocksFun j < N}

中文:
定义 compPartialSumTargetSet
  签名: (m M N : 自然数)
  定义体: {i | m <= i.2.length ∧ i.2.length < M ∧ forall j : Fin i.2.length, i.2.blocksFun j < N}

Depends on / 依赖: blocksFun, length
-/
def compPartialSumTargetSet (m M N : Nat) : Set (Σ n, Composition n) :=
  {i | m <= i.2.length ∧ i.2.length < M ∧ forall j : Fin i.2.length, i.2.blocksFun j < N}

/--
theorem `compPartialSumTargetSet_image_compPartialSumSource` / 定理 `compPartialSumTargetSet_image_compPartialSumSource`

English:
theorem compPartialSumTargetSet_image_compPartialSumSource
  statement: (m M N : Nat)
  proof: by
  rcases i with ⟨n, c⟩
  refine ⟨⟨c.length, c.blocksFun⟩, ?_, ?_⟩
  · simp only [compPartialSumTargetSet, Set.mem_ofPred_eq] at hi
    simp only [mem_compPartialSumSource_iff, hi.left, hi.right, true_and, and_true]
    exact fun a => c.one_le_blocks' _
  · dsimp [compChangeOfVariables]
    rw [Co

中文:
定理 compPartialSumTargetSet_image_compPartialSumSource
  结论: (m M N : 自然数)
  证明: by
  rcases i with ⟨n, c⟩
  refine ⟨⟨c.length, c.blocksFun⟩, ?_, ?_⟩
  · simp only [compPartialSumTargetSet, Set.mem_ofPred_eq] at hi
    simp only [mem_compPartialSumSource_iff, hi.left, hi.right, true_and, and_true]
    exact fun a => c.one_le_blocks' _
  · dsimp [compChangeOfVariables]
    rw [Co

Depends on / 依赖: Composition, Composition.blocksFun, Composition.sigma_eq_iff_blocks_eq, List.ofFn_get, Set.mem_ofPred_eq, and_true, blocks, blocksFun, c.blocks, c.blocksFun, c.length, c.one_le_blocks, compChangeOfVariables, compPartialSumTargetSet, conv_rhs, hi.left, hi.right, length, mem_compPartialSumSource_iff, mem_ofPred_eq
-/
theorem compPartialSumTargetSet_image_compPartialSumSource (m M N : Nat)
    (i : Σ n, Composition n) (hi : i in compPartialSumTargetSet m M N) :
    exists (j : _) (hj : j in compPartialSumSource m M N), compChangeOfVariables m M N j hj = i := by
  rcases i with ⟨n, c⟩
  refine ⟨⟨c.length, c.blocksFun⟩, ?_, ?_⟩
  · simp only [compPartialSumTargetSet, Set.mem_ofPred_eq] at hi
    simp only [mem_compPartialSumSource_iff, hi.left, hi.right, true_and, and_true]
    exact fun a => c.one_le_blocks' _
  · dsimp [compChangeOfVariables]
    rw [Composition.sigma_eq_iff_blocks_eq]
    simp only [Composition.blocksFun]
    conv_rhs => rw [← List.ofFn_get c.blocks]

/--
Definition of `compPartialSumTarget` / `compPartialSumTarget` 的定义

English:
definition compPartialSumTarget
  signature: (m M N : Nat)
  body: Set.Finite.toFinset
((Finset.finite_toSet _).dependent_image _).subset
      compPartialSumTargetSet_image_compPartialSumSource m M N

@[simp]

中文:
定义 compPartialSumTarget
  签名: (m M N : 自然数)
  定义体: Set.Finite.toFinset
((Finset.finite_toSet _).dependent_image _).subset
      compPartialSumTargetSet_image_compPartialSumSource m M N

@[simp]

Depends on / 依赖: Finite, Finset, Finset.finite_toSet, Set.Finite.toFinset, compPartialSumTargetSet_image_compPartialSumSource, dependent_image, finite_toSet, subset, toFinset
-/
def compPartialSumTarget (m M N : Nat) : Finset (Σ n, Composition n) :=
Set.Finite.toFinset
((Finset.finite_toSet _).dependent_image _).subset
      compPartialSumTargetSet_image_compPartialSumSource m M N

@[simp]
/--
theorem `mem_compPartialSumTarget_iff` / 定理 `mem_compPartialSumTarget_iff`

English:
theorem mem_compPartialSumTarget_iff
  given: {m M N : Nat} {a : Σ n, Composition n}
  proof: by
  simp [compPartialSumTarget, compPartialSumTargetSet]

中文:
定理 mem_compPartialSumTarget_iff
  条件: {m M N : 自然数} {a : Σ n, Composition n}
  证明: by
  simp [compPartialSumTarget, compPartialSumTargetSet]

Depends on / 依赖: compPartialSumTarget, compPartialSumTargetSet
-/
theorem mem_compPartialSumTarget_iff {m M N : Nat} {a : Σ n, Composition n} :
    a in compPartialSumTarget m M N ↔
      m <= a.2.length ∧ a.2.length < M ∧ forall j : Fin a.2.length, a.2.blocksFun j < N := by
  simp [compPartialSumTarget, compPartialSumTargetSet]

/--
theorem `compChangeOfVariables_sum` / 定理 `compChangeOfVariables_sum`

English:
theorem compChangeOfVariables_sum
  statement: {α : Type*} [AddCommMonoid α] (m M N : Nat)
  proof: by
  apply Finset.sum_bij (compChangeOfVariables m M N)
  -- We should show that the correspondence we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `compPartialSumTarget m N N`
  · rintro ⟨k, blocks_fun⟩ H
    rw [mem_compPart

中文:
定理 compChangeOfVariables_sum
  结论: {α : 类型} [AddCommMonoid α] (m M N : 自然数)
  证明: by
  apply Finset.sum_bij (compChangeOfVariables m M N)
  -- We should show that the correspondence we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `compPartialSumTarget m N N`
  · rintro ⟨k, blocks_fun⟩ H
    rw [mem_compPart

Depends on / 依赖: Finset, Finset.sum_bij, compChangeOfVariables, sum_bij
-/
theorem compChangeOfVariables_sum {α : Type*} [AddCommMonoid α] (m M N : Nat)
    (f : (Σ n : Nat, Fin n -> Nat) -> α) (g : (Σ n, Composition n) -> α)
    (h : forall (e) (he : e in compPartialSumSource m M N), f e = g (compChangeOfVariables m M N e he)) :
    ∑ e in compPartialSumSource m M N, f e = ∑ e in compPartialSumTarget m M N, g e := by
  apply Finset.sum_bij (compChangeOfVariables m M N)
  -- We should show that the correspondence we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `compPartialSumTarget m N N`
  · rintro ⟨k, blocks_fun⟩ H
    rw [mem_compPartialSumSource_iff] at H
    simp only [mem_compPartialSumTarget_iff, Composition.length, H.left,
      length_ofFn, true_and, compChangeOfVariables]
    intro j
    simp only [Composition.blocksFun, (H.right _).right, List.get_ofFn]
  -- 2 - show that the map is injective
  · rintro ⟨k, blocks_fun⟩ H ⟨k', blocks_fun'⟩ H' heq
    obtain rfl : k = k' := by
      have := (compChangeOfVariables_length m M N H).symm
      rwa [heq, compChangeOfVariables_length] at this
    congr
    funext i
    calc
      blocks_fun i = (compChangeOfVariables m M N _ H).2.blocksFun _ :=
        (compChangeOfVariables_blocksFun m M N H i).symm
      _ = (compChangeOfVariables m M N _ H').2.blocksFun _ := by
        grind
      _ = blocks_fun' i := compChangeOfVariables_blocksFun m M N H' i
  -- 3 - show that the map is surjective
  · intro i hi
    apply compPartialSumTargetSet_image_compPartialSumSource m M N i
    simpa [compPartialSumTarget] using hi
  -- 4 - show that the composition gives the `compAlongComposition` application
  · assumption

/--
theorem `compPartialSumTarget_tendsto_prod_atTop` / 定理 `compPartialSumTarget_tendsto_prod_atTop`

English:
theorem compPartialSumTarget_tendsto_prod_atTop
  proof: by
  apply Monotone.tendsto_atTop_finset
  · intro m n hmn a ha
    have : forall i, i < m.1 -> i < n.1 := fun i hi => lt_of_lt_of_le hi hmn.1
    have : forall i, i < m.2 -> i < n.2 := fun i hi => lt_of_lt_of_le hi hmn.2
    simp_all
  · rintro ⟨n, c⟩
    simp only [mem_compPartialSumTarget_iff]
  

中文:
定理 compPartialSumTarget_tendsto_prod_atTop
  证明: by
  apply Monotone.tendsto_atTop_finset
  · intro m n hmn a ha
    have : forall i, i < m.1 -> i < n.1 := fun i hi => lt_of_lt_of_le hi hmn.1
    have : forall i, i < m.2 -> i < n.2 := fun i hi => lt_of_lt_of_le hi hmn.2
    simp_all
  · rintro ⟨n, c⟩
    simp only [mem_compPartialSumTarget_iff]
  

Depends on / 依赖: BddAbove, Finset, Finset.bddAbove, Finset.univ.image, Monotone, Monotone.tendsto_atTop_finset, bddAbove, blocksFun, bot_le, c.blocksFun, c.length, le_max_right, length, lt_add_one, lt_of, lt_of_le_of_lt, lt_of_lt_of_le, mem_compPartialSumTarget_iff, tendsto_atTop_finset
-/
theorem compPartialSumTarget_tendsto_prod_atTop :
    Tendsto (fun (p : Nat × Nat) => compPartialSumTarget 0 p.1 p.2) atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro m n hmn a ha
    have : forall i, i < m.1 -> i < n.1 := fun i hi => lt_of_lt_of_le hi hmn.1
    have : forall i, i < m.2 -> i < n.2 := fun i hi => lt_of_lt_of_le hi hmn.2
    simp_all
  · rintro ⟨n, c⟩
    simp only [mem_compPartialSumTarget_iff]
    obtain ⟨n, hn⟩ : BddAbove ((Finset.univ.image fun i : Fin c.length => c.blocksFun i) : Set Nat) :=
      Finset.bddAbove _
    refine
      ⟨max n c.length + 1, bot_le, lt_of_le_of_lt (le_max_right n c.length) (lt_add_one _), fun j =>
        lt_of_le_of_lt (le_trans ?_ (le_max_left _ _)) (lt_add_one _)⟩
    apply hn
    simp only [Finset.mem_image_of_mem, Finset.mem_coe, Finset.mem_univ]

/--
theorem `compPartialSumTarget_tendsto_atTop` / 定理 `compPartialSumTarget_tendsto_atTop`

English:
theorem compPartialSumTarget_tendsto_atTop
  proof: by
  apply Tendsto.comp compPartialSumTarget_tendsto_prod_atTop tendsto_atTop_diagonal

中文:
定理 compPartialSumTarget_tendsto_atTop
  证明: by
  apply Tendsto.comp compPartialSumTarget_tendsto_prod_atTop tendsto_atTop_diagonal

Depends on / 依赖: Tendsto, Tendsto.comp, compPartialSumTarget_tendsto_prod_atTop, tendsto_atTop_diagonal
-/
theorem compPartialSumTarget_tendsto_atTop :
    Tendsto (fun N => compPartialSumTarget 0 N N) atTop atTop := by
  apply Tendsto.comp compPartialSumTarget_tendsto_prod_atTop tendsto_atTop_diagonal

/--
theorem `comp_partialSum` / 定理 `comp_partialSum`

English:
theorem comp_partialSum
  statement: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H :
    (∑ n in Finset.range M,
        ∑ r in Fintype.piFinset fun i : Fin n => Finset.Ico 1 N,
          q n fun i : Fin n => p (r i) fun _j => z) =
      ∑ i in compPartialSumTarget 0 M 

中文:
定理 comp_partialSum
  结论: (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H :
    (∑ n in Finset.range M,
        ∑ r in Fintype.piFinset fun i : Fin n => Finset.Ico 1 N,
          q n fun i : Fin n => p (r i) fun _j => z) =
      ∑ i in compPartialSumTarget 0 M 
-/
theorem comp_partialSum (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (M N : Nat) (z : E) :
    q.partialSum M (∑ i in Finset.Ico 1 N, p i fun _j => z) =
      ∑ i in compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fun _j => z := by
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H :
    (∑ n in Finset.range M,
        ∑ r in Fintype.piFinset fun i : Fin n => Finset.Ico 1 N,
          q n fun i : Fin n => p (r i) fun _j => z) =
      ∑ i in compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fun _j => z by
    simpa only [FormalMultilinearSeries.partialSum, ContinuousMultilinearMap.map_sum_finset] using H
  -- rewrite the first sum as a big sum over a sigma type, in the finset
  -- `compPartialSumTarget 0 N N`
  rw [Finset.range_eq_Ico]; rw [Finset.sum_sigma']
  -- use `compChangeOfVariables_sum`, saying that this change of variables respects sums
  apply compChangeOfVariables_sum 0 M N
  rintro ⟨k, blocks_fun⟩ H
  apply congr _ (compChangeOfVariables_length 0 M N H).symm
  intros
  rw [← compChangeOfVariables_blocksFun 0 M N H]; rw [applyComposition]; rw [Function.comp_def]

end FormalMultilinearSeries

open FormalMultilinearSeries

/--
theorem `HasFPowerSeriesWithinAt.comp` / 定理 `HasFPowerSeriesWithinAt.comp`

English:
theorem HasFPowerSeriesWithinAt.comp
  statement: {g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G}
  proof: by
  /- Consider `rf` and `rg` such that `f` and `g` have power series expansion on the disks
    of radius `rf` and `rg`. -/
  rcases hg with ⟨rg, Hg⟩
  rcases hf with ⟨rf, Hf⟩
  -- The terms defining `q.comp p` are geometrically summable in a disk of some radius `r`.
  rcases q.comp_summable_nnrea

中文:
定理 HasFPowerSeriesWithinAt.comp
  结论: {g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G}
  证明: by
  /- Consider `rf` and `rg` such that `f` and `g` have power series expansion on the disks
    of radius `rf` and `rg`. -/
  rcases hg with ⟨rg, Hg⟩
  rcases hf with ⟨rf, Hf⟩
  -- The terms defining `q.comp p` are geometrically summable in a disk of some radius `r`.
  rcases q.comp_summable_nnrea
-/
theorem HasFPowerSeriesWithinAt.comp {g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E} {t : Set F} {s : Set E}
    (hg : HasFPowerSeriesWithinAt g q t (f x)) (hf : HasFPowerSeriesWithinAt f p s x)
    (hs : Set.MapsTo f s t) : HasFPowerSeriesWithinAt (g ∘ f) (q.comp p) s x := by
  /- Consider `rf` and `rg` such that `f` and `g` have power series expansion on the disks
    of radius `rf` and `rg`. -/
  rcases hg with ⟨rg, Hg⟩
  rcases hf with ⟨rf, Hf⟩
  -- The terms defining `q.comp p` are geometrically summable in a disk of some radius `r`.
  rcases q.comp_summable_nnreal p Hg.radius_pos Hf.radius_pos with ⟨r, r_pos : 0 < r, hr⟩
  /- We will consider `y` which is smaller than `r` and `rf`, and also small enough that
    `f (x + y)` is close enough to `f x` to be in the disk where `g` is well behaved. Let
    `min (r, rf, δ)` be this new radius. -/
  obtain ⟨δ, δpos, hδ⟩ :
    exists δ : Real>=0∞, 0 < δ ∧ forall {z : E}, z in insert x s inter Metric.eball x δ
      -> f z in insert (f x) t inter Metric.eball (f x) rg := by
    have : insert (f x) t inter Metric.eball (f x) rg in 𝓝[insert (f x) t] (f x) := by
      apply inter_mem_nhdsWithin
      exact Metric.eball_mem_nhds _ Hg.r_pos
    have := Hf.analyticWithinAt.continuousWithinAt_insert.tendsto_nhdsWithin (hs.insert x) this
    rcases EMetric.mem_nhdsWithin_iff.1 this with ⟨δ, δpos, Hδ⟩
    exact ⟨δ, δpos, fun {z} hz => Hδ (by rwa [Set.inter_comm])⟩
  let rf' := min rf δ
  have min_pos : 0 < min rf' r := by
    simp only [rf', r_pos, Hf.r_pos, δpos, lt_min_iff, ENNReal.coe_pos, and_self_iff]
  /- We will show that `g ∘ f` admits the power series `q.comp p` in the disk of
    radius `min (r, rf', δ)`. -/
  refine ⟨min rf' r, ?_⟩
  refine
    ⟨le_trans (min_le_right rf' r) (FormalMultilinearSeries.le_comp_radius_of_summable q p r hr),
      min_pos, fun {y} h'y hy => ?_⟩
  /- Let `y` satisfy `‖y‖ < min (r, rf', δ)`. We want to show that `g (f (x + y))` is the sum of
    `q.comp p` applied to `y`. -/
  -- First, check that `y` is small enough so that estimates for `f` and `g` apply.
  have y_mem : y in Metric.eball (0 : E) rf :=
    (Metric.eball_subset_eball (le_trans (min_le_left _ _) (min_le_left _ _))) hy
  have fy_mem : f (x + y) in insert (f x) t inter Metric.eball (f x) rg := by
    apply hδ
    have : y in Metric.eball (0 : E) δ :=
      (Metric.eball_subset_eball (le_trans (min_le_left _ _) (min_le_right _ _))) hy
    simpa [-Set.mem_insert_iff, edist_eq_enorm_sub, h'y]
  /- Now the proof starts. To show that the sum of `q.comp p` at `y` is `g (f (x + y))`,
    we will write `q.comp p` applied to `y` as a big sum over all compositions.
    Since the sum is summable, to get its convergence it suffices to get
    the convergence along some increasing sequence of sets.
    We will use the sequence of sets `compPartialSumTarget 0 n n`,
    along which the sum is exactly the composition of the partial sums of `q` and `p`, by design.
    To show that it converges to `g (f (x + y))`, pointwise convergence would not be enough,
    but we have uniform convergence to save the day. -/
  -- First step: the partial sum of `p` converges to `f (x + y)`.
  have A : Tendsto (fun n => (n, ∑ a in Finset.Ico 1 n, p a fun _ => y))
      atTop (atTop ×ˢ 𝓝 (f (x + y) - f x)) := by
    apply Tendsto.prodMk tendsto_id
    have L : forallᶠ n in atTop, (∑ a in Finset.range n, p a fun _b => y) - f x
        = ∑ a in Finset.Ico 1 n, p a fun _b => y := by
      rw [eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      symm
      rw [eq_sub_iff_add_eq']; rw [Finset.range_eq_Ico]; rw [← Hf.coeff_zero fun _i => y]; rw [Finset.sum_eq_sum_Ico_succ_bot hn]
    have :
      Tendsto (fun n => (∑ a in Finset.range n, p a fun _b => y) - f x) atTop
        (𝓝 (f (x + y) - f x)) :=
      (Hf.hasSum h'y y_mem).tendsto_sum_nat.sub tendsto_const_nhds
    exact Tendsto.congr' L this
  -- Second step: the composition of the partial sums of `q` and `p` converges to `g (f (x + y))`.
  have B : Tendsto (fun n => q.partialSum n (∑ a in Finset.Ico 1 n, p a fun _b => y)) atTop
      (𝓝 (g (f (x + y)))) := by
    -- we use the fact that the partial sums of `q` converge to `g (f (x + y))`, uniformly on a
    -- neighborhood of `f (x + y)`.
    have : Tendsto (fun (z : Nat × F) => q.partialSum z.1 z.2)
        (atTop ×ˢ 𝓝 (f (x + y) - f x)) (𝓝 (g (f x + (f (x + y) - f x)))) := by
      apply Hg.tendsto_partialSum_prod (y := f (x + y) - f x)
      · simpa [edist_eq_enorm_sub] using! fy_mem.2
      · simpa using! fy_mem.1
    simpa using! this.comp A
  -- Third step: the sum over all compositions in `compPartialSumTarget 0 n n` converges to
  -- `g (f (x + y))`. As this sum is exactly the composition of the partial sum, this is a direct
  -- consequence of the second step
  have C :
    Tendsto
      (fun n => ∑ i in compPartialSumTarget 0 n n, q.compAlongComposition p i.2 fun _j => y)
      atTop (𝓝 (g (f (x + y)))) := by
    simpa [comp_partialSum] using! B
  -- Fourth step: the sum over all compositions is `g (f (x + y))`. This follows from the
  -- convergence along a subsequence proved in the third step, and the fact that the sum is Cauchy
  -- thanks to the summability properties.
  have D :
    HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (g (f (x + y))) :=
    haveI cau :
      CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i in s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ <=
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ <= ‖compAlongComposition q p c‖ * (r : Real) ^ n := by
          rw [Finset.prod_const]; rw [Finset.card_fin]
          gcongr
          rw [Metric.mem_eball]; rw [edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    tendsto_nhds_of_cauchySeq_of_subseq cau compPartialSumTarget_tendsto_atTop C
  -- Fifth step: the sum over `n` of `q.comp p n` can be expressed as a particular resummation of
  -- the sum over all compositions, by grouping together the compositions of the same
  -- integer `n`. The convergence of the whole sum therefore implies the convergence of the sum
  -- of `q.comp p n`
  have E : HasSum (fun n => (q.comp p) n fun _j => y) (g (f (x + y))) := by
    apply D.sigma
    intro n
    simp only [compAlongComposition_apply, FormalMultilinearSeries.comp, sum_apply]
    exact hasSum_fintype _
  rw [Function.comp_apply]
  exact E

/--
theorem `HasFPowerSeriesAt.comp` / 定理 `HasFPowerSeriesAt.comp`

English:
theorem HasFPowerSeriesAt.comp
  statement: {g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G}
  proof: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf hg ⊢
  apply hg.comp hf (by simp)

中文:
定理 HasFPowerSeriesAt.comp
  结论: {g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G}
  证明: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf hg ⊢
  apply hg.comp hf (by simp)

Depends on / 依赖: hasFPowerSeriesWithinAt_univ, hg.comp
-/
theorem HasFPowerSeriesAt.comp {g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hg : HasFPowerSeriesAt g q (f x)) (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt (g ∘ f) (q.comp p) x := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf hg ⊢
  apply hg.comp hf (by simp)

/--
theorem `AnalyticWithinAt.comp` / 定理 `AnalyticWithinAt.comp`

English:
theorem AnalyticWithinAt.comp
  statement: {g : F -> G} {f : E -> F} {x : E} {t : Set F} {s : Set E}
  proof: by
  let ⟨_q, hq⟩ := hg
  let ⟨_p, hp⟩ := hf
  exact (hq.comp hp h).analyticWithinAt

中文:
定理 AnalyticWithinAt.comp
  结论: {g : F -> G} {f : E -> F} {x : E} {t : Set F} {s : Set E}
  证明: by
  let ⟨_q, hq⟩ := hg
  let ⟨_p, hp⟩ := hf
  exact (hq.comp hp h).analyticWithinAt

Depends on / 依赖: analyticWithinAt, hq.comp
-/
theorem AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {x : E} {t : Set F} {s : Set E}
    (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : AnalyticWithinAt 𝕜 f s x) (h : Set.MapsTo f s t) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  let ⟨_q, hq⟩ := hg
  let ⟨_p, hp⟩ := hf
  exact (hq.comp hp h).analyticWithinAt

/--
theorem `AnalyticWithinAt.comp_of_eq` / 定理 `AnalyticWithinAt.comp_of_eq`

English:
theorem AnalyticWithinAt.comp_of_eq
  statement: {g : F -> G} {f : E -> F} {y : F} {x : E} {t : Set F} {s : Set E}
  proof: by
  rw [← hy] at hg
  exact hg.comp hf h

中文:
定理 AnalyticWithinAt.comp_of_eq
  结论: {g : F -> G} {f : E -> F} {y : F} {x : E} {t : Set F} {s : Set E}
  证明: by
  rw [← hy] at hg
  exact hg.comp hf h

Depends on / 依赖: hg.comp
-/
theorem AnalyticWithinAt.comp_of_eq {g : F -> G} {f : E -> F} {y : F} {x : E} {t : Set F} {s : Set E}
    (hg : AnalyticWithinAt 𝕜 g t y) (hf : AnalyticWithinAt 𝕜 f s x) (h : Set.MapsTo f s t)
    (hy : f x = y) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← hy] at hg
  exact hg.comp hf h

/--
lemma `AnalyticOn.comp` / 引理 `AnalyticOn.comp`

English:
lemma AnalyticOn.comp
  statement: {f : F -> G} {g : E -> F} {s : Set F}
  proof: fun x m => (hf _ (h m)).comp (hg x m) h

中文:
引理 AnalyticOn.comp
  结论: {f : F -> G} {g : E -> F} {s : Set F}
  证明: fun x m => (hf _ (h m)).comp (hg x m) h
-/
lemma AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F}
    {t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) :
    AnalyticOn 𝕜 (f ∘ g) t :=
  fun x m => (hf _ (h m)).comp (hg x m) h

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g ∘ f` is
analytic at `x`. -/
@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.comp` / 定理 `AnalyticAt.comp`

English:
theorem AnalyticAt.comp
  statement: {g : F -> G} {f : E -> F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
  proof: by
  rw [← analyticWithinAt_univ] at hg hf ⊢
  apply hg.comp hf (by simp)

@[deprecated (since := "2026-01-24")] alias AnalyticAt.comp' := AnalyticAt.fun_comp

中文:
定理 AnalyticAt.comp
  结论: {g : F -> G} {f : E -> F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
  证明: by
  rw [← analyticWithinAt_univ] at hg hf ⊢
  apply hg.comp hf (by simp)

@[deprecated (since := "2026-01-24")] alias AnalyticAt.comp' := AnalyticAt.fun_comp

Depends on / 依赖: analyticWithinAt_univ, hg.comp
-/
theorem AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
    (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x := by
  rw [← analyticWithinAt_univ] at hg hf ⊢
  apply hg.comp hf (by simp)

@[deprecated (since := "2026-01-24")] alias AnalyticAt.comp' := AnalyticAt.fun_comp

/-- Version of `AnalyticAt.comp` where point equality is a separate hypothesis. -/
@[to_fun]
/--
theorem `AnalyticAt.comp_of_eq` / 定理 `AnalyticAt.comp_of_eq`

English:
theorem AnalyticAt.comp_of_eq
  statement: {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : AnalyticAt 𝕜 g y)
  proof: by
  rw [← hy] at hg
  exact hg.comp hf
@[deprecated (since := "2026-05-18")] alias AnalyticAt.comp_of_eq' := AnalyticAt.fun_comp_of_eq

中文:
定理 AnalyticAt.comp_of_eq
  结论: {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : AnalyticAt 𝕜 g y)
  证明: by
  rw [← hy] at hg
  exact hg.comp hf
@[deprecated (since := "2026-05-18")] alias AnalyticAt.comp_of_eq' := AnalyticAt.fun_comp_of_eq

Depends on / 依赖: AnalyticAt, AnalyticAt.comp_of_eq, AnalyticAt.fun_comp_of_eq, comp_of_eq, deprecated, fun_comp_of_eq, hg.comp
-/
theorem AnalyticAt.comp_of_eq {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : AnalyticAt 𝕜 g y)
    (hf : AnalyticAt 𝕜 f x) (hy : f x = y) : AnalyticAt 𝕜 (g ∘ f) x := by
  rw [← hy] at hg
  exact hg.comp hf
@[deprecated (since := "2026-05-18")] alias AnalyticAt.comp_of_eq' := AnalyticAt.fun_comp_of_eq

/--
theorem `AnalyticAt.comp_analyticWithinAt` / 定理 `AnalyticAt.comp_analyticWithinAt`

English:
theorem AnalyticAt.comp_analyticWithinAt
  statement: {g : F -> G} {f : E -> F} {x : E} {s : Set E}
  proof: by
  rw [← analyticWithinAt_univ] at hg
  exact hg.comp hf (Set.mapsTo_univ _ _)

中文:
定理 AnalyticAt.comp_analyticWithinAt
  结论: {g : F -> G} {f : E -> F} {x : E} {s : Set E}
  证明: by
  rw [← analyticWithinAt_univ] at hg
  exact hg.comp hf (Set.mapsTo_univ _ _)

Depends on / 依赖: Set.mapsTo_univ, analyticWithinAt_univ, hg.comp, mapsTo_univ
-/
theorem AnalyticAt.comp_analyticWithinAt {g : F -> G} {f : E -> F} {x : E} {s : Set E}
    (hg : AnalyticAt 𝕜 g (f x)) (hf : AnalyticWithinAt 𝕜 f s x) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← analyticWithinAt_univ] at hg
  exact hg.comp hf (Set.mapsTo_univ _ _)

/--
theorem `AnalyticAt.comp_analyticWithinAt_of_eq` / 定理 `AnalyticAt.comp_analyticWithinAt_of_eq`

English:
theorem AnalyticAt.comp_analyticWithinAt_of_eq
  statement: {g : F -> G} {f : E -> F} {x : E} {y : F} {s : Set E}
  proof: by
  rw [← h] at hg
  exact hg.comp_analyticWithinAt hf

中文:
定理 AnalyticAt.comp_analyticWithinAt_of_eq
  结论: {g : F -> G} {f : E -> F} {x : E} {y : F} {s : Set E}
  证明: by
  rw [← h] at hg
  exact hg.comp_analyticWithinAt hf

Depends on / 依赖: comp_analyticWithinAt, hg.comp_analyticWithinAt
-/
theorem AnalyticAt.comp_analyticWithinAt_of_eq {g : F -> G} {f : E -> F} {x : E} {y : F} {s : Set E}
    (hg : AnalyticAt 𝕜 g y) (hf : AnalyticWithinAt 𝕜 f s x) (h : f x = y) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← h] at hg
  exact hg.comp_analyticWithinAt hf

/--
theorem `AnalyticOnNhd.comp'` / 定理 `AnalyticOnNhd.comp'`

English:
theorem AnalyticOnNhd.comp'
  statement: {s : Set E} {g : F -> G} {f : E -> F} (hg : AnalyticOnNhd 𝕜 g (s.image f))
  proof: fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)

中文:
定理 AnalyticOnNhd.comp'
  结论: {s : Set E} {g : F -> G} {f : E -> F} (hg : AnalyticOnNhd 𝕜 g (s.image f))
  证明: fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem
-/
theorem AnalyticOnNhd.comp' {s : Set E} {g : F -> G} {f : E -> F} (hg : AnalyticOnNhd 𝕜 g (s.image f))
    (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (g ∘ f) s :=
  fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)

/--
theorem `AnalyticOnNhd.comp` / 定理 `AnalyticOnNhd.comp`

English:
theorem AnalyticOnNhd.comp
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F}
  proof: comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

中文:
定理 AnalyticOnNhd.comp
  结论: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F}
  证明: comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

Depends on / 依赖: Set.mapsTo_iff_image_subset.mp, mapsTo_iff_image_subset
-/
theorem AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F}
    (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set.MapsTo f s t) :
    AnalyticOnNhd 𝕜 (g ∘ f) s :=
  comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

/--
lemma `AnalyticOnNhd.comp_analyticOn` / 引理 `AnalyticOnNhd.comp_analyticOn`

English:
lemma AnalyticOnNhd.comp_analyticOn
  statement: {f : F -> G} {g : E -> F} {s : Set F}
  proof: fun x m => (hf _ (h m)).comp_analyticWithinAt (hg x m)

中文:
引理 AnalyticOnNhd.comp_analyticOn
  结论: {f : F -> G} {g : E -> F} {s : Set F}
  证明: fun x m => (hf _ (h m)).comp_analyticWithinAt (hg x m)

Depends on / 依赖: comp_analyticWithinAt
-/
lemma AnalyticOnNhd.comp_analyticOn {f : F -> G} {g : E -> F} {s : Set F}
    {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) :
    AnalyticOn 𝕜 (f ∘ g) t :=
  fun x m => (hf _ (h m)).comp_analyticWithinAt (hg x m)

/--
theorem `HasFiniteFPowerSeriesAt.comp` / 定理 `HasFiniteFPowerSeriesAt.comp`

English:
theorem HasFiniteFPowerSeriesAt.comp
  statement: {m n : Nat} {g : F -> G} {f : E -> F}
  proof: by
  rcases hg.hasFPowerSeriesAt.comp hf.hasFPowerSeriesAt with ⟨r, hr⟩
  refine ⟨r, hr, fun i hi => ?_⟩
  apply Finset.sum_eq_zero
  rintro c -
  ext v
  simp only [compAlongComposition_apply, _root_.zero_apply]
  rcases le_or_gt m c.length with hc | hc
  · simp [hg.finite _ hc]
  obtain ⟨j, hj⟩ : 

中文:
定理 HasFiniteFPowerSeriesAt.comp
  结论: {m n : 自然数} {g : F -> G} {f : E -> F}
  证明: by
  rcases hg.hasFPowerSeriesAt.comp hf.hasFPowerSeriesAt with ⟨r, hr⟩
  refine ⟨r, hr, fun i hi => ?_⟩
  apply Finset.sum_eq_zero
  rintro c -
  ext v
  simp only [compAlongComposition_apply, _root_.zero_apply]
  rcases le_or_gt m c.length with hc | hc
  · simp [hg.finite _ hc]
  obtain ⟨j, hj⟩ : 

Depends on / 依赖: Finset, Finset.sum_eq_zero, _root_, _root_.zero_apply, blocksFun, c.blocksFun, c.length, c.sum_blocksFun, compAlongComposition_apply, contrapose, eq_zero_or_pos, finite, hasFPowerSeriesAt, hf.hasFPowerSeriesAt, hg.finite, hg.hasFPowerSeriesAt.comp, le_or_gt, length, sum_blocksFun, sum_eq_zero
-/
theorem HasFiniteFPowerSeriesAt.comp {m n : Nat} {g : F -> G} {f : E -> F}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hg : HasFiniteFPowerSeriesAt g q (f x) m) (hf : HasFiniteFPowerSeriesAt f p x n) (hn : 0 < n) :
    HasFiniteFPowerSeriesAt (g ∘ f) (q.comp p) x (m * n) := by
  rcases hg.hasFPowerSeriesAt.comp hf.hasFPowerSeriesAt with ⟨r, hr⟩
  refine ⟨r, hr, fun i hi => ?_⟩
  apply Finset.sum_eq_zero
  rintro c -
  ext v
  simp only [compAlongComposition_apply, _root_.zero_apply]
  rcases le_or_gt m c.length with hc | hc
  · simp [hg.finite _ hc]
  obtain ⟨j, hj⟩ : exists j, n <= c.blocksFun j := by
    contrapose! hi
    rw [← c.sum_blocksFun]
    rcases eq_zero_or_pos c.length with h'c | h'c
    · have : ∑ j : Fin c.length, c.blocksFun j = 0 := by
        apply Finset.sum_eq_zero (fun j hj => ?_)
        have := j.2
        grind
      rw [this]
      exact mul_pos (by grind) hn
    · calc ∑ j : Fin c.length, c.blocksFun j
      _ < ∑ j : Fin c.length, n := by
        apply Finset.sum_lt_sum (fun j hj => (hi j).le)
        exact ⟨⟨0, h'c⟩, Finset.mem_univ _, hi _⟩
      _ = c.length * n := by simp
      _ <= m * n := by gcongr
  apply ContinuousMultilinearMap.map_coord_zero _ j
  simp [applyComposition, hf.finite _ hj]

/-- If two functions `g` and `f` are continuously polynomial respectively at `f x` and `x`,
then `g ∘ f` is continuously polynomial at `x`. -/
@[to_fun]
/--
theorem `CPolynomialAt.comp` / 定理 `CPolynomialAt.comp`

English:
theorem CPolynomialAt.comp
  statement: {g : F -> G} {f : E -> F} {x : E}
  proof: by
  rcases hg with ⟨q, m, hm⟩
  rcases hf with ⟨p, n, hn⟩
  refine ⟨q.comp p, m * (n + 1), ?_⟩
  exact hm.comp (hn.of_le (Nat.le_succ n)) (Nat.zero_lt_succ n)

中文:
定理 CPolynomialAt.comp
  结论: {g : F -> G} {f : E -> F} {x : E}
  证明: by
  rcases hg with ⟨q, m, hm⟩
  rcases hf with ⟨p, n, hn⟩
  refine ⟨q.comp p, m * (n + 1), ?_⟩
  exact hm.comp (hn.of_le (Nat.le_succ n)) (Nat.zero_lt_succ n)

Depends on / 依赖: Nat.le_succ, Nat.zero_lt_succ, hm.comp, hn.of_le, le_succ, of_le, q.comp, zero_lt_succ
-/
theorem CPolynomialAt.comp {g : F -> G} {f : E -> F} {x : E}
    (hg : CPolynomialAt 𝕜 g (f x)) (hf : CPolynomialAt 𝕜 f x) :
    CPolynomialAt 𝕜 (g ∘ f) x := by
  rcases hg with ⟨q, m, hm⟩
  rcases hf with ⟨p, n, hn⟩
  refine ⟨q.comp p, m * (n + 1), ?_⟩
  exact hm.comp (hn.of_le (Nat.le_succ n)) (Nat.zero_lt_succ n)

/-- Version of `CPolynomialAt.comp` where point equality is a separate hypothesis. -/
@[to_fun]
/--
theorem `CPolynomialAt.comp_of_eq` / 定理 `CPolynomialAt.comp_of_eq`

English:
theorem CPolynomialAt.comp_of_eq
  statement: {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : CPolynomialAt 𝕜 g y)
  proof: by
  rw [← hy] at hg
  exact hg.comp hf

中文:
定理 CPolynomialAt.comp_of_eq
  结论: {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : CPolynomialAt 𝕜 g y)
  证明: by
  rw [← hy] at hg
  exact hg.comp hf

Depends on / 依赖: hg.comp
-/
theorem CPolynomialAt.comp_of_eq {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : CPolynomialAt 𝕜 g y)
    (hf : CPolynomialAt 𝕜 f x) (hy : f x = y) : CPolynomialAt 𝕜 (g ∘ f) x := by
  rw [← hy] at hg
  exact hg.comp hf

/--
theorem `CPolynomialOn.comp'` / 定理 `CPolynomialOn.comp'`

English:
theorem CPolynomialOn.comp'
  statement: {s : Set E} {g : F -> G} {f : E -> F} (hg : CPolynomialOn 𝕜 g (s.image f))
  proof: fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)

中文:
定理 CPolynomialOn.comp'
  结论: {s : Set E} {g : F -> G} {f : E -> F} (hg : CPolynomialOn 𝕜 g (s.image f))
  证明: fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem
-/
theorem CPolynomialOn.comp' {s : Set E} {g : F -> G} {f : E -> F} (hg : CPolynomialOn 𝕜 g (s.image f))
    (hf : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s :=
  fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)

/--
theorem `CPolynomialOn.comp` / 定理 `CPolynomialOn.comp`

English:
theorem CPolynomialOn.comp
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F}
  proof: comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

中文:
定理 CPolynomialOn.comp
  结论: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F}
  证明: comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

Depends on / 依赖: Set.mapsTo_iff_image_subset.mp, mapsTo_iff_image_subset
-/
theorem CPolynomialOn.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F}
    (hg : CPolynomialOn 𝕜 g t) (hf : CPolynomialOn 𝕜 f s) (st : Set.MapsTo f s t) :
    CPolynomialOn 𝕜 (g ∘ f) s :=
  comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

/-!
### Associativity of the composition of formal multilinear series

In this paragraph, we prove the associativity of the composition of formal power series.
By definition,
```
(r.comp q).comp p n v
= ∑_{i₁ + ... + iₖ = n} (r.comp q)ₖ (p_{i₁} (v₀, ..., v_{i₁ -1}), p_{i₂} (...), ..., p_{iₖ}(...))
= ∑_{a : Composition n} (r.comp q) a.length (applyComposition p a v)
```
decomposing `r.comp q` in the same way, we get
```
(r.comp q).comp p n v
= ∑_{a : Composition n} ∑_{b : Composition a.length}
  r b.length (applyComposition q b (applyComposition p a v))
```
On the other hand,
```
r.comp (q.comp p) n v = ∑_{c : Composition n} r c.length (applyComposition (q.comp p) c v)
```
Here, `applyComposition (q.comp p) c v` is a vector of length `c.length`, whose `i`-th term is
given by `(q.comp p) (c.blocksFun i) (v_l, v_{l+1}, ..., v_{m-1})` where `{l, ..., m-1}` is the
`i`-th block in the composition `c`, of length `c.blocksFun i` by definition. To compute this term,
we expand it as `∑_{dᵢ : Composition (c.blocksFun i)} q dᵢ.length (applyComposition p dᵢ v')`,
where `v' = (v_l, v_{l+1}, ..., v_{m-1})`. Therefore, we get
```
r.comp (q.comp p) n v =
∑_{c : Composition n} ∑_{d₀ : Composition (c.blocksFun 0),
  ..., d_{c.length - 1} : Composition (c.blocksFun (c.length - 1))}
  r c.length (fun i ↦ q dᵢ.length (applyComposition p dᵢ v'ᵢ))
```
To show that these terms coincide, we need to explain how to reindex the sums to put them in
bijection (and then the terms we are summing will correspond to each other). Suppose we have a
composition `a` of `n`, and a composition `b` of `a.length`. Then `b` indicates how to group
together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of blocks
can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by saying that
each `dᵢ` is one single block. Conversely, if one starts from `c` and the `dᵢ`s, one can concatenate
the `dᵢ`s to obtain a composition `a` of `n`, and register the lengths of the `dᵢ`s in a composition
`b` of `a.length`.

An example might be enlightening. Suppose `a = [2, 2, 3, 4, 2]`. It is a composition of
length 5 of 13. The content of the blocks may be represented as `0011222333344`.
Now take `b = [2, 3]` as a composition of `a.length = 5`. It says that the first 2 blocks of `a`
should be merged, and the last 3 blocks of `a` should be merged, giving a new composition of `13`
made of two blocks of length `4` and `9`, i.e., `c = [4, 9]`. But one can also remember that
the new first block was initially made of two blocks of size `2`, so `d₀ = [2, 2]`, and the new
second block was initially made of three blocks of size `3`, `4` and `2`, so `d₁ = [3, 4, 2]`.

This equivalence is called `Composition.sigmaEquivSigmaPi n` below.

We start with preliminary results on compositions, of a very specialized nature, then define the
equivalence `Composition.sigmaEquivSigmaPi n`, and we deduce finally the associativity of
composition of formal multilinear series in `FormalMultilinearSeries.comp_assoc`.
-/


namespace Composition

variable {n : Nat}

/--
theorem `sigma_composition_eq_iff` / 定理 `sigma_composition_eq_iff`

English:
theorem sigma_composition_eq_iff
  given: (i j : Σ a : Composition n, Composition a.length)
  proof: by
  refine ⟨by rintro rfl; exact ⟨rfl, rfl⟩, ?_⟩
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rintro ⟨h, h'⟩
  obtain rfl : a = a' := by ext1; exact h
  obtain rfl : b = b' := by ext1; exact h'
  rfl

中文:
定理 sigma_composition_eq_iff
  条件: (i j : Σ a : Composition n, Composition a.length)
  证明: by
  refine ⟨by rintro rfl; exact ⟨rfl, rfl⟩, ?_⟩
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rintro ⟨h, h'⟩
  obtain rfl : a = a' := by ext1; exact h
  obtain rfl : b = b' := by ext1; exact h'
  rfl
-/
theorem sigma_composition_eq_iff (i j : Σ a : Composition n, Composition a.length) :
    i = j ↔ i.1.blocks = j.1.blocks ∧ i.2.blocks = j.2.blocks := by
  refine ⟨by rintro rfl; exact ⟨rfl, rfl⟩, ?_⟩
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rintro ⟨h, h'⟩
  obtain rfl : a = a' := by ext1; exact h
  obtain rfl : b = b' := by ext1; exact h'
  rfl

/--
theorem `sigma_pi_composition_eq_iff` / 定理 `sigma_pi_composition_eq_iff`

English:
theorem sigma_pi_composition_eq_iff
  proof: by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases u with ⟨a, b⟩
  rcases v with ⟨a', b'⟩
  dsimp at H
  obtain rfl : a = a' := by
    ext1
    have :
      map List.sum (ofFn fun i : Fin (Composition.length a) => (b i).blocks) =
        map List.sum (ofFn fun i : Fin (Composition.length a') => 

中文:
定理 sigma_pi_composition_eq_iff
  证明: by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases u with ⟨a, b⟩
  rcases v with ⟨a', b'⟩
  dsimp at H
  obtain rfl : a = a' := by
    ext1
    have :
      map List.sum (ofFn fun i : Fin (Composition.length a) => (b i).blocks) =
        map List.sum (ofFn fun i : Fin (Composition.length a') => 

Depends on / 依赖: Composition, Composition.blocks_sum, Composition.length, List.sum, blocks, blocks.sum, blocks_sum, length, map_ofFn
-/
theorem sigma_pi_composition_eq_iff
    (u v : Σ c : Composition n, forall i : Fin c.length, Composition (c.blocksFun i)) :
    u = v ↔ (ofFn fun i => (u.2 i).blocks) = ofFn fun i => (v.2 i).blocks := by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases u with ⟨a, b⟩
  rcases v with ⟨a', b'⟩
  dsimp at H
  obtain rfl : a = a' := by
    ext1
    have :
      map List.sum (ofFn fun i : Fin (Composition.length a) => (b i).blocks) =
        map List.sum (ofFn fun i : Fin (Composition.length a') => (b' i).blocks) := by
      rw [H]
    simp only [map_ofFn] at this
    change
      (ofFn fun i : Fin (Composition.length a) => (b i).blocks.sum) =
        ofFn fun i : Fin (Composition.length a') => (b' i).blocks.sum at this
    simpa [Composition.blocks_sum, Composition.ofFn_blocksFun] using this
  ext1
  · rfl
  · simp only [heq_eq_eq, ofFn_inj] at H ⊢
    ext1 i
    ext1
    exact congrFun H i

/--
Definition of `gather` / `gather` 的定义

English:
definition gather
  signature: (a : Composition n) (b : Composition a.length)
  body: (a.blocks.splitWrtComposition b).map sum
  blocks_pos := by
    rw [forall_mem_map]
    intro j hj
    suffices H : forall i in j, 1 <= i from calc
      0 < j.length := length_pos_of_mem_splitWrtComposition hj
      _ <= j.sum := length_le_sum_of_one_le _ H
    intro i hi
    apply a.one_le_blocks


中文:
定义 gather
  签名: (a : Composition n) (b : Composition a.length)
  定义体: (a.blocks.splitWrtComposition b).map sum
  blocks_pos := by
    rw [forall_mem_map]
    intro j hj
    suffices H : forall i in j, 1 <= i from calc
      0 < j.length := length_pos_of_mem_splitWrtComposition hj
      _ <= j.sum := length_le_sum_of_one_le _ H
    intro i hi
    apply a.one_le_blocks


Depends on / 依赖: a.blocks.splitWrtComposition, blocks, splitWrtComposition
-/
def gather (a : Composition n) (b : Composition a.length) : Composition n where
  blocks := (a.blocks.splitWrtComposition b).map sum
  blocks_pos := by
    rw [forall_mem_map]
    intro j hj
    suffices H : forall i in j, 1 <= i from calc
      0 < j.length := length_pos_of_mem_splitWrtComposition hj
      _ <= j.sum := length_le_sum_of_one_le _ H
    intro i hi
    apply a.one_le_blocks
    rw [← a.blocks.flatten_splitWrtComposition b]
    exact mem_flatten_of_mem hj hi
  blocks_sum := by rw [← sum_flatten, flatten_splitWrtComposition, a.blocks_sum]

/--
theorem `length_gather` / 定理 `length_gather`

English:
theorem length_gather
  given: (a : Composition n) (b : Composition a.length)
  proof: show (map List.sum (a.blocks.splitWrtComposition b)).length = b.blocks.length by
    rw [length_map]; rw [length_splitWrtComposition]

中文:
定理 length_gather
  条件: (a : Composition n) (b : Composition a.length)
  证明: show (map List.sum (a.blocks.splitWrtComposition b)).length = b.blocks.length by
    rw [length_map]; rw [length_splitWrtComposition]

Depends on / 依赖: List.sum, a.blocks.splitWrtComposition, b.blocks.length, blocks, length, length_map, length_splitWrtComposition, splitWrtComposition
-/
theorem length_gather (a : Composition n) (b : Composition a.length) :
    length (a.gather b) = b.length :=
  show (map List.sum (a.blocks.splitWrtComposition b)).length = b.blocks.length by
    rw [length_map]; rw [length_splitWrtComposition]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sigmaCompositionAux` / `sigmaCompositionAux` 的定义

English:
definition sigmaCompositionAux
  signature: (a : Composition n) (b : Composition a.length)
  body: (a.blocks.splitWrtComposition b)[i.val]'(by
      rw [length_splitWrtComposition]; rw [← length_gather]; exact i.2)
  blocks_pos {i} hi :=
    a.blocks_pos
      (by
        rw [← a.blocks.flatten_splitWrtComposition b]
        exact mem_flatten_of_mem (List.getElem_mem _) hi)
  blocks_sum := by sim

中文:
定义 sigmaCompositionAux
  签名: (a : Composition n) (b : Composition a.length)
  定义体: (a.blocks.splitWrtComposition b)[i.val]'(by
      rw [length_splitWrtComposition]; rw [← length_gather]; exact i.2)
  blocks_pos {i} hi :=
    a.blocks_pos
      (by
        rw [← a.blocks.flatten_splitWrtComposition b]
        exact mem_flatten_of_mem (List.getElem_mem _) hi)
  blocks_sum := by sim

Depends on / 依赖: Composition, Composition.blocksFun, Composition.gather, List.getElem_mem, a.blocks.flatten_splitWrtComposition, a.blocks.splitWrtComposition, a.blocks_pos, blocks, blocksFun, blocks_pos, blocks_sum, flatten_splitWrtComposition, gather, getElem_map, getElem_mem, i.val, length_gather, length_splitWrtComposition, mem_flatten_of_mem, splitWrtComposition
-/
def sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin (a.gather b).length) : Composition ((a.gather b).blocksFun i) where
  blocks :=
    (a.blocks.splitWrtComposition b)[i.val]'(by
      rw [length_splitWrtComposition]; rw [← length_gather]; exact i.2)
  blocks_pos {i} hi :=
    a.blocks_pos
      (by
        rw [← a.blocks.flatten_splitWrtComposition b]
        exact mem_flatten_of_mem (List.getElem_mem _) hi)
  blocks_sum := by simp [Composition.blocksFun, getElem_map, Composition.gather]

/--
theorem `length_sigmaCompositionAux` / 定理 `length_sigmaCompositionAux`

English:
theorem length_sigmaCompositionAux
  statement: (a : Composition n) (b : Composition a.length)
  proof: show List.length ((splitWrtComposition a.blocks b)[i.1]) = blocksFun b i by
    rw [getElem_map_rev List.length]; rw [getElem_of_eq (map_length_splitWrtComposition _ _)]; rw [blocksFun]; rw [get_eq_getElem]

中文:
定理 length_sigmaCompositionAux
  结论: (a : Composition n) (b : Composition a.length)
  证明: show List.length ((splitWrtComposition a.blocks b)[i.1]) = blocksFun b i by
    rw [getElem_map_rev List.length]; rw [getElem_of_eq (map_length_splitWrtComposition _ _)]; rw [blocksFun]; rw [get_eq_getElem]

Depends on / 依赖: List.length, a.blocks, blocks, blocksFun, getElem_map_rev, getElem_of_eq, get_eq_getElem, length, map_length_splitWrtComposition, splitWrtComposition
-/
theorem length_sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin b.length) :
    Composition.length (Composition.sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩) =
      Composition.blocksFun b i :=
  show List.length ((splitWrtComposition a.blocks b)[i.1]) = blocksFun b i by
    rw [getElem_map_rev List.length]; rw [getElem_of_eq (map_length_splitWrtComposition _ _)]; rw [blocksFun]; rw [get_eq_getElem]

/--
theorem `blocksFun_sigmaCompositionAux` / 定理 `blocksFun_sigmaCompositionAux`

English:
theorem blocksFun_sigmaCompositionAux
  statement: (a : Composition n) (b : Composition a.length)
  proof: by
  unfold sigmaCompositionAux
  rw [blocksFun]; rw [get_eq_getElem]; rw [getElem_of_eq (getElem_splitWrtComposition _ _ _ _)]; rw [getElem_drop]; rw [getElem_take]; rfl

中文:
定理 blocksFun_sigmaCompositionAux
  结论: (a : Composition n) (b : Composition a.length)
  证明: by
  unfold sigmaCompositionAux
  rw [blocksFun]; rw [get_eq_getElem]; rw [getElem_of_eq (getElem_splitWrtComposition _ _ _ _)]; rw [getElem_drop]; rw [getElem_take]; rfl

Depends on / 依赖: blocksFun, getElem_drop, getElem_of_eq, getElem_splitWrtComposition, getElem_take, get_eq_getElem, sigmaCompositionAux
-/
theorem blocksFun_sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin b.length) (j : Fin (blocksFun b i)) :
    blocksFun (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩)
        ⟨j, (length_sigmaCompositionAux a b i).symm ▸ j.2⟩ =
      blocksFun a (embedding b i j) := by
  unfold sigmaCompositionAux
  rw [blocksFun]; rw [get_eq_getElem]; rw [getElem_of_eq (getElem_splitWrtComposition _ _ _ _)]; rw [getElem_drop]; rw [getElem_take]; rfl

/--
theorem `sizeUpTo_sizeUpTo_add` / 定理 `sizeUpTo_sizeUpTo_add`

English:
theorem sizeUpTo_sizeUpTo_add
  statement: (a : Composition n) (b : Composition a.length) {i j : Nat}
  proof: by
  induction j with
  | zero =>
    change
      sum (take (b.blocks.take i).sum a.blocks) =
        sum (take i (map sum (splitWrtComposition a.blocks b)))
    induction i with
    | zero => rfl
    | succ i IH =>
      have A : i < b.length := Nat.lt_of_succ_lt hi
      have B : i < List.length 

中文:
定理 sizeUpTo_sizeUpTo_add
  结论: (a : Composition n) (b : Composition a.length) {i j : 自然数}
  证明: by
  induction j with
  | zero =>
    change
      sum (take (b.blocks.take i).sum a.blocks) =
        sum (take i (map sum (splitWrtComposition a.blocks b)))
    induction i with
    | zero => rfl
    | succ i IH =>
      have A : i < b.length := Nat.lt_of_succ_lt hi
      have B : i < List.length 

Depends on / 依赖: Composition, Composition.blocks_pos, List.length, List.sum, Nat.lt_of_succ_lt, a.blocks, b.blocks, b.blocks.take, b.length, blocks, blocksFun, blocks_pos, length, lt_of_succ_lt, splitWrtComposition, sum_take_succ
-/
theorem sizeUpTo_sizeUpTo_add (a : Composition n) (b : Composition a.length) {i j : Nat}
    (hi : i < b.length) (hj : j < blocksFun b ⟨i, hi⟩) :
    sizeUpTo a (sizeUpTo b i + j) =
      sizeUpTo (a.gather b) i +
        sizeUpTo (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ hi⟩) j := by
  induction j with
  | zero =>
    change
      sum (take (b.blocks.take i).sum a.blocks) =
        sum (take i (map sum (splitWrtComposition a.blocks b)))
    induction i with
    | zero => rfl
    | succ i IH =>
      have A : i < b.length := Nat.lt_of_succ_lt hi
      have B : i < List.length (map List.sum (splitWrtComposition a.blocks b)) := by simp [A]
      have C : 0 < blocksFun b ⟨i, A⟩ := Composition.blocks_pos' _ _ _
      rw [sum_take_succ _ _ B]; rw [← IH A C]
      have :
        take (sum (take i b.blocks)) a.blocks =
          take (sum (take i b.blocks)) (take (sum (take (i + 1) b.blocks)) a.blocks) := by
        rw [take_take]; rw [min_eq_left]
        apply monotone_sum_take _ (Nat.le_succ _)
      rw [this]; rw [getElem_map]; rw [getElem_splitWrtComposition]; rw [←
        take_append_drop (sum (take i b.blocks)) (take (sum (take (Nat.succ i) b.blocks)) a.blocks)]; rw [sum_append]
      congr
      rw [take_append_drop]
  | succ j IHj =>
    have A : j < blocksFun b ⟨i, hi⟩ := lt_trans (lt_add_one j) hj
    have B : j < length (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ hi⟩) := by
      convert! A; rw [← length_sigmaCompositionAux]
    have C : sizeUpTo b i + j < sizeUpTo b (i + 1) := by
      simp only [sizeUpTo_succ b hi, add_lt_add_iff_left]
      exact A
    have D : sizeUpTo b i + j < length a := lt_of_lt_of_le C (b.sizeUpTo_le _)
    have : sizeUpTo b i + Nat.succ j = (sizeUpTo b i + j).succ := rfl
    rw [this]; rw [sizeUpTo_succ _ D]; rw [IHj A]; rw [sizeUpTo_succ _ B]
    simp only [sigmaCompositionAux, add_assoc]
    rw [getElem_of_eq (getElem_splitWrtComposition _ _ _ _)]; rw [getElem_drop]; rw [getElem_take]

/--
Definition of `sigmaEquivSigmaPi` / `sigmaEquivSigmaPi` 的定义

English:
definition sigmaEquivSigmaPi
  signature: (n : Nat)
  body: ⟨i.1.gather i.2, i.1.sigmaCompositionAux i.2⟩
  invFun i :=
    ⟨{ blocks := (ofFn fun j => (i.2 j).blocks).flatten
        blocks_pos := by
          simp only [and_imp, List.mem_flatten, exists_imp, forall_mem_ofFn_iff]
          exact fun {i} j hj => Composition.blocks_pos _ hj
        blocks_sum

中文:
定义 sigmaEquivSigmaPi
  签名: (n : 自然数)
  定义体: ⟨i.1.gather i.2, i.1.sigmaCompositionAux i.2⟩
  invFun i :=
    ⟨{ blocks := (ofFn fun j => (i.2 j).blocks).flatten
        blocks_pos := by
          simp only [and_imp, List.mem_flatten, exists_imp, forall_mem_ofFn_iff]
          exact fun {i} j hj => Composition.blocks_pos _ hj
        blocks_sum

Depends on / 依赖: gather, sigmaCompositionAux
-/
def sigmaEquivSigmaPi (n : Nat) :
    (Σ a : Composition n, Composition a.length) ≃
      Σ c : Composition n, forall i : Fin c.length, Composition (c.blocksFun i) where
  toFun i := ⟨i.1.gather i.2, i.1.sigmaCompositionAux i.2⟩
  invFun i :=
    ⟨{ blocks := (ofFn fun j => (i.2 j).blocks).flatten
        blocks_pos := by
          simp only [and_imp, List.mem_flatten, exists_imp, forall_mem_ofFn_iff]
          exact fun {i} j hj => Composition.blocks_pos _ hj
        blocks_sum := by simp [sum_ofFn, Composition.blocks_sum, Composition.sum_blocksFun] },
      { blocks := ofFn fun j => (i.2 j).length
        blocks_pos := by
          intro k hk
          refine ((forall_mem_ofFn_iff (P := fun i => 0 < i)).2 fun j => ?_) k hk
          exact Composition.length_pos_of_pos _ (Composition.blocks_pos' _ _ _)
        blocks_sum := by dsimp only [Composition.length]; simp [sum_ofFn] }⟩
  left_inv := by
    -- the fact that we have a left inverse is essentially `join_splitWrtComposition`,
    -- but we need to massage it to take care of the dependent setting.
    rintro ⟨a, b⟩
    rw [sigma_composition_eq_iff]
    dsimp
    constructor
    · conv_rhs =>
        rw [← flatten_splitWrtComposition a.blocks b]; rw [← ofFn_get (splitWrtComposition a.blocks b)]
      have A : length (gather a b) = List.length (splitWrtComposition a.blocks b) := by
        simp only [length, gather, length_map, length_splitWrtComposition]
      congr! 2
      exact (Fin.heq_fun_iff A (α := List Nat)).2 fun i => rfl
    · have B : Composition.length (Composition.gather a b) = List.length b.blocks :=
        Composition.length_gather _ _
      conv_rhs => rw [← ofFn_getElem (xs := b.blocks)]
      congr 1
      refine (Fin.heq_fun_iff B).2 fun i => ?_
      rw [sigmaCompositionAux]; rw [Composition.length]; rw [List.getElem_map_rev List.length]; rw [List.getElem_of_eq (map_length_splitWrtComposition _ _)]
  right_inv := by
    -- the fact that we have a right inverse is essentially `splitWrtComposition_join`,
    -- but we need to massage it to take care of the dependent setting.
    rintro ⟨c, d⟩
    have : map List.sum (ofFn fun i : Fin (Composition.length c) => (d i).blocks) = c.blocks := by
      simp [map_ofFn, Function.comp_def, Composition.blocks_sum, Composition.ofFn_blocksFun]
    rw [sigma_pi_composition_eq_iff]
    dsimp
    congr! 1
    · congr
      ext1
      dsimp [Composition.gather]
      rwa [splitWrtComposition_flatten]
      simp only [map_ofFn, Function.comp_def]
    · rw [Fin.heq_fun_iff]
      · intro i
        dsimp [Composition.sigmaCompositionAux]
        rw [getElem_of_eq (splitWrtComposition_flatten _ _ _)]
        · simp only [List.getElem_ofFn]
        · simp only [map_ofFn, Function.comp_def]
      · congr

end Composition

namespace FormalMultilinearSeries

open Composition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: (r : FormalMultilinearSeries 𝕜 G H) (q : FormalMultilinearSeries 𝕜 F G)
  proof: by
  ext n v
  /- First, rewrite the two compositions appearing in the theorem as two sums over complicated
    sigma types, as in the description of the proof above. -/
  let f : (Σ a : Composition n, Composition a.length) -> H := fun c =>
    r c.2.length (applyComposition q c.2 (applyComposition 

中文:
定理 comp_assoc
  结论: (r : FormalMultilinearSeries 𝕜 G H) (q : FormalMultilinearSeries 𝕜 F G)
  证明: by
  ext n v
  /- First, rewrite the two compositions appearing in the theorem as two sums over complicated
    sigma types, as in the description of the proof above. -/
  let f : (Σ a : Composition n, Composition a.length) -> H := fun c =>
    r c.2.length (applyComposition q c.2 (applyComposition 
-/
theorem comp_assoc (r : FormalMultilinearSeries 𝕜 G H) (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) : (r.comp q).comp p = r.comp (q.comp p) := by
  ext n v
  /- First, rewrite the two compositions appearing in the theorem as two sums over complicated
    sigma types, as in the description of the proof above. -/
  let f : (Σ a : Composition n, Composition a.length) -> H := fun c =>
    r c.2.length (applyComposition q c.2 (applyComposition p c.1 v))
  let g : (Σ c : Composition n, forall i : Fin c.length, Composition (c.blocksFun i)) -> H := fun c =>
    r c.1.length fun i : Fin c.1.length =>
      q (c.2 i).length (applyComposition p (c.2 i) (v ∘ c.1.embedding i))
  suffices ∑ c, f c = ∑ c, g c by
    simpa +unfoldPartialApp only [FormalMultilinearSeries.comp, sum_apply,
      compAlongComposition_apply, Finset.sum_sigma', applyComposition,
      ContinuousMultilinearMap.map_sum]
  /- Now, we use `Composition.sigmaEquivSigmaPi n` to change
    variables in the second sum, and check that we get exactly the same sums. -/
  rw [← (sigmaEquivSigmaPi n).sum_comp]
  /- To check that we have the same terms, we should check that we apply the same component of
    `r`, and the same component of `q`, and the same component of `p`, to the same coordinate of
    `v`. This is true by definition, but at each step one needs to convince Lean that the types
    one considers are the same, using a suitable congruence lemma to avoid dependent type issues.
    This dance has to be done three times, one for `r`, one for `q` and one for `p`. -/
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ _
  dsimp [sigmaEquivSigmaPi]
  -- check that the `r` components are the same. Based on `Composition.length_gather`
  apply r.congr (Composition.length_gather a b).symm
  intro i hi1 hi2
  -- check that the `q` components are the same. Based on `length_sigmaCompositionAux`
  apply q.congr (length_sigmaCompositionAux a b _).symm
  intro j hj1 hj2
  -- check that the `p` components are the same. Based on `blocksFun_sigmaCompositionAux`
  apply p.congr (blocksFun_sigmaCompositionAux a b _ _).symm
  intro k hk1 hk2
  -- finally, check that the coordinates of `v` one is using are the same. Based on
  -- `sizeUpTo_sizeUpTo_add`.
  refine congr_arg v (Fin.ext ?_)
  dsimp [Composition.embedding]
  rw [← add_assoc]; rw [← sizeUpTo_sizeUpTo_add _ _ hi1 hj1]

end FormalMultilinearSeries
