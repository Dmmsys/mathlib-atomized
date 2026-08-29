/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Basic

/-!
# Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `Fin n` of cardinality `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this file, we implement this. The new power series is called `p.changeOrigin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open. All these arguments
require the target space to be complete, as otherwise the series might not converge.

### Main results

In a complete space, if a function admits a power series in a ball, then it is analytic at any
point `y` of this ball, and the power series there can be expressed in terms of the initial power
series `p` as `p.changeOrigin y`. See `HasFPowerSeriesOnBall.changeOrigin`. It follows in particular
that the set of points at which a given function is analytic is open, see `isOpen_analyticAt`.
-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal Topology
open Filter Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

section

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r : Real>=0}

/--
Definition of `changeOriginSeriesTerm` / `changeOriginSeriesTerm` 的定义

English:
definition changeOriginSeriesTerm
  signature: (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l)
  body: let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  a (p (k + l))

中文:
定义 changeOriginSeriesTerm
  签名: (k l : 自然数) (s : Finset (Fin (k + l))) (hs : s.card = l)
  定义体: let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  a (p (k + l))

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryFinFinset, Finset, Finset.card_compl, Fintype, Fintype.card_fin, add_tsub_cancel_right, card_compl, card_fin, curryFinFinset
-/
def changeOriginSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    E [×l]->L[𝕜] E [×k]->L[𝕜] F :=
  let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  a (p (k + l))

/--
theorem `changeOriginSeriesTerm_apply` / 定理 `changeOriginSeriesTerm_apply`

English:
theorem changeOriginSeriesTerm_apply
  statement: (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l)
  proof: ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _

@[simp]

中文:
定理 changeOriginSeriesTerm_apply
  结论: (k l : 自然数) (s : Finset (Fin (k + l))) (hs : s.card = l)
  证明: ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryFinFinset_apply_const, curryFinFinset_apply_const
-/
theorem changeOriginSeriesTerm_apply (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l)
    (x y : E) :
    (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y) =
      p (k + l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _

@[simp]
/--
theorem `norm_changeOriginSeriesTerm` / 定理 `norm_changeOriginSeriesTerm`

English:
theorem norm_changeOriginSeriesTerm
  given: (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l)
  proof: by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.norm_map]

@[simp]

中文:
定理 norm_changeOriginSeriesTerm
  条件: (k l : 自然数) (s : Finset (Fin (k + l))) (hs : s.card = l)
  证明: by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, changeOriginSeriesTerm, norm_map
-/
theorem norm_changeOriginSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖ = ‖p (k + l)‖ := by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `nnnorm_changeOriginSeriesTerm` / 定理 `nnnorm_changeOriginSeriesTerm`

English:
theorem nnnorm_changeOriginSeriesTerm
  given: (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l)
  proof: by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.nnnorm_map]

中文:
定理 nnnorm_changeOriginSeriesTerm
  条件: (k l : 自然数) (s : Finset (Fin (k + l))) (hs : s.card = l)
  证明: by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.nnnorm_map]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.nnnorm_map, changeOriginSeriesTerm, nnnorm_map
-/
theorem nnnorm_changeOriginSeriesTerm (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊ := by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.nnnorm_map]

/--
theorem `nnnorm_changeOriginSeriesTerm_apply_le` / 定理 `nnnorm_changeOriginSeriesTerm_apply_le`

English:
theorem nnnorm_changeOriginSeriesTerm_apply_le
  statement: (k l : Nat) (s : Finset (Fin (k + l)))
  proof: by
  rw [← p.nnnorm_changeOriginSeriesTerm k l s hs]; rw [← Fin.prod_const]; rw [← Fin.prod_const]
  apply ContinuousMultilinearMap.le_of_opNNNorm_le
  apply ContinuousMultilinearMap.le_opNNNorm

中文:
定理 nnnorm_changeOriginSeriesTerm_apply_le
  结论: (k l : 自然数) (s : Finset (Fin (k + l)))
  证明: by
  rw [← p.nnnorm_changeOriginSeriesTerm k l s hs]; rw [← Fin.prod_const]; rw [← Fin.prod_const]
  apply ContinuousMultilinearMap.le_of_opNNNorm_le
  apply ContinuousMultilinearMap.le_opNNNorm

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.le_of_opNNNorm_le, ContinuousMultilinearMap.le_opNNNorm, Fin.prod_const, le_of_opNNNorm_le, le_opNNNorm, nnnorm_changeOriginSeriesTerm, p.nnnorm_changeOriginSeriesTerm, prod_const
-/
theorem nnnorm_changeOriginSeriesTerm_apply_le (k l : Nat) (s : Finset (Fin (k + l)))
    (hs : s.card = l) (x y : E) :
    ‖p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y‖₊ <=
      ‖p (k + l)‖₊ * ‖x‖₊ ^ l * ‖y‖₊ ^ k := by
  rw [← p.nnnorm_changeOriginSeriesTerm k l s hs]; rw [← Fin.prod_const]; rw [← Fin.prod_const]
  apply ContinuousMultilinearMap.le_of_opNNNorm_le
  apply ContinuousMultilinearMap.le_opNNNorm

/--
Definition of `changeOriginSeries` / `changeOriginSeries` 的定义

English:
definition changeOriginSeries
  signature: (k : Nat)
  body: fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2

中文:
定义 changeOriginSeries
  签名: (k : 自然数)
  定义体: fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2
-/
def changeOriginSeries (k : Nat) : FormalMultilinearSeries 𝕜 E (E [×k]->L[𝕜] F) := fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2

/--
theorem `nnnorm_changeOriginSeries_le_tsum` / 定理 `nnnorm_changeOriginSeries_le_tsum`

English:
theorem nnnorm_changeOriginSeries_le_tsum
  given: (k l : Nat)
  proof: (nnnorm_sum_le _ (fun t => changeOriginSeriesTerm p k l (Subtype.val t) t.prop)).trans_eq by
    simp_rw [tsum_fintype, nnnorm_changeOriginSeriesTerm (p := p) (k := k) (l := l)]

中文:
定理 nnnorm_changeOriginSeries_le_tsum
  条件: (k l : 自然数)
  证明: (nnnorm_sum_le _ (fun t => changeOriginSeriesTerm p k l (Subtype.val t) t.prop)).trans_eq by
    simp_rw [tsum_fintype, nnnorm_changeOriginSeriesTerm (p := p) (k := k) (l := l)]

Depends on / 依赖: Subtype, Subtype.val, changeOriginSeriesTerm, nnnorm_changeOriginSeriesTerm, nnnorm_sum_le, simp_rw, t.prop, trans_eq, tsum_fintype
-/
theorem nnnorm_changeOriginSeries_le_tsum (k l : Nat) :
    ‖p.changeOriginSeries k l‖₊ <=
      ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ :=
(nnnorm_sum_le _ (fun t => changeOriginSeriesTerm p k l (Subtype.val t) t.prop)).trans_eq by
    simp_rw [tsum_fintype, nnnorm_changeOriginSeriesTerm (p := p) (k := k) (l := l)]

/--
theorem `nnnorm_changeOriginSeries_apply_le_tsum` / 定理 `nnnorm_changeOriginSeries_apply_le_tsum`

English:
theorem nnnorm_changeOriginSeries_apply_le_tsum
  given: (k l : Nat) (x : E)
  proof: by
  rw [NNReal.tsum_mul_right]; rw [← Fin.prod_const]
  exact (p.changeOriginSeries k l).le_of_opNNNorm_le (p.nnnorm_changeOriginSeries_le_tsum _ _) _

中文:
定理 nnnorm_changeOriginSeries_apply_le_tsum
  条件: (k l : 自然数) (x : E)
  证明: by
  rw [NNReal.tsum_mul_right]; rw [← Fin.prod_const]
  exact (p.changeOriginSeries k l).le_of_opNNNorm_le (p.nnnorm_changeOriginSeries_le_tsum _ _) _

Depends on / 依赖: Fin.prod_const, NNReal, NNReal.tsum_mul_right, changeOriginSeries, le_of_opNNNorm_le, nnnorm_changeOriginSeries_le_tsum, p.changeOriginSeries, p.nnnorm_changeOriginSeries_le_tsum, prod_const, tsum_mul_right
-/
theorem nnnorm_changeOriginSeries_apply_le_tsum (k l : Nat) (x : E) :
    ‖p.changeOriginSeries k l fun _ => x‖₊ <=
      ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ * ‖x‖₊ ^ l := by
  rw [NNReal.tsum_mul_right]; rw [← Fin.prod_const]
  exact (p.changeOriginSeries k l).le_of_opNNNorm_le (p.nnnorm_changeOriginSeries_le_tsum _ _) _

/--
Definition of `changeOrigin` / `changeOrigin` 的定义

English:
definition changeOrigin
  signature: (x : E)
  body: fun k => (p.changeOriginSeries k).sum x

中文:
定义 changeOrigin
  签名: (x : E)
  定义体: fun k => (p.changeOriginSeries k).sum x

Depends on / 依赖: changeOriginSeries, p.changeOriginSeries
-/
def changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun k => (p.changeOriginSeries k).sum x

/-- An auxiliary equivalence useful in the proofs about
`FormalMultilinearSeries.changeOriginSeries`: the set of triples `(k, l, s)`, where `s` is a
`Finset (Fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`Finset (Fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - Finset.card s, Finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps]
/--
Definition of `changeOriginIndexEquiv` / `changeOriginIndexEquiv` 的定义

English:
definition changeOriginIndexEquiv
  signature: :
  body: ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
        (finCongr <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subt

中文:
定义 changeOriginIndexEquiv
  签名: :
  定义体: ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
        (finCongr <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subt
-/
def changeOriginIndexEquiv :
    (Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l }) ≃ Σ n : Nat, Finset (Fin n) where
  toFun s := ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
        (finCongr <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subtype.coe_mk]
    -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
    -- formulate the generalized goal
    suffices forall k' l', k' = k -> l' = l -> forall (hkl : k + l = k' + l') (hs'),
        (⟨k', l', ⟨s.map (finCongr hkl).toEmbedding, hs'⟩⟩ :
          Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l }) = ⟨k, l, ⟨s, hs⟩⟩ by
      apply this <;> simp only [hs, add_tsub_cancel_right]
    simp
  right_inv := by
    rintro ⟨n, s⟩
    simp [tsub_add_cancel_of_le (card_finset_fin_le s), finCongr_eq_equivCast]

/--
lemma `changeOriginSeriesTerm_changeOriginIndexEquiv_symm` / 引理 `changeOriginSeriesTerm_changeOriginIndexEquiv_symm`

English:
lemma changeOriginSeriesTerm_changeOriginIndexEquiv_symm
  given: (n t)
  proof: changeOriginIndexEquiv.symm ⟨n, t⟩
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) (fun _ => y) =
    p n (t.piecewise (fun _ => x) fun _ => y) := by
  have : forall (m) (hm : n = m), p n (t.piecewise (fun _ => x) fun _ => y) =
      p m ((t.map (finCongr hm).toEmbedding).piecewise

中文:
引理 changeOriginSeriesTerm_changeOriginIndexEquiv_symm
  条件: (n t)
  证明: changeOriginIndexEquiv.symm ⟨n, t⟩
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) (fun _ => y) =
    p n (t.piecewise (fun _ => x) fun _ => y) := by
  have : forall (m) (hm : n = m), p n (t.piecewise (fun _ => x) fun _ => y) =
      p m ((t.map (finCongr hm).toEmbedding).piecewise

Depends on / 依赖: changeOriginIndexEquiv, changeOriginIndexEquiv.symm
-/
lemma changeOriginSeriesTerm_changeOriginIndexEquiv_symm (n t) :
    let s := changeOriginIndexEquiv.symm ⟨n, t⟩
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) (fun _ => y) =
    p n (t.piecewise (fun _ => x) fun _ => y) := by
  have : forall (m) (hm : n = m), p n (t.piecewise (fun _ => x) fun _ => y) =
      p m ((t.map (finCongr hm).toEmbedding).piecewise (fun _ => x) fun _ => y) := by
    rintro m rfl
    simp +unfoldPartialApp [Finset.piecewise]
  simp_rw [changeOriginSeriesTerm_apply, eq_comm]; apply this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `changeOriginSeries_summable_aux₁` / 定理 `changeOriginSeries_summable_aux₁`

English:
theorem changeOriginSeries_summable_aux₁
  given: {r r' : Real>=0} (hr : (r + r' : Real>=0∞) < p.radius)
  proof: by
  rw [← changeOriginIndexEquiv.symm.summable_iff]
  dsimp only [Function.comp_def, changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst]
  have : forall n : Nat,
      HasSum (fun s : Finset (Fin n) => ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
  

中文:
定理 changeOriginSeries_summable_aux₁
  条件: {r r' : 实数>=0} (hr : (r + r' : 实数>=0∞) < p.radius)
  证明: by
  rw [← changeOriginIndexEquiv.symm.summable_iff]
  dsimp only [Function.comp_def, changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst]
  have : forall n : Nat,
      HasSum (fun s : Finset (Fin n) => ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
  

Depends on / 依赖: Finset, Function, Function.comp_def, HasSum, changeOriginIndexEquiv, changeOriginIndexEquiv.symm.summable_iff, changeOriginIndexEquiv_symm_apply_fst, changeOriginIndexEquiv_symm_apply_snd_fst, comp_def, s.card, summable_iff
-/
theorem changeOriginSeries_summable_aux₁ {r r' : Real>=0} (hr : (r + r' : Real>=0∞) < p.radius) :
    Summable fun s : Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (s.1 + s.2.1)‖₊ * r ^ s.2.1 * r' ^ s.1 := by
  rw [← changeOriginIndexEquiv.symm.summable_iff]
  dsimp only [Function.comp_def, changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst]
  have : forall n : Nat,
      HasSum (fun s : Finset (Fin n) => ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
        (‖p n‖₊ * (r + r') ^ n) := by
    intro n
    -- TODO: why `simp only [tsub_add_cancel_of_le (card_finset_fin_le _)]` fails?
    convert_to HasSum (fun s : Finset (Fin n) => ‖p n‖₊ * (r ^ s.card * r' ^ (n - s.card))) _
    · ext1 s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _)]; rw [mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  refine NNReal.summable_sigma.2 ⟨fun n => (this n).summable, ?_⟩
  simp only [(this _).tsum_eq]
  exact p.summable_nnnorm_mul_pow hr

/--
theorem `changeOriginSeries_summable_aux₂` / 定理 `changeOriginSeries_summable_aux₂`

English:
theorem changeOriginSeries_summable_aux₂
  given: (hr : (r : Real>=0∞) < p.radius) (k : Nat)
  proof: by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹

中文:
定理 changeOriginSeries_summable_aux₂
  条件: (hr : (r : 实数>=0∞) < p.radius) (k : 自然数)
  证明: by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_add_pos_lt, NNReal, NNReal.summable_sigma, lt_iff_exists_add_pos_lt, mul_right, p.changeOriginSeries_summable_aux, pow_pos, summable_sigma
-/
theorem changeOriginSeries_summable_aux₂ (hr : (r : Real>=0∞) < p.radius) (k : Nat) :
    Summable fun s : Σ l : Nat, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (k + s.1)‖₊ * r ^ s.1 := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹

/--
theorem `changeOriginSeries_summable_aux₃` / 定理 `changeOriginSeries_summable_aux₃`

English:
theorem changeOriginSeries_summable_aux₃
  given: {r : Real>=0} (hr : ↑r < p.radius) (k : Nat)
  proof: by
  refine NNReal.summable_of_le
    (fun n => ?_) (NNReal.summable_sigma.1 <| p.changeOriginSeries_summable_aux₂ hr k).2
  simp only [NNReal.tsum_mul_right]
  gcongr
  apply p.nnnorm_changeOriginSeries_le_tsum

中文:
定理 changeOriginSeries_summable_aux₃
  条件: {r : 实数>=0} (hr : ↑r < p.radius) (k : 自然数)
  证明: by
  refine NNReal.summable_of_le
    (fun n => ?_) (NNReal.summable_sigma.1 <| p.changeOriginSeries_summable_aux₂ hr k).2
  simp only [NNReal.tsum_mul_right]
  gcongr
  apply p.nnnorm_changeOriginSeries_le_tsum

Depends on / 依赖: NNReal, NNReal.summable_of_le, NNReal.summable_sigma, NNReal.tsum_mul_right, nnnorm_changeOriginSeries_le_tsum, p.changeOriginSeries_summable_aux, p.nnnorm_changeOriginSeries_le_tsum, summable_of_le, summable_sigma, tsum_mul_right
-/
theorem changeOriginSeries_summable_aux₃ {r : Real>=0} (hr : ↑r < p.radius) (k : Nat) :
    Summable fun l : Nat => ‖p.changeOriginSeries k l‖₊ * r ^ l := by
  refine NNReal.summable_of_le
    (fun n => ?_) (NNReal.summable_sigma.1 <| p.changeOriginSeries_summable_aux₂ hr k).2
  simp only [NNReal.tsum_mul_right]
  gcongr
  apply p.nnnorm_changeOriginSeries_le_tsum

/--
theorem `le_changeOriginSeries_radius` / 定理 `le_changeOriginSeries_radius`

English:
theorem le_changeOriginSeries_radius
  given: (k : Nat)
  statement: p.radius <= (p.changeOriginSeries k).radius
  proof: ENNReal.le_of_forall_nnreal_lt fun _r hr =>
    le_radius_of_summable_nnnorm _ (p.changeOriginSeries_summable_aux₃ hr k)

中文:
定理 le_changeOriginSeries_radius
  条件: (k : 自然数)
  结论: p.radius <= (p.changeOriginSeries k).radius
  证明: ENNReal.le_of_forall_nnreal_lt fun _r hr =>
    le_radius_of_summable_nnnorm _ (p.changeOriginSeries_summable_aux₃ hr k)

Depends on / 依赖: ENNReal, ENNReal.le_of_forall_nnreal_lt, le_of_forall_nnreal_lt, le_radius_of_summable_nnnorm, p.changeOriginSeries_summable_aux
-/
theorem le_changeOriginSeries_radius (k : Nat) : p.radius <= (p.changeOriginSeries k).radius :=
  ENNReal.le_of_forall_nnreal_lt fun _r hr =>
    le_radius_of_summable_nnnorm _ (p.changeOriginSeries_summable_aux₃ hr k)

/--
theorem `nnnorm_changeOrigin_le` / 定理 `nnnorm_changeOrigin_le`

English:
theorem nnnorm_changeOrigin_le
  given: (k : Nat) (h : (‖x‖₊ : Real>=0∞) < p.radius)
  proof: by
  refine tsum_of_nnnorm_bounded ?_ fun l => p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  have := p.changeOriginSeries_summable_aux₂ h k
  refine HasSum.sigma this.hasSum fun l => ?_
  exact ((NNReal.summable_sigma.1 this).1 l).hasSum

中文:
定理 nnnorm_changeOrigin_le
  条件: (k : 自然数) (h : (‖x‖₊ : 实数>=0∞) < p.radius)
  证明: by
  refine tsum_of_nnnorm_bounded ?_ fun l => p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  have := p.changeOriginSeries_summable_aux₂ h k
  refine HasSum.sigma this.hasSum fun l => ?_
  exact ((NNReal.summable_sigma.1 this).1 l).hasSum

Depends on / 依赖: HasSum, HasSum.sigma, NNReal, NNReal.summable_sigma, hasSum, nnnorm_changeOriginSeries_apply_le_tsum, p.changeOriginSeries_summable_aux, p.nnnorm_changeOriginSeries_apply_le_tsum, summable_sigma, this.hasSum, tsum_of_nnnorm_bounded
-/
theorem nnnorm_changeOrigin_le (k : Nat) (h : (‖x‖₊ : Real>=0∞) < p.radius) :
    ‖p.changeOrigin x k‖₊ <=
      ∑' s : Σ l : Nat, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1 := by
  refine tsum_of_nnnorm_bounded ?_ fun l => p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  have := p.changeOriginSeries_summable_aux₂ h k
  refine HasSum.sigma this.hasSum fun l => ?_
  exact ((NNReal.summable_sigma.1 this).1 l).hasSum

/--
theorem `changeOrigin_radius` / 定理 `changeOrigin_radius`

English:
theorem changeOrigin_radius
  statement: p.radius - ‖x‖₊ <= (p.changeOrigin x).radius
  proof: by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _h0 hr => ?_
  rw [lt_tsub_iff_right]; rw [add_comm] at hr
  have hr' : (‖x‖₊ : Real>=0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have (k : Nat) :
      ‖p.changeOrigin x k‖₊ * r ^ k <=
        (∑' s 

中文:
定理 changeOrigin_radius
  结论: p.radius - ‖x‖₊ <= (p.changeOrigin x).radius
  证明: by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _h0 hr => ?_
  rw [lt_tsub_iff_right]; rw [add_comm] at hr
  have hr' : (‖x‖₊ : Real>=0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have (k : Nat) :
      ‖p.changeOrigin x k‖₊ * r ^ k <=
        (∑' s 

Depends on / 依赖: ENNReal, ENNReal.le_of_forall_pos_nnreal_lt, Finset, NNReal, NNReal.summable_of_le, NNReal.tsum_mul_right, add_comm, changeOrigin, le_add_right, le_of_forall_pos_nnreal_lt, le_radius_of_summable_nnnorm, le_rfl, lt_tsub_iff_right, nnnorm_changeOrigin_le, p.changeOrigin, p.nnnorm_changeOrigin_le, p.radius, radius, s.card, summable_of_le
-/
theorem changeOrigin_radius : p.radius - ‖x‖₊ <= (p.changeOrigin x).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _h0 hr => ?_
  rw [lt_tsub_iff_right]; rw [add_comm] at hr
  have hr' : (‖x‖₊ : Real>=0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have (k : Nat) :
      ‖p.changeOrigin x k‖₊ * r ^ k <=
        (∑' s : Σ l : Nat, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1) *
          r ^ k := by
    gcongr; exact p.nnnorm_changeOrigin_le k hr'
  refine NNReal.summable_of_le this ?_
  simpa only [← NNReal.tsum_mul_right] using
    (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr)).2

/--
Definition of `derivSeries` / `derivSeries` 的定义

English:
definition derivSeries
  signature: : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)
  body: (continuousMultilinearCurryFin1 𝕜 E F : (E [×1]->L[𝕜] F) ->L[𝕜] E ->L[𝕜] F)
.compFormalMultilinearSeries (p.changeOriginSeries 1)

中文:
定义 derivSeries
  签名: : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)
  定义体: (continuousMultilinearCurryFin1 𝕜 E F : (E [×1]->L[𝕜] F) ->L[𝕜] E ->L[𝕜] F)
.compFormalMultilinearSeries (p.changeOriginSeries 1)

Depends on / 依赖: changeOriginSeries, compFormalMultilinearSeries, continuousMultilinearCurryFin1, p.changeOriginSeries
-/
def derivSeries : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F) :=
  (continuousMultilinearCurryFin1 𝕜 E F : (E [×1]->L[𝕜] F) ->L[𝕜] E ->L[𝕜] F)
.compFormalMultilinearSeries (p.changeOriginSeries 1)

/--
theorem `radius_le_radius_derivSeries` / 定理 `radius_le_radius_derivSeries`

English:
theorem radius_le_radius_derivSeries
  statement: p.radius <= p.derivSeries.radius
  proof: by
  apply (p.le_changeOriginSeries_radius 1).trans (radius_le_of_le (fun n => ?_))
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

中文:
定理 radius_le_radius_derivSeries
  结论: p.radius <= p.derivSeries.radius
  证明: by
  apply (p.le_changeOriginSeries_radius 1).trans (radius_le_of_le (fun n => ?_))
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_compContinuousMultilinearMap_le, ContinuousLinearMap.opNorm_le_bound, le_changeOriginSeries_radius, mul_le_of_le_one_left, norm_compContinuousMultilinearMap_le, norm_nonneg, opNorm_le_bound, p.le_changeOriginSeries_radius, radius_le_of_le, zero_le_one
-/
theorem radius_le_radius_derivSeries : p.radius <= p.derivSeries.radius := by
  apply (p.le_changeOriginSeries_radius 1).trans (radius_le_of_le (fun n => ?_))
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

/--
theorem `derivSeries_eq_zero` / 定理 `derivSeries_eq_zero`

English:
theorem derivSeries_eq_zero
  given: {n : Nat} (hp : p (n + 1) = 0)
  statement: p.derivSeries n = 0
  proof: by
  suffices p.changeOriginSeries 1 n = 0 by ext v; simp [derivSeries, this]
  apply Finset.sum_eq_zero (fun s hs => ?_)
  have : p (1 + n) = 0 := p.congr_zero (by abel) hp
  simp [changeOriginSeriesTerm, this]

中文:
定理 derivSeries_eq_zero
  条件: {n : 自然数} (hp : p (n + 1) = 0)
  结论: p.derivSeries n = 0
  证明: by
  suffices p.changeOriginSeries 1 n = 0 by ext v; simp [derivSeries, this]
  apply Finset.sum_eq_zero (fun s hs => ?_)
  have : p (1 + n) = 0 := p.congr_zero (by abel) hp
  simp [changeOriginSeriesTerm, this]

Depends on / 依赖: Finset, Finset.sum_eq_zero, changeOriginSeries, changeOriginSeriesTerm, congr_zero, derivSeries, p.changeOriginSeries, p.congr_zero, sum_eq_zero
-/
theorem derivSeries_eq_zero {n : Nat} (hp : p (n + 1) = 0) : p.derivSeries n = 0 := by
  suffices p.changeOriginSeries 1 n = 0 by ext v; simp [derivSeries, this]
  apply Finset.sum_eq_zero (fun s hs => ?_)
  have : p (1 + n) = 0 := p.congr_zero (by abel) hp
  simp [changeOriginSeriesTerm, this]

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E}

/--
theorem `hasFPowerSeriesOnBall_changeOrigin` / 定理 `hasFPowerSeriesOnBall_changeOrigin`

English:
theorem hasFPowerSeriesOnBall_changeOrigin
  given: (k : Nat) (hr : 0 < p.radius)
  proof: have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFPowerSeriesOnBall (hr.trans_le this)).mono hr this

中文:
定理 hasFPowerSeriesOnBall_changeOrigin
  条件: (k : 自然数) (hr : 0 < p.radius)
  证明: have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFPowerSeriesOnBall (hr.trans_le this)).mono hr this

Depends on / 依赖: changeOriginSeries, hasFPowerSeriesOnBall, hr.trans_le, le_changeOriginSeries_radius, p.changeOriginSeries, p.le_changeOriginSeries_radius, trans_le
-/
theorem hasFPowerSeriesOnBall_changeOrigin (k : Nat) (hr : 0 < p.radius) :
    HasFPowerSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius :=
  have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFPowerSeriesOnBall (hr.trans_le this)).mono hr this

/--
theorem `changeOrigin_eval` / 定理 `changeOrigin_eval`

English:
theorem changeOrigin_eval
  given: (h : (‖x‖₊ + ‖y‖₊ : Real>=0∞) < p.radius)
  proof: by
  have x_mem_ball : x in Metric.eball (0 : E) p.radius :=
    mem_eball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y in Metric.eball (0 : E) (p.changeOrigin x).radius := by
    refine mem_eball_zero_iff.2 (lt_of_lt_of_le ?_ p.changeOrigin_radius)
    rwa [lt_tsub_iff_right,

中文:
定理 changeOrigin_eval
  条件: (h : (‖x‖₊ + ‖y‖₊ : 实数>=0∞) < p.radius)
  证明: by
  have x_mem_ball : x in Metric.eball (0 : E) p.radius :=
    mem_eball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y in Metric.eball (0 : E) (p.changeOrigin x).radius := by
    refine mem_eball_zero_iff.2 (lt_of_lt_of_le ?_ p.changeOrigin_radius)
    rwa [lt_tsub_iff_right,

Depends on / 依赖: Finset, Metric, Metric.eball, add_comm, changeOrigin, changeOrigin_radius, le_add_right, le_rfl, lt_of_le_of_lt, lt_of_lt_of_le, lt_tsub_iff_right, mem_eball_zero_iff, mod_cast, nnnorm_add_le, p.changeOrigin, p.changeOrigin_radius, p.radius, radius, trans_lt, x_add_y_mem_ball
-/
theorem changeOrigin_eval (h : (‖x‖₊ + ‖y‖₊ : Real>=0∞) < p.radius) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  have x_mem_ball : x in Metric.eball (0 : E) p.radius :=
    mem_eball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y in Metric.eball (0 : E) (p.changeOrigin x).radius := by
    refine mem_eball_zero_iff.2 (lt_of_lt_of_le ?_ p.changeOrigin_radius)
    rwa [lt_tsub_iff_right, add_comm]
  have x_add_y_mem_ball : x + y in Metric.eball (0 : E) p.radius := by
    refine mem_eball_zero_iff.2 (lt_of_le_of_lt ?_ h)
    exact mod_cast nnnorm_add_le x y
  set f : (Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l }) -> F := fun s =>
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have hsf : Summable f := by
    refine .of_nnnorm_bounded (p.changeOriginSeries_summable_aux₁ h) ?_
    rintro ⟨k, l, s, hs⟩
    dsimp only [Subtype.coe_mk]
    exact p.nnnorm_changeOriginSeriesTerm_apply_le _ _ _ _ _ _
  have hf : HasSum f ((p.changeOrigin x).sum y) := by
    refine HasSum.sigma_of_hasSum ((p.changeOrigin x).summable y_mem_ball).hasSum (fun k => ?_) hsf
    · dsimp +instances only [f]
      refine ContinuousMultilinearMap.hasSum_eval ?_ _
      have := (p.hasFPowerSeriesOnBall_changeOrigin k h.pos).hasSum x_mem_ball
      rw [zero_add] at this
      refine HasSum.sigma_of_hasSum this (fun l => ?_) ?_
      · simp only [changeOriginSeries, sum_apply]
        apply hasSum_fintype
      · refine .of_nnnorm_bounded
          (p.changeOriginSeries_summable_aux₂ (mem_eball_zero_iff.1 x_mem_ball) k)
            fun s => ?_
        refine (ContinuousMultilinearMap.le_opNNNorm _ _).trans_eq ?_
        simp
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine HasSum.sigma_of_hasSum
    (p.hasSum x_add_y_mem_ball) (fun n => ?_) (changeOriginIndexEquiv.symm.summable_iff.2 hsf)
  rw [← Pi.add_def]; rw [(p n).map_add_univ (fun _ => x) fun _ => y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype (fun c => f (changeOriginIndexEquiv.symm ⟨n, c⟩))

/--
theorem `analyticAt_changeOrigin` / 定理 `analyticAt_changeOrigin`

English:
theorem analyticAt_changeOrigin
  given: (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius > 0) (n : Nat)
  proof: (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p n rp).analyticAt

中文:
定理 analyticAt_changeOrigin
  条件: (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius > 0) (n : 自然数)
  证明: (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p n rp).analyticAt

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin, analyticAt, hasFPowerSeriesOnBall_changeOrigin
-/
theorem analyticAt_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius > 0) (n : Nat) :
    AnalyticAt 𝕜 (fun x => p.changeOrigin x n) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p n rp).analyticAt

end FormalMultilinearSeries


section

variable [CompleteSpace F] {f : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
  {x y : E} {r : Real>=0∞}

/--
theorem `HasFPowerSeriesWithinOnBall.changeOrigin` / 定理 `HasFPowerSeriesWithinOnBall.changeOrigin`

English:
theorem HasFPowerSeriesWithinOnBall.changeOrigin
  statement: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  proof: by
    apply le_trans _ p.changeOrigin_radius
    exact tsub_le_tsub hf.r_le le_rfl
  r_pos := by simp [h]
  hasSum {z} h'z hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff]; rw [lt_tsub_iff_right]

中文:
定理 HasFPowerSeriesWithinOnBall.changeOrigin
  结论: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  证明: by
    apply le_trans _ p.changeOrigin_radius
    exact tsub_le_tsub hf.r_le le_rfl
  r_pos := by simp [h]
  hasSum {z} h'z hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff]; rw [lt_tsub_iff_right]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.changeOrigin, FormalMultilinearSeries.sum, add_assoc, add_comm, changeOrigin, changeOrigin_eval, changeOrigin_radius, hasSum, hf.r_le, hf.sum, hz.trans_le, insert, insert_eq_of, insert_subset_insert, le_rfl, le_trans, lt_tsub_iff_right, mem_eball_zero_iff, p.changeOrigin_eval
-/
theorem HasFPowerSeriesWithinOnBall.changeOrigin (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (h : ‖y‖ₑ < r) (hy : x + y in insert x s) :
    HasFPowerSeriesWithinOnBall f (p.changeOrigin y) s (x + y) (r - ‖y‖ₑ) where
  r_le := by
    apply le_trans _ p.changeOrigin_radius
    exact tsub_le_tsub hf.r_le le_rfl
  r_pos := by simp [h]
  hasSum {z} h'z hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff]; rw [lt_tsub_iff_right]; rw [add_comm] at hz
      rw [p.changeOrigin_eval (hz.trans_le hf.r_le)]; rw [add_assoc]; rw [hf.sum]
      · have : insert (x + y) s subseteq insert (x + y) (insert x s) := by
          apply insert_subset_insert (subset_insert _ _)
        rw [insert_eq_of_mem hy] at this
        apply this
        simpa [add_assoc] using h'z
      exact mem_eball_zero_iff.2 (lt_of_le_of_lt (enorm_add_le _ _) hz)
    rw [this]
    apply (p.changeOrigin y).hasSum
    refine Metric.eball_subset_eball (le_trans ?_ p.changeOrigin_radius) hz
    exact tsub_le_tsub hf.r_le le_rfl

/--
theorem `HasFPowerSeriesOnBall.changeOrigin` / 定理 `HasFPowerSeriesOnBall.changeOrigin`

English:
theorem HasFPowerSeriesOnBall.changeOrigin
  statement: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.changeOrigin h (by simp)

中文:
定理 HasFPowerSeriesOnBall.changeOrigin
  结论: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.changeOrigin h (by simp)

Depends on / 依赖: changeOrigin, hasFPowerSeriesWithinOnBall_univ, hf.changeOrigin
-/
theorem HasFPowerSeriesOnBall.changeOrigin (hf : HasFPowerSeriesOnBall f p x r)
    (h : (‖y‖₊ : Real>=0∞) < r) : HasFPowerSeriesOnBall f (p.changeOrigin y) (x + y) (r - ‖y‖₊) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.changeOrigin h (by simp)

/--
theorem `HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem` / 定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem`

English:
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem
  proof: by
  have : (‖y - x‖₊ : Real>=0∞) < r := by simpa [edist_eq_enorm_sub] using! h.2
  have := hf.changeOrigin this (by simpa using! h.1)
  rw [add_sub_cancel] at this
  exact this.analyticWithinAt

中文:
定理 HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem
  证明: by
  have : (‖y - x‖₊ : Real>=0∞) < r := by simpa [edist_eq_enorm_sub] using! h.2
  have := hf.changeOrigin this (by simpa using! h.1)
  rw [add_sub_cancel] at this
  exact this.analyticWithinAt

Depends on / 依赖: add_sub_cancel, analyticWithinAt, changeOrigin, edist_eq_enorm_sub, hf.changeOrigin, this.analyticWithinAt
-/
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem
    (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (h : y in insert x s inter Metric.eball x r) : AnalyticWithinAt 𝕜 f s y := by
  have : (‖y - x‖₊ : Real>=0∞) < r := by simpa [edist_eq_enorm_sub] using! h.2
  have := hf.changeOrigin this (by simpa using! h.1)
  rw [add_sub_cancel] at this
  exact this.analyticWithinAt

/--
theorem `HasFPowerSeriesOnBall.analyticAt_of_mem` / 定理 `HasFPowerSeriesOnBall.analyticAt_of_mem`

English:
theorem HasFPowerSeriesOnBall.analyticAt_of_mem
  statement: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  rw [← analyticWithinAt_univ]
  exact hf.analyticWithinAt_of_mem (by simpa using h)

中文:
定理 HasFPowerSeriesOnBall.analyticAt_of_mem
  结论: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  rw [← analyticWithinAt_univ]
  exact hf.analyticWithinAt_of_mem (by simpa using h)

Depends on / 依赖: analyticWithinAt_of_mem, analyticWithinAt_univ, hasFPowerSeriesWithinOnBall_univ, hf.analyticWithinAt_of_mem
-/
theorem HasFPowerSeriesOnBall.analyticAt_of_mem (hf : HasFPowerSeriesOnBall f p x r)
    (h : y in Metric.eball x r) : AnalyticAt 𝕜 f y := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  rw [← analyticWithinAt_univ]
  exact hf.analyticWithinAt_of_mem (by simpa using h)

/--
theorem `HasFPowerSeriesWithinOnBall.analyticOn` / 定理 `HasFPowerSeriesWithinOnBall.analyticOn`

English:
theorem HasFPowerSeriesWithinOnBall.analyticOn
  given: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  proof: fun _ hy => ((analyticWithinAt_insert (y := x)).2 (hf.analyticWithinAt_of_mem hy)).mono
    inter_subset_left

中文:
定理 HasFPowerSeriesWithinOnBall.analyticOn
  条件: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  证明: fun _ hy => ((analyticWithinAt_insert (y := x)).2 (hf.analyticWithinAt_of_mem hy)).mono
    inter_subset_left

Depends on / 依赖: analyticWithinAt_insert, analyticWithinAt_of_mem, hf.analyticWithinAt_of_mem, inter_subset_left
-/
theorem HasFPowerSeriesWithinOnBall.analyticOn (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    AnalyticOn 𝕜 f (insert x s inter Metric.eball x r) :=
  fun _ hy => ((analyticWithinAt_insert (y := x)).2 (hf.analyticWithinAt_of_mem hy)).mono
    inter_subset_left

/--
theorem `HasFPowerSeriesOnBall.analyticOnNhd` / 定理 `HasFPowerSeriesOnBall.analyticOnNhd`

English:
theorem HasFPowerSeriesOnBall.analyticOnNhd
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: fun _y hy => hf.analyticAt_of_mem hy

中文:
定理 HasFPowerSeriesOnBall.analyticOnNhd
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: fun _y hy => hf.analyticAt_of_mem hy

Depends on / 依赖: analyticAt_of_mem, hf.analyticAt_of_mem
-/
theorem HasFPowerSeriesOnBall.analyticOnNhd (hf : HasFPowerSeriesOnBall f p x r) :
    AnalyticOnNhd 𝕜 f (Metric.eball x r) :=
  fun _y hy => hf.analyticAt_of_mem hy

variable (𝕜 f) in
/--
theorem `isOpen_analyticAt` / 定理 `isOpen_analyticAt`

English:
theorem isOpen_analyticAt
  statement: IsOpen { x | AnalyticAt 𝕜 f x }
  proof: by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.analyticAt_of_mem hy

中文:
定理 isOpen_analyticAt
  结论: IsOpen { x | AnalyticAt 𝕜 f x }
  证明: by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.analyticAt_of_mem hy

Depends on / 依赖: Metric, Metric.eball_mem_nhds, analyticAt_of_mem, eball_mem_nhds, hr.analyticAt_of_mem, hr.r_pos, isOpen_iff_mem_nhds, mem_of_superset, r_pos
-/
theorem isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.analyticAt_of_mem hy

/--
theorem `AnalyticAt.eventually_analyticAt` / 定理 `AnalyticAt.eventually_analyticAt`

English:
theorem AnalyticAt.eventually_analyticAt
  given: (h : AnalyticAt 𝕜 f x)
  proof: (isOpen_analyticAt 𝕜 f).mem_nhds h

中文:
定理 AnalyticAt.eventually_analyticAt
  条件: (h : AnalyticAt 𝕜 f x)
  证明: (isOpen_analyticAt 𝕜 f).mem_nhds h

Depends on / 依赖: isOpen_analyticAt, mem_nhds
-/
theorem AnalyticAt.eventually_analyticAt (h : AnalyticAt 𝕜 f x) :
    forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y :=
  (isOpen_analyticAt 𝕜 f).mem_nhds h

/--
theorem `AnalyticAt.exists_mem_nhds_analyticOnNhd` / 定理 `AnalyticAt.exists_mem_nhds_analyticOnNhd`

English:
theorem AnalyticAt.exists_mem_nhds_analyticOnNhd
  given: (h : AnalyticAt 𝕜 f x)
  proof: h.eventually_analyticAt.exists_mem

中文:
定理 AnalyticAt.exists_mem_nhds_analyticOnNhd
  条件: (h : AnalyticAt 𝕜 f x)
  证明: h.eventually_analyticAt.exists_mem

Depends on / 依赖: eventually_analyticAt, exists_mem, h.eventually_analyticAt.exists_mem
-/
theorem AnalyticAt.exists_mem_nhds_analyticOnNhd (h : AnalyticAt 𝕜 f x) :
    exists s in 𝓝 x, AnalyticOnNhd 𝕜 f s :=
  h.eventually_analyticAt.exists_mem

/--
theorem `AnalyticAt.exists_ball_analyticOnNhd` / 定理 `AnalyticAt.exists_ball_analyticOnNhd`

English:
theorem AnalyticAt.exists_ball_analyticOnNhd
  given: (h : AnalyticAt 𝕜 f x)
  proof: Metric.isOpen_iff.mp (isOpen_analyticAt _ _) _ h

中文:
定理 AnalyticAt.exists_ball_analyticOnNhd
  条件: (h : AnalyticAt 𝕜 f x)
  证明: Metric.isOpen_iff.mp (isOpen_analyticAt _ _) _ h

Depends on / 依赖: Metric, Metric.isOpen_iff.mp, isOpen_analyticAt, isOpen_iff
-/
theorem AnalyticAt.exists_ball_analyticOnNhd (h : AnalyticAt 𝕜 f x) :
    exists r : Real, 0 < r ∧ AnalyticOnNhd 𝕜 f (Metric.ball x r) :=
  Metric.isOpen_iff.mp (isOpen_analyticAt _ _) _ h

/--
theorem `FormalMultilinearSeries.analyticOnNhd` / 定理 `FormalMultilinearSeries.analyticOnNhd`

English:
theorem FormalMultilinearSeries.analyticOnNhd
  proof: by
  by_cases hr : p.radius = 0
  · simp [hr]
  exact (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (pos_of_ne_zero hr)).analyticOnNhd

中文:
定理 FormalMultilinearSeries.analyticOnNhd
  证明: by
  by_cases hr : p.radius = 0
  · simp [hr]
  exact (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (pos_of_ne_zero hr)).analyticOnNhd
-/
protected theorem FormalMultilinearSeries.analyticOnNhd :
    AnalyticOnNhd 𝕜 p.sum (Metric.eball 0 p.radius) := by
  by_cases hr : p.radius = 0
  · simp [hr]
  exact (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (pos_of_ne_zero hr)).analyticOnNhd

end
