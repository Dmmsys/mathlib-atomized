/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The radical of a quadratic form

We define the radical of a quadratic form. This is a standard construction if 2 is invertible
in the coefficient ring, but is more fiddly otherwise. We follow the account in
Chapter II, §7 of [elman-karpenko-merkurjev-2008].
-/

open Finset QuadraticMap

@[expose] public noncomputable section

namespace QuadraticMap

variable {R M M' P : Type*} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup P]
  [CommRing R] [Module R M] [Module R M'] [Module R P] (Q : QuadraticMap R M P)

/--
Definition of `radical` / `radical` 的定义

English:
definition radical
  signature: : Submodule R M where
  body: {x : M | Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0}
  zero_mem' := by simp
  smul_mem' a x hx := by simp [QuadraticMap.map_smul, hx.1, hx.2]
  add_mem' := fun {x y} hx hy => by
    refine ⟨?_, by simp [hx.2, hy.2]⟩
    have := congr_arg (· y) hx.2
    simp only [QuadraticMap.polarBilin_apply_apply, 

中文:
定义 radical
  签名: : Submodule R M where
  定义体: {x : M | Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0}
  zero_mem' := by simp
  smul_mem' a x hx := by simp [QuadraticMap.map_smul, hx.1, hx.2]
  add_mem' := fun {x y} hx hy => by
    refine ⟨?_, by simp [hx.2, hy.2]⟩
    have := congr_arg (· y) hx.2
    simp only [QuadraticMap.polarBilin_apply_apply, 

Depends on / 依赖: QuadraticMap, QuadraticMap.polarBilin, polarBilin
-/
def radical : Submodule R M where
  carrier := {x : M | Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0}
  zero_mem' := by simp
  smul_mem' a x hx := by simp [QuadraticMap.map_smul, hx.1, hx.2]
  add_mem' := fun {x y} hx hy => by
    refine ⟨?_, by simp [hx.2, hy.2]⟩
    have := congr_arg (· y) hx.2
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.zero_apply, sub_sub, sub_eq_zero] at this
    rw [this]; rw [hx.1]; rw [hy.1]; rw [zero_add]

variable {Q}

/--
lemma `mem_radical_iff'` / 引理 `mem_radical_iff'`

English:
lemma mem_radical_iff'
  given: {m : M}
  proof: by
  simp +contextual [radical, QuadraticMap.polarBilin, LinearMap.ext_iff,
    QuadraticMap.polar, sub_sub, sub_eq_zero]

中文:
引理 mem_radical_iff'
  条件: {m : M}
  证明: by
  simp +contextual [radical, QuadraticMap.polarBilin, LinearMap.ext_iff,
    QuadraticMap.polar, sub_sub, sub_eq_zero]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, QuadraticMap, QuadraticMap.polar, QuadraticMap.polarBilin, contextual, ext_iff, polarBilin, radical, sub_eq_zero, sub_sub
-/
lemma mem_radical_iff' {m : M} :
    m in Q.radical ↔ Q m = 0 ∧ forall n : M, Q (m + n) = Q n := by
  simp +contextual [radical, QuadraticMap.polarBilin, LinearMap.ext_iff,
    QuadraticMap.polar, sub_sub, sub_eq_zero]

/--
lemma `IsometryEquiv.map_radical` / 引理 `IsometryEquiv.map_radical`

English:
lemma IsometryEquiv.map_radical
  statement: {Q' : QuadraticMap R M' P}
  proof: by
  ext
  simp [mem_radical_iff', ← e.map_app, -map_app, e.toEquiv.forall_congr_left]

中文:
引理 IsometryEquiv.map_radical
  结论: {Q' : QuadraticMap R M' P}
  证明: by
  ext
  simp [mem_radical_iff', ← e.map_app, -map_app, e.toEquiv.forall_congr_left]
-/
@[simp] lemma IsometryEquiv.map_radical {Q' : QuadraticMap R M' P}
    (e : IsometryEquiv Q Q') : Q.radical.map e.toLinearMap = Q'.radical := by
  ext
  simp [mem_radical_iff', ← e.map_app, -map_app, e.toEquiv.forall_congr_left]

/--
lemma `Equivalent.rank_radical_eq` / 引理 `Equivalent.rank_radical_eq`

English:
lemma Equivalent.rank_radical_eq
  given: {Q' : QuadraticMap R M' P} (h : Equivalent Q Q')
  proof: by
  obtain ⟨e⟩ := h
  rw [← e.map_radical]; rw [LinearEquiv.finrank_map_eq]

中文:
引理 Equivalent.rank_radical_eq
  条件: {Q' : QuadraticMap R M' P} (h : Equivalent Q Q')
  证明: by
  obtain ⟨e⟩ := h
  rw [← e.map_radical]; rw [LinearEquiv.finrank_map_eq]

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_map_eq, e.map_radical, finrank_map_eq, map_radical
-/
lemma Equivalent.rank_radical_eq {Q' : QuadraticMap R M' P} (h : Equivalent Q Q') :
    Module.finrank R Q.radical = Module.finrank R Q'.radical := by
  obtain ⟨e⟩ := h
  rw [← e.map_radical]; rw [LinearEquiv.finrank_map_eq]

-- auxiliary lemma for lifting quadratic maps to quotients
/--
lemma `lift_aux` / 引理 `lift_aux`

English:
lemma lift_aux
  statement: {N : Submodule R M} (hN : N <= Q.radical)
  proof: by
  rw [Submodule.quotientRel_def] at hmm'
  rw [(by simp : m = m' + (m - m'))]; rw [QuadraticMap.map_add Q m' (m - m')]; rw [(hN hmm').1]; rw [add_zero]; rw [polar_comm]; rw [← polarBilin_apply_apply]
  simp [(hN hmm').2]

中文:
引理 lift_aux
  结论: {N : Submodule R M} (hN : N <= Q.radical)
  证明: by
  rw [Submodule.quotientRel_def] at hmm'
  rw [(by simp : m = m' + (m - m'))]; rw [QuadraticMap.map_add Q m' (m - m')]; rw [(hN hmm').1]; rw [add_zero]; rw [polar_comm]; rw [← polarBilin_apply_apply]
  simp [(hN hmm').2]
-/
private lemma lift_aux {N : Submodule R M} (hN : N <= Q.radical)
    (m m' : M) (hmm' : Submodule.quotientRel N m m') : Q m = Q m' := by
  rw [Submodule.quotientRel_def] at hmm'
  rw [(by simp : m = m' + (m - m'))]; rw [QuadraticMap.map_add Q m' (m - m')]; rw [(hN hmm').1]; rw [add_zero]; rw [polar_comm]; rw [← polarBilin_apply_apply]
  simp [(hN hmm').2]

variable (Q) in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (N : Submodule R M) (hN : N <= Q.radical)
  body: by
  refine QuadraticMap.mk (Quotient.lift Q <| by exact lift_aux hN)
    (fun a m => m.inductionOn (Q.map_smul a)) ?_
  use Q.polarBilin.liftQ₂ N N (fun n hn => (hN hn).2) (fun n hn => ?_)
  · simp only [Submodule.Quotient.forall]
    exact QuadraticMap.map_add Q -- remarkably, this works
  · simp_

中文:
定义 lift
  签名: (N : Submodule R M) (hN : N <= Q.radical)
  定义体: by
  refine QuadraticMap.mk (Quotient.lift Q <| by exact lift_aux hN)
    (fun a m => m.inductionOn (Q.map_smul a)) ?_
  use Q.polarBilin.liftQ₂ N N (fun n hn => (hN hn).2) (fun n hn => ?_)
  · simp only [Submodule.Quotient.forall]
    exact QuadraticMap.map_add Q -- remarkably, this works
  · simp_
-/
protected def lift (N : Submodule R M) (hN : N <= Q.radical) : QuadraticMap R (M ⧸ N) P := by
  refine QuadraticMap.mk (Quotient.lift Q <| by exact lift_aux hN)
    (fun a m => m.inductionOn (Q.map_smul a)) ?_
  use Q.polarBilin.liftQ₂ N N (fun n hn => (hN hn).2) (fun n hn => ?_)
  · simp only [Submodule.Quotient.forall]
    exact QuadraticMap.map_add Q -- remarkably, this works
  · simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
      polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply, (hN hn).2, forall_true_iff]

@[simp]
/--
lemma `lift_mk` / 引理 `lift_mk`

English:
lemma lift_mk
  given: {N : Submodule R M} (hN : N <= Q.radical) (m : M)
  proof: rfl

中文:
引理 lift_mk
  条件: {N : Submodule R M} (hN : N <= Q.radical) (m : M)
  证明: rfl
-/
lemma lift_mk {N : Submodule R M} (hN : N <= Q.radical) (m : M) :
    Q.lift N hN (Submodule.Quotient.mk m) = Q m :=
  rfl

/--
lemma `le_radical_iff` / 引理 `le_radical_iff`

English:
lemma le_radical_iff
  given: {N : Submodule R M}
  proof: by
  constructor
  · exact fun hN => ⟨Q.lift N hN, rfl⟩
  · rintro ⟨Q', rfl⟩ m hm
    simp [radical, (Submodule.Quotient.mk_eq_zero _).mpr hm, LinearMap.ext_iff, polar]

中文:
引理 le_radical_iff
  条件: {N : Submodule R M}
  证明: by
  constructor
  · exact fun hN => ⟨Q.lift N hN, rfl⟩
  · rintro ⟨Q', rfl⟩ m hm
    simp [radical, (Submodule.Quotient.mk_eq_zero _).mpr hm, LinearMap.ext_iff, polar]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, Q.lift, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, ext_iff, mk_eq_zero, radical
-/
lemma le_radical_iff {N : Submodule R M} :
    N <= Q.radical ↔ exists Q' : QuadraticMap R (M ⧸ N) P, Q'.comp N.mkQ = Q := by
  constructor
  · exact fun hN => ⟨Q.lift N hN, rfl⟩
  · rintro ⟨Q', rfl⟩ m hm
    simp [radical, (Submodule.Quotient.mk_eq_zero _).mpr hm, LinearMap.ext_iff, polar]

/--
lemma `radical_le_ker_polarBilin` / 引理 `radical_le_ker_polarBilin`

English:
lemma radical_le_ker_polarBilin
  statement: Q.radical <= Q.polarBilin.ker
  proof: by
  intro m
  simp +contextual [mem_radical_iff', LinearMap.ext_iff, QuadraticMap.polar]

中文:
引理 radical_le_ker_polarBilin
  结论: Q.radical <= Q.polarBilin.ker
  证明: by
  intro m
  simp +contextual [mem_radical_iff', LinearMap.ext_iff, QuadraticMap.polar]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, QuadraticMap, QuadraticMap.polar, contextual, ext_iff, mem_radical_iff
-/
lemma radical_le_ker_polarBilin : Q.radical <= Q.polarBilin.ker := by
  intro m
  simp +contextual [mem_radical_iff', LinearMap.ext_iff, QuadraticMap.polar]

/--
Definition of `Nondegenerate` / `Nondegenerate` 的定义

English:
structure Nondegenerate
  parameters: : Prop where
  axioms and operations (2):
    - radical_eq_bot : Q.radical = ⊥
    - rank_rad_polar_le : Module.rank R Q.polarBilin.ker <= 1

中文:
结构 Nondegenerate
  参数: : 命题 where
  公理与运算 (2 个):
    - radical_eq_bot : Q.radical = ⊥
    - rank_rad_polar_le : Module.rank R Q.polarBilin.ker <= 1
-/
structure Nondegenerate : Prop where
  radical_eq_bot : Q.radical = ⊥
  rank_rad_polar_le : Module.rank R Q.polarBilin.ker <= 1

section InvertibleTwo

variable [Invertible (2 : R)]

/--
lemma `radical_eq_ker_polarBilin` / 引理 `radical_eq_ker_polarBilin`

English:
lemma radical_eq_ker_polarBilin
  statement: Q.radical = Q.polarBilin.ker
  proof: by
  ext m
  simp only [mem_radical_iff', LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  refine ⟨by simp +contextual, fun h => ?_⟩
  suffices Q m = 0 by grind
  specialize h m
  rwa [← two_smul R, QuadraticMap.map_smul, sub_

中文:
引理 radical_eq_ker_polarBilin
  结论: Q.radical = Q.polarBilin.ker
  证明: by
  ext m
  simp only [mem_radical_iff', LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  refine ⟨by simp +contextual, fun h => ?_⟩
  suffices Q m = 0 by grind
  specialize h m
  rwa [← two_smul R, QuadraticMap.map_smul, sub_

Depends on / 依赖: LinearMap, LinearMap.ext_iff, LinearMap.mem_ker, LinearMap.zero_apply, QuadraticMap, QuadraticMap.map_smul, QuadraticMap.polar, QuadraticMap.polarBilin_apply_apply, add_sub_cancel_right, contextual, ext_iff, isUnit_of_invertible, map_smul, mem_ker, mem_radical_iff, mul_smul, polarBilin_apply_apply, smul_eq_zero, smul_sub, specialize
-/
lemma radical_eq_ker_polarBilin : Q.radical = Q.polarBilin.ker := by
  ext m
  simp only [mem_radical_iff', LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  refine ⟨by simp +contextual, fun h => ?_⟩
  suffices Q m = 0 by grind
  specialize h m
  rwa [← two_smul R, QuadraticMap.map_smul, sub_sub, ← two_smul R, mul_smul, ← smul_sub,
    (isUnit_of_invertible 2).smul_eq_zero, two_smul, add_sub_cancel_right] at h

/--
lemma `radical_eq_ker_associated` / 引理 `radical_eq_ker_associated`

English:
lemma radical_eq_ker_associated
  statement: Q.radical = (QuadraticMap.associated Q).ker
  proof: by
  rw [radical_eq_ker_polarBilin]
  ext m
  simp [associated_apply, LinearMap.ext_iff, QuadraticMap.polar, invOf_smul_eq_iff]

中文:
引理 radical_eq_ker_associated
  结论: Q.radical = (QuadraticMap.associated Q).ker
  证明: by
  rw [radical_eq_ker_polarBilin]
  ext m
  simp [associated_apply, LinearMap.ext_iff, QuadraticMap.polar, invOf_smul_eq_iff]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, QuadraticMap, QuadraticMap.polar, associated_apply, ext_iff, invOf_smul_eq_iff, radical_eq_ker_polarBilin
-/
lemma radical_eq_ker_associated : Q.radical = (QuadraticMap.associated Q).ker := by
  rw [radical_eq_ker_polarBilin]
  ext m
  simp [associated_apply, LinearMap.ext_iff, QuadraticMap.polar, invOf_smul_eq_iff]

/--
lemma `nondegenerate_iff_radical_eq_bot` / 引理 `nondegenerate_iff_radical_eq_bot`

English:
lemma nondegenerate_iff_radical_eq_bot
  proof: by
  refine ⟨Nondegenerate.radical_eq_bot, fun h => ⟨h, ?_⟩⟩
  rw [← QuadraticMap.radical_eq_ker_polarBilin]; rw [h]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

中文:
引理 nondegenerate_iff_radical_eq_bot
  证明: by
  refine ⟨Nondegenerate.radical_eq_bot, fun h => ⟨h, ?_⟩⟩
  rw [← QuadraticMap.radical_eq_ker_polarBilin]; rw [h]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

Depends on / 依赖: Nondegenerate, Nondegenerate.radical_eq_bot, QuadraticMap, QuadraticMap.radical_eq_ker_polarBilin, nontriviality, radical_eq_bot, radical_eq_ker_polarBilin, rank_subsingleton, zero_le
-/
lemma nondegenerate_iff_radical_eq_bot :
    Q.Nondegenerate ↔ Q.radical = ⊥ := by
  refine ⟨Nondegenerate.radical_eq_bot, fun h => ⟨h, ?_⟩⟩
  rw [← QuadraticMap.radical_eq_ker_polarBilin]; rw [h]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

/--
lemma `nondegenerate_associated_iff` / 引理 `nondegenerate_associated_iff`

English:
lemma nondegenerate_associated_iff
  proof: by
  rw [nondegenerate_iff_radical_eq_bot]; rw [radical_eq_ker_associated]; rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft]; rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y => (congr_arg (· x y) (associated_flip R Q)).trans

中文:
引理 nondegenerate_associated_iff
  证明: by
  rw [nondegenerate_iff_radical_eq_bot]; rw [radical_eq_ker_associated]; rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft]; rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y => (congr_arg (· x y) (associated_flip R Q)).trans

Depends on / 依赖: IsRefl, LinearMap, LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot, associated_flip, congr_arg, nondegenerate_iff_radical_eq_bot, nondegenerate_iff_separatingLeft, radical_eq_ker_associated, separatingLeft_iff_ker_eq_bot
-/
lemma nondegenerate_associated_iff :
    (QuadraticMap.associated Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot]; rw [radical_eq_ker_associated]; rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft]; rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y => (congr_arg (· x y) (associated_flip R Q)).trans

/--
lemma `nondegenerate_polar_iff` / 引理 `nondegenerate_polar_iff`

English:
lemma nondegenerate_polar_iff
  proof: by
  rw [nondegenerate_iff_radical_eq_bot]; rw [radical_eq_ker_polarBilin]; rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft]; rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y => (polar_comm Q y x).trans

中文:
引理 nondegenerate_polar_iff
  证明: by
  rw [nondegenerate_iff_radical_eq_bot]; rw [radical_eq_ker_polarBilin]; rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft]; rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y => (polar_comm Q y x).trans

Depends on / 依赖: IsRefl, LinearMap, LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot, nondegenerate_iff_radical_eq_bot, nondegenerate_iff_separatingLeft, polar_comm, radical_eq_ker_polarBilin, separatingLeft_iff_ker_eq_bot
-/
lemma nondegenerate_polar_iff :
    (QuadraticMap.polarBilin Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot]; rw [radical_eq_ker_polarBilin]; rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft]; rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y => (polar_comm Q y x).trans

end InvertibleTwo

end QuadraticMap

namespace QuadraticForm
variable {𝕜 ι : Type*} [Field 𝕜] [NeZero (2 : 𝕜)] [Fintype ι] {w : ι -> 𝕜}

/--
lemma `radical_weightedSumSquares` / 引理 `radical_weightedSumSquares`

English:
lemma radical_weightedSumSquares
  proof: by
  classical
  ext v
  simp only [mem_radical_iff', weightedSumSquares_apply, ← pow_two, smul_eq_mul, Pi.add_apply,
    add_sq, mul_add, sum_add_distrib, add_eq_right, Pi.mem_spanSubset_iff]
  constructor
  · rintro ⟨hv, hvv'⟩ i
    simpa [hv, Pi.single_apply, NeZero.ne, or_iff_not_imp_left] using

中文:
引理 radical_weightedSumSquares
  证明: by
  classical
  ext v
  simp only [mem_radical_iff', weightedSumSquares_apply, ← pow_two, smul_eq_mul, Pi.add_apply,
    add_sq, mul_add, sum_add_distrib, add_eq_right, Pi.mem_spanSubset_iff]
  constructor
  · rintro ⟨hv, hvv'⟩ i
    simpa [hv, Pi.single_apply, NeZero.ne, or_iff_not_imp_left] using

Depends on / 依赖: NeZero, NeZero.ne, Pi.add_apply, Pi.mem_spanSubset_iff, Pi.single, Pi.single_apply, add_apply, add_eq_right, add_sq, classical, mem_radical_iff, mem_spanSubset_iff, mul_add, or_iff_not_imp_left, pow_two, single, single_apply, smul_eq_mul, sum_add_distrib, sum_eq_zero
-/
lemma radical_weightedSumSquares :
    radical (weightedSumSquares 𝕜 w) = Pi.spanSubset 𝕜 {i | w i = 0} := by
  classical
  ext v
  simp only [mem_radical_iff', weightedSumSquares_apply, ← pow_two, smul_eq_mul, Pi.add_apply,
    add_sq, mul_add, sum_add_distrib, add_eq_right, Pi.mem_spanSubset_iff]
  constructor
  · rintro ⟨hv, hvv'⟩ i
    simpa [hv, Pi.single_apply, NeZero.ne, or_iff_not_imp_left] using hvv' (Pi.single i 1)
  · simpa only [← sum_add_distrib]
      using fun h => ⟨sum_eq_zero (by grind), fun v => sum_eq_zero (by grind)⟩

/--
lemma `finrank_radical_of_equiv_weightedSumSquares` / 引理 `finrank_radical_of_equiv_weightedSumSquares`

English:
lemma finrank_radical_of_equiv_weightedSumSquares
  statement: {M : Type*} [AddCommGroup M] [Module 𝕜 M]
  proof: by
  rw [hQ.rank_radical_eq]; rw [radical_weightedSumSquares]; rw [Pi.dim_spanSubset]

中文:
引理 finrank_radical_of_equiv_weightedSumSquares
  结论: {M : 类型} [AddCommGroup M] [Module 𝕜 M]
  证明: by
  rw [hQ.rank_radical_eq]; rw [radical_weightedSumSquares]; rw [Pi.dim_spanSubset]

Depends on / 依赖: Pi.dim_spanSubset, dim_spanSubset, hQ.rank_radical_eq, radical_weightedSumSquares, rank_radical_eq
-/
lemma finrank_radical_of_equiv_weightedSumSquares {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    {Q : QuadraticForm 𝕜 M} (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    Module.finrank 𝕜 Q.radical = {i | w i = 0}.ncard := by
  rw [hQ.rank_radical_eq]; rw [radical_weightedSumSquares]; rw [Pi.dim_spanSubset]

end QuadraticForm
