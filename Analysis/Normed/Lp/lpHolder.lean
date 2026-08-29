/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic.Positivity.Finset

/-! # Hölder's inequality for `lp` spaces

This file proves Hölder's inequality for `lp` spaces. We follow the established pattern for
Hölder's inequality for `MeasureTheory.Lp` of generalizing multiplication to any continuous bilinear
map. Since `lp` is a dependent Π-type, we actually need a uniformly bounded family of bilinear maps.

## Implementation notes

Although it would be possible to bundle the uniformly bounded family of bilinear maps into a term
`B : lp (fun i ↦ E i →L[𝕜] F i →L[𝕜] G i) ∞`, this has some downsides. For example, we would
then have to bundle `fun i ↦ (B i).flip` into a term of this type in order to use it, so we opt to
leave `B` unbundled.

-/

@[expose] public section

open scoped lp ENNReal NNReal

namespace lp
-- the material in this section could be moved to `lpSpace`, but would require some extra imports

section NontriviallyNormedField

variable {α 𝕜 : Type*} {E F : α -> Type*} [NontriviallyNormedField 𝕜]
variable [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
  [forall i, NormedAddCommGroup (F i)] [forall i, NormedSpace 𝕜 (F i)]
variable {p q r : Real>=0∞}

set_option backward.isDefEq.respectTransparency.types false in
/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `lp` space. -/
@[simps!]
/--
Definition of `mapCLM` / `mapCLM` 的定义

English:
definition mapCLM
  signature: (p : Real>=0∞) [Fact (1 <= p)]
  body: haveI key (i : α) (x : E i) : ‖T i x‖ <= K * ‖x‖ := (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i => T i (⇑x i), lp.memℓp x |>.norm.const_mul K |>.mono
.of_norm⟩ (fun _ => by simpa [abs_of_nonneg hK] using key ..)
      map_add' _ _ := by ext; simp
      map_smul' 

中文:
定义 mapCLM
  签名: (p : 实数>=0∞) [Fact (1 <= p)]
  定义体: haveI key (i : α) (x : E i) : ‖T i x‖ <= K * ‖x‖ := (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i => T i (⇑x i), lp.memℓp x |>.norm.const_mul K |>.mono
.of_norm⟩ (fun _ => by simpa [abs_of_nonneg hK] using key ..)
      map_add' _ _ := by ext; simp
      map_smul' 

Depends on / 依赖: Fact.out, LinearMap, LinearMap.mkContinuous, Real.norm_eq_abs, abs_of_n, abs_of_nonneg, const_mul, conv_rhs, le_of_opNorm_le, lp.mem, map_add, map_smul, mkContinuous, norm.const_mul, norm_eq_abs, norm_mono, norm_smul, norm_toNorm, of_norm, trans_le
-/
noncomputable def mapCLM (p : Real>=0∞) [Fact (1 <= p)]
    (T : forall i, E i ->L[𝕜] F i) {K : Real} (hK : 0 <= K) (hTK : forall i, ‖T i‖ <= K) :
    lp E p ->L[𝕜] lp F p :=
  haveI key (i : α) (x : E i) : ‖T i x‖ <= K * ‖x‖ := (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i => T i (⇑x i), lp.memℓp x |>.norm.const_mul K |>.mono
.of_norm⟩ (fun _ => by simpa [abs_of_nonneg hK] using key ..)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    K
    fun x => by
      rw [← norm_toNorm]
      conv_rhs => rw [← norm_toNorm, ← abs_of_nonneg hK, ← Real.norm_eq_abs, ← norm_smul]
      apply norm_mono (zero_lt_one.trans_le Fact.out).ne' fun i => ?_
      simpa [abs_of_nonneg hK] using key ..

/--
lemma `norm_mapCLM_le` / 引理 `norm_mapCLM_le`

English:
lemma norm_mapCLM_le
  statement: (p : Real>=0∞) [Fact (1 <= p)]
  proof: LinearMap.mkContinuous_norm_le _ hK _

中文:
引理 norm_mapCLM_le
  结论: (p : 实数>=0∞) [Fact (1 <= p)]
  证明: LinearMap.mkContinuous_norm_le _ hK _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, mkContinuous_norm_le
-/
lemma norm_mapCLM_le (p : Real>=0∞) [Fact (1 <= p)]
    (T : forall i, E i ->L[𝕜] F i) {K : Real} (hK : 0 <= K) (hTK : forall i, ‖T i‖ <= K) :
    ‖mapCLM p T hK hTK‖ <= K :=
  LinearMap.mkContinuous_norm_le _ hK _

end NontriviallyNormedField

/--
lemma `norm_tsumCLM_le` / 引理 `norm_tsumCLM_le`

English:
lemma norm_tsumCLM_le
  statement: {α 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  proof: LinearMap.mkContinuous_norm_le _ zero_le_one _

中文:
引理 norm_tsumCLM_le
  结论: {α 𝕜 E : 类型} [NontriviallyNormedField 𝕜]
  证明: LinearMap.mkContinuous_norm_le _ zero_le_one _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, mkContinuous_norm_le, zero_le_one
-/
lemma norm_tsumCLM_le {α 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    ‖tsumCLM 𝕜 α E‖ <= 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end lp

variable {ι 𝕜 : Type*} {E F G : ι -> Type*} [RCLike 𝕜]
variable [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
  [forall i, NormedAddCommGroup (F i)] [forall i, NormedSpace 𝕜 (F i)]
  [forall i, NormedAddCommGroup (G i)] [forall i, NormedSpace 𝕜 (G i)]

open ENNReal

variable {p q : Real>=0∞} (r : Real>=0∞) [hpqr : p.HolderTriple q r]

namespace Memℓp

/--
theorem `bilin_of_top_left` / 定理 `bilin_of_top_left`

English:
theorem bilin_of_top_left
  statement: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  proof: by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  obtain ⟨C, hC⟩ := by
    simpa [memℓp_infty_iff, BddAbove, Set.Nonempty, Set.range, upperBounds] using he
.mono fun i => ?_ refine hf.norm.const_mul (K * C)
.trans hBK _ have hK_nonneg : 0 <= K := norm_nonneg (B (Classical.arbitrary ι))


中文:
定理 bilin_of_top_left
  结论: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  证明: by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  obtain ⟨C, hC⟩ := by
    simpa [memℓp_infty_iff, BddAbove, Set.Nonempty, Set.range, upperBounds] using he
.mono fun i => ?_ refine hf.norm.const_mul (K * C)
.trans hBK _ have hK_nonneg : 0 <= K := norm_nonneg (B (Classical.arbitrary ι))


Depends on / 依赖: BddAbove, Classical, Classical.arbitrary, Nonempty, Set.Nonempty, Set.range, arbitrary, const_mul, exacts, hK_nonneg, hf.norm.const_mul, isEmpty_or_nonempty, le_of_opNorm_le, le_opNorm, norm_nonneg, upperBounds
-/
theorem bilin_of_top_left (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
    {K : Real} (hBK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e ∞) (hf : Memℓp f q) :
    Memℓp (fun i => B i (e i) (f i)) q := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  obtain ⟨C, hC⟩ := by
    simpa [memℓp_infty_iff, BddAbove, Set.Nonempty, Set.range, upperBounds] using he
.mono fun i => ?_ refine hf.norm.const_mul (K * C)
.trans hBK _ have hK_nonneg : 0 <= K := norm_nonneg (B (Classical.arbitrary ι))
  calc
    ‖B i (e i) (f i)‖ <= ‖B i‖ * ‖e i‖ * ‖f i‖ := (B i (e i)).le_of_opNorm_le ((B i).le_opNorm _) _
    _ <= K * C * ‖f i‖ := by gcongr; exacts [hBK i, hC i]

/--
theorem `bilin_of_top_right` / 定理 `bilin_of_top_right`

English:
theorem bilin_of_top_right
  statement: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  proof: hf.bilin_of_top_left (fun i => (B i).flip) (by simpa using hBK) he

中文:
定理 bilin_of_top_right
  结论: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  证明: hf.bilin_of_top_left (fun i => (B i).flip) (by simpa using hBK) he

Depends on / 依赖: bilin_of_top_left, hf.bilin_of_top_left
-/
theorem bilin_of_top_right (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
    {K : Real} (hBK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e p) (hf : Memℓp f ∞) :
    Memℓp (fun i => B i (e i) (f i)) p :=
  hf.bilin_of_top_left (fun i => (B i).flip) (by simpa using hBK) he

/--
theorem `bilin_of_zero_left` / 定理 `bilin_of_zero_left`

English:
theorem bilin_of_zero_left
  statement: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  proof: by
  rw [memℓp_zero_iff] at he ⊢
exact he.subset fun i hi h => hi by simp [h]

中文:
定理 bilin_of_zero_left
  结论: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  证明: by
  rw [memℓp_zero_iff] at he ⊢
exact he.subset fun i hi h => hi by simp [h]

Depends on / 依赖: he.subset, subset
-/
theorem bilin_of_zero_left (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (he : Memℓp e 0) :
    Memℓp (fun i => B i (e i) (f i)) 0 := by
  rw [memℓp_zero_iff] at he ⊢
exact he.subset fun i hi h => hi by simp [h]

/--
theorem `bilin_of_zero_right` / 定理 `bilin_of_zero_right`

English:
theorem bilin_of_zero_right
  statement: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  proof: hf.bilin_of_zero_left (fun i => (B i).flip)

中文:
定理 bilin_of_zero_right
  结论: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
  证明: hf.bilin_of_zero_left (fun i => (B i).flip)

Depends on / 依赖: bilin_of_zero_left, hf.bilin_of_zero_left
-/
theorem bilin_of_zero_right (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (hf : Memℓp f 0) :
    Memℓp (fun i => B i (e i) (f i)) 0 :=
  hf.bilin_of_zero_left (fun i => (B i).flip)

/--
lemma `holder_top_left_bound` / 引理 `holder_top_left_bound`

English:
lemma holder_top_left_bound
  proof: by
  grw [← hDf s, s.mul_sum]
  apply s.sum_le_sum fun i hi => ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le_of_le (hBK i) (hCe i)) _

中文:
引理 holder_top_left_bound
  证明: by
  grw [← hDf s, s.mul_sum]
  apply s.sum_le_sum fun i hi => ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le_of_le (hBK i) (hCe i)) _

Depends on / 依赖: Real.mul_rpow, le_of_opNorm_le, le_of_opNorm_le_of_le, mul_rpow, mul_sum, s.mul_sum, s.sum_le_sum, sum_le_sum
-/
lemma holder_top_left_bound
    {e : (i : ι) -> E i} {f : (i : ι) -> F i} (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
    {K C D : Real} (hBK : forall i, ‖B i‖ <= K) (hK : 0 <= K) (hC : 0 <= C)
    (hCe : forall i, ‖e i‖ <= C) (hDf : forall s, ∑ i in s, ‖f i‖ ^ q.toReal <= D) (s : Finset ι) :
    ∑ i in s, ‖B i (e i) (f i)‖ ^ q.toReal <= (K * C) ^ q.toReal * D := by
  grw [← hDf s, s.mul_sum]
  apply s.sum_le_sum fun i hi => ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le_of_le (hBK i) (hCe i)) _

/--
lemma `holder_top_right_bound` / 引理 `holder_top_right_bound`

English:
lemma holder_top_right_bound
  proof: holder_top_left_bound (B · |>.flip) (by simpa) hK hD hDf hCe s

中文:
引理 holder_top_right_bound
  证明: holder_top_left_bound (B · |>.flip) (by simpa) hK hD hDf hCe s

Depends on / 依赖: holder_top_left_bound
-/
lemma holder_top_right_bound
    {e : (i : ι) -> E i} {f : (i : ι) -> F i} (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i)
    {K C D : Real} (hBK : forall i, ‖B i‖ <= K) (hK : 0 <= K) (hD : 0 <= D)
    (hCe : forall s, ∑ i in s, ‖e i‖ ^ p.toReal <= C) (hDf : forall i, ‖f i‖ <= D) (s : Finset ι) :
    ∑ i in s, ‖B i (e i) (f i)‖ ^ p.toReal <= (K * D) ^ p.toReal * C :=
  holder_top_left_bound (B · |>.flip) (by simpa) hK hD hDf hCe s

/--
lemma `holder_gen_bound` / 引理 `holder_gen_bound`

English:
lemma holder_gen_bound
  statement: {e : (i : ι) -> E i} {f : (i : ι) -> F i}
  proof: by
  have hpqr := hpqr.toReal r hp hq
  have hr := hpqr.pos'
  suffices ∑ i in s, (‖e i‖ * ‖f i‖) ^ r.toReal <=
      C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) from calc
    ∑ i in s, ‖B i (e i) (f i)‖ ^ r.toReal
    _ <= K ^ r.toReal * ∑ i in s, (‖e i‖ * ‖f i‖) ^ r.toReal := by
      rw

中文:
引理 holder_gen_bound
  结论: {e : (i : ι) -> E i} {f : (i : ι) -> F i}
  证明: by
  have hpqr := hpqr.toReal r hp hq
  have hr := hpqr.pos'
  suffices ∑ i in s, (‖e i‖ * ‖f i‖) ^ r.toReal <=
      C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) from calc
    ∑ i in s, ‖B i (e i) (f i)‖ ^ r.toReal
    _ <= K ^ r.toReal * ∑ i in s, (‖e i‖ * ‖f i‖) ^ r.toReal := by
      rw

Depends on / 依赖: Real.mul_rpow, hpqr.pos, hpqr.toReal, le_of_opNorm_le, mul_assoc, mul_rpow, mul_sum, p.toReal, q.toReal, r.toReal, s.mul_sum, toReal
-/
lemma holder_gen_bound {e : (i : ι) -> E i} {f : (i : ι) -> F i}
    (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K C D : Real} (hBK : forall i, ‖B i‖ <= K)
    (hK : 0 <= K) (hC : 0 <= C) (hCe : forall s, ∑ i in s, ‖e i‖ ^ p.toReal <= C)
    (hDf : forall s, ∑ i in s, ‖f i‖ ^ q.toReal <= D) (s : Finset ι) :
    ∑ i in s, ‖B i (e i) (f i)‖ ^ r.toReal <=
      K ^ r.toReal * C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) := by
  have hpqr := hpqr.toReal r hp hq
  have hr := hpqr.pos'
  suffices ∑ i in s, (‖e i‖ * ‖f i‖) ^ r.toReal <=
      C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) from calc
    ∑ i in s, ‖B i (e i) (f i)‖ ^ r.toReal
    _ <= K ^ r.toReal * ∑ i in s, (‖e i‖ * ‖f i‖) ^ r.toReal := by
      rw [s.mul_sum]
      gcongr with i hi
      rw [← Real.mul_rpow (by positivity) (by positivity)]; rw [← mul_assoc]
      gcongr
      exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le (hBK i) _) _
    _ <= _ := by
      rw [mul_assoc]
      gcongr
  calc
    _ <= (∑ i in s, ‖e i‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
        (∑ i in s, ‖f i‖ ^ q.toReal) ^ (r.toReal / q.toReal) := by
      apply Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s hpqr <;> (intros; positivity)
    _ <= _ := by
      gcongr
      · exact hCe s
      · exact hDf s

/--
lemma `holder` / 引理 `holder`

English:
lemma holder
  statement: {e : (i : ι) -> E i} {f : (i : ι) -> F i} (he : Memℓp e p) (hf : Memℓp f q)
  proof: by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
.trans hBK _ have hK : 0 <= K := norm_nonneg (B (Classical.arbitrary ι))
  have hpqr' := hpqr.inv_eq
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_all only [ENNReal.inv_zero, top_add, inv_eq_top]
    exact he.bilin_of_zero_left B
  · 

中文:
引理 holder
  结论: {e : (i : ι) -> E i} {f : (i : ι) -> F i} (he : Memℓp e p) (hf : Memℓp f q)
  证明: by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
.trans hBK _ have hK : 0 <= K := norm_nonneg (B (Classical.arbitrary ι))
  have hpqr' := hpqr.inv_eq
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_all only [ENNReal.inv_zero, top_add, inv_eq_top]
    exact he.bilin_of_zero_left B
  · 

Depends on / 依赖: Classical, Classical.arbitrary, ENNReal, ENNReal.inv_zero, add_top, arbitrary, bilin_of_top_left, bilin_of_zero_left, bilin_of_zero_right, he.bilin_of_top_left, he.bilin_of_zero_left, hf.bilin_of_zero_right, hpqr.inv_eq, inv_eq, inv_eq_top, inv_inj, inv_top, inv_zero, isEmpty_or_nonempty, norm_nonneg
-/
lemma holder {e : (i : ι) -> E i} {f : (i : ι) -> F i} (he : Memℓp e p) (hf : Memℓp f q)
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K) :
    Memℓp (fun i => B i (e i) (f i)) r := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
.trans hBK _ have hK : 0 <= K := norm_nonneg (B (Classical.arbitrary ι))
  have hpqr' := hpqr.inv_eq
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_all only [ENNReal.inv_zero, top_add, inv_eq_top]
    exact he.bilin_of_zero_left B
  · simp_all only [inv_top, zero_add, inv_inj]
    exact he.bilin_of_top_left B hBK hf
  obtain (rfl | rfl | hq) := q.trichotomy
  · simp_all only [ENNReal.inv_zero, add_top, inv_eq_top]
    exact hf.bilin_of_zero_right B
  · simp_all only [inv_top, add_zero, inv_inj]
    exact he.bilin_of_top_right B hBK hf
.mp he obtain ⟨C, hC, hCe⟩ := memℓp_gen_iff'' hp
.mp hf obtain ⟨D, hD, hDf⟩ := memℓp_gen_iff'' hq
exact memℓp_gen' holder_gen_bound r hp hq B hBK hK hC hCe hDf

end Memℓp

namespace lp

/-- The map between `lp` spaces satisfying `ENNReal.HolderTriple` induced by a
uniformly bounded family of continuous bilinear maps on the underlying spaces. -/
@[simps]
/--
Definition of `holder` / `holder` 的定义

English:
definition holder
  signature: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K)
  body: fun i => B i (e i) (f i)
  property := (lp.memℓp e).holder _ (lp.memℓp f) B hBK

中文:
定义 holder
  签名: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : 实数} (hBK : 对任意 i, ‖B i‖ <= K)
  定义体: fun i => B i (e i) (f i)
  property := (lp.memℓp e).holder _ (lp.memℓp f) B hBK
-/
def holder (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K)
    (e : lp E p) (f : lp F q) :
    lp G r where
  val := fun i => B i (e i) (f i)
  property := (lp.memℓp e).holder _ (lp.memℓp f) B hBK

/-- `lp.holder` as a bilinear map. -/
@[simps!]
/--
Definition of `holderₗ` / `holderₗ` 的定义

English:
definition holderₗ
  signature: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K)
  body: .mk₂ 𝕜 (holder r B hBK) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

中文:
定义 holderₗ
  签名: (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : 实数} (hBK : 对任意 i, ‖B i‖ <= K)
  定义体: .mk₂ 𝕜 (holder r B hBK) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

Depends on / 依赖: all_goals, finally, holder, intros
-/
noncomputable def holderₗ (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K) :
    lp E p ->ₗ[𝕜] lp F q ->ₗ[𝕜] lp G r :=
  .mk₂ 𝕜 (holder r B hBK) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

/--
Definition of `holderL` / `holderL` 的定义

English:
definition holderL
  signature: [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]
  body: .mkContinuous₂ K fun e f => by holderₗ r B hBK
    obtain ⟨(rfl | hp), (rfl | hq)⟩ := And.intro p.dichotomy q.dichotomy
    · obtain rfl : r = ⊤ := ENNReal.HolderTriple.unique ∞ ∞ r ∞
      refine norm_le_of_forall_le (by positivity) fun i => ?_
      refine (B i).le_of_opNorm₂_le_of_le (hBK i) ?_ ?

中文:
定义 holderL
  签名: [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]
  定义体: .mkContinuous₂ K fun e f => by holderₗ r B hBK
    obtain ⟨(rfl | hp), (rfl | hq)⟩ := And.intro p.dichotomy q.dichotomy
    · obtain rfl : r = ⊤ := ENNReal.HolderTriple.unique ∞ ∞ r ∞
      refine norm_le_of_forall_le (by positivity) fun i => ?_
      refine (B i).le_of_opNorm₂_le_of_le (hBK i) ?_ ?

Depends on / 依赖: And.intro, ENNReal, ENNReal.HolderTriple.unique, HolderTriple, Real.mul_rpow, all_goals, dichotomy, mul_rpow, norm_apply_le_norm, norm_le_of_forall_le, norm_le_of_forall_sum_le, p.dichotomy, q.dichotomy, trans_le, unique, zero_lt_one, zero_lt_one.trans_le
-/
noncomputable def holderL [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) :
    lp E p ->L[𝕜] lp F q ->L[𝕜] lp G r :=
.mkContinuous₂ K fun e f => by holderₗ r B hBK
    obtain ⟨(rfl | hp), (rfl | hq)⟩ := And.intro p.dichotomy q.dichotomy
    · obtain rfl : r = ⊤ := ENNReal.HolderTriple.unique ∞ ∞ r ∞
      refine norm_le_of_forall_le (by positivity) fun i => ?_
      refine (B i).le_of_opNorm₂_le_of_le (hBK i) ?_ ?_
      all_goals exact norm_apply_le_norm (by simp) ..
    · obtain rfl : r = q := ENNReal.HolderTriple.unique ∞ q r q
      refine norm_le_of_forall_sum_le (zero_lt_one.trans_le hq) (by positivity) fun s => ?_
      rw [Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_left_bound B hBK
        (by positivity) (by positivity) (norm_apply_le_norm (by simp) _) ?_ s
      exact sum_rpow_le_norm_rpow (zero_lt_one.trans_le hq) f
    · obtain rfl : r = p := ENNReal.HolderTriple.unique p ∞ r p
      refine norm_le_of_forall_sum_le (zero_lt_one.trans_le hp) (by positivity) fun s => ?_
      rw [mul_right_comm]; rw [Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_right_bound B hBK
        (by positivity) (by positivity) ?_ (norm_apply_le_norm (by simp) _) s
      exact sum_rpow_le_norm_rpow (zero_lt_one.trans_le hp) e
    · have hpqr := hpqr.toReal r (zero_lt_one.trans_le hp) (zero_lt_one.trans_le hq)
      have hp := hpqr.pos
      have hq := hpqr.symm.pos
      refine norm_le_of_forall_sum_le hpqr.pos' (by positivity) fun s => ?_
      simp only [holderₗ_apply_apply_coe]
      calc
        _ <= K ^ r.toReal * (‖e‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
          (‖f‖ ^ q.toReal) ^ (r.toReal / q.toReal) :=
          Memℓp.holder_gen_bound r hp hq B hBK (by positivity) (by positivity)
            (sum_rpow_le_norm_rpow hp e) (sum_rpow_le_norm_rpow hq f) s
        _ <= _ := by
          rw [← Real.rpow_mul]; rw [← Real.rpow_mul]
          · simp only [← mul_div_assoc, ne_eq, hp.ne', not_false_eq_true, mul_div_cancel_left₀,
            hq.ne', fieldLe]
            rw [Real.mul_rpow]; rw [Real.mul_rpow]
            all_goals positivity
          all_goals positivity

/--
lemma `norm_holderL_le` / 引理 `norm_holderL_le`

English:
lemma norm_holderL_le
  statement: [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]
  proof: LinearMap.mkContinuous₂_norm_le _ K.2 _

中文:
引理 norm_holderL_le
  结论: [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]
  证明: LinearMap.mkContinuous₂_norm_le _ K.2 _
-/
lemma norm_holderL_le [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) :
    ‖holderL (p := p) (q := q) r B hBK‖ <= K :=
  LinearMap.mkContinuous₂_norm_le _ K.2 _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

variable (p q) in
/--
Definition of `dualPairing` / `dualPairing` 的定义

English:
definition dualPairing
  signature: [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
  body: (tsumCLM 𝕜 ι H |>.postcomp <| lp F q) ∘L (holderL 1 B hBK)

中文:
定义 dualPairing
  签名: [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
  定义体: (tsumCLM 𝕜 ι H |>.postcomp <| lp F q) ∘L (holderL 1 B hBK)

Depends on / 依赖: holderL, postcomp, tsumCLM
-/
noncomputable def dualPairing [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) :
    lp E p ->L[𝕜] lp F q ->L[𝕜] H :=
  (tsumCLM 𝕜 ι H |>.postcomp <| lp F q) ∘L (holderL 1 B hBK)

/--
lemma `dualPairing_apply` / 引理 `dualPairing_apply`

English:
lemma dualPairing_apply
  statement: [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
  proof: rfl

中文:
引理 dualPairing_apply
  结论: [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
  证明: rfl
-/
lemma dualPairing_apply [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K)
    (e : lp E p) (f : lp F q) :
    dualPairing p q B hBK e f = ∑' i, B i (e i) (f i) :=
  rfl

/--
lemma `norm_dualPairing` / 引理 `norm_dualPairing`

English:
lemma norm_dualPairing
  statement: [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
  proof: calc
  ‖dualPairing p q B hBK‖
  _ <= ‖(tsumCLM 𝕜 ι H).postcomp (lp F q)‖ * ‖holderL 1 B hBK‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  _ <= 1 * K := by
    gcongr
.trans norm_tsumCLM_le · exact ContinuousLinearMap.norm_postcomp_le _
    · exact norm_holderL_le 1 B hBK
  _ = K := one_mul _

中文:
引理 norm_dualPairing
  结论: [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
  证明: calc
  ‖dualPairing p q B hBK‖
  _ <= ‖(tsumCLM 𝕜 ι H).postcomp (lp F q)‖ * ‖holderL 1 B hBK‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  _ <= 1 * K := by
    gcongr
.trans norm_tsumCLM_le · exact ContinuousLinearMap.norm_postcomp_le _
    · exact norm_holderL_le 1 B hBK
  _ = K := one_mul _
-/
lemma norm_dualPairing [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q]
    (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) :
    ‖dualPairing p q B hBK‖ <= K := calc
  ‖dualPairing p q B hBK‖
  _ <= ‖(tsumCLM 𝕜 ι H).postcomp (lp F q)‖ * ‖holderL 1 B hBK‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  _ <= 1 * K := by
    gcongr
.trans norm_tsumCLM_le · exact ContinuousLinearMap.norm_postcomp_le _
    · exact norm_holderL_le 1 B hBK
  _ = K := one_mul _

end lp
