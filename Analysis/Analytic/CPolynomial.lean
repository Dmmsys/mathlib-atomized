/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.CPolynomialDef

/-! # Properties of continuously polynomial functions

We expand the API around continuously polynomial functions. Notably, we show that this class is
stable under the usual operations (addition, subtraction, negation).

We also prove that continuous multilinear maps are continuously polynomial, and so
are continuous linear maps into continuous multilinear maps. In particular, such maps are
analytic.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology
open Set Filter Asymptotics NNReal ENNReal

variable {f g : E -> F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : Real>=0∞} {n m : Nat}

/--
theorem `hasFiniteFPowerSeriesOnBall_const` / 定理 `hasFiniteFPowerSeriesOnBall_const`

English:
theorem hasFiniteFPowerSeriesOnBall_const
  given: {c : F} {e : E}
  proof: ⟨hasFPowerSeriesOnBall_const,
    fun _ hn => constFormalMultilinearSeries_apply_of_nonzero (Nat.ne_zero_of_lt hn)⟩

中文:
定理 hasFiniteFPowerSeriesOnBall_const
  条件: {c : F} {e : E}
  证明: ⟨hasFPowerSeriesOnBall_const,
    fun _ hn => constFormalMultilinearSeries_apply_of_nonzero (Nat.ne_zero_of_lt hn)⟩

Depends on / 依赖: Nat.ne_zero_of_lt, constFormalMultilinearSeries_apply_of_nonzero, hasFPowerSeriesOnBall_const, ne_zero_of_lt
-/
theorem hasFiniteFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFiniteFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 ⊤ :=
  ⟨hasFPowerSeriesOnBall_const,
    fun _ hn => constFormalMultilinearSeries_apply_of_nonzero (Nat.ne_zero_of_lt hn)⟩

/--
theorem `hasFiniteFPowerSeriesAt_const` / 定理 `hasFiniteFPowerSeriesAt_const`

English:
theorem hasFiniteFPowerSeriesAt_const
  given: {c : F} {e : E}
  proof: ⟨⊤, hasFiniteFPowerSeriesOnBall_const⟩

中文:
定理 hasFiniteFPowerSeriesAt_const
  条件: {c : F} {e : E}
  证明: ⟨⊤, hasFiniteFPowerSeriesOnBall_const⟩

Depends on / 依赖: hasFiniteFPowerSeriesOnBall_const
-/
theorem hasFiniteFPowerSeriesAt_const {c : F} {e : E} :
    HasFiniteFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 :=
  ⟨⊤, hasFiniteFPowerSeriesOnBall_const⟩

/--
theorem `CPolynomialAt_const` / 定理 `CPolynomialAt_const`

English:
theorem CPolynomialAt_const
  given: {v : F}
  statement: CPolynomialAt 𝕜 (fun _ => v) x
  proof: ⟨constFormalMultilinearSeries 𝕜 E v, 1, hasFiniteFPowerSeriesAt_const⟩

中文:
定理 CPolynomialAt_const
  条件: {v : F}
  结论: CPolynomialAt 𝕜 (fun _ => v) x
  证明: ⟨constFormalMultilinearSeries 𝕜 E v, 1, hasFiniteFPowerSeriesAt_const⟩

Depends on / 依赖: constFormalMultilinearSeries, hasFiniteFPowerSeriesAt_const
-/
theorem CPolynomialAt_const {v : F} : CPolynomialAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, 1, hasFiniteFPowerSeriesAt_const⟩

/--
theorem `CPolynomialOn_const` / 定理 `CPolynomialOn_const`

English:
theorem CPolynomialOn_const
  given: {v : F} {s : Set E}
  statement: CPolynomialOn 𝕜 (fun _ => v) s
  proof: fun _ _ => CPolynomialAt_const

中文:
定理 CPolynomialOn_const
  条件: {v : F} {s : 集合 E}
  结论: CPolynomialOn 𝕜 (fun _ => v) s
  证明: fun _ _ => CPolynomialAt_const

Depends on / 依赖: CPolynomialAt_const
-/
theorem CPolynomialOn_const {v : F} {s : Set E} : CPolynomialOn 𝕜 (fun _ => v) s :=
  fun _ _ => CPolynomialAt_const

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasFiniteFPowerSeriesOnBall.add` / 定理 `HasFiniteFPowerSeriesOnBall.add`

English:
theorem HasFiniteFPowerSeriesOnBall.add
  statement: (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
  proof: ⟨hf.1.add hg.1, fun N hN => by
    rw [Pi.add_apply]; rw [hf.finite _ ((le_max_left n m).trans hN)]; rw [hg.finite _ ((le_max_right n m).trans hN)]; rw [zero_add]⟩

中文:
定理 有FiniteFPowerSeriesOnBall.add
  结论: (hf : 有FiniteFPowerSeriesOnBall f pf x n r)
  证明: ⟨hf.1.add hg.1, fun N hN => by
    rw [Pi.add_apply]; rw [hf.finite _ ((le_max_left n m).trans hN)]; rw [hg.finite _ ((le_max_right n m).trans hN)]; rw [zero_add]⟩

Depends on / 依赖: Pi.add_apply, add_apply, finite, hf.finite, hg.finite, le_max_left, le_max_right, zero_add
-/
theorem HasFiniteFPowerSeriesOnBall.add (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f + g) (pf + pg) x (max n m) r :=
  ⟨hf.1.add hg.1, fun N hN => by
    rw [Pi.add_apply]; rw [hf.finite _ ((le_max_left n m).trans hN)]; rw [hg.finite _ ((le_max_right n m).trans hN)]; rw [zero_add]⟩

/--
theorem `HasFiniteFPowerSeriesAt.add` / 定理 `HasFiniteFPowerSeriesAt.add`

English:
theorem HasFiniteFPowerSeriesAt.add
  statement: (hf : HasFiniteFPowerSeriesAt f pf x n)
  proof: by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

中文:
定理 HasFiniteFPowerSeriesAt.add
  结论: (hf : HasFiniteFPowerSeriesAt f pf x n)
  证明: by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

Depends on / 依赖: eventually, hf.eventually.and, hg.eventually
-/
theorem HasFiniteFPowerSeriesAt.add (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

/--
theorem `CPolynomialAt.add` / 定理 `CPolynomialAt.add`

English:
theorem CPolynomialAt.add
  given: (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x)
  proof: let ⟨_, _, hpf⟩ := hf
  let ⟨_, _, hqf⟩ := hg
  (hpf.add hqf).cpolynomialAt

中文:
定理 CPolynomialAt.add
  条件: (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x)
  证明: let ⟨_, _, hpf⟩ := hf
  let ⟨_, _, hqf⟩ := hg
  (hpf.add hqf).cpolynomialAt

Depends on / 依赖: cpolynomialAt, hpf.add
-/
theorem CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f + g) x :=
  let ⟨_, _, hpf⟩ := hf
  let ⟨_, _, hqf⟩ := hg
  (hpf.add hqf).cpolynomialAt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasFiniteFPowerSeriesOnBall.neg` / 定理 `HasFiniteFPowerSeriesOnBall.neg`

English:
theorem HasFiniteFPowerSeriesOnBall.neg
  given: (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
  proof: ⟨hf.1.neg, fun m hm => by rw [Pi.neg_apply, hf.finite m hm, neg_zero]⟩

中文:
定理 有FiniteFPowerSeriesOnBall.neg
  条件: (hf : 有FiniteFPowerSeriesOnBall f pf x n r)
  证明: ⟨hf.1.neg, fun m hm => by rw [Pi.neg_apply, hf.finite m hm, neg_zero]⟩

Depends on / 依赖: Pi.neg_apply, finite, hf.finite, neg_apply, neg_zero
-/
theorem HasFiniteFPowerSeriesOnBall.neg (hf : HasFiniteFPowerSeriesOnBall f pf x n r) :
    HasFiniteFPowerSeriesOnBall (-f) (-pf) x n r :=
  ⟨hf.1.neg, fun m hm => by rw [Pi.neg_apply, hf.finite m hm, neg_zero]⟩

/--
theorem `HasFiniteFPowerSeriesAt.neg` / 定理 `HasFiniteFPowerSeriesAt.neg`

English:
theorem HasFiniteFPowerSeriesAt.neg
  given: (hf : HasFiniteFPowerSeriesAt f pf x n)
  proof: let ⟨_, hrf⟩ := hf
  hrf.neg.hasFiniteFPowerSeriesAt

中文:
定理 HasFiniteFPowerSeriesAt.neg
  条件: (hf : HasFiniteFPowerSeriesAt f pf x n)
  证明: let ⟨_, hrf⟩ := hf
  hrf.neg.hasFiniteFPowerSeriesAt

Depends on / 依赖: hasFiniteFPowerSeriesAt, hrf.neg.hasFiniteFPowerSeriesAt
-/
theorem HasFiniteFPowerSeriesAt.neg (hf : HasFiniteFPowerSeriesAt f pf x n) :
    HasFiniteFPowerSeriesAt (-f) (-pf) x n :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFiniteFPowerSeriesAt

/--
theorem `CPolynomialAt.neg` / 定理 `CPolynomialAt.neg`

English:
theorem CPolynomialAt.neg
  given: (hf : CPolynomialAt 𝕜 f x)
  statement: CPolynomialAt 𝕜 (-f) x
  proof: let ⟨_, _, hpf⟩ := hf
  hpf.neg.cpolynomialAt

中文:
定理 CPolynomialAt.neg
  条件: (hf : CPolynomialAt 𝕜 f x)
  结论: CPolynomialAt 𝕜 (-f) x
  证明: let ⟨_, _, hpf⟩ := hf
  hpf.neg.cpolynomialAt

Depends on / 依赖: cpolynomialAt, hpf.neg.cpolynomialAt
-/
theorem CPolynomialAt.neg (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (-f) x :=
  let ⟨_, _, hpf⟩ := hf
  hpf.neg.cpolynomialAt

/--
theorem `HasFiniteFPowerSeriesOnBall.sub` / 定理 `HasFiniteFPowerSeriesOnBall.sub`

English:
theorem HasFiniteFPowerSeriesOnBall.sub
  statement: (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 有FiniteFPowerSeriesOnBall.sub
  结论: (hf : 有FiniteFPowerSeriesOnBall f pf x n r)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFiniteFPowerSeriesOnBall.sub (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f - g) (pf - pg) x (max n m) r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `HasFiniteFPowerSeriesAt.sub` / 定理 `HasFiniteFPowerSeriesAt.sub`

English:
theorem HasFiniteFPowerSeriesAt.sub
  statement: (hf : HasFiniteFPowerSeriesAt f pf x n)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 HasFiniteFPowerSeriesAt.sub
  结论: (hf : HasFiniteFPowerSeriesAt f pf x n)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFiniteFPowerSeriesAt.sub (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f - g) (pf - pg) x (max n m) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `CPolynomialAt.sub` / 定理 `CPolynomialAt.sub`

English:
theorem CPolynomialAt.sub
  given: (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 CPolynomialAt.sub
  条件: (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `CPolynomialOn.add` / 定理 `CPolynomialOn.add`

English:
theorem CPolynomialOn.add
  given: {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s)
  proof: fun z hz => (hf z hz).add (hg z hz)

中文:
定理 CPolynomialOn.add
  条件: {s : 集合 E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s)
  证明: fun z hz => (hf z hz).add (hg z hz)
-/
theorem CPolynomialOn.add {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

/--
theorem `CPolynomialOn.sub` / 定理 `CPolynomialOn.sub`

English:
theorem CPolynomialOn.sub
  given: {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s)
  proof: fun z hz => (hf z hz).sub (hg z hz)

中文:
定理 CPolynomialOn.sub
  条件: {s : 集合 E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s)
  证明: fun z hz => (hf z hz).sub (hg z hz)
-/
theorem CPolynomialOn.sub {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)


/-!
### Continuous multilinear maps

We show that continuous multilinear maps are continuously polynomial, and therefore analytic.
-/

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em : ι -> Type*} [forall i, NormedAddCommGroup (Em i)] [forall i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em F) {x : Π i, Em i} {s : Set (Π i, Em i)}

open FormalMultilinearSeries

/--
theorem `hasFiniteFPowerSeriesOnBall` / 定理 `hasFiniteFPowerSeriesOnBall`

English:
theorem hasFiniteFPowerSeriesOnBall
  proof: .mk' (fun _ hm => dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ => by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _)]; rw [zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl

中文:
定理 hasFiniteFPowerSeriesOnBall
  证明: .mk' (fun _ hm => dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ => by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _)]; rw [zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl
-/
protected theorem hasFiniteFPowerSeriesOnBall :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 (Fintype.card ι + 1) ⊤ :=
  .mk' (fun _ hm => dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ => by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _)]; rw [zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl

/--
lemma `cpolynomialAt` / 引理 `cpolynomialAt`

English:
lemma cpolynomialAt
  statement: CPolynomialAt 𝕜 f x
  proof: f.hasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

中文:
引理 cpolynomialAt
  结论: CPolynomialAt 𝕜 f x
  证明: f.hasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

Depends on / 依赖: Metric, Metric.eball_top, Set.mem_univ, cpolynomialAt_of_mem, eball_top, f.hasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem, hasFiniteFPowerSeriesOnBall, mem_univ
-/
lemma cpolynomialAt : CPolynomialAt 𝕜 f x :=
  f.hasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

/--
lemma `cpolynomialOn` / 引理 `cpolynomialOn`

English:
lemma cpolynomialOn
  statement: CPolynomialOn 𝕜 f s
  proof: fun _ _ => f.cpolynomialAt

中文:
引理 cpolynomialOn
  结论: CPolynomialOn 𝕜 f s
  证明: fun _ _ => f.cpolynomialAt

Depends on / 依赖: cpolynomialAt, f.cpolynomialAt
-/
lemma cpolynomialOn : CPolynomialOn 𝕜 f s := fun _ _ => f.cpolynomialAt

/--
lemma `analyticOnNhd` / 引理 `analyticOnNhd`

English:
lemma analyticOnNhd
  statement: AnalyticOnNhd 𝕜 f s
  proof: f.cpolynomialOn.analyticOnNhd

中文:
引理 analyticOnNhd
  结论: AnalyticOnNhd 𝕜 f s
  证明: f.cpolynomialOn.analyticOnNhd

Depends on / 依赖: analyticOnNhd, cpolynomialOn, f.cpolynomialOn.analyticOnNhd
-/
lemma analyticOnNhd : AnalyticOnNhd 𝕜 f s := f.cpolynomialOn.analyticOnNhd

/--
lemma `analyticOn` / 引理 `analyticOn`

English:
lemma analyticOn
  statement: AnalyticOn 𝕜 f s
  proof: f.analyticOnNhd.analyticOn

中文:
引理 analyticOn
  结论: AnalyticOn 𝕜 f s
  证明: f.analyticOnNhd.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd, f.analyticOnNhd.analyticOn
-/
lemma analyticOn : AnalyticOn 𝕜 f s := f.analyticOnNhd.analyticOn

/--
lemma `analyticAt` / 引理 `analyticAt`

English:
lemma analyticAt
  statement: AnalyticAt 𝕜 f x
  proof: f.cpolynomialAt.analyticAt

中文:
引理 analyticAt
  结论: AnalyticAt 𝕜 f x
  证明: f.cpolynomialAt.analyticAt

Depends on / 依赖: analyticAt, cpolynomialAt, f.cpolynomialAt.analyticAt
-/
lemma analyticAt : AnalyticAt 𝕜 f x := f.cpolynomialAt.analyticAt

/--
lemma `analyticWithinAt` / 引理 `analyticWithinAt`

English:
lemma analyticWithinAt
  statement: AnalyticWithinAt 𝕜 f s x
  proof: f.analyticAt.analyticWithinAt

中文:
引理 analyticWithinAt
  结论: AnalyticWithinAt 𝕜 f s x
  证明: f.analyticAt.analyticWithinAt

Depends on / 依赖: analyticAt, analyticWithinAt, f.analyticAt.analyticWithinAt
-/
lemma analyticWithinAt : AnalyticWithinAt 𝕜 f s x := f.analyticAt.analyticWithinAt

end ContinuousMultilinearMap


/-!
### Continuous linear maps into continuous multilinear maps

We show that a continuous linear map into continuous multilinear maps is continuously polynomial
(as a function of two variables, i.e., uncurried). Therefore, it is also analytic.
-/

namespace ContinuousLinearMap

variable {ι : Type*} {Em : ι -> Type*} [forall i, NormedAddCommGroup (Em i)] [forall i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 Em F)
  {s : Set (G × (Π i, Em i))} {x : G × (Π i, Em i)}

/--
Definition of `toFormalMultilinearSeriesOfMultilinear` / `toFormalMultilinearSeriesOfMultilinear` 的定义

English:
definition toFormalMultilinearSeriesOfMultilinear
  signature: :
  body: fun n => if h : Fintype.card (Option ι) = n then
    (f.continuousMultilinearMapOption).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

中文:
定义 toFormalMultilinearSeriesOfMultilinear
  签名: :
  定义体: fun n => if h : Fintype.card (Option ι) = n then
    (f.continuousMultilinearMapOption).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

Depends on / 依赖: Fintype, Fintype.card, Fintype.equivFinOfCardEq, continuousMultilinearMapOption, domDomCongr, equivFinOfCardEq, f.continuousMultilinearMapOption
-/
noncomputable def toFormalMultilinearSeriesOfMultilinear :
    FormalMultilinearSeries 𝕜 (G × (Π i, Em i)) F :=
  fun n => if h : Fintype.card (Option ι) = n then
    (f.continuousMultilinearMapOption).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

/--
theorem `hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear` / 定理 `hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear`

English:
theorem hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear
  proof: by
  apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
  · intro m hm
    apply dif_neg
    exact Nat.ne_of_lt hm
  · intro y _
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _)]; rw [zero_add]
    · rw [toFormalMultilinearSeriesOfMultilinear, dif_pos rfl]; rfl
    ·

中文:
定理 hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear
  证明: by
  apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
  · intro m hm
    apply dif_neg
    exact Nat.ne_of_lt hm
  · intro y _
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _)]; rw [zero_add]
    · rw [toFormalMultilinearSeriesOfMultilinear, dif_pos rfl]; rfl
    ·
-/
protected theorem hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear :
    HasFiniteFPowerSeriesOnBall (fun (p : G × (Π i, Em i)) => f p.1 p.2)
      f.toFormalMultilinearSeriesOfMultilinear 0 (Fintype.card (Option ι) + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
  · intro m hm
    apply dif_neg
    exact Nat.ne_of_lt hm
  · intro y _
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _)]; rw [zero_add]
    · rw [toFormalMultilinearSeriesOfMultilinear, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeriesOfMultilinear, dif_neg ne.symm]; rfl

/--
lemma `cpolynomialAt_uncurry_of_multilinear` / 引理 `cpolynomialAt_uncurry_of_multilinear`

English:
lemma cpolynomialAt_uncurry_of_multilinear
  proof: f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

中文:
引理 cpolynomialAt_uncurry_of_multilinear
  证明: f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

Depends on / 依赖: Metric, Metric.eball_top, Set.mem_univ, cpolynomialAt_of_mem, eball_top, f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cpolynomialAt_of_mem, hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear, mem_univ
-/
lemma cpolynomialAt_uncurry_of_multilinear :
    CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) x :=
  f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

/--
lemma `cpolynomialOn_uncurry_of_multilinear` / 引理 `cpolynomialOn_uncurry_of_multilinear`

English:
lemma cpolynomialOn_uncurry_of_multilinear
  proof: fun _ _ => f.cpolynomialAt_uncurry_of_multilinear

中文:
引理 cpolynomialOn_uncurry_of_multilinear
  证明: fun _ _ => f.cpolynomialAt_uncurry_of_multilinear

Depends on / 依赖: cpolynomialAt_uncurry_of_multilinear, f.cpolynomialAt_uncurry_of_multilinear
-/
lemma cpolynomialOn_uncurry_of_multilinear :
    CPolynomialOn 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) s :=
  fun _ _ => f.cpolynomialAt_uncurry_of_multilinear

/--
lemma `analyticOnNhd_uncurry_of_multilinear` / 引理 `analyticOnNhd_uncurry_of_multilinear`

English:
lemma analyticOnNhd_uncurry_of_multilinear
  proof: f.cpolynomialOn_uncurry_of_multilinear.analyticOnNhd

中文:
引理 analyticOnNhd_uncurry_of_multilinear
  证明: f.cpolynomialOn_uncurry_of_multilinear.analyticOnNhd

Depends on / 依赖: analyticOnNhd, cpolynomialOn_uncurry_of_multilinear, f.cpolynomialOn_uncurry_of_multilinear.analyticOnNhd
-/
lemma analyticOnNhd_uncurry_of_multilinear :
    AnalyticOnNhd 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) s :=
  f.cpolynomialOn_uncurry_of_multilinear.analyticOnNhd

/--
lemma `analyticOn_uncurry_of_multilinear` / 引理 `analyticOn_uncurry_of_multilinear`

English:
lemma analyticOn_uncurry_of_multilinear
  proof: f.analyticOnNhd_uncurry_of_multilinear.analyticOn

中文:
引理 analyticOn_uncurry_of_multilinear
  证明: f.analyticOnNhd_uncurry_of_multilinear.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_uncurry_of_multilinear, f.analyticOnNhd_uncurry_of_multilinear.analyticOn
-/
lemma analyticOn_uncurry_of_multilinear :
    AnalyticOn 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_multilinear.analyticOn

/--
lemma `analyticAt_uncurry_of_multilinear` / 引理 `analyticAt_uncurry_of_multilinear`

English:
lemma analyticAt_uncurry_of_multilinear
  statement: AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) x
  proof: f.cpolynomialAt_uncurry_of_multilinear.analyticAt

中文:
引理 analyticAt_uncurry_of_multilinear
  结论: AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) x
  证明: f.cpolynomialAt_uncurry_of_multilinear.analyticAt

Depends on / 依赖: analyticAt, cpolynomialAt_uncurry_of_multilinear, f.cpolynomialAt_uncurry_of_multilinear.analyticAt
-/
lemma analyticAt_uncurry_of_multilinear : AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_multilinear.analyticAt

/--
lemma `analyticWithinAt_uncurry_of_multilinear` / 引理 `analyticWithinAt_uncurry_of_multilinear`

English:
lemma analyticWithinAt_uncurry_of_multilinear
  proof: f.analyticAt_uncurry_of_multilinear.analyticWithinAt

中文:
引理 analyticWithinAt_uncurry_of_multilinear
  证明: f.analyticAt_uncurry_of_multilinear.analyticWithinAt

Depends on / 依赖: analyticAt_uncurry_of_multilinear, analyticWithinAt, f.analyticAt_uncurry_of_multilinear.analyticWithinAt
-/
lemma analyticWithinAt_uncurry_of_multilinear :
    AnalyticWithinAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_multilinear.analyticWithinAt

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em Fm : ι -> Type*}
  [forall i, NormedAddCommGroup (Em i)] [forall i, NormedSpace 𝕜 (Em i)]
  [forall i, NormedAddCommGroup (Fm i)] [forall i, NormedSpace 𝕜 (Fm i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em (G ->L[𝕜] F))
  {s : Set ((Π i, Em i) × G)} {x : (Π i, Em i) × G}

/--
lemma `cpolynomialAt_uncurry_of_linear` / 引理 `cpolynomialAt_uncurry_of_linear`

English:
lemma cpolynomialAt_uncurry_of_linear
  proof: by
  have : CPolynomialAt 𝕜 (ContinuousLinearEquiv.prodComm 𝕜 (Π i, Em i) G).toContinuousLinearMap x :=
    ContinuousLinearMap.cpolynomialAt _ _
  exact f.flipLinear.cpolynomialAt_uncurry_of_multilinear.comp this

中文:
引理 cpolynomialAt_uncurry_of_linear
  证明: by
  have : CPolynomialAt 𝕜 (ContinuousLinearEquiv.prodComm 𝕜 (Π i, Em i) G).toContinuousLinearMap x :=
    ContinuousLinearMap.cpolynomialAt _ _
  exact f.flipLinear.cpolynomialAt_uncurry_of_multilinear.comp this

Depends on / 依赖: CPolynomialAt, ContinuousLinearEquiv, ContinuousLinearEquiv.prodComm, ContinuousLinearMap, ContinuousLinearMap.cpolynomialAt, cpolynomialAt, cpolynomialAt_uncurry_of_multilinear, f.flipLinear.cpolynomialAt_uncurry_of_multilinear.comp, flipLinear, prodComm, toContinuousLinearMap
-/
lemma cpolynomialAt_uncurry_of_linear :
    CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x := by
  have : CPolynomialAt 𝕜 (ContinuousLinearEquiv.prodComm 𝕜 (Π i, Em i) G).toContinuousLinearMap x :=
    ContinuousLinearMap.cpolynomialAt _ _
  exact f.flipLinear.cpolynomialAt_uncurry_of_multilinear.comp this

/--
lemma `cpolyomialOn_uncurry_of_linear` / 引理 `cpolyomialOn_uncurry_of_linear`

English:
lemma cpolyomialOn_uncurry_of_linear
  proof: fun _ _ => f.cpolynomialAt_uncurry_of_linear

中文:
引理 cpolyomialOn_uncurry_of_linear
  证明: fun _ _ => f.cpolynomialAt_uncurry_of_linear

Depends on / 依赖: cpolynomialAt_uncurry_of_linear, f.cpolynomialAt_uncurry_of_linear
-/
lemma cpolyomialOn_uncurry_of_linear :
    CPolynomialOn 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s :=
  fun _ _ => f.cpolynomialAt_uncurry_of_linear

/--
lemma `analyticOnNhd_uncurry_of_linear` / 引理 `analyticOnNhd_uncurry_of_linear`

English:
lemma analyticOnNhd_uncurry_of_linear
  proof: f.cpolyomialOn_uncurry_of_linear.analyticOnNhd

中文:
引理 analyticOnNhd_uncurry_of_linear
  证明: f.cpolyomialOn_uncurry_of_linear.analyticOnNhd

Depends on / 依赖: analyticOnNhd, cpolyomialOn_uncurry_of_linear, f.cpolyomialOn_uncurry_of_linear.analyticOnNhd
-/
lemma analyticOnNhd_uncurry_of_linear :
    AnalyticOnNhd 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s :=
  f.cpolyomialOn_uncurry_of_linear.analyticOnNhd

/--
lemma `analyticOn_uncurry_of_linear` / 引理 `analyticOn_uncurry_of_linear`

English:
lemma analyticOn_uncurry_of_linear
  proof: f.analyticOnNhd_uncurry_of_linear.analyticOn

中文:
引理 analyticOn_uncurry_of_linear
  证明: f.analyticOnNhd_uncurry_of_linear.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_uncurry_of_linear, f.analyticOnNhd_uncurry_of_linear.analyticOn
-/
lemma analyticOn_uncurry_of_linear :
    AnalyticOn 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_linear.analyticOn

/--
lemma `analyticAt_uncurry_of_linear` / 引理 `analyticAt_uncurry_of_linear`

English:
lemma analyticAt_uncurry_of_linear
  statement: AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
  proof: f.cpolynomialAt_uncurry_of_linear.analyticAt

中文:
引理 analyticAt_uncurry_of_linear
  结论: AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
  证明: f.cpolynomialAt_uncurry_of_linear.analyticAt

Depends on / 依赖: analyticAt, cpolynomialAt_uncurry_of_linear, f.cpolynomialAt_uncurry_of_linear.analyticAt
-/
lemma analyticAt_uncurry_of_linear : AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_linear.analyticAt

/--
lemma `analyticWithinAt_uncurry_of_linear` / 引理 `analyticWithinAt_uncurry_of_linear`

English:
lemma analyticWithinAt_uncurry_of_linear
  proof: f.analyticAt_uncurry_of_linear.analyticWithinAt

中文:
引理 analyticWithinAt_uncurry_of_linear
  证明: f.analyticAt_uncurry_of_linear.analyticWithinAt

Depends on / 依赖: analyticAt_uncurry_of_linear, analyticWithinAt, f.analyticAt_uncurry_of_linear.analyticWithinAt
-/
lemma analyticWithinAt_uncurry_of_linear :
    AnalyticWithinAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_linear.analyticWithinAt

variable {t : Set ((Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))}
  {q : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)}

/--
lemma `cpolynomialAt_uncurry_compContinuousLinearMap` / 引理 `cpolynomialAt_uncurry_compContinuousLinearMap`

English:
lemma cpolynomialAt_uncurry_compContinuousLinearMap
  proof: cpolynomialAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

中文:
引理 cpolynomialAt_uncurry_compContinuousLinearMap
  证明: cpolynomialAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, compContinuousLinearMapContinuousMultilinear, cpolynomialAt_uncurry_of_linear
-/
lemma cpolynomialAt_uncurry_compContinuousLinearMap :
    CPolynomialAt 𝕜 (fun (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      => p.2.compContinuousLinearMap p.1) q :=
  cpolynomialAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

/--
lemma `cpolynomialOn_uncurry_compContinuousLinearMap` / 引理 `cpolynomialOn_uncurry_compContinuousLinearMap`

English:
lemma cpolynomialOn_uncurry_compContinuousLinearMap
  proof: cpolyomialOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

中文:
引理 cpolynomialOn_uncurry_compContinuousLinearMap
  证明: cpolyomialOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, compContinuousLinearMapContinuousMultilinear, cpolyomialOn_uncurry_of_linear
-/
lemma cpolynomialOn_uncurry_compContinuousLinearMap :
    CPolynomialOn 𝕜 (fun (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      => p.2.compContinuousLinearMap p.1) t :=
  cpolyomialOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

/--
lemma `analyticOnNhd_uncurry_compContinuousLinearMap` / 引理 `analyticOnNhd_uncurry_compContinuousLinearMap`

English:
lemma analyticOnNhd_uncurry_compContinuousLinearMap
  proof: analyticOnNhd_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

中文:
引理 analyticOnNhd_uncurry_compContinuousLinearMap
  证明: analyticOnNhd_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, analyticOnNhd_uncurry_of_linear, compContinuousLinearMapContinuousMultilinear
-/
lemma analyticOnNhd_uncurry_compContinuousLinearMap :
    AnalyticOnNhd 𝕜 (fun (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      => p.2.compContinuousLinearMap p.1) t :=
  analyticOnNhd_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

/--
lemma `analyticOn_uncurry_compContinuousLinearMap` / 引理 `analyticOn_uncurry_compContinuousLinearMap`

English:
lemma analyticOn_uncurry_compContinuousLinearMap
  proof: analyticOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

中文:
引理 analyticOn_uncurry_compContinuousLinearMap
  证明: analyticOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, analyticOn_uncurry_of_linear, compContinuousLinearMapContinuousMultilinear
-/
lemma analyticOn_uncurry_compContinuousLinearMap :
    AnalyticOn 𝕜 (fun (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      => p.2.compContinuousLinearMap p.1) t :=
  analyticOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

/--
lemma `analyticAt_uncurry_compContinuousLinearMap` / 引理 `analyticAt_uncurry_compContinuousLinearMap`

English:
lemma analyticAt_uncurry_compContinuousLinearMap
  proof: analyticAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

中文:
引理 analyticAt_uncurry_compContinuousLinearMap
  证明: analyticAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, analyticAt_uncurry_of_linear, compContinuousLinearMapContinuousMultilinear
-/
lemma analyticAt_uncurry_compContinuousLinearMap :
    AnalyticAt 𝕜 (fun (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      => p.2.compContinuousLinearMap p.1) q :=
  analyticAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

/--
lemma `analyticWithinAt_uncurry_compContinuousLinearMap` / 引理 `analyticWithinAt_uncurry_compContinuousLinearMap`

English:
lemma analyticWithinAt_uncurry_compContinuousLinearMap
  proof: analyticWithinAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

中文:
引理 analyticWithinAt_uncurry_compContinuousLinearMap
  证明: analyticWithinAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, analyticWithinAt_uncurry_of_linear, compContinuousLinearMapContinuousMultilinear
-/
lemma analyticWithinAt_uncurry_compContinuousLinearMap :
    AnalyticWithinAt 𝕜 (fun (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      => p.2.compContinuousLinearMap p.1) t q :=
  analyticWithinAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

end ContinuousMultilinearMap
