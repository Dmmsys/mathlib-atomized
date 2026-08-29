/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Geoffrey Irving, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Various ways to combine analytic functions

We show that the following are analytic:

1. Cartesian products of analytic functions
2. Arithmetic on analytic functions: `mul`, `smul`, `inv`, `div`
3. Finite sums and products: `Finset.sum`, `Finset.prod`
-/

@[expose] public section

noncomputable section

open scoped Topology Ring
open Filter Asymptotics ENNReal NNReal

variable {α : Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
variable {𝕝 : Type*} [NormedDivisionRing 𝕝] [NormedAlgebra 𝕜 𝕝]


/--
theorem `hasFPowerSeriesOnBall_const` / 定理 `hasFPowerSeriesOnBall_const`

English:
theorem hasFPowerSeriesOnBall_const
  given: {c : F} {e : E}
  proof: by
  refine ⟨by simp, WithTop.top_pos, fun _ => hasSum_single 0 fun n hn => ?_⟩
  simp [constFormalMultilinearSeries_apply_of_nonzero hn]

中文:
定理 hasFPowerSeriesOnBall_const
  条件: {c : F} {e : E}
  证明: by
  refine ⟨by simp, WithTop.top_pos, fun _ => hasSum_single 0 fun n hn => ?_⟩
  simp [constFormalMultilinearSeries_apply_of_nonzero hn]

Depends on / 依赖: WithTop, WithTop.top_pos, constFormalMultilinearSeries_apply_of_nonzero, hasSum_single, top_pos
-/
theorem hasFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤ := by
  refine ⟨by simp, WithTop.top_pos, fun _ => hasSum_single 0 fun n hn => ?_⟩
  simp [constFormalMultilinearSeries_apply_of_nonzero hn]

/--
theorem `hasFPowerSeriesAt_const` / 定理 `hasFPowerSeriesAt_const`

English:
theorem hasFPowerSeriesAt_const
  given: {c : F} {e : E}
  proof: ⟨⊤, hasFPowerSeriesOnBall_const⟩

@[fun_prop]

中文:
定理 hasFPowerSeriesAt_const
  条件: {c : F} {e : E}
  证明: ⟨⊤, hasFPowerSeriesOnBall_const⟩

@[fun_prop]

Depends on / 依赖: hasFPowerSeriesOnBall_const
-/
theorem hasFPowerSeriesAt_const {c : F} {e : E} :
    HasFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e :=
  ⟨⊤, hasFPowerSeriesOnBall_const⟩

@[fun_prop]
/--
theorem `analyticAt_const` / 定理 `analyticAt_const`

English:
theorem analyticAt_const
  given: {v : F} {x : E}
  statement: AnalyticAt 𝕜 (fun _ => v) x
  proof: ⟨constFormalMultilinearSeries 𝕜 E v, hasFPowerSeriesAt_const⟩

中文:
定理 analyticAt_const
  条件: {v : F} {x : E}
  结论: AnalyticAt 𝕜 (fun _ => v) x
  证明: ⟨constFormalMultilinearSeries 𝕜 E v, hasFPowerSeriesAt_const⟩

Depends on / 依赖: constFormalMultilinearSeries, hasFPowerSeriesAt_const
-/
theorem analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, hasFPowerSeriesAt_const⟩

/--
theorem `analyticOnNhd_const` / 定理 `analyticOnNhd_const`

English:
theorem analyticOnNhd_const
  given: {v : F} {s : Set E}
  statement: AnalyticOnNhd 𝕜 (fun _ => v) s
  proof: fun _ _ => analyticAt_const

中文:
定理 analyticOnNhd_const
  条件: {v : F} {s : Set E}
  结论: AnalyticOnNhd 𝕜 (fun _ => v) s
  证明: fun _ _ => analyticAt_const

Depends on / 依赖: analyticAt_const
-/
theorem analyticOnNhd_const {v : F} {s : Set E} : AnalyticOnNhd 𝕜 (fun _ => v) s :=
  fun _ _ => analyticAt_const

/--
theorem `analyticWithinAt_const` / 定理 `analyticWithinAt_const`

English:
theorem analyticWithinAt_const
  given: {v : F} {s : Set E} {x : E}
  statement: AnalyticWithinAt 𝕜 (fun _ => v) s x
  proof: analyticAt_const.analyticWithinAt

中文:
定理 analyticWithinAt_const
  条件: {v : F} {s : Set E} {x : E}
  结论: AnalyticWithinAt 𝕜 (fun _ => v) s x
  证明: analyticAt_const.analyticWithinAt

Depends on / 依赖: analyticAt_const, analyticAt_const.analyticWithinAt, analyticWithinAt
-/
theorem analyticWithinAt_const {v : F} {s : Set E} {x : E} : AnalyticWithinAt 𝕜 (fun _ => v) s x :=
  analyticAt_const.analyticWithinAt

/--
theorem `analyticOn_const` / 定理 `analyticOn_const`

English:
theorem analyticOn_const
  given: {v : F} {s : Set E}
  statement: AnalyticOn 𝕜 (fun _ => v) s
  proof: analyticOnNhd_const.analyticOn

中文:
定理 analyticOn_const
  条件: {v : F} {s : Set E}
  结论: AnalyticOn 𝕜 (fun _ => v) s
  证明: analyticOnNhd_const.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_const, analyticOnNhd_const.analyticOn
-/
theorem analyticOn_const {v : F} {s : Set E} : AnalyticOn 𝕜 (fun _ => v) s :=
  analyticOnNhd_const.analyticOn

/-!
### Addition, negation, subtraction, scalar multiplication
-/

section

variable {f g : E -> F} {pf pg : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : Real>=0∞}
  {R : Type*} [NormedRing R] [Module R F] [IsBoundedSMul R F] [SMulCommClass 𝕜 R F] {c : R}

/--
theorem `HasFPowerSeriesWithinOnBall.add` / 定理 `HasFPowerSeriesWithinOnBall.add`

English:
theorem HasFPowerSeriesWithinOnBall.add
  statement: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  proof: { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).add (hg.hasSum hy h'y) }

中文:
定理 HasFPowerSeriesWithinOnBall.add
  结论: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  证明: { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).add (hg.hasSum hy h'y) }

Depends on / 依赖: hasSum, hf.hasSum, hf.r_le, hf.r_pos, hg.hasSum, hg.r_le, le_min_iff, le_trans, min_radius_le_radius_add, pf.min_radius_le_radius_add, r_le, r_pos
-/
theorem HasFPowerSeriesWithinOnBall.add (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (hg : HasFPowerSeriesWithinOnBall g pg s x r) :
    HasFPowerSeriesWithinOnBall (f + g) (pf + pg) s x r :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).add (hg.hasSum hy h'y) }

/--
theorem `HasFPowerSeriesOnBall.add` / 定理 `HasFPowerSeriesOnBall.add`

English:
theorem HasFPowerSeriesOnBall.add
  statement: (hf : HasFPowerSeriesOnBall f pf x r)
  proof: { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).add (hg.hasSum hy) }

中文:
定理 HasFPowerSeriesOnBall.add
  结论: (hf : HasFPowerSeriesOnBall f pf x r)
  证明: { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).add (hg.hasSum hy) }

Depends on / 依赖: hasSum, hf.hasSum, hf.r_le, hf.r_pos, hg.hasSum, hg.r_le, le_min_iff, le_trans, min_radius_le_radius_add, pf.min_radius_le_radius_add, r_le, r_pos
-/
theorem HasFPowerSeriesOnBall.add (hf : HasFPowerSeriesOnBall f pf x r)
    (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall (f + g) (pf + pg) x r :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).add (hg.hasSum hy) }

/--
theorem `HasFPowerSeriesWithinAt.add` / 定理 `HasFPowerSeriesWithinAt.add`

English:
theorem HasFPowerSeriesWithinAt.add
  proof: by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

中文:
定理 HasFPowerSeriesWithinAt.add
  证明: by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

Depends on / 依赖: eventually, hf.eventually.and, hg.eventually
-/
theorem HasFPowerSeriesWithinAt.add
    (hf : HasFPowerSeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) :
    HasFPowerSeriesWithinAt (f + g) (pf + pg) s x := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

/--
theorem `HasFPowerSeriesAt.add` / 定理 `HasFPowerSeriesAt.add`

English:
theorem HasFPowerSeriesAt.add
  given: (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x)
  proof: by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

中文:
定理 HasFPowerSeriesAt.add
  条件: (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x)
  证明: by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

Depends on / 依赖: eventually, hf.eventually.and, hg.eventually
-/
theorem HasFPowerSeriesAt.add (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x) :
    HasFPowerSeriesAt (f + g) (pf + pg) x := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

/--
theorem `AnalyticWithinAt.add` / 定理 `AnalyticWithinAt.add`

English:
theorem AnalyticWithinAt.add
  given: (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x)
  proof: let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticWithinAt

@[to_fun (attr := fun_prop)]

中文:
定理 AnalyticWithinAt.add
  条件: (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x)
  证明: let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticWithinAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: analyticWithinAt, hpf.add
-/
theorem AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (f + g) s x :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticWithinAt

@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.add` / 定理 `AnalyticAt.add`

English:
theorem AnalyticAt.add
  given: (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
  proof: let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticAt

中文:
定理 AnalyticAt.add
  条件: (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
  证明: let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticAt

Depends on / 依赖: analyticAt, hpf.add
-/
theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (f + g) x :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticAt

/--
theorem `AnalyticOn.add` / 定理 `AnalyticOn.add`

English:
theorem AnalyticOn.add
  given: (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s)
  proof: fun z hz => (hf z hz).add (hg z hz)

中文:
定理 AnalyticOn.add
  条件: (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s)
  证明: fun z hz => (hf z hz).add (hg z hz)
-/
theorem AnalyticOn.add (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

/--
theorem `AnalyticOnNhd.add` / 定理 `AnalyticOnNhd.add`

English:
theorem AnalyticOnNhd.add
  given: (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s)
  proof: fun z hz => (hf z hz).add (hg z hz)

中文:
定理 AnalyticOnNhd.add
  条件: (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s)
  证明: fun z hz => (hf z hz).add (hg z hz)
-/
theorem AnalyticOnNhd.add (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

/--
theorem `HasFPowerSeriesWithinOnBall.neg` / 定理 `HasFPowerSeriesWithinOnBall.neg`

English:
theorem HasFPowerSeriesWithinOnBall.neg
  given: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  proof: { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).neg }

中文:
定理 HasFPowerSeriesWithinOnBall.neg
  条件: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  证明: { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).neg }

Depends on / 依赖: hasSum, hf.hasSum, hf.r_le, hf.r_pos, pf.radius_neg, r_le, r_pos, radius_neg
-/
theorem HasFPowerSeriesWithinOnBall.neg (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (-f) (-pf) s x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).neg }

/--
theorem `HasFPowerSeriesOnBall.neg` / 定理 `HasFPowerSeriesOnBall.neg`

English:
theorem HasFPowerSeriesOnBall.neg
  given: (hf : HasFPowerSeriesOnBall f pf x r)
  proof: { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).neg }

中文:
定理 HasFPowerSeriesOnBall.neg
  条件: (hf : HasFPowerSeriesOnBall f pf x r)
  证明: { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).neg }

Depends on / 依赖: hasSum, hf.hasSum, hf.r_le, hf.r_pos, pf.radius_neg, r_le, r_pos, radius_neg
-/
theorem HasFPowerSeriesOnBall.neg (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (-f) (-pf) x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).neg }

/--
theorem `HasFPowerSeriesWithinAt.neg` / 定理 `HasFPowerSeriesWithinAt.neg`

English:
theorem HasFPowerSeriesWithinAt.neg
  given: (hf : HasFPowerSeriesWithinAt f pf s x)
  proof: let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesWithinAt

中文:
定理 HasFPowerSeriesWithinAt.neg
  条件: (hf : HasFPowerSeriesWithinAt f pf s x)
  证明: let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesWithinAt

Depends on / 依赖: hasFPowerSeriesWithinAt, hrf.neg.hasFPowerSeriesWithinAt
-/
theorem HasFPowerSeriesWithinAt.neg (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (-f) (-pf) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesWithinAt

/--
theorem `HasFPowerSeriesAt.neg` / 定理 `HasFPowerSeriesAt.neg`

English:
theorem HasFPowerSeriesAt.neg
  given: (hf : HasFPowerSeriesAt f pf x)
  statement: HasFPowerSeriesAt (-f) (-pf) x
  proof: let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesAt

中文:
定理 HasFPowerSeriesAt.neg
  条件: (hf : HasFPowerSeriesAt f pf x)
  结论: HasFPowerSeriesAt (-f) (-pf) x
  证明: let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesAt

Depends on / 依赖: hasFPowerSeriesAt, hrf.neg.hasFPowerSeriesAt
-/
theorem HasFPowerSeriesAt.neg (hf : HasFPowerSeriesAt f pf x) : HasFPowerSeriesAt (-f) (-pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesAt

/--
theorem `AnalyticWithinAt.neg` / 定理 `AnalyticWithinAt.neg`

English:
theorem AnalyticWithinAt.neg
  given: (hf : AnalyticWithinAt 𝕜 f s x)
  statement: AnalyticWithinAt 𝕜 (-f) s x
  proof: let ⟨_, hpf⟩ := hf
  hpf.neg.analyticWithinAt

@[to_fun (attr := fun_prop)]

中文:
定理 AnalyticWithinAt.neg
  条件: (hf : AnalyticWithinAt 𝕜 f s x)
  结论: AnalyticWithinAt 𝕜 (-f) s x
  证明: let ⟨_, hpf⟩ := hf
  hpf.neg.analyticWithinAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: analyticWithinAt, hpf.neg.analyticWithinAt
-/
theorem AnalyticWithinAt.neg (hf : AnalyticWithinAt 𝕜 f s x) : AnalyticWithinAt 𝕜 (-f) s x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticWithinAt

@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.neg` / 定理 `AnalyticAt.neg`

English:
theorem AnalyticAt.neg
  given: (hf : AnalyticAt 𝕜 f x)
  statement: AnalyticAt 𝕜 (-f) x
  proof: let ⟨_, hpf⟩ := hf
  hpf.neg.analyticAt

中文:
定理 AnalyticAt.neg
  条件: (hf : AnalyticAt 𝕜 f x)
  结论: AnalyticAt 𝕜 (-f) x
  证明: let ⟨_, hpf⟩ := hf
  hpf.neg.analyticAt

Depends on / 依赖: analyticAt, hpf.neg.analyticAt
-/
theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticAt

/--
lemma `analyticAt_neg` / 引理 `analyticAt_neg`

English:
lemma analyticAt_neg
  statement: AnalyticAt 𝕜 (-f) x ↔ AnalyticAt 𝕜 f x where
  proof: by simpa using hf.neg
  mpr := .neg

中文:
引理 analyticAt_neg
  结论: AnalyticAt 𝕜 (-f) x ↔ AnalyticAt 𝕜 f x where
  证明: by simpa using hf.neg
  mpr := .neg
-/
@[simp] lemma analyticAt_neg : AnalyticAt 𝕜 (-f) x ↔ AnalyticAt 𝕜 f x where
  mp hf := by simpa using hf.neg
  mpr := .neg

/--
theorem `AnalyticOn.neg` / 定理 `AnalyticOn.neg`

English:
theorem AnalyticOn.neg
  given: (hf : AnalyticOn 𝕜 f s)
  statement: AnalyticOn 𝕜 (-f) s
  proof: fun z hz => (hf z hz).neg

中文:
定理 AnalyticOn.neg
  条件: (hf : AnalyticOn 𝕜 f s)
  结论: AnalyticOn 𝕜 (-f) s
  证明: fun z hz => (hf z hz).neg
-/
theorem AnalyticOn.neg (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (-f) s :=
  fun z hz => (hf z hz).neg

/--
theorem `AnalyticOnNhd.neg` / 定理 `AnalyticOnNhd.neg`

English:
theorem AnalyticOnNhd.neg
  given: (hf : AnalyticOnNhd 𝕜 f s)
  statement: AnalyticOnNhd 𝕜 (-f) s
  proof: fun z hz => (hf z hz).neg

中文:
定理 AnalyticOnNhd.neg
  条件: (hf : AnalyticOnNhd 𝕜 f s)
  结论: AnalyticOnNhd 𝕜 (-f) s
  证明: fun z hz => (hf z hz).neg
-/
theorem AnalyticOnNhd.neg (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (-f) s :=
  fun z hz => (hf z hz).neg

/--
theorem `HasFPowerSeriesWithinOnBall.sub` / 定理 `HasFPowerSeriesWithinOnBall.sub`

English:
theorem HasFPowerSeriesWithinOnBall.sub
  statement: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 HasFPowerSeriesWithinOnBall.sub
  结论: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFPowerSeriesWithinOnBall.sub (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (hg : HasFPowerSeriesWithinOnBall g pg s x r) :
    HasFPowerSeriesWithinOnBall (f - g) (pf - pg) s x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `HasFPowerSeriesOnBall.sub` / 定理 `HasFPowerSeriesOnBall.sub`

English:
theorem HasFPowerSeriesOnBall.sub
  statement: (hf : HasFPowerSeriesOnBall f pf x r)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 HasFPowerSeriesOnBall.sub
  结论: (hf : HasFPowerSeriesOnBall f pf x r)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFPowerSeriesOnBall.sub (hf : HasFPowerSeriesOnBall f pf x r)
    (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall (f - g) (pf - pg) x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `HasFPowerSeriesWithinAt.sub` / 定理 `HasFPowerSeriesWithinAt.sub`

English:
theorem HasFPowerSeriesWithinAt.sub
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 HasFPowerSeriesWithinAt.sub
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFPowerSeriesWithinAt.sub
    (hf : HasFPowerSeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) :
    HasFPowerSeriesWithinAt (f - g) (pf - pg) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `HasFPowerSeriesAt.sub` / 定理 `HasFPowerSeriesAt.sub`

English:
theorem HasFPowerSeriesAt.sub
  given: (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 HasFPowerSeriesAt.sub
  条件: (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFPowerSeriesAt.sub (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x) :
    HasFPowerSeriesAt (f - g) (pf - pg) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `AnalyticWithinAt.sub` / 定理 `AnalyticWithinAt.sub`

English:
theorem AnalyticWithinAt.sub
  given: (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]

中文:
定理 AnalyticWithinAt.sub
  条件: (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem AnalyticWithinAt.sub (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (f - g) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.sub` / 定理 `AnalyticAt.sub`

English:
theorem AnalyticAt.sub
  given: (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 AnalyticAt.sub
  条件: (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `AnalyticOn.sub` / 定理 `AnalyticOn.sub`

English:
theorem AnalyticOn.sub
  given: (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s)
  proof: fun z hz => (hf z hz).sub (hg z hz)

中文:
定理 AnalyticOn.sub
  条件: (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s)
  证明: fun z hz => (hf z hz).sub (hg z hz)
-/
theorem AnalyticOn.sub (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)

/--
theorem `AnalyticOnNhd.sub` / 定理 `AnalyticOnNhd.sub`

English:
theorem AnalyticOnNhd.sub
  given: (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s)
  proof: fun z hz => (hf z hz).sub (hg z hz)

中文:
定理 AnalyticOnNhd.sub
  条件: (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s)
  证明: fun z hz => (hf z hz).sub (hg z hz)
-/
theorem AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)

/--
theorem `HasFPowerSeriesWithinOnBall.const_smul` / 定理 `HasFPowerSeriesWithinOnBall.const_smul`

English:
theorem HasFPowerSeriesWithinOnBall.const_smul
  given: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  proof: le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy h'y => (hf.hasSum hy h'y).const_smul _

中文:
定理 HasFPowerSeriesWithinOnBall.const_smul
  条件: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  证明: le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy h'y => (hf.hasSum hy h'y).const_smul _

Depends on / 依赖: hf.r_le, le_trans, pf.radius_le_smul, r_le, radius_le_smul
-/
theorem HasFPowerSeriesWithinOnBall.const_smul (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (c • f) (c • pf) s x r where
  r_le := le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy h'y => (hf.hasSum hy h'y).const_smul _

/--
theorem `HasFPowerSeriesOnBall.const_smul` / 定理 `HasFPowerSeriesOnBall.const_smul`

English:
theorem HasFPowerSeriesOnBall.const_smul
  given: (hf : HasFPowerSeriesOnBall f pf x r)
  proof: le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy => (hf.hasSum hy).const_smul _

中文:
定理 HasFPowerSeriesOnBall.const_smul
  条件: (hf : HasFPowerSeriesOnBall f pf x r)
  证明: le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy => (hf.hasSum hy).const_smul _

Depends on / 依赖: hf.r_le, le_trans, pf.radius_le_smul, r_le, radius_le_smul
-/
theorem HasFPowerSeriesOnBall.const_smul (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (c • f) (c • pf) x r where
  r_le := le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy => (hf.hasSum hy).const_smul _

/--
theorem `HasFPowerSeriesWithinAt.const_smul` / 定理 `HasFPowerSeriesWithinAt.const_smul`

English:
theorem HasFPowerSeriesWithinAt.const_smul
  given: (hf : HasFPowerSeriesWithinAt f pf s x)
  proof: let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesWithinAt

中文:
定理 HasFPowerSeriesWithinAt.const_smul
  条件: (hf : HasFPowerSeriesWithinAt f pf s x)
  证明: let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesWithinAt

Depends on / 依赖: const_smul, hasFPowerSeriesWithinAt, hrf.const_smul.hasFPowerSeriesWithinAt
-/
theorem HasFPowerSeriesWithinAt.const_smul (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (c • f) (c • pf) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesWithinAt

/--
theorem `HasFPowerSeriesAt.const_smul` / 定理 `HasFPowerSeriesAt.const_smul`

English:
theorem HasFPowerSeriesAt.const_smul
  given: (hf : HasFPowerSeriesAt f pf x)
  proof: let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesAt

中文:
定理 HasFPowerSeriesAt.const_smul
  条件: (hf : HasFPowerSeriesAt f pf x)
  证明: let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesAt

Depends on / 依赖: const_smul, hasFPowerSeriesAt, hrf.const_smul.hasFPowerSeriesAt
-/
theorem HasFPowerSeriesAt.const_smul (hf : HasFPowerSeriesAt f pf x) :
    HasFPowerSeriesAt (c • f) (c • pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesAt

/--
theorem `AnalyticWithinAt.const_smul` / 定理 `AnalyticWithinAt.const_smul`

English:
theorem AnalyticWithinAt.const_smul
  given: (hf : AnalyticWithinAt 𝕜 f s x)
  proof: let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticWithinAt

@[to_fun (attr := fun_prop)]

中文:
定理 AnalyticWithinAt.const_smul
  条件: (hf : AnalyticWithinAt 𝕜 f s x)
  证明: let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticWithinAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: analyticWithinAt, const_smul, hpf.const_smul.analyticWithinAt
-/
theorem AnalyticWithinAt.const_smul (hf : AnalyticWithinAt 𝕜 f s x) :
    AnalyticWithinAt 𝕜 (c • f) s x :=
  let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticWithinAt

@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.const_smul` / 定理 `AnalyticAt.const_smul`

English:
theorem AnalyticAt.const_smul
  given: (hf : AnalyticAt 𝕜 f x)
  statement: AnalyticAt 𝕜 (c • f) x
  proof: let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticAt

@[to_fun]

中文:
定理 AnalyticAt.const_smul
  条件: (hf : AnalyticAt 𝕜 f x)
  结论: AnalyticAt 𝕜 (c • f) x
  证明: let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticAt

@[to_fun]

Depends on / 依赖: analyticAt, const_smul, hpf.const_smul.analyticAt
-/
theorem AnalyticAt.const_smul (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (c • f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticAt

@[to_fun]
/--
theorem `AnalyticOn.const_smul` / 定理 `AnalyticOn.const_smul`

English:
theorem AnalyticOn.const_smul
  given: (hf : AnalyticOn 𝕜 f s)
  statement: AnalyticOn 𝕜 (c • f) s
  proof: fun x hx => (hf x hx).const_smul

@[to_fun]

中文:
定理 AnalyticOn.const_smul
  条件: (hf : AnalyticOn 𝕜 f s)
  结论: AnalyticOn 𝕜 (c • f) s
  证明: fun x hx => (hf x hx).const_smul

@[to_fun]

Depends on / 依赖: const_smul
-/
theorem AnalyticOn.const_smul (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (c • f) s :=
  fun x hx => (hf x hx).const_smul

@[to_fun]
/--
theorem `AnalyticOnNhd.const_smul` / 定理 `AnalyticOnNhd.const_smul`

English:
theorem AnalyticOnNhd.const_smul
  given: (hf : AnalyticOnNhd 𝕜 f s)
  statement: AnalyticOnNhd 𝕜 (c • f) s
  proof: fun x hx => (hf x hx).const_smul

中文:
定理 AnalyticOnNhd.const_smul
  条件: (hf : AnalyticOnNhd 𝕜 f s)
  结论: AnalyticOnNhd 𝕜 (c • f) s
  证明: fun x hx => (hf x hx).const_smul

Depends on / 依赖: const_smul
-/
theorem AnalyticOnNhd.const_smul (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (c • f) s :=
  fun x hx => (hf x hx).const_smul

/--
lemma `AnalyticWithinAt.div_const` / 引理 `AnalyticWithinAt.div_const`

English:
lemma AnalyticWithinAt.div_const
  given: {f : E -> 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c : 𝕝}
  proof: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

@[fun_prop]

中文:
引理 AnalyticWithinAt.div_const
  条件: {f : E -> 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c : 𝕝}
  证明: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

@[fun_prop]

Depends on / 依赖: const_smul, div_eq_mul_inv, hf.const_smul
-/
lemma AnalyticWithinAt.div_const {f : E -> 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c : 𝕝} :
    AnalyticWithinAt 𝕜 (f · / c) s x := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

@[fun_prop]
/--
lemma `AnalyticAt.div_const` / 引理 `AnalyticAt.div_const`

English:
lemma AnalyticAt.div_const
  given: {f : E -> 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝}
  proof: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

中文:
引理 AnalyticAt.div_const
  条件: {f : E -> 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝}
  证明: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

Depends on / 依赖: const_smul, div_eq_mul_inv, hf.const_smul
-/
lemma AnalyticAt.div_const {f : E -> 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝} :
    AnalyticAt 𝕜 (f · / c) x := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

/--
lemma `AnalyticOn.div_const` / 引理 `AnalyticOn.div_const`

English:
lemma AnalyticOn.div_const
  given: {f : E -> 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝}
  proof: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

中文:
引理 AnalyticOn.div_const
  条件: {f : E -> 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝}
  证明: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

Depends on / 依赖: const_smul, div_eq_mul_inv, hf.const_smul
-/
lemma AnalyticOn.div_const {f : E -> 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝} :
    AnalyticOn 𝕜 (f · / c) s := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

/--
lemma `AnalyticOnNhd.div_const` / 引理 `AnalyticOnNhd.div_const`

English:
lemma AnalyticOnNhd.div_const
  given: {f : E -> 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝}
  proof: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

中文:
引理 AnalyticOnNhd.div_const
  条件: {f : E -> 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝}
  证明: by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

Depends on / 依赖: const_smul, div_eq_mul_inv, hf.const_smul
-/
lemma AnalyticOnNhd.div_const {f : E -> 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝} :
    AnalyticOnNhd 𝕜 (f · / c) s := by
  simpa [div_eq_mul_inv] using! hf.const_smul (R := 𝕝ᵐᵒᵖ)

end

/-!
### Cartesian products are analytic
-/

/--
lemma `FormalMultilinearSeries.radius_prod_eq_min` / 引理 `FormalMultilinearSeries.radius_prod_eq_min`

English:
lemma FormalMultilinearSeries.radius_prod_eq_min
  proof: by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [le_min_iff]
    have := (p.prod q).isLittleO_one_of_lt_radius hr
    constructor
    all_goals
      apply FormalMultilinearSeries.le_radius_of_isBigO
      refine (isBigO_of_le _ fun n => ?_).trans this.isBigO
 

中文:
引理 FormalMultilinearSeries.radius_prod_eq_min
  证明: by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [le_min_iff]
    have := (p.prod q).isLittleO_one_of_lt_radius hr
    constructor
    all_goals
      apply FormalMultilinearSeries.le_radius_of_isBigO
      refine (isBigO_of_le _ fun n => ?_).trans this.isBigO
 

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_prod, ENNReal, ENNReal.le_of_forall_nnreal_lt, FormalMultilinearSeries, FormalMultilinearSeries.le_radius_of_isBigO, FormalMultilinearSeries.prod, all_goals, isBigO, isBigO_of_le, isLittleO_one_of_lt_radius, le_antisymm, le_max_left, le_max_right, le_min_iff, le_of_forall_nnreal_lt, le_radius_of_isBigO, mul_le_mul_of_nonneg_right, norm_mul, norm_nonneg
-/
lemma FormalMultilinearSeries.radius_prod_eq_min
    (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    (p.prod q).radius = min p.radius q.radius := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [le_min_iff]
    have := (p.prod q).isLittleO_one_of_lt_radius hr
    constructor
    all_goals
      apply FormalMultilinearSeries.le_radius_of_isBigO
      refine (isBigO_of_le _ fun n => ?_).trans this.isBigO
      rw [norm_mul]; rw [norm_norm]; rw [norm_mul]; rw [norm_norm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [FormalMultilinearSeries.prod]; rw [ContinuousMultilinearMap.opNorm_prod]
    · apply le_max_left
    · apply le_max_right
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [lt_min_iff] at hr
    have := ((p.isLittleO_one_of_lt_radius hr.1).add
      (q.isLittleO_one_of_lt_radius hr.2)).isBigO
    refine (p.prod q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
    rw [norm_mul]; rw [norm_norm]; rw [← add_mul]; rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [FormalMultilinearSeries.prod]; rw [ContinuousMultilinearMap.opNorm_prod]
    refine (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans ?_
    apply Real.le_norm_self

/--
lemma `HasFPowerSeriesWithinOnBall.prod` / 引理 `HasFPowerSeriesWithinOnBall.prod`

English:
lemma HasFPowerSeriesWithinOnBall.prod
  statement: {e : E} {f : E -> F} {g : E -> G} {r s : Real>=0∞} {t : Set E}
  proof: by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y h'y hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum h'y ?_).prodMk (hg.hasSum h'y ?_)
    · exact Metric.mem_e

中文:
引理 HasFPowerSeriesWithinOnBall.prod
  结论: {e : E} {f : E -> F} {g : E -> G} {r s : 实数>=0∞} {t : Set E}
  证明: by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y h'y hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum h'y ?_).prodMk (hg.hasSum h'y ?_)
    · exact Metric.mem_e

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.prod_apply, FormalMultilinearSeries, FormalMultilinearSeries.prod, Metric, Metric.mem_eball.mpr, hasSum, hf.hasSum, hf.r_le, hf.r_pos, hg.hasSum, hg.r_le, hg.r_pos, lt_min, lt_of_lt_of_le, mem_eball, min_le_left, min_le_min, min_le_right, p.radius_prod_eq_min
-/
lemma HasFPowerSeriesWithinOnBall.prod {e : E} {f : E -> F} {g : E -> G} {r s : Real>=0∞} {t : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinOnBall f p t e r) (hg : HasFPowerSeriesWithinOnBall g q t e s) :
    HasFPowerSeriesWithinOnBall (fun x => (f x, g x)) (p.prod q) t e (min r s) where
  r_le := by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y h'y hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum h'y ?_).prodMk (hg.hasSum h'y ?_)
    · exact Metric.mem_eball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
    · exact Metric.mem_eball.mpr (lt_of_lt_of_le hy (min_le_right _ _))

/--
lemma `HasFPowerSeriesOnBall.prod` / 引理 `HasFPowerSeriesOnBall.prod`

English:
lemma HasFPowerSeriesOnBall.prod
  statement: {e : E} {f : E -> F} {g : E -> G} {r s : Real>=0∞}
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.prod hg

中文:
引理 HasFPowerSeriesOnBall.prod
  结论: {e : E} {f : E -> F} {g : E -> G} {r s : 实数>=0∞}
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.prod hg

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.prod
-/
lemma HasFPowerSeriesOnBall.prod {e : E} {f : E -> F} {g : E -> G} {r s : Real>=0∞}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesOnBall f p e r) (hg : HasFPowerSeriesOnBall g q e s) :
    HasFPowerSeriesOnBall (fun x => (f x, g x)) (p.prod q) e (min r s) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.prod hg

/--
lemma `HasFPowerSeriesWithinAt.prod` / 引理 `HasFPowerSeriesWithinAt.prod`

English:
lemma HasFPowerSeriesWithinAt.prod
  statement: {e : E} {f : E -> F} {g : E -> G} {s : Set E}
  proof: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

中文:
引理 HasFPowerSeriesWithinAt.prod
  结论: {e : E} {f : E -> F} {g : E -> G} {s : Set E}
  证明: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

Depends on / 依赖: hf.prod
-/
lemma HasFPowerSeriesWithinAt.prod {e : E} {f : E -> F} {g : E -> G} {s : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinAt f p s e) (hg : HasFPowerSeriesWithinAt g q s e) :
    HasFPowerSeriesWithinAt (fun x => (f x, g x)) (p.prod q) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/--
lemma `HasFPowerSeriesAt.prod` / 引理 `HasFPowerSeriesAt.prod`

English:
lemma HasFPowerSeriesAt.prod
  statement: {e : E} {f : E -> F} {g : E -> G}
  proof: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

中文:
引理 HasFPowerSeriesAt.prod
  结论: {e : E} {f : E -> F} {g : E -> G}
  证明: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

Depends on / 依赖: hf.prod
-/
lemma HasFPowerSeriesAt.prod {e : E} {f : E -> F} {g : E -> G}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesAt f p e) (hg : HasFPowerSeriesAt g q e) :
    HasFPowerSeriesAt (fun x => (f x, g x)) (p.prod q) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/--
lemma `AnalyticWithinAt.prod` / 引理 `AnalyticWithinAt.prod`

English:
lemma AnalyticWithinAt.prod
  statement: {e : E} {f : E -> F} {g : E -> G} {s : Set E}
  proof: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

中文:
引理 AnalyticWithinAt.prod
  结论: {e : E} {f : E -> F} {g : E -> G} {s : Set E}
  证明: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

Depends on / 依赖: hf.prod
-/
lemma AnalyticWithinAt.prod {e : E} {f : E -> F} {g : E -> G} {s : Set E}
    (hf : AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s e) :
    AnalyticWithinAt 𝕜 (fun x => (f x, g x)) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
@[fun_prop]
/--
lemma `AnalyticAt.prod` / 引理 `AnalyticAt.prod`

English:
lemma AnalyticAt.prod
  statement: {e : E} {f : E -> F} {g : E -> G}
  proof: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

中文:
引理 AnalyticAt.prod
  结论: {e : E} {f : E -> F} {g : E -> G}
  证明: by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

Depends on / 依赖: hf.prod
-/
lemma AnalyticAt.prod {e : E} {f : E -> F} {g : E -> G}
    (hf : AnalyticAt 𝕜 f e) (hg : AnalyticAt 𝕜 g e) :
    AnalyticAt 𝕜 (fun x => (f x, g x)) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/--
lemma `AnalyticOn.prod` / 引理 `AnalyticOn.prod`

English:
lemma AnalyticOn.prod
  statement: {f : E -> F} {g : E -> G} {s : Set E}
  proof: fun x hx => (hf x hx).prod (hg x hx)

中文:
引理 AnalyticOn.prod
  结论: {f : E -> F} {g : E -> G} {s : Set E}
  证明: fun x hx => (hf x hx).prod (hg x hx)
-/
lemma AnalyticOn.prod {f : E -> F} {g : E -> G} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod (hg x hx)

/--
lemma `AnalyticOnNhd.prod` / 引理 `AnalyticOnNhd.prod`

English:
lemma AnalyticOnNhd.prod
  statement: {f : E -> F} {g : E -> G} {s : Set E}
  proof: fun x hx => (hf x hx).prod (hg x hx)

中文:
引理 AnalyticOnNhd.prod
  结论: {f : E -> F} {g : E -> G} {s : Set E}
  证明: fun x hx => (hf x hx).prod (hg x hx)
-/
lemma AnalyticOnNhd.prod {f : E -> F} {g : E -> G} {s : Set E}
    (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod (hg x hx)

/--
theorem `AnalyticAt.comp₂` / 定理 `AnalyticAt.comp₂`

English:
theorem AnalyticAt.comp₂
  statement: {h : F × G -> H} {f : E -> F} {g : E -> G} {x : E}
  proof: AnalyticAt.comp ha (fa.prod ga)

中文:
定理 AnalyticAt.comp₂
  结论: {h : F × G -> H} {f : E -> F} {g : E -> G} {x : E}
  证明: AnalyticAt.comp ha (fa.prod ga)

Depends on / 依赖: AnalyticAt, AnalyticAt.comp, fa.prod
-/
theorem AnalyticAt.comp₂ {h : F × G -> H} {f : E -> F} {g : E -> G} {x : E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x)
    (ga : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun x => h (f x, g x)) x :=
  AnalyticAt.comp ha (fa.prod ga)

/--
theorem `AnalyticWithinAt.comp₂` / 定理 `AnalyticWithinAt.comp₂`

English:
theorem AnalyticWithinAt.comp₂
  statement: {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)}
  proof: AnalyticWithinAt.comp ha (fa.prod ga) hf

中文:
定理 AnalyticWithinAt.comp₂
  结论: {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)}
  证明: AnalyticWithinAt.comp ha (fa.prod ga) hf

Depends on / 依赖: AnalyticWithinAt, AnalyticWithinAt.comp, fa.prod
-/
theorem AnalyticWithinAt.comp₂ {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)}
    {t : Set E} {x : E}
    (ha : AnalyticWithinAt 𝕜 h s (f x, g x)) (fa : AnalyticWithinAt 𝕜 f t x)
    (ga : AnalyticWithinAt 𝕜 g t x) (hf : Set.MapsTo (fun y => (f y, g y)) t s) :
    AnalyticWithinAt 𝕜 (fun x => h (f x, g x)) t x :=
  AnalyticWithinAt.comp ha (fa.prod ga) hf

/--
theorem `AnalyticAt.comp₂_analyticWithinAt` / 定理 `AnalyticAt.comp₂_analyticWithinAt`

English:
theorem AnalyticAt.comp₂_analyticWithinAt
  proof: AnalyticAt.comp_analyticWithinAt ha (fa.prod ga)

中文:
定理 AnalyticAt.comp₂_analyticWithinAt
  证明: AnalyticAt.comp_analyticWithinAt ha (fa.prod ga)

Depends on / 依赖: AnalyticAt, AnalyticAt.comp_analyticWithinAt, comp_analyticWithinAt, fa.prod
-/
theorem AnalyticAt.comp₂_analyticWithinAt
    {h : F × G -> H} {f : E -> F} {g : E -> G} {x : E} {s : Set E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticWithinAt 𝕜 f s x)
    (ga : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (fun x => h (f x, g x)) s x :=
  AnalyticAt.comp_analyticWithinAt ha (fa.prod ga)

/--
theorem `AnalyticOnNhd.comp₂` / 定理 `AnalyticOnNhd.comp₂`

English:
theorem AnalyticOnNhd.comp₂
  statement: {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)} {t : Set E}
  proof: fun _ xt => (ha _ (m _ xt)).comp₂ (fa _ xt) (ga _ xt)

中文:
定理 AnalyticOnNhd.comp₂
  结论: {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)} {t : Set E}
  证明: fun _ xt => (ha _ (m _ xt)).comp₂ (fa _ xt) (ga _ xt)
-/
theorem AnalyticOnNhd.comp₂ {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)} {t : Set E}
    (ha : AnalyticOnNhd 𝕜 h s) (fa : AnalyticOnNhd 𝕜 f t) (ga : AnalyticOnNhd 𝕜 g t)
    (m : forall x, x in t -> (f x, g x) in s) : AnalyticOnNhd 𝕜 (fun x => h (f x, g x)) t :=
  fun _ xt => (ha _ (m _ xt)).comp₂ (fa _ xt) (ga _ xt)

/--
theorem `AnalyticOn.comp₂` / 定理 `AnalyticOn.comp₂`

English:
theorem AnalyticOn.comp₂
  statement: {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)}
  proof: fun x hx => (ha _ (m hx)).comp₂ (fa x hx) (ga x hx) m

中文:
定理 AnalyticOn.comp₂
  结论: {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)}
  证明: fun x hx => (ha _ (m hx)).comp₂ (fa x hx) (ga x hx) m
-/
theorem AnalyticOn.comp₂ {h : F × G -> H} {f : E -> F} {g : E -> G} {s : Set (F × G)}
    {t : Set E}
    (ha : AnalyticOn 𝕜 h s) (fa : AnalyticOn 𝕜 f t)
    (ga : AnalyticOn 𝕜 g t) (m : Set.MapsTo (fun y => (f y, g y)) t s) :
    AnalyticOn 𝕜 (fun x => h (f x, g x)) t :=
  fun x hx => (ha _ (m hx)).comp₂ (fa x hx) (ga x hx) m

/--
theorem `AnalyticAt.curry_left` / 定理 `AnalyticAt.curry_left`

English:
theorem AnalyticAt.curry_left
  given: {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p)
  proof: AnalyticAt.comp₂ fa analyticAt_id analyticAt_const
alias AnalyticAt.along_fst := AnalyticAt.curry_left

中文:
定理 AnalyticAt.curry_left
  条件: {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p)
  证明: AnalyticAt.comp₂ fa analyticAt_id analyticAt_const
alias AnalyticAt.along_fst := AnalyticAt.curry_left

Depends on / 依赖: AnalyticAt, AnalyticAt.along_fst, AnalyticAt.comp, AnalyticAt.curry_left, along_fst, analyticAt_const, analyticAt_id, curry_left
-/
theorem AnalyticAt.curry_left {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun x => f (x, p.2)) p.1 :=
  AnalyticAt.comp₂ fa analyticAt_id analyticAt_const
alias AnalyticAt.along_fst := AnalyticAt.curry_left

/--
theorem `AnalyticWithinAt.curry_left` / 定理 `AnalyticWithinAt.curry_left`

English:
theorem AnalyticWithinAt.curry_left
  proof: AnalyticWithinAt.comp₂ fa analyticWithinAt_id analyticWithinAt_const (fun _ hx => hx)

中文:
定理 AnalyticWithinAt.curry_left
  证明: AnalyticWithinAt.comp₂ fa analyticWithinAt_id analyticWithinAt_const (fun _ hx => hx)

Depends on / 依赖: AnalyticWithinAt, AnalyticWithinAt.comp, analyticWithinAt_const, analyticWithinAt_id
-/
theorem AnalyticWithinAt.curry_left
    {f : E × F -> G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun x => f (x, p.2)) {x | (x, p.2) in s} p.1 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_id analyticWithinAt_const (fun _ hx => hx)

/--
theorem `AnalyticAt.curry_right` / 定理 `AnalyticAt.curry_right`

English:
theorem AnalyticAt.curry_right
  given: {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p)
  proof: AnalyticAt.comp₂ fa analyticAt_const analyticAt_id
alias AnalyticAt.along_snd := AnalyticAt.curry_right

中文:
定理 AnalyticAt.curry_right
  条件: {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p)
  证明: AnalyticAt.comp₂ fa analyticAt_const analyticAt_id
alias AnalyticAt.along_snd := AnalyticAt.curry_right

Depends on / 依赖: AnalyticAt, AnalyticAt.along_snd, AnalyticAt.comp, AnalyticAt.curry_right, along_snd, analyticAt_const, analyticAt_id, curry_right
-/
theorem AnalyticAt.curry_right {f : E × F -> G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun y => f (p.1, y)) p.2 :=
  AnalyticAt.comp₂ fa analyticAt_const analyticAt_id
alias AnalyticAt.along_snd := AnalyticAt.curry_right

/--
theorem `AnalyticWithinAt.curry_right` / 定理 `AnalyticWithinAt.curry_right`

English:
theorem AnalyticWithinAt.curry_right
  proof: AnalyticWithinAt.comp₂ fa analyticWithinAt_const analyticWithinAt_id (fun _ hx => hx)

中文:
定理 AnalyticWithinAt.curry_right
  证明: AnalyticWithinAt.comp₂ fa analyticWithinAt_const analyticWithinAt_id (fun _ hx => hx)

Depends on / 依赖: AnalyticWithinAt, AnalyticWithinAt.comp, analyticWithinAt_const, analyticWithinAt_id
-/
theorem AnalyticWithinAt.curry_right
    {f : E × F -> G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun y => f (p.1, y)) {y | (p.1, y) in s} p.2 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_const analyticWithinAt_id (fun _ hx => hx)

/--
theorem `AnalyticOnNhd.curry_left` / 定理 `AnalyticOnNhd.curry_left`

English:
theorem AnalyticOnNhd.curry_left
  statement: {f : E × F -> G} {s : Set (E × F)} {y : F}
  proof: fun x m => (fa (x, y) m).curry_left
alias AnalyticOnNhd.along_fst := AnalyticOnNhd.curry_left

中文:
定理 AnalyticOnNhd.curry_left
  结论: {f : E × F -> G} {s : Set (E × F)} {y : F}
  证明: fun x m => (fa (x, y) m).curry_left
alias AnalyticOnNhd.along_fst := AnalyticOnNhd.curry_left

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.along_fst, AnalyticOnNhd.curry_left, along_fst, curry_left
-/
theorem AnalyticOnNhd.curry_left {f : E × F -> G} {s : Set (E × F)} {y : F}
    (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun x => f (x, y)) {x | (x, y) in s} :=
  fun x m => (fa (x, y) m).curry_left
alias AnalyticOnNhd.along_fst := AnalyticOnNhd.curry_left

/--
theorem `AnalyticOn.curry_left` / 定理 `AnalyticOn.curry_left`

English:
theorem AnalyticOn.curry_left
  proof: fun x m => (fa (x, y) m).curry_left

中文:
定理 AnalyticOn.curry_left
  证明: fun x m => (fa (x, y) m).curry_left

Depends on / 依赖: curry_left
-/
theorem AnalyticOn.curry_left
    {f : E × F -> G} {s : Set (E × F)} {y : F} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun x => f (x, y)) {x | (x, y) in s} :=
  fun x m => (fa (x, y) m).curry_left

/--
theorem `AnalyticOnNhd.curry_right` / 定理 `AnalyticOnNhd.curry_right`

English:
theorem AnalyticOnNhd.curry_right
  statement: {f : E × F -> G} {x : E} {s : Set (E × F)}
  proof: fun y m => (fa (x, y) m).curry_right
alias AnalyticOnNhd.along_snd := AnalyticOnNhd.curry_right

中文:
定理 AnalyticOnNhd.curry_right
  结论: {f : E × F -> G} {x : E} {s : Set (E × F)}
  证明: fun y m => (fa (x, y) m).curry_right
alias AnalyticOnNhd.along_snd := AnalyticOnNhd.curry_right

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.along_snd, AnalyticOnNhd.curry_right, along_snd, curry_right
-/
theorem AnalyticOnNhd.curry_right {f : E × F -> G} {x : E} {s : Set (E × F)}
    (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun y => f (x, y)) {y | (x, y) in s} :=
  fun y m => (fa (x, y) m).curry_right
alias AnalyticOnNhd.along_snd := AnalyticOnNhd.curry_right

/--
theorem `AnalyticOn.curry_right` / 定理 `AnalyticOn.curry_right`

English:
theorem AnalyticOn.curry_right
  proof: fun y m => (fa (x, y) m).curry_right

中文:
定理 AnalyticOn.curry_right
  证明: fun y m => (fa (x, y) m).curry_right

Depends on / 依赖: curry_right
-/
theorem AnalyticOn.curry_right
    {f : E × F -> G} {x : E} {s : Set (E × F)} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun y => f (x, y)) {y | (x, y) in s} :=
  fun y m => (fa (x, y) m).curry_right

/-!
### Analyticity in Pi spaces

In this section, `f : Π i, E → Fm i` is a family of functions, i.e., each `f i` is a function,
from `E` to a space `Fm i`. We discuss whether the family as a whole is analytic as a function
of `x : E`, i.e., whether `x ↦ (f 1 x, ..., f n x)` is analytic from `E` to the product space
`Π i, Fm i`. This function is denoted either by `fun x ↦ (fun i ↦ f i x)`, or `fun x i ↦ f i x`,
or `fun x ↦ (f ⬝ x)`. We use the latter spelling in the statements, for readability purposes.
-/

section

variable {ι : Type*} [Fintype ι] {e : E} {Fm : ι -> Type*}
    [forall i, NormedAddCommGroup (Fm i)] [forall i, NormedSpace 𝕜 (Fm i)]
    {f : Π i, E -> Fm i} {s : Set E} {r : Real>=0∞}
    {p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)}

/--
lemma `FormalMultilinearSeries.radius_pi_le` / 引理 `FormalMultilinearSeries.radius_pi_le`

English:
lemma FormalMultilinearSeries.radius_pi_le
  given: (p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)) (i : ι)
  proof: by
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  obtain ⟨C, -, hC⟩ : exists C > 0, forall n, ‖pi p n‖ * ↑r' ^ n <= C := norm_mul_pow_le_of_lt_radius _ hr'
  apply le_radius_of_bound _ C (fun n => ?_)
  apply le_trans _ (hC n)
  gcongr
  rw [pi]; rw [ContinuousMultilinearMap.opNorm_pi]
  exact 

中文:
引理 FormalMultilinearSeries.radius_pi_le
  条件: (p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)) (i : ι)
  证明: by
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  obtain ⟨C, -, hC⟩ : exists C > 0, forall n, ‖pi p n‖ * ↑r' ^ n <= C := norm_mul_pow_le_of_lt_radius _ hr'
  apply le_radius_of_bound _ C (fun n => ?_)
  apply le_trans _ (hC n)
  gcongr
  rw [pi]; rw [ContinuousMultilinearMap.opNorm_pi]
  exact 

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_pi, le_of_forall_nnreal_lt, le_radius_of_bound, le_trans, norm_le_pi_norm, norm_mul_pow_le_of_lt_radius, opNorm_pi
-/
lemma FormalMultilinearSeries.radius_pi_le (p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)) (i : ι) :
    (FormalMultilinearSeries.pi p).radius <= (p i).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  obtain ⟨C, -, hC⟩ : exists C > 0, forall n, ‖pi p n‖ * ↑r' ^ n <= C := norm_mul_pow_le_of_lt_radius _ hr'
  apply le_radius_of_bound _ C (fun n => ?_)
  apply le_trans _ (hC n)
  gcongr
  rw [pi]; rw [ContinuousMultilinearMap.opNorm_pi]
  exact norm_le_pi_norm (fun i => p i n) i

/--
lemma `FormalMultilinearSeries.le_radius_pi` / 引理 `FormalMultilinearSeries.le_radius_pi`

English:
lemma FormalMultilinearSeries.le_radius_pi
  given: (h : forall i, r <= (p i).radius)
  proof: by
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  have I i : exists C > 0, forall n, ‖p i n‖ * (r' : Real) ^ n <= C :=
    norm_mul_pow_le_of_lt_radius _ (hr'.trans_le (h i))
  choose C C_pos hC using I
  obtain ⟨D, D_nonneg, hD⟩ : exists D >= 0, forall i, C i <= D :=
    ⟨∑ i, C i, Finset.sum_

中文:
引理 FormalMultilinearSeries.le_radius_pi
  条件: (h : 对任意 i, r <= (p i).radius)
  证明: by
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  have I i : exists C > 0, forall n, ‖p i n‖ * (r' : Real) ^ n <= C :=
    norm_mul_pow_le_of_lt_radius _ (hr'.trans_le (h i))
  choose C C_pos hC using I
  obtain ⟨D, D_nonneg, hD⟩ : exists D >= 0, forall i, C i <= D :=
    ⟨∑ i, C i, Finset.sum_

Depends on / 依赖: C_pos, D_nonneg, Finset, Finset.mem_univ, Finset.single_le_sum, Finset.sum_nonneg, le_of_forall_nnreal_lt, le_or_gt, le_radius_of_bound, mem_univ, norm_mul_pow_le_of_lt_radius, single_le_sum, sum_nonneg, trans_le
-/
lemma FormalMultilinearSeries.le_radius_pi (h : forall i, r <= (p i).radius) :
    r <= (FormalMultilinearSeries.pi p).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  have I i : exists C > 0, forall n, ‖p i n‖ * (r' : Real) ^ n <= C :=
    norm_mul_pow_le_of_lt_radius _ (hr'.trans_le (h i))
  choose C C_pos hC using I
  obtain ⟨D, D_nonneg, hD⟩ : exists D >= 0, forall i, C i <= D :=
    ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => (C_pos i).le),
      fun i => Finset.single_le_sum (fun j _ => (C_pos j).le) (Finset.mem_univ _)⟩
  apply le_radius_of_bound _ D (fun n => ?_)
  rcases le_or_gt ((r' : Real) ^ n) 0 with hr' | hr'
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hr') D_nonneg
  · simp only [pi]
    rw [← le_div_iff₀ hr']; rw [ContinuousMultilinearMap.opNorm_pi]; rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    exact (le_div_iff₀ hr').2 ((hC i n).trans (hD i))

/--
lemma `FormalMultilinearSeries.radius_pi_eq_iInf` / 引理 `FormalMultilinearSeries.radius_pi_eq_iInf`

English:
lemma FormalMultilinearSeries.radius_pi_eq_iInf
  proof: by
  refine le_antisymm (by simp [radius_pi_le]) ?_
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  exact le_radius_pi (fun i => le_iInf_iff.1 hr'.le i)

中文:
引理 FormalMultilinearSeries.radius_pi_eq_iInf
  证明: by
  refine le_antisymm (by simp [radius_pi_le]) ?_
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  exact le_radius_pi (fun i => le_iInf_iff.1 hr'.le i)

Depends on / 依赖: le_antisymm, le_iInf_iff, le_of_forall_nnreal_lt, le_radius_pi, radius_pi_le
-/
lemma FormalMultilinearSeries.radius_pi_eq_iInf :
    (FormalMultilinearSeries.pi p).radius = ⨅ i, (p i).radius := by
  refine le_antisymm (by simp [radius_pi_le]) ?_
  apply le_of_forall_nnreal_lt (fun r' hr' => ?_)
  exact le_radius_pi (fun i => le_iInf_iff.1 hr'.le i)

/--
lemma `HasFPowerSeriesWithinOnBall.pi` / 引理 `HasFPowerSeriesWithinOnBall.pi`

English:
lemma HasFPowerSeriesWithinOnBall.pi
  proof: by
    apply FormalMultilinearSeries.le_radius_pi (fun i => ?_)
    exact (hf i).r_le
  r_pos := hr
  hasSum {_} m hy := Pi.hasSum.2 (fun i => (hf i).hasSum m hy)

中文:
引理 HasFPowerSeriesWithinOnBall.pi
  证明: by
    apply FormalMultilinearSeries.le_radius_pi (fun i => ?_)
    exact (hf i).r_le
  r_pos := hr
  hasSum {_} m hy := Pi.hasSum.2 (fun i => (hf i).hasSum m hy)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.le_radius_pi, Pi.hasSum, hasSum, le_radius_pi, r_le, r_pos
-/
lemma HasFPowerSeriesWithinOnBall.pi
    (hf : forall i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x => (f · x)) (FormalMultilinearSeries.pi p) s e r where
  r_le := by
    apply FormalMultilinearSeries.le_radius_pi (fun i => ?_)
    exact (hf i).r_le
  r_pos := hr
  hasSum {_} m hy := Pi.hasSum.2 (fun i => (hf i).hasSum m hy)

/--
lemma `hasFPowerSeriesWithinOnBall_pi_iff` / 引理 `hasFPowerSeriesWithinOnBall_pi_iff`

English:
lemma hasFPowerSeriesWithinOnBall_pi_iff
  given: (hr : 0 < r)
  proof: ⟨h.r_le.trans (FormalMultilinearSeries.radius_pi_le _ _), hr,
      fun m hy => Pi.hasSum.1 (h.hasSum m hy) i⟩
  mpr h := .pi h hr

中文:
引理 hasFPowerSeriesWithinOnBall_pi_iff
  条件: (hr : 0 < r)
  证明: ⟨h.r_le.trans (FormalMultilinearSeries.radius_pi_le _ _), hr,
      fun m hy => Pi.hasSum.1 (h.hasSum m hy) i⟩
  mpr h := .pi h hr

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.radius_pi_le, Pi.hasSum, h.hasSum, h.r_le.trans, hasSum, r_le, radius_pi_le
-/
lemma hasFPowerSeriesWithinOnBall_pi_iff (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x => (f · x)) (FormalMultilinearSeries.pi p) s e r ↔
      forall i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r where
  mp h i :=
    ⟨h.r_le.trans (FormalMultilinearSeries.radius_pi_le _ _), hr,
      fun m hy => Pi.hasSum.1 (h.hasSum m hy) i⟩
  mpr h := .pi h hr

/--
lemma `HasFPowerSeriesOnBall.pi` / 引理 `HasFPowerSeriesOnBall.pi`

English:
lemma HasFPowerSeriesOnBall.pi
  proof: by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact HasFPowerSeriesWithinOnBall.pi hf hr

中文:
引理 HasFPowerSeriesOnBall.pi
  证明: by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact HasFPowerSeriesWithinOnBall.pi hf hr

Depends on / 依赖: HasFPowerSeriesWithinOnBall, HasFPowerSeriesWithinOnBall.pi, hasFPowerSeriesWithinOnBall_univ, simp_rw
-/
lemma HasFPowerSeriesOnBall.pi
    (hf : forall i, HasFPowerSeriesOnBall (f i) (p i) e r) (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x => (f · x)) (FormalMultilinearSeries.pi p) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact HasFPowerSeriesWithinOnBall.pi hf hr

/--
lemma `hasFPowerSeriesOnBall_pi_iff` / 引理 `hasFPowerSeriesOnBall_pi_iff`

English:
lemma hasFPowerSeriesOnBall_pi_iff
  given: (hr : 0 < r)
  proof: by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ]
  exact hasFPowerSeriesWithinOnBall_pi_iff hr

中文:
引理 hasFPowerSeriesOnBall_pi_iff
  条件: (hr : 0 < r)
  证明: by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ]
  exact hasFPowerSeriesWithinOnBall_pi_iff hr

Depends on / 依赖: hasFPowerSeriesWithinOnBall_pi_iff, hasFPowerSeriesWithinOnBall_univ, simp_rw
-/
lemma hasFPowerSeriesOnBall_pi_iff (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x => (f · x)) (FormalMultilinearSeries.pi p) e r ↔
      forall i, HasFPowerSeriesOnBall (f i) (p i) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ]
  exact hasFPowerSeriesWithinOnBall_pi_iff hr

/--
lemma `HasFPowerSeriesWithinAt.pi` / 引理 `HasFPowerSeriesWithinAt.pi`

English:
lemma HasFPowerSeriesWithinAt.pi
  proof: by
  have : forallᶠ r in 𝓝[>] 0, forall i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r :=
    eventually_all.mpr (fun i => (hf i).eventually)
  obtain ⟨r, hr, r_pos⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨r, HasFPowerSeriesWithinOnBall.pi hr r_pos⟩

中文:
引理 HasFPowerSeriesWithinAt.pi
  证明: by
  have : forallᶠ r in 𝓝[>] 0, forall i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r :=
    eventually_all.mpr (fun i => (hf i).eventually)
  obtain ⟨r, hr, r_pos⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨r, HasFPowerSeriesWithinOnBall.pi hr r_pos⟩

Depends on / 依赖: HasFPowerSeriesWithinOnBall, HasFPowerSeriesWithinOnBall.pi, eventually, eventually_all, eventually_all.mpr, r_pos, self_mem_nhdsWithin, this.and
-/
lemma HasFPowerSeriesWithinAt.pi
    (hf : forall i, HasFPowerSeriesWithinAt (f i) (p i) s e) :
    HasFPowerSeriesWithinAt (fun x => (f · x)) (FormalMultilinearSeries.pi p) s e := by
  have : forallᶠ r in 𝓝[>] 0, forall i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r :=
    eventually_all.mpr (fun i => (hf i).eventually)
  obtain ⟨r, hr, r_pos⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨r, HasFPowerSeriesWithinOnBall.pi hr r_pos⟩

/--
lemma `hasFPowerSeriesWithinAt_pi_iff` / 引理 `hasFPowerSeriesWithinAt_pi_iff`

English:
lemma hasFPowerSeriesWithinAt_pi_iff
  proof: by
  refine ⟨fun h i => ?_, fun h => .pi h⟩
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (hasFPowerSeriesWithinOnBall_pi_iff hr.r_pos).1 hr i⟩

中文:
引理 hasFPowerSeriesWithinAt_pi_iff
  证明: by
  refine ⟨fun h i => ?_, fun h => .pi h⟩
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (hasFPowerSeriesWithinOnBall_pi_iff hr.r_pos).1 hr i⟩

Depends on / 依赖: hasFPowerSeriesWithinOnBall_pi_iff, hr.r_pos, r_pos
-/
lemma hasFPowerSeriesWithinAt_pi_iff :
    HasFPowerSeriesWithinAt (fun x => (f · x)) (FormalMultilinearSeries.pi p) s e ↔
      forall i, HasFPowerSeriesWithinAt (f i) (p i) s e := by
  refine ⟨fun h i => ?_, fun h => .pi h⟩
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (hasFPowerSeriesWithinOnBall_pi_iff hr.r_pos).1 hr i⟩

/--
lemma `HasFPowerSeriesAt.pi` / 引理 `HasFPowerSeriesAt.pi`

English:
lemma HasFPowerSeriesAt.pi
  proof: by
  simp_rw [← hasFPowerSeriesWithinAt_univ] at hf ⊢
  exact HasFPowerSeriesWithinAt.pi hf

中文:
引理 HasFPowerSeriesAt.pi
  证明: by
  simp_rw [← hasFPowerSeriesWithinAt_univ] at hf ⊢
  exact HasFPowerSeriesWithinAt.pi hf

Depends on / 依赖: HasFPowerSeriesWithinAt, HasFPowerSeriesWithinAt.pi, hasFPowerSeriesWithinAt_univ, simp_rw
-/
lemma HasFPowerSeriesAt.pi
    (hf : forall i, HasFPowerSeriesAt (f i) (p i) e) :
    HasFPowerSeriesAt (fun x => (f · x)) (FormalMultilinearSeries.pi p) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ] at hf ⊢
  exact HasFPowerSeriesWithinAt.pi hf

/--
lemma `hasFPowerSeriesAt_pi_iff` / 引理 `hasFPowerSeriesAt_pi_iff`

English:
lemma hasFPowerSeriesAt_pi_iff
  proof: by
  simp_rw [← hasFPowerSeriesWithinAt_univ]
  exact hasFPowerSeriesWithinAt_pi_iff

中文:
引理 hasFPowerSeriesAt_pi_iff
  证明: by
  simp_rw [← hasFPowerSeriesWithinAt_univ]
  exact hasFPowerSeriesWithinAt_pi_iff

Depends on / 依赖: hasFPowerSeriesWithinAt_pi_iff, hasFPowerSeriesWithinAt_univ, simp_rw
-/
lemma hasFPowerSeriesAt_pi_iff :
    HasFPowerSeriesAt (fun x => (f · x)) (FormalMultilinearSeries.pi p) e ↔
      forall i, HasFPowerSeriesAt (f i) (p i) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ]
  exact hasFPowerSeriesWithinAt_pi_iff

/--
lemma `AnalyticWithinAt.pi` / 引理 `AnalyticWithinAt.pi`

English:
lemma AnalyticWithinAt.pi
  given: (hf : forall i, AnalyticWithinAt 𝕜 (f i) s e)
  proof: by
  choose p hp using hf
  exact ⟨FormalMultilinearSeries.pi p, HasFPowerSeriesWithinAt.pi hp⟩

中文:
引理 AnalyticWithinAt.pi
  条件: (hf : 对任意 i, AnalyticWithinAt 𝕜 (f i) s e)
  证明: by
  choose p hp using hf
  exact ⟨FormalMultilinearSeries.pi p, HasFPowerSeriesWithinAt.pi hp⟩

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.pi, HasFPowerSeriesWithinAt, HasFPowerSeriesWithinAt.pi
-/
lemma AnalyticWithinAt.pi (hf : forall i, AnalyticWithinAt 𝕜 (f i) s e) :
    AnalyticWithinAt 𝕜 (fun x => (f · x)) s e := by
  choose p hp using hf
  exact ⟨FormalMultilinearSeries.pi p, HasFPowerSeriesWithinAt.pi hp⟩

/--
lemma `analyticWithinAt_pi_iff` / 引理 `analyticWithinAt_pi_iff`

English:
lemma analyticWithinAt_pi_iff
  proof: by
  refine ⟨fun h i => ?_, fun h => .pi h⟩
  exact ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt _).comp_analyticWithinAt h

中文:
引理 analyticWithinAt_pi_iff
  证明: by
  refine ⟨fun h i => ?_, fun h => .pi h⟩
  exact ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt _).comp_analyticWithinAt h

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.proj, analyticAt, comp_analyticWithinAt
-/
lemma analyticWithinAt_pi_iff :
    AnalyticWithinAt 𝕜 (fun x => (f · x)) s e ↔ forall i, AnalyticWithinAt 𝕜 (f i) s e := by
  refine ⟨fun h i => ?_, fun h => .pi h⟩
  exact ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt _).comp_analyticWithinAt h

/--
lemma `AnalyticAt.pi` / 引理 `AnalyticAt.pi`

English:
lemma AnalyticAt.pi
  given: (hf : forall i, AnalyticAt 𝕜 (f i) e)
  proof: by
  simp_rw [← analyticWithinAt_univ] at hf ⊢
  exact AnalyticWithinAt.pi hf

中文:
引理 AnalyticAt.pi
  条件: (hf : 对任意 i, AnalyticAt 𝕜 (f i) e)
  证明: by
  simp_rw [← analyticWithinAt_univ] at hf ⊢
  exact AnalyticWithinAt.pi hf

Depends on / 依赖: AnalyticWithinAt, AnalyticWithinAt.pi, analyticWithinAt_univ, simp_rw
-/
lemma AnalyticAt.pi (hf : forall i, AnalyticAt 𝕜 (f i) e) :
    AnalyticAt 𝕜 (fun x => (f · x)) e := by
  simp_rw [← analyticWithinAt_univ] at hf ⊢
  exact AnalyticWithinAt.pi hf

/--
lemma `analyticAt_pi_iff` / 引理 `analyticAt_pi_iff`

English:
lemma analyticAt_pi_iff
  proof: by
  simp_rw [← analyticWithinAt_univ]
  exact analyticWithinAt_pi_iff

中文:
引理 analyticAt_pi_iff
  证明: by
  simp_rw [← analyticWithinAt_univ]
  exact analyticWithinAt_pi_iff

Depends on / 依赖: analyticWithinAt_pi_iff, analyticWithinAt_univ, simp_rw
-/
lemma analyticAt_pi_iff :
    AnalyticAt 𝕜 (fun x => (f · x)) e ↔ forall i, AnalyticAt 𝕜 (f i) e := by
  simp_rw [← analyticWithinAt_univ]
  exact analyticWithinAt_pi_iff

/--
lemma `AnalyticOn.pi` / 引理 `AnalyticOn.pi`

English:
lemma AnalyticOn.pi
  given: (hf : forall i, AnalyticOn 𝕜 (f i) s)
  proof: fun x hx => AnalyticWithinAt.pi (fun i => hf i x hx)

中文:
引理 AnalyticOn.pi
  条件: (hf : 对任意 i, AnalyticOn 𝕜 (f i) s)
  证明: fun x hx => AnalyticWithinAt.pi (fun i => hf i x hx)

Depends on / 依赖: AnalyticWithinAt, AnalyticWithinAt.pi
-/
lemma AnalyticOn.pi (hf : forall i, AnalyticOn 𝕜 (f i) s) :
    AnalyticOn 𝕜 (fun x => (f · x)) s :=
  fun x hx => AnalyticWithinAt.pi (fun i => hf i x hx)

/--
lemma `analyticOn_pi_iff` / 引理 `analyticOn_pi_iff`

English:
lemma analyticOn_pi_iff
  proof: ⟨fun h i x hx => analyticWithinAt_pi_iff.1 (h x hx) i, fun h => .pi h⟩

中文:
引理 analyticOn_pi_iff
  证明: ⟨fun h i x hx => analyticWithinAt_pi_iff.1 (h x hx) i, fun h => .pi h⟩

Depends on / 依赖: analyticWithinAt_pi_iff
-/
lemma analyticOn_pi_iff :
    AnalyticOn 𝕜 (fun x => (f · x)) s ↔ forall i, AnalyticOn 𝕜 (f i) s :=
  ⟨fun h i x hx => analyticWithinAt_pi_iff.1 (h x hx) i, fun h => .pi h⟩

/--
lemma `AnalyticOnNhd.pi` / 引理 `AnalyticOnNhd.pi`

English:
lemma AnalyticOnNhd.pi
  given: (hf : forall i, AnalyticOnNhd 𝕜 (f i) s)
  proof: fun x hx => AnalyticAt.pi (fun i => hf i x hx)

中文:
引理 AnalyticOnNhd.pi
  条件: (hf : 对任意 i, AnalyticOnNhd 𝕜 (f i) s)
  证明: fun x hx => AnalyticAt.pi (fun i => hf i x hx)

Depends on / 依赖: AnalyticAt, AnalyticAt.pi
-/
lemma AnalyticOnNhd.pi (hf : forall i, AnalyticOnNhd 𝕜 (f i) s) :
    AnalyticOnNhd 𝕜 (fun x => (f · x)) s :=
  fun x hx => AnalyticAt.pi (fun i => hf i x hx)

/--
lemma `analyticOnNhd_pi_iff` / 引理 `analyticOnNhd_pi_iff`

English:
lemma analyticOnNhd_pi_iff
  proof: ⟨fun h i x hx => analyticAt_pi_iff.1 (h x hx) i, fun h => .pi h⟩

中文:
引理 analyticOnNhd_pi_iff
  证明: ⟨fun h i x hx => analyticAt_pi_iff.1 (h x hx) i, fun h => .pi h⟩

Depends on / 依赖: analyticAt_pi_iff
-/
lemma analyticOnNhd_pi_iff :
    AnalyticOnNhd 𝕜 (fun x => (f · x)) s ↔ forall i, AnalyticOnNhd 𝕜 (f i) s :=
  ⟨fun h i x hx => analyticAt_pi_iff.1 (h x hx) i, fun h => .pi h⟩

end

/-!
### Arithmetic on analytic functions
-/

/-- Scalar multiplication is analytic (jointly in both variables). The statement is a little
pedantic to allow towers of field extensions. -/
@[fun_prop]
/--
lemma `analyticAt_smul` / 引理 `analyticAt_smul`

English:
lemma analyticAt_smul
  given: [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] (z : A × E)
  proof: (ContinuousLinearMap.lsmul 𝕜 A).analyticAt_bilinear z

中文:
引理 analyticAt_smul
  条件: [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] (z : A × E)
  证明: (ContinuousLinearMap.lsmul 𝕜 A).analyticAt_bilinear z

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, analyticAt_bilinear
-/
lemma analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] (z : A × E) :
    AnalyticAt 𝕜 (fun x : A × E => x.1 • x.2) z :=
  (ContinuousLinearMap.lsmul 𝕜 A).analyticAt_bilinear z

/-- Multiplication in a normed algebra over `𝕜` is analytic. -/
@[fun_prop]
/--
lemma `analyticAt_mul` / 引理 `analyticAt_mul`

English:
lemma analyticAt_mul
  given: (z : A × A)
  statement: AnalyticAt 𝕜 (fun x : A × A => x.1 * x.2) z
  proof: analyticAt_smul z

中文:
引理 analyticAt_mul
  条件: (z : A × A)
  结论: AnalyticAt 𝕜 (fun x : A × A => x.1 * x.2) z
  证明: analyticAt_smul z

Depends on / 依赖: analyticAt_smul
-/
lemma analyticAt_mul (z : A × A) : AnalyticAt 𝕜 (fun x : A × A => x.1 * x.2) z :=
  analyticAt_smul z

/--
lemma `AnalyticWithinAt.smul` / 引理 `AnalyticWithinAt.smul`

English:
lemma AnalyticWithinAt.smul
  statement: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
  proof: (analyticAt_smul _).comp₂_analyticWithinAt hf hg

中文:
引理 AnalyticWithinAt.smul
  结论: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
  证明: (analyticAt_smul _).comp₂_analyticWithinAt hf hg

Depends on / 依赖: analyticAt_smul
-/
lemma AnalyticWithinAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : E -> A} {g : E -> F} {s : Set E} {z : E}
    (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) :
    AnalyticWithinAt 𝕜 (fun x => f x • g x) s z :=
  (analyticAt_smul _).comp₂_analyticWithinAt hf hg

/-- Scalar multiplication of one analytic function by another. -/
@[to_fun (attr := fun_prop)]
/--
lemma `AnalyticAt.smul` / 引理 `AnalyticAt.smul`

English:
lemma AnalyticAt.smul
  statement: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f : E -> A}
  proof: (analyticAt_smul _).comp₂ hf hg

中文:
引理 AnalyticAt.smul
  结论: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f : E -> A}
  证明: (analyticAt_smul _).comp₂ hf hg

Depends on / 依赖: analyticAt_smul
-/
lemma AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f : E -> A}
    {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (f • g) z :=
  (analyticAt_smul _).comp₂ hf hg

/--
lemma `AnalyticOn.smul` / 引理 `AnalyticOn.smul`

English:
lemma AnalyticOn.smul
  statement: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
  proof: fun _ m => (hf _ m).smul (hg _ m)

中文:
引理 AnalyticOn.smul
  结论: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
  证明: fun _ m => (hf _ m).smul (hg _ m)
-/
lemma AnalyticOn.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : E -> A} {g : E -> F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x => f x • g x) s :=
  fun _ m => (hf _ m).smul (hg _ m)

/--
lemma `AnalyticOnNhd.smul` / 引理 `AnalyticOnNhd.smul`

English:
lemma AnalyticOnNhd.smul
  statement: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
  proof: fun _ m => (hf _ m).smul (hg _ m)

中文:
引理 AnalyticOnNhd.smul
  结论: [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
  证明: fun _ m => (hf _ m).smul (hg _ m)
-/
lemma AnalyticOnNhd.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : E -> A} {g : E -> F} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x => f x • g x) s :=
  fun _ m => (hf _ m).smul (hg _ m)

/--
lemma `AnalyticWithinAt.mul` / 引理 `AnalyticWithinAt.mul`

English:
lemma AnalyticWithinAt.mul
  statement: {f g : E -> A} {s : Set E} {z : E}
  proof: (analyticAt_mul _).comp₂_analyticWithinAt hf hg

中文:
引理 AnalyticWithinAt.mul
  结论: {f g : E -> A} {s : Set E} {z : E}
  证明: (analyticAt_mul _).comp₂_analyticWithinAt hf hg

Depends on / 依赖: analyticAt_mul
-/
lemma AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z : E}
    (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) :
    AnalyticWithinAt 𝕜 (fun x => f x * g x) s z :=
  (analyticAt_mul _).comp₂_analyticWithinAt hf hg

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
@[to_fun (attr := fun_prop)]
/--
lemma `AnalyticAt.mul` / 引理 `AnalyticAt.mul`

English:
lemma AnalyticAt.mul
  given: {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z)
  proof: hf.smul hg

中文:
引理 AnalyticAt.mul
  条件: {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z)
  证明: hf.smul hg

Depends on / 依赖: hf.smul
-/
lemma AnalyticAt.mul {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (f * g) z :=
  hf.smul hg

/--
lemma `AnalyticOn.mul` / 引理 `AnalyticOn.mul`

English:
lemma AnalyticOn.mul
  statement: {f g : E -> A} {s : Set E}
  proof: hf.smul hg

中文:
引理 AnalyticOn.mul
  结论: {f g : E -> A} {s : Set E}
  证明: hf.smul hg

Depends on / 依赖: hf.smul
-/
lemma AnalyticOn.mul {f g : E -> A} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x => f x * g x) s :=
  hf.smul hg

/--
lemma `AnalyticOnNhd.mul` / 引理 `AnalyticOnNhd.mul`

English:
lemma AnalyticOnNhd.mul
  statement: {f g : E -> A} {s : Set E}
  proof: hf.smul hg

中文:
引理 AnalyticOnNhd.mul
  结论: {f g : E -> A} {s : Set E}
  证明: hf.smul hg

Depends on / 依赖: hf.smul
-/
lemma AnalyticOnNhd.mul {f g : E -> A} {s : Set E}
    (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x => f x * g x) s :=
  hf.smul hg

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
/--
lemma `AnalyticWithinAt.pow` / 引理 `AnalyticWithinAt.pow`

English:
lemma AnalyticWithinAt.pow
  statement: {f : E -> A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z)
  proof: by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply analyticWithinAt_const
  | succ m hm =>
    simp only [pow_succ]
    exact hm.mul hf

中文:
引理 AnalyticWithinAt.pow
  结论: {f : E -> A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z)
  证明: by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply analyticWithinAt_const
  | succ m hm =>
    simp only [pow_succ]
    exact hm.mul hf

Depends on / 依赖: analyticWithinAt_const, hm.mul, pow_succ, pow_zero
-/
lemma AnalyticWithinAt.pow {f : E -> A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z)
    (n : Nat) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply analyticWithinAt_const
  | succ m hm =>
    simp only [pow_succ]
    exact hm.mul hf

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun (attr := fun_prop)]
/--
lemma `AnalyticAt.pow` / 引理 `AnalyticAt.pow`

English:
lemma AnalyticAt.pow
  given: {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : Nat)
  proof: by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.pow n

中文:
引理 AnalyticAt.pow
  条件: {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : 自然数)
  证明: by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.pow n

Depends on / 依赖: analyticWithinAt_univ, hf.pow
-/
lemma AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : Nat) :
    AnalyticAt 𝕜 (f ^ n) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
/--
lemma `AnalyticOn.pow` / 引理 `AnalyticOn.pow`

English:
lemma AnalyticOn.pow
  given: {f : E -> A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : Nat)
  proof: fun _ m => (hf _ m).pow n

中文:
引理 AnalyticOn.pow
  条件: {f : E -> A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : 自然数)
  证明: fun _ m => (hf _ m).pow n
-/
lemma AnalyticOn.pow {f : E -> A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : Nat) :
    AnalyticOn 𝕜 (f ^ n) s :=
  fun _ m => (hf _ m).pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
/--
lemma `AnalyticOnNhd.pow` / 引理 `AnalyticOnNhd.pow`

English:
lemma AnalyticOnNhd.pow
  given: {f : E -> A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n : Nat)
  proof: fun _ m => (hf _ m).pow n

中文:
引理 AnalyticOnNhd.pow
  条件: {f : E -> A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n : 自然数)
  证明: fun _ m => (hf _ m).pow n
-/
lemma AnalyticOnNhd.pow {f : E -> A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n : Nat) :
    AnalyticOnNhd 𝕜 (f ^ n) s :=
  fun _ m => (hf _ m).pow n

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/--
lemma `AnalyticWithinAt.zpow_nonneg` / 引理 `AnalyticWithinAt.zpow_nonneg`

English:
lemma AnalyticWithinAt.zpow_nonneg
  statement: {f : E -> 𝕝} {z : E} {s : Set E} {n : Int}
  proof: by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

中文:
引理 AnalyticWithinAt.zpow_nonneg
  结论: {f : E -> 𝕝} {z : E} {s : Set E} {n : 整数}
  证明: by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

Depends on / 依赖: hf.pow, n.toNat, zpow_natCast
-/
lemma AnalyticWithinAt.zpow_nonneg {f : E -> 𝕝} {z : E} {s : Set E} {n : Int}
    (hf : AnalyticWithinAt 𝕜 f s z) (hn : 0 <= n) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/--
lemma `AnalyticAt.zpow_nonneg` / 引理 `AnalyticAt.zpow_nonneg`

English:
lemma AnalyticAt.zpow_nonneg
  given: {f : E -> 𝕝} {z : E} {n : Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n)
  proof: by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

中文:
引理 AnalyticAt.zpow_nonneg
  条件: {f : E -> 𝕝} {z : E} {n : 整数} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n)
  证明: by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

Depends on / 依赖: hf.pow, n.toNat, zpow_natCast
-/
lemma AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n : Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n) :
    AnalyticAt 𝕜 (f ^ n) z := by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/--
lemma `AnalyticOn.zpow_nonneg` / 引理 `AnalyticOn.zpow_nonneg`

English:
lemma AnalyticOn.zpow_nonneg
  statement: {f : E -> 𝕝} {s : Set E} {n : Int} (hf : AnalyticOn 𝕜 f s)
  proof: by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

中文:
引理 AnalyticOn.zpow_nonneg
  结论: {f : E -> 𝕝} {s : Set E} {n : 整数} (hf : AnalyticOn 𝕜 f s)
  证明: by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

Depends on / 依赖: hf.pow, n.toNat, zpow_natCast
-/
lemma AnalyticOn.zpow_nonneg {f : E -> 𝕝} {s : Set E} {n : Int} (hf : AnalyticOn 𝕜 f s)
    (hn : 0 <= n) :
    AnalyticOn 𝕜 (f ^ n) s := by
  simpa [← zpow_natCast, hn] using hf.pow n.toNat

/-- ZPowers of analytic functions (into a normed division algebra over `𝕜`) are analytic if the
exponent is nonnegative. -/
@[to_fun]
/--
lemma `AnalyticOnNhd.zpow_nonneg` / 引理 `AnalyticOnNhd.zpow_nonneg`

English:
lemma AnalyticOnNhd.zpow_nonneg
  statement: {f : E -> 𝕝} {s : Set E} {n : Int} (hf : AnalyticOnNhd 𝕜 f s)
  proof: by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply pow hf

中文:
引理 AnalyticOnNhd.zpow_nonneg
  结论: {f : E -> 𝕝} {s : Set E} {n : 整数} (hf : AnalyticOnNhd 𝕜 f s)
  证明: by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply pow hf

Depends on / 依赖: Eq.symm, Int.toNat_of_nonneg, OfNat.ofNat, n.toNat, simp_rw, toNat_of_nonneg, zpow_ofNat
-/
lemma AnalyticOnNhd.zpow_nonneg {f : E -> 𝕝} {s : Set E} {n : Int} (hf : AnalyticOnNhd 𝕜 f s)
    (hn : 0 <= n) :
    AnalyticOnNhd 𝕜 (f ^ n) s := by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply pow hf

/-!
### Composition with a linear map
-/

section compContinuousLinearMap

variable {u : E ->L[𝕜] F} {f : F -> G} {pf : FormalMultilinearSeries 𝕜 F G} {s : Set F} {x : E}
  {r : Real>=0∞}

/--
theorem `HasFPowerSeriesWithinOnBall.compContinuousLinearMap` / 定理 `HasFPowerSeriesWithinOnBall.compContinuousLinearMap`

English:
theorem HasFPowerSeriesWithinOnBall.compContinuousLinearMap
  proof: by
    calc
      _ <= pf.radius / ‖u‖ₑ := by
        gcongr
        exact hf.r_le
      _ <= _ := pf.div_le_radius_compContinuousLinearMap _
  r_pos := by
    simp only [ENNReal.div_pos_iff, ne_eq, enorm_ne_top, not_false_eq_true, and_true]
    exact pos_iff_ne_zero.mp hf.r_pos
  hasSum hy1 hy2 := 

中文:
定理 HasFPowerSeriesWithinOnBall.compContinuousLinearMap
  证明: by
    calc
      _ <= pf.radius / ‖u‖ₑ := by
        gcongr
        exact hf.r_le
      _ <= _ := pf.div_le_radius_compContinuousLinearMap _
  r_pos := by
    simp only [ENNReal.div_pos_iff, ne_eq, enorm_ne_top, not_false_eq_true, and_true]
    exact pos_iff_ne_zero.mp hf.r_pos
  hasSum hy1 hy2 := 

Depends on / 依赖: ENNReal, ENNReal.div_pos_iff, Metric, Metric.eball, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_eq_left, and_true, convert, div_le_radius_compContinuousLinearMap, div_pos_iff, edist_zero_right, enorm_ne_top, hasSum, hf.hasSum, hf.r_le, hf.r_pos, lt_of_l, map_add
-/
theorem HasFPowerSeriesWithinOnBall.compContinuousLinearMap
    (hf : HasFPowerSeriesWithinOnBall f pf s (u x) r) :
    HasFPowerSeriesWithinOnBall (f ∘ u) (pf.compContinuousLinearMap u) (u ⁻¹' s) x (r / ‖u‖ₑ) where
  r_le := by
    calc
      _ <= pf.radius / ‖u‖ₑ := by
        gcongr
        exact hf.r_le
      _ <= _ := pf.div_le_radius_compContinuousLinearMap _
  r_pos := by
    simp only [ENNReal.div_pos_iff, ne_eq, enorm_ne_top, not_false_eq_true, and_true]
    exact pos_iff_ne_zero.mp hf.r_pos
  hasSum hy1 hy2 := by
    convert! hf.hasSum _ _
    · simp
    · simp only [Set.mem_insert_iff, add_eq_left, Set.mem_preimage, map_add] at hy1 ⊢
      rcases hy1 with (hy1 | hy1) <;> simp [hy1]
    · simp only [Metric.eball, edist_zero_right, Set.mem_ofPred_eq] at hy2 ⊢
      exact lt_of_le_of_lt (ContinuousLinearMap.le_opENorm _ _) (mul_lt_of_lt_div' hy2)

/--
theorem `HasFPowerSeriesOnBall.compContinuousLinearMap` / 定理 `HasFPowerSeriesOnBall.compContinuousLinearMap`

English:
theorem HasFPowerSeriesOnBall.compContinuousLinearMap
  given: (hf : HasFPowerSeriesOnBall f pf (u x) r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.compContinuousLinearMap

中文:
定理 HasFPowerSeriesOnBall.compContinuousLinearMap
  条件: (hf : HasFPowerSeriesOnBall f pf (u x) r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.compContinuousLinearMap

Depends on / 依赖: compContinuousLinearMap, hasFPowerSeriesWithinOnBall_univ, hf.compContinuousLinearMap
-/
theorem HasFPowerSeriesOnBall.compContinuousLinearMap (hf : HasFPowerSeriesOnBall f pf (u x) r) :
    HasFPowerSeriesOnBall (f ∘ u) (pf.compContinuousLinearMap u) x (r / ‖u‖ₑ) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.compContinuousLinearMap

/--
theorem `HasFPowerSeriesAt.compContinuousLinearMap` / 定理 `HasFPowerSeriesAt.compContinuousLinearMap`

English:
theorem HasFPowerSeriesAt.compContinuousLinearMap
  given: (hf : HasFPowerSeriesAt f pf (u x))
  proof: let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩

中文:
定理 HasFPowerSeriesAt.compContinuousLinearMap
  条件: (hf : HasFPowerSeriesAt f pf (u x))
  证明: let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩

Depends on / 依赖: compContinuousLinearMap, hr.compContinuousLinearMap
-/
theorem HasFPowerSeriesAt.compContinuousLinearMap (hf : HasFPowerSeriesAt f pf (u x)) :
    HasFPowerSeriesAt (f ∘ u) (pf.compContinuousLinearMap u) x :=
  let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩

/--
theorem `HasFPowerSeriesWithinAt.compContinuousLinearMap` / 定理 `HasFPowerSeriesWithinAt.compContinuousLinearMap`

English:
theorem HasFPowerSeriesWithinAt.compContinuousLinearMap
  proof: let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩

中文:
定理 HasFPowerSeriesWithinAt.compContinuousLinearMap
  证明: let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩

Depends on / 依赖: compContinuousLinearMap, hr.compContinuousLinearMap
-/
theorem HasFPowerSeriesWithinAt.compContinuousLinearMap
    (hf : HasFPowerSeriesWithinAt f pf s (u x)) :
    HasFPowerSeriesWithinAt (f ∘ u) (pf.compContinuousLinearMap u) (u ⁻¹' s) x :=
  let ⟨r, hr⟩ := hf
  ⟨r / ‖u‖ₑ, hr.compContinuousLinearMap⟩

/--
theorem `AnalyticAt.compContinuousLinearMap` / 定理 `AnalyticAt.compContinuousLinearMap`

English:
theorem AnalyticAt.compContinuousLinearMap
  given: (hf : AnalyticAt 𝕜 f (u x))
  proof: let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

中文:
定理 AnalyticAt.compContinuousLinearMap
  条件: (hf : AnalyticAt 𝕜 f (u x))
  证明: let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

Depends on / 依赖: compContinuousLinearMap, hp.compContinuousLinearMap, p.compContinuousLinearMap
-/
theorem AnalyticAt.compContinuousLinearMap (hf : AnalyticAt 𝕜 f (u x)) :
    AnalyticAt 𝕜 (f ∘ u) x :=
  let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

/--
theorem `AnalyticAtWithin.compContinuousLinearMap` / 定理 `AnalyticAtWithin.compContinuousLinearMap`

English:
theorem AnalyticAtWithin.compContinuousLinearMap
  given: (hf : AnalyticWithinAt 𝕜 f s (u x))
  proof: let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

中文:
定理 AnalyticAtWithin.compContinuousLinearMap
  条件: (hf : AnalyticWithinAt 𝕜 f s (u x))
  证明: let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

Depends on / 依赖: compContinuousLinearMap, hp.compContinuousLinearMap, p.compContinuousLinearMap
-/
theorem AnalyticAtWithin.compContinuousLinearMap (hf : AnalyticWithinAt 𝕜 f s (u x)) :
    AnalyticWithinAt 𝕜 (f ∘ u) (u ⁻¹' s) x :=
  let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

/--
theorem `AnalyticOn.compContinuousLinearMap` / 定理 `AnalyticOn.compContinuousLinearMap`

English:
theorem AnalyticOn.compContinuousLinearMap
  given: (hf : AnalyticOn 𝕜 f s)
  proof: fun x hx =>
  AnalyticAtWithin.compContinuousLinearMap (hf (u x) hx)

中文:
定理 AnalyticOn.compContinuousLinearMap
  条件: (hf : AnalyticOn 𝕜 f s)
  证明: fun x hx =>
  AnalyticAtWithin.compContinuousLinearMap (hf (u x) hx)
-/
theorem AnalyticOn.compContinuousLinearMap (hf : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (f ∘ u) (u ⁻¹' s) := fun x hx =>
  AnalyticAtWithin.compContinuousLinearMap (hf (u x) hx)

/--
theorem `AnalyticOnNhd.compContinuousLinearMap` / 定理 `AnalyticOnNhd.compContinuousLinearMap`

English:
theorem AnalyticOnNhd.compContinuousLinearMap
  given: (hf : AnalyticOnNhd 𝕜 f s)
  proof: fun x hx =>
  AnalyticAt.compContinuousLinearMap (hf (u x) hx)

中文:
定理 AnalyticOnNhd.compContinuousLinearMap
  条件: (hf : AnalyticOnNhd 𝕜 f s)
  证明: fun x hx =>
  AnalyticAt.compContinuousLinearMap (hf (u x) hx)
-/
theorem AnalyticOnNhd.compContinuousLinearMap (hf : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (f ∘ u) (u ⁻¹' s) := fun x hx =>
  AnalyticAt.compContinuousLinearMap (hf (u x) hx)

end compContinuousLinearMap

/-!
### Restriction of scalars
-/

section

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {f : E -> F} {p : FormalMultilinearSeries 𝕜' E F} {x : E} {s : Set E} {r : Real>=0∞}

/--
lemma `HasFPowerSeriesWithinOnBall.restrictScalars` / 引理 `HasFPowerSeriesWithinOnBall.restrictScalars`

English:
lemma HasFPowerSeriesWithinOnBall.restrictScalars
  given: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  proof: ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n => by simp)), hf.r_pos, hf.hasSum⟩

中文:
引理 HasFPowerSeriesWithinOnBall.restrictScalars
  条件: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  证明: ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n => by simp)), hf.r_pos, hf.hasSum⟩

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.radius_le_of_le, hasSum, hf.hasSum, hf.r_le.trans, hf.r_pos, r_le, r_pos, radius_le_of_le
-/
lemma HasFPowerSeriesWithinOnBall.restrictScalars (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    HasFPowerSeriesWithinOnBall f (p.restrictScalars 𝕜) s x r :=
  ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n => by simp)), hf.r_pos, hf.hasSum⟩

/--
lemma `HasFPowerSeriesOnBall.restrictScalars` / 引理 `HasFPowerSeriesOnBall.restrictScalars`

English:
lemma HasFPowerSeriesOnBall.restrictScalars
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n => by simp)), hf.r_pos, hf.hasSum⟩

中文:
引理 HasFPowerSeriesOnBall.restrictScalars
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n => by simp)), hf.r_pos, hf.hasSum⟩

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.radius_le_of_le, hasSum, hf.hasSum, hf.r_le.trans, hf.r_pos, r_le, r_pos, radius_le_of_le
-/
lemma HasFPowerSeriesOnBall.restrictScalars (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall f (p.restrictScalars 𝕜) x r :=
  ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n => by simp)), hf.r_pos, hf.hasSum⟩

/--
lemma `HasFPowerSeriesWithinAt.restrictScalars` / 引理 `HasFPowerSeriesWithinAt.restrictScalars`

English:
lemma HasFPowerSeriesWithinAt.restrictScalars
  given: (hf : HasFPowerSeriesWithinAt f p s x)
  proof: by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

中文:
引理 HasFPowerSeriesWithinAt.restrictScalars
  条件: (hf : HasFPowerSeriesWithinAt f p s x)
  证明: by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

Depends on / 依赖: hr.restrictScalars, restrictScalars
-/
lemma HasFPowerSeriesWithinAt.restrictScalars (hf : HasFPowerSeriesWithinAt f p s x) :
    HasFPowerSeriesWithinAt f (p.restrictScalars 𝕜) s x := by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

/--
lemma `HasFPowerSeriesAt.restrictScalars` / 引理 `HasFPowerSeriesAt.restrictScalars`

English:
lemma HasFPowerSeriesAt.restrictScalars
  given: (hf : HasFPowerSeriesAt f p x)
  proof: by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

中文:
引理 HasFPowerSeriesAt.restrictScalars
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

Depends on / 依赖: hr.restrictScalars, restrictScalars
-/
lemma HasFPowerSeriesAt.restrictScalars (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt f (p.restrictScalars 𝕜) x := by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

/--
lemma `AnalyticWithinAt.restrictScalars` / 引理 `AnalyticWithinAt.restrictScalars`

English:
lemma AnalyticWithinAt.restrictScalars
  given: (hf : AnalyticWithinAt 𝕜' f s x)
  proof: by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

中文:
引理 AnalyticWithinAt.restrictScalars
  条件: (hf : AnalyticWithinAt 𝕜' f s x)
  证明: by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

Depends on / 依赖: hp.restrictScalars, p.restrictScalars, restrictScalars
-/
lemma AnalyticWithinAt.restrictScalars (hf : AnalyticWithinAt 𝕜' f s x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

/--
lemma `AnalyticAt.restrictScalars` / 引理 `AnalyticAt.restrictScalars`

English:
lemma AnalyticAt.restrictScalars
  given: (hf : AnalyticAt 𝕜' f x)
  proof: by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

中文:
引理 AnalyticAt.restrictScalars
  条件: (hf : AnalyticAt 𝕜' f x)
  证明: by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

Depends on / 依赖: hp.restrictScalars, p.restrictScalars, restrictScalars
-/
lemma AnalyticAt.restrictScalars (hf : AnalyticAt 𝕜' f x) :
    AnalyticAt 𝕜 f x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

/--
lemma `AnalyticOn.restrictScalars` / 引理 `AnalyticOn.restrictScalars`

English:
lemma AnalyticOn.restrictScalars
  given: (hf : AnalyticOn 𝕜' f s)
  proof: fun x hx => (hf x hx).restrictScalars

中文:
引理 AnalyticOn.restrictScalars
  条件: (hf : AnalyticOn 𝕜' f s)
  证明: fun x hx => (hf x hx).restrictScalars

Depends on / 依赖: restrictScalars
-/
lemma AnalyticOn.restrictScalars (hf : AnalyticOn 𝕜' f s) :
    AnalyticOn 𝕜 f s :=
  fun x hx => (hf x hx).restrictScalars

/--
lemma `AnalyticOnNhd.restrictScalars` / 引理 `AnalyticOnNhd.restrictScalars`

English:
lemma AnalyticOnNhd.restrictScalars
  given: (hf : AnalyticOnNhd 𝕜' f s)
  proof: fun x hx => (hf x hx).restrictScalars

中文:
引理 AnalyticOnNhd.restrictScalars
  条件: (hf : AnalyticOnNhd 𝕜' f s)
  证明: fun x hx => (hf x hx).restrictScalars

Depends on / 依赖: restrictScalars
-/
lemma AnalyticOnNhd.restrictScalars (hf : AnalyticOnNhd 𝕜' f s) :
    AnalyticOnNhd 𝕜 f s :=
  fun x hx => (hf x hx).restrictScalars

end


/-!
### Inversion is analytic
-/

section Geometric
variable (𝕜 A)

/--
Definition of `formalMultilinearSeries_geometric` / `formalMultilinearSeries_geometric` 的定义

English:
definition formalMultilinearSeries_geometric
  signature: : FormalMultilinearSeries 𝕜 A A
  body: fun n => ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A

中文:
定义 formalMultilinearSeries_geometric
  签名: : FormalMultilinearSeries 𝕜 A A
  定义体: fun n => ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin, mkPiAlgebraFin
-/
def formalMultilinearSeries_geometric : FormalMultilinearSeries 𝕜 A A :=
  fun n => ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A

/--
theorem `formalMultilinearSeries_geometric_eq_ofScalars` / 定理 `formalMultilinearSeries_geometric_eq_ofScalars`

English:
theorem formalMultilinearSeries_geometric_eq_ofScalars
  proof: by
  simp_rw [FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.ofScalars,
    formalMultilinearSeries_geometric, one_smul, implies_true]

中文:
定理 formalMultilinearSeries_geometric_eq_ofScalars
  证明: by
  simp_rw [FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.ofScalars,
    formalMultilinearSeries_geometric, one_smul, implies_true]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.ofScalars, ext_iff, formalMultilinearSeries_geometric, implies_true, ofScalars, one_smul, simp_rw
-/
theorem formalMultilinearSeries_geometric_eq_ofScalars :
    formalMultilinearSeries_geometric 𝕜 A =
      FormalMultilinearSeries.ofScalars A fun _ => (1 : 𝕜) := by
  simp_rw [FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.ofScalars,
    formalMultilinearSeries_geometric, one_smul, implies_true]

/--
lemma `formalMultilinearSeries_geometric_apply_norm_le` / 引理 `formalMultilinearSeries_geometric_apply_norm_le`

English:
lemma formalMultilinearSeries_geometric_apply_norm_le
  given: (n : Nat)
  proof: ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

中文:
引理 formalMultilinearSeries_geometric_apply_norm_le
  条件: (n : 自然数)
  证明: ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_mkPiAlgebraFin_le, norm_mkPiAlgebraFin_le
-/
lemma formalMultilinearSeries_geometric_apply_norm_le (n : Nat) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ <= max 1 ‖(1 : A)‖ :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

/--
lemma `formalMultilinearSeries_geometric_apply_norm` / 引理 `formalMultilinearSeries_geometric_apply_norm`

English:
lemma formalMultilinearSeries_geometric_apply_norm
  given: [NormOneClass A] (n : Nat)
  proof: ContinuousMultilinearMap.norm_mkPiAlgebraFin

中文:
引理 formalMultilinearSeries_geometric_apply_norm
  条件: [NormOneClass A] (n : 自然数)
  证明: ContinuousMultilinearMap.norm_mkPiAlgebraFin

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_mkPiAlgebraFin, norm_mkPiAlgebraFin
-/
lemma formalMultilinearSeries_geometric_apply_norm [NormOneClass A] (n : Nat) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ = 1 :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin

/--
lemma `one_le_formalMultilinearSeries_geometric_radius` / 引理 `one_le_formalMultilinearSeries_geometric_radius`

English:
lemma one_le_formalMultilinearSeries_geometric_radius
  proof: by
  convert!
    formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
      FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto A _ one_ne_zero (by simp)
  simp

中文:
引理 one_le_formalMultilinearSeries_geometric_radius
  证明: by
  convert!
    formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
      FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto A _ one_ne_zero (by simp)
  simp

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto, convert, formalMultilinearSeries_geometric_eq_ofScalars, inv_le_ofScalars_radius_of_tendsto, one_ne_zero
-/
lemma one_le_formalMultilinearSeries_geometric_radius :
    1 <= (formalMultilinearSeries_geometric 𝕜 A).radius := by
  convert!
    formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
      FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto A _ one_ne_zero (by simp)
  simp

/--
lemma `formalMultilinearSeries_geometric_radius` / 引理 `formalMultilinearSeries_geometric_radius`

English:
lemma formalMultilinearSeries_geometric_radius
  given: [NormOneClass A]
  proof: formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
    FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)

中文:
引理 formalMultilinearSeries_geometric_radius
  条件: [NormOneClass A]
  证明: formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
    FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto, formalMultilinearSeries_geometric_eq_ofScalars, ofScalars_radius_eq_of_tendsto, one_ne_zero
-/
lemma formalMultilinearSeries_geometric_radius [NormOneClass A] :
    (formalMultilinearSeries_geometric 𝕜 A).radius = 1 :=
  formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
    FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)

/--
lemma `hasFPowerSeriesOnBall_inverse_one_sub` / 引理 `hasFPowerSeriesOnBall_inverse_one_sub`

English:
lemma hasFPowerSeriesOnBall_inverse_one_sub
  given: [HasSummableGeomSeries A]
  proof: by
  constructor
  · exact one_le_formalMultilinearSeries_geometric_radius 𝕜 A
  · exact one_pos
  · intro y hy
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ofReal_lt_one] at hy
    simp only [zero_add, NormedRing.inverse_one_sub _ hy, Units.oneSub, Units.inv_mk,
      formalMultili

中文:
引理 hasFPowerSeriesOnBall_inverse_one_sub
  条件: [HasSummableGeomSeries A]
  证明: by
  constructor
  · exact one_le_formalMultilinearSeries_geometric_radius 𝕜 A
  · exact one_pos
  · intro y hy
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ofReal_lt_one] at hy
    simp only [zero_add, NormedRing.inverse_one_sub _ hy, Units.oneSub, Units.inv_mk,
      formalMultili

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate, Metric, Metric.mem_eball, NormedRing, NormedRing.inverse_one_sub, Units.inv_mk, Units.oneSub, dist_zero_right, edist_dist, formalMultilinearSeries_geometric, hasSum, inv_mk, inverse_one_sub, mem_eball, mkPiAlgebraFin_apply, ofFn_const, ofReal_lt_one
-/
lemma hasFPowerSeriesOnBall_inverse_one_sub [HasSummableGeomSeries A] :
    HasFPowerSeriesOnBall (fun x : A => (1 - x)⁻¹ʳ)
      (formalMultilinearSeries_geometric 𝕜 A) 0 1 := by
  constructor
  · exact one_le_formalMultilinearSeries_geometric_radius 𝕜 A
  · exact one_pos
  · intro y hy
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ofReal_lt_one] at hy
    simp only [zero_add, NormedRing.inverse_one_sub _ hy, Units.oneSub, Units.inv_mk,
      formalMultilinearSeries_geometric, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.ofFn_const, List.prod_replicate]
    exact (summable_geometric_of_norm_lt_one hy).hasSum

@[fun_prop]
/--
lemma `analyticAt_inverse_one_sub` / 引理 `analyticAt_inverse_one_sub`

English:
lemma analyticAt_inverse_one_sub
  given: [HasSummableGeomSeries A]
  proof: ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A⟩⟩

中文:
引理 analyticAt_inverse_one_sub
  条件: [HasSummableGeomSeries A]
  证明: ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A⟩⟩

Depends on / 依赖: hasFPowerSeriesOnBall_inverse_one_sub
-/
lemma analyticAt_inverse_one_sub [HasSummableGeomSeries A] :
    AnalyticAt 𝕜 (fun x : A => (1 - x)⁻¹ʳ) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A⟩⟩

/--
Definition of `alternatingGeometricSeries` / `alternatingGeometricSeries` 的定义

English:
definition alternatingGeometricSeries
  signature: : FormalMultilinearSeries 𝕜 A A
  body: .ofScalars A fun n => (-1 : 𝕜) ^ n

中文:
定义 alternatingGeometricSeries
  签名: : FormalMultilinearSeries 𝕜 A A
  定义体: .ofScalars A fun n => (-1 : 𝕜) ^ n

Depends on / 依赖: ofScalars
-/
def alternatingGeometricSeries : FormalMultilinearSeries 𝕜 A A :=
  .ofScalars A fun n => (-1 : 𝕜) ^ n

/--
lemma `alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg` / 引理 `alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg`

English:
lemma alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg
  proof: by
  simp [formalMultilinearSeries_geometric_eq_ofScalars, alternatingGeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]

中文:
引理 alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg
  证明: by
  simp [formalMultilinearSeries_geometric_eq_ofScalars, alternatingGeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_comp_neg_id, alternatingGeometricSeries, formalMultilinearSeries_geometric_eq_ofScalars, ofScalars_comp_neg_id
-/
lemma alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg :
    alternatingGeometricSeries 𝕜 A =
    (formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap
      (-ContinuousLinearMap.id 𝕜 A) := by
  simp [formalMultilinearSeries_geometric_eq_ofScalars, alternatingGeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]

/--
lemma `alternatingGeometricSeries_apply_norm_le` / 引理 `alternatingGeometricSeries_apply_norm_le`

English:
lemma alternatingGeometricSeries_apply_norm_le
  given: (n : Nat)
  proof: by
  simpa [alternatingGeometricSeries] using
    ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

中文:
引理 alternatingGeometricSeries_apply_norm_le
  条件: (n : 自然数)
  证明: by
  simpa [alternatingGeometricSeries] using
    ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_mkPiAlgebraFin_le, alternatingGeometricSeries, norm_mkPiAlgebraFin_le
-/
lemma alternatingGeometricSeries_apply_norm_le (n : Nat) :
    ‖alternatingGeometricSeries 𝕜 A n‖ <= max 1 ‖(1 : A)‖ := by
  simpa [alternatingGeometricSeries] using
    ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

/--
lemma `alternatingGeometricSeries_apply_norm` / 引理 `alternatingGeometricSeries_apply_norm`

English:
lemma alternatingGeometricSeries_apply_norm
  given: [NormOneClass A] (n : Nat)
  proof: by
  simp [alternatingGeometricSeries]

中文:
引理 alternatingGeometricSeries_apply_norm
  条件: [NormOneClass A] (n : 自然数)
  证明: by
  simp [alternatingGeometricSeries]

Depends on / 依赖: alternatingGeometricSeries
-/
lemma alternatingGeometricSeries_apply_norm [NormOneClass A] (n : Nat) :
    ‖alternatingGeometricSeries 𝕜 A n‖ = 1 := by
  simp [alternatingGeometricSeries]

/--
lemma `one_le_alternatingGeometricSeries_radius` / 引理 `one_le_alternatingGeometricSeries_radius`

English:
lemma one_le_alternatingGeometricSeries_radius
  given: [Nontrivial A]
  proof: by
  simpa only [FormalMultilinearSeries.radius_compNeg,
    alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
    using one_le_formalMultilinearSeries_geometric_radius 𝕜 A

中文:
引理 one_le_alternatingGeometricSeries_radius
  条件: [Nontrivial A]
  证明: by
  simpa only [FormalMultilinearSeries.radius_compNeg,
    alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
    using one_le_formalMultilinearSeries_geometric_radius 𝕜 A

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.radius_compNeg, alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg, one_le_formalMultilinearSeries_geometric_radius, radius_compNeg
-/
lemma one_le_alternatingGeometricSeries_radius [Nontrivial A] :
    1 <= (alternatingGeometricSeries 𝕜 A).radius := by
  simpa only [FormalMultilinearSeries.radius_compNeg,
    alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
    using one_le_formalMultilinearSeries_geometric_radius 𝕜 A

/--
lemma `alternatingGeometricSeries_radius` / 引理 `alternatingGeometricSeries_radius`

English:
lemma alternatingGeometricSeries_radius
  given: [NormOneClass A]
  proof: FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)

中文:
引理 alternatingGeometricSeries_radius
  条件: [NormOneClass A]
  证明: FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto, ofScalars_radius_eq_of_tendsto, one_ne_zero
-/
lemma alternatingGeometricSeries_radius [NormOneClass A] :
    (alternatingGeometricSeries 𝕜 A).radius = 1 :=
  FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto A _ one_ne_zero (by simp)

/--
lemma `hasFPowerSeriesOnBall_inverse_one_add` / 引理 `hasFPowerSeriesOnBall_inverse_one_add`

English:
lemma hasFPowerSeriesOnBall_inverse_one_add
  given: [HasSummableGeomSeries A] [Nontrivial A]
  proof: by
  rw [alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
  convert_to HasFPowerSeriesOnBall ((fun x => Ring.inverse (1 - x)) ∘ (-ContinuousLinearMap.id 𝕜 A))
    ((formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap (-ContinuousLinearMap.id 𝕜 A))
    0 1
  · ext;

中文:
引理 hasFPowerSeriesOnBall_inverse_one_add
  条件: [HasSummableGeomSeries A] [Nontrivial A]
  证明: by
  rw [alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
  convert_to HasFPowerSeriesOnBall ((fun x => Ring.inverse (1 - x)) ∘ (-ContinuousLinearMap.id 𝕜 A))
    ((formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap (-ContinuousLinearMap.id 𝕜 A))
    0 1
  · ext;

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, HasFPowerSeriesOnBall, HasFPowerSeriesOnBall.compContinuousLinearMap, Ring.inverse, alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg, compContinuousLinearMap, convert, convert_to, formalMultilinearSeries_geometric, hasFPowerSeriesOnBall_inverse_one_sub, inverse, ofReal_norm
-/
lemma hasFPowerSeriesOnBall_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] :
    HasFPowerSeriesOnBall (fun x : A => Ring.inverse (1 + x))
      (alternatingGeometricSeries 𝕜 A) 0 1 := by
  rw [alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
  convert_to HasFPowerSeriesOnBall ((fun x => Ring.inverse (1 - x)) ∘ (-ContinuousLinearMap.id 𝕜 A))
    ((formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap (-ContinuousLinearMap.id 𝕜 A))
    0 1
  · ext; simp
  convert HasFPowerSeriesOnBall.compContinuousLinearMap _ (r := 1)
  · simp [← ofReal_norm]
  · simpa using (hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A)

@[fun_prop]
/--
lemma `analyticAt_inverse_one_add` / 引理 `analyticAt_inverse_one_add`

English:
lemma analyticAt_inverse_one_add
  given: [HasSummableGeomSeries A] [Nontrivial A]
  proof: ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_add 𝕜 A⟩⟩

中文:
引理 analyticAt_inverse_one_add
  条件: [HasSummableGeomSeries A] [Nontrivial A]
  证明: ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_add 𝕜 A⟩⟩

Depends on / 依赖: hasFPowerSeriesOnBall_inverse_one_add
-/
lemma analyticAt_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] :
    AnalyticAt 𝕜 (fun x : A => Ring.inverse (1 + x)) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_add 𝕜 A⟩⟩

end Geometric

/-- If `A` is a normed algebra over `𝕜` with summable geometric series, then inversion on `A` is
analytic at any unit. -/
@[fun_prop]
/--
lemma `analyticAt_inverse` / 引理 `analyticAt_inverse`

English:
lemma analyticAt_inverse
  given: [HasSummableGeomSeries A] (z : Aˣ)
  proof: by
  rcases subsingleton_or_nontrivial A with hA | hA
  · convert! analyticAt_const (v := (0 : A))
  · let f1 : A -> A := fun a => a * z.inv
    let f2 : A -> A := fun b => (1 - b)⁻¹ʳ
    let f3 : A -> A := fun c => 1 - z.inv * c
    have feq : forallᶠ y in 𝓝 (z : A), (f1 ∘ f2 ∘ f3) y = y⁻¹ʳ := by
 

中文:
引理 analyticAt_inverse
  条件: [HasSummableGeomSeries A] (z : Aˣ)
  证明: by
  rcases subsingleton_or_nontrivial A with hA | hA
  · convert! analyticAt_const (v := (0 : A))
  · let f1 : A -> A := fun a => a * z.inv
    let f2 : A -> A := fun b => (1 - b)⁻¹ʳ
    let f3 : A -> A := fun c => 1 - z.inv * c
    have feq : forallᶠ y in 𝓝 (z : A), (f1 ∘ f2 ∘ f3) y = y⁻¹ʳ := by
 

Depends on / 依赖: Metric, Metric.ball, Metric.ball_mem_nhds, Metric.mem_ball, Units.ofNearby, analyticAt_const, ball_mem_nhds, convert, dist_eq_norm, filter_upwards, mem_ball, ofNearby, subsingleton_or_nontrivial, z.inv
-/
lemma analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ) :
    AnalyticAt 𝕜 Ring.inverse (z : A) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · convert! analyticAt_const (v := (0 : A))
  · let f1 : A -> A := fun a => a * z.inv
    let f2 : A -> A := fun b => (1 - b)⁻¹ʳ
    let f3 : A -> A := fun c => 1 - z.inv * c
    have feq : forallᶠ y in 𝓝 (z : A), (f1 ∘ f2 ∘ f3) y = y⁻¹ʳ := by
      have : Metric.ball (z : A) (‖(↑z⁻¹ : A)‖⁻¹) in 𝓝 (z : A) := by
        apply Metric.ball_mem_nhds
        simp
      filter_upwards [this] with y hy
      simp only [Metric.mem_ball, dist_eq_norm] at hy
      have : y = Units.ofNearby z y hy := rfl
      rw [this]; rw [Eq.comm]
      simp only [Ring.inverse_unit, Function.comp_apply]
      simp only [Units.ofNearby, Units.add, mul_sub, Units.inv_mul, neg_sub, add_sub_cancel,
        mul_inv_rev, Units.val_mul, Units.val_inv_copy, Units.inv_eq_val_inv, Units.val_copy,
        _root_.sub_sub_cancel, Units.mul_left_inj, f1, f2, f3]
      rw [← Ring.inverse_unit]
      congr
      simp
    apply AnalyticAt.congr _ feq
    apply (analyticAt_id.mul analyticAt_const).comp
    apply AnalyticAt.comp
    · simp only [Units.inv_eq_val_inv, Units.inv_mul, sub_self, f2, f3]
      exact analyticAt_inverse_one_sub 𝕜 A
    · exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)

/--
lemma `analyticOnNhd_inverse` / 引理 `analyticOnNhd_inverse`

English:
lemma analyticOnNhd_inverse
  given: [HasSummableGeomSeries A]
  proof: fun _ hx => analyticAt_inverse (IsUnit.unit hx)

中文:
引理 analyticOnNhd_inverse
  条件: [HasSummableGeomSeries A]
  证明: fun _ hx => analyticAt_inverse (IsUnit.unit hx)

Depends on / 依赖: IsUnit, IsUnit.unit, analyticAt_inverse
-/
lemma analyticOnNhd_inverse [HasSummableGeomSeries A] :
    AnalyticOnNhd 𝕜 Ring.inverse {x : A | IsUnit x} :=
  fun _ hx => analyticAt_inverse (IsUnit.unit hx)

variable (𝕜 𝕝) in
/--
lemma `hasFPowerSeriesOnBall_inv_one_sub` / 引理 `hasFPowerSeriesOnBall_inv_one_sub`

English:
lemma hasFPowerSeriesOnBall_inv_one_sub
  proof: by
  convert! hasFPowerSeriesOnBall_inverse_one_sub 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

中文:
引理 hasFPowerSeriesOnBall_inv_one_sub
  证明: by
  convert! hasFPowerSeriesOnBall_inverse_one_sub 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

Depends on / 依赖: Ring.inverse_eq_inv, convert, hasFPowerSeriesOnBall_inverse_one_sub, inverse_eq_inv
-/
lemma hasFPowerSeriesOnBall_inv_one_sub :
    HasFPowerSeriesOnBall (fun x : 𝕝 => (1 - x)⁻¹) (formalMultilinearSeries_geometric 𝕜 𝕝) 0 1 := by
  convert! hasFPowerSeriesOnBall_inverse_one_sub 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

variable (𝕝) in
@[fun_prop]
/--
lemma `analyticAt_inv_one_sub` / 引理 `analyticAt_inv_one_sub`

English:
lemma analyticAt_inv_one_sub
  statement: AnalyticAt 𝕜 (fun x : 𝕝 => (1 - x)⁻¹) 0
  proof: ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_sub 𝕜 𝕝⟩⟩

中文:
引理 analyticAt_inv_one_sub
  结论: AnalyticAt 𝕜 (fun x : 𝕝 => (1 - x)⁻¹) 0
  证明: ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_sub 𝕜 𝕝⟩⟩

Depends on / 依赖: hasFPowerSeriesOnBall_inv_one_sub
-/
lemma analyticAt_inv_one_sub : AnalyticAt 𝕜 (fun x : 𝕝 => (1 - x)⁻¹) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_sub 𝕜 𝕝⟩⟩

variable (𝕜 𝕝) in
/--
lemma `hasFPowerSeriesOnBall_inv_one_add` / 引理 `hasFPowerSeriesOnBall_inv_one_add`

English:
lemma hasFPowerSeriesOnBall_inv_one_add
  proof: by
  convert! hasFPowerSeriesOnBall_inverse_one_add 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

中文:
引理 hasFPowerSeriesOnBall_inv_one_add
  证明: by
  convert! hasFPowerSeriesOnBall_inverse_one_add 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

Depends on / 依赖: Ring.inverse_eq_inv, convert, hasFPowerSeriesOnBall_inverse_one_add, inverse_eq_inv
-/
lemma hasFPowerSeriesOnBall_inv_one_add :
    HasFPowerSeriesOnBall (fun x : 𝕝 => (1 + x)⁻¹) (alternatingGeometricSeries 𝕜 𝕝) 0 1 := by
  convert! hasFPowerSeriesOnBall_inverse_one_add 𝕜 𝕝
  exact Ring.inverse_eq_inv'.symm

variable (𝕝) in
@[fun_prop]
/--
lemma `analyticAt_inv_one_add` / 引理 `analyticAt_inv_one_add`

English:
lemma analyticAt_inv_one_add
  statement: AnalyticAt 𝕜 (fun x : 𝕝 => (1 + x)⁻¹) 0
  proof: ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_add 𝕜 𝕝⟩⟩

中文:
引理 analyticAt_inv_one_add
  结论: AnalyticAt 𝕜 (fun x : 𝕝 => (1 + x)⁻¹) 0
  证明: ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_add 𝕜 𝕝⟩⟩

Depends on / 依赖: hasFPowerSeriesOnBall_inv_one_add
-/
lemma analyticAt_inv_one_add : AnalyticAt 𝕜 (fun x : 𝕝 => (1 + x)⁻¹) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_add 𝕜 𝕝⟩⟩

/-- If `𝕝` is a normed field extension of `𝕜`, then the inverse map `𝕝 → 𝕝` is `𝕜`-analytic
away from 0. -/
@[fun_prop]
/--
lemma `analyticAt_inv` / 引理 `analyticAt_inv`

English:
lemma analyticAt_inv
  given: {z : 𝕝} (hz : z != 0)
  statement: AnalyticAt 𝕜 Inv.inv z
  proof: by
  convert! analyticAt_inverse (𝕜 := 𝕜) (Units.mk0 _ hz)
  exact Ring.inverse_eq_inv'.symm

中文:
引理 analyticAt_inv
  条件: {z : 𝕝} (hz : z != 0)
  结论: AnalyticAt 𝕜 Inv.inv z
  证明: by
  convert! analyticAt_inverse (𝕜 := 𝕜) (Units.mk0 _ hz)
  exact Ring.inverse_eq_inv'.symm

Depends on / 依赖: Ring.inverse_eq_inv, Units.mk0, analyticAt_inverse, convert, inverse_eq_inv
-/
lemma analyticAt_inv {z : 𝕝} (hz : z != 0) : AnalyticAt 𝕜 Inv.inv z := by
  convert! analyticAt_inverse (𝕜 := 𝕜) (Units.mk0 _ hz)
  exact Ring.inverse_eq_inv'.symm

/--
lemma `analyticOnNhd_inv` / 引理 `analyticOnNhd_inv`

English:
lemma analyticOnNhd_inv
  statement: AnalyticOnNhd 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0}
  proof: by
  intro z m; exact analyticAt_inv m

中文:
引理 analyticOnNhd_inv
  结论: AnalyticOnNhd 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0}
  证明: by
  intro z m; exact analyticAt_inv m

Depends on / 依赖: analyticAt_inv
-/
lemma analyticOnNhd_inv : AnalyticOnNhd 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0} := by
  intro z m; exact analyticAt_inv m

/--
lemma `analyticOn_inv` / 引理 `analyticOn_inv`

English:
lemma analyticOn_inv
  statement: AnalyticOn 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0}
  proof: analyticOnNhd_inv.analyticOn

中文:
引理 analyticOn_inv
  结论: AnalyticOn 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0}
  证明: analyticOnNhd_inv.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_inv, analyticOnNhd_inv.analyticOn
-/
lemma analyticOn_inv : AnalyticOn 𝕜 (fun z => z⁻¹) {z : 𝕝 | z != 0} :=
  analyticOnNhd_inv.analyticOn

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun]
/--
theorem `AnalyticWithinAt.inv` / 定理 `AnalyticWithinAt.inv`

English:
theorem AnalyticWithinAt.inv
  statement: {f : E -> 𝕝} {x : E} {s : Set E} (fa : AnalyticWithinAt 𝕜 f s x)
  proof: (analyticAt_inv f0).comp_analyticWithinAt fa

中文:
定理 AnalyticWithinAt.inv
  结论: {f : E -> 𝕝} {x : E} {s : Set E} (fa : AnalyticWithinAt 𝕜 f s x)
  证明: (analyticAt_inv f0).comp_analyticWithinAt fa

Depends on / 依赖: analyticAt_inv, comp_analyticWithinAt
-/
theorem AnalyticWithinAt.inv {f : E -> 𝕝} {x : E} {s : Set E} (fa : AnalyticWithinAt 𝕜 f s x)
    (f0 : f x != 0) :
    AnalyticWithinAt 𝕜 f⁻¹ s x :=
  (analyticAt_inv f0).comp_analyticWithinAt fa

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.inv` / 定理 `AnalyticAt.inv`

English:
theorem AnalyticAt.inv
  given: {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x != 0)
  proof: (analyticAt_inv f0).comp fa

中文:
定理 AnalyticAt.inv
  条件: {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x != 0)
  证明: (analyticAt_inv f0).comp fa

Depends on / 依赖: analyticAt_inv
-/
theorem AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x != 0) :
    AnalyticAt 𝕜 f⁻¹ x :=
  (analyticAt_inv f0).comp fa

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun]
/--
theorem `AnalyticOn.inv` / 定理 `AnalyticOn.inv`

English:
theorem AnalyticOn.inv
  given: {f : E -> 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : forall x in s, f x != 0)
  proof: fun x m => (fa x m).inv (f0 x m)

中文:
定理 AnalyticOn.inv
  条件: {f : E -> 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : 对任意 x in s, f x != 0)
  证明: fun x m => (fa x m).inv (f0 x m)
-/
theorem AnalyticOn.inv {f : E -> 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : forall x in s, f x != 0) :
    AnalyticOn 𝕜 f⁻¹ s :=
  fun x m => (fa x m).inv (f0 x m)

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
@[to_fun]
/--
theorem `AnalyticOnNhd.inv` / 定理 `AnalyticOnNhd.inv`

English:
theorem AnalyticOnNhd.inv
  statement: {f : E -> 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s)
  proof: fun x m => (fa x m).inv (f0 x m)

中文:
定理 AnalyticOnNhd.inv
  结论: {f : E -> 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s)
  证明: fun x m => (fa x m).inv (f0 x m)
-/
theorem AnalyticOnNhd.inv {f : E -> 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s)
    (f0 : forall x in s, f x != 0) :
    AnalyticOnNhd 𝕜 f⁻¹ s :=
  fun x m => (fa x m).inv (f0 x m)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/--
lemma `AnalyticWithinAt.zpow` / 引理 `AnalyticWithinAt.zpow`

English:
lemma AnalyticWithinAt.zpow
  statement: {f : E -> 𝕝} {z : E} {s : Set E} {n : Int}
  proof: by
  by_cases hn : 0 <= n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

中文:
引理 AnalyticWithinAt.zpow
  结论: {f : E -> 𝕝} {z : E} {s : Set E} {n : 整数}
  证明: by
  by_cases hn : 0 <= n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

Depends on / 依赖: Int.eq_neg_comm.mp, eq_neg_comm, f.zpow_nonneg, zpow_ne_zero, zpow_neg, zpow_nonneg
-/
lemma AnalyticWithinAt.zpow {f : E -> 𝕝} {z : E} {s : Set E} {n : Int}
    (h₁f : AnalyticWithinAt 𝕜 f s z) (h₂f : f z != 0) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  by_cases hn : 0 <= n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/--
lemma `AnalyticAt.zpow` / 引理 `AnalyticAt.zpow`

English:
lemma AnalyticAt.zpow
  given: {f : E -> 𝕝} {z : E} {n : Int} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z != 0)
  proof: by
  by_cases hn : 0 <= n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

中文:
引理 AnalyticAt.zpow
  条件: {f : E -> 𝕝} {z : E} {n : 整数} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z != 0)
  证明: by
  by_cases hn : 0 <= n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

Depends on / 依赖: Int.eq_neg_comm.mp, eq_neg_comm, f.zpow_nonneg, zpow_ne_zero, zpow_neg, zpow_nonneg
-/
lemma AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z != 0) :
    AnalyticAt 𝕜 (f ^ n) z := by
  by_cases hn : 0 <= n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = -(-n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/--
lemma `AnalyticOn.zpow` / 引理 `AnalyticOn.zpow`

English:
lemma AnalyticOn.zpow
  statement: {f : E -> 𝕝} {s : Set E} {n : Int} (h₁f : AnalyticOn 𝕜 f s)
  proof: fun z hz => (h₁f z hz).zpow (h₂f z hz)

中文:
引理 AnalyticOn.zpow
  结论: {f : E -> 𝕝} {s : Set E} {n : 整数} (h₁f : AnalyticOn 𝕜 f s)
  证明: fun z hz => (h₁f z hz).zpow (h₂f z hz)
-/
lemma AnalyticOn.zpow {f : E -> 𝕝} {s : Set E} {n : Int} (h₁f : AnalyticOn 𝕜 f s)
    (h₂f : forall z in s, f z != 0) :
    AnalyticOn 𝕜 (f ^ n) s :=
  fun z hz => (h₁f z hz).zpow (h₂f z hz)

/-- ZPowers of analytic functions (into a normed field over `𝕜`) are analytic away from the zeros.
-/
@[to_fun]
/--
lemma `AnalyticOnNhd.zpow` / 引理 `AnalyticOnNhd.zpow`

English:
lemma AnalyticOnNhd.zpow
  statement: {f : E -> 𝕝} {s : Set E} {n : Int} (h₁f : AnalyticOnNhd 𝕜 f s)
  proof: fun z hz => (h₁f z hz).zpow (h₂f z hz)

中文:
引理 AnalyticOnNhd.zpow
  结论: {f : E -> 𝕝} {s : Set E} {n : 整数} (h₁f : AnalyticOnNhd 𝕜 f s)
  证明: fun z hz => (h₁f z hz).zpow (h₂f z hz)
-/
lemma AnalyticOnNhd.zpow {f : E -> 𝕝} {s : Set E} {n : Int} (h₁f : AnalyticOnNhd 𝕜 f s)
    (h₂f : forall z in s, f z != 0) :
    AnalyticOnNhd 𝕜 (f ^ n) s :=
  fun z hz => (h₁f z hz).zpow (h₂f z hz)

/--
theorem `analyticAt_iff_analytic_fun_smul` / 定理 `analyticAt_iff_analytic_fun_smul`

English:
theorem analyticAt_iff_analytic_fun_smul
  statement: [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
  proof: by
  constructor
  · exact fun a => h₁f.smul a
  · intro hprod
    rw [analyticAt_congr (g := (f⁻¹ • f) • g)]; rw [smul_assoc]
    · exact (h₁f.inv h₂f).fun_smul hprod
    · filter_upwards [h₁f.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.2 h₂f)]
      intro y hy
      rw [Set.preima

中文:
定理 analyticAt_iff_analytic_fun_smul
  结论: [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
  证明: by
  constructor
  · exact fun a => h₁f.smul a
  · intro hprod
    rw [analyticAt_congr (g := (f⁻¹ • f) • g)]; rw [smul_assoc]
    · exact (h₁f.inv h₂f).fun_smul hprod
    · filter_upwards [h₁f.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.2 h₂f)]
      intro y hy
      rw [Set.preima

Depends on / 依赖: Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.preimage_compl, analyticAt_congr, compl_singleton_mem_nhds_iff, continuousAt, f.continuousAt.preimage_mem_nhds, f.inv, f.smul, filter_upwards, fun_smul, mem_compl_iff, mem_preimage, mem_singleton_iff, preimage_compl, preimage_mem_nhds, smul_assoc
-/
theorem analyticAt_iff_analytic_fun_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E -> 𝕝} {g : E -> F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z != 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (fun z => f z • g z) z := by
  constructor
  · exact fun a => h₁f.smul a
  · intro hprod
    rw [analyticAt_congr (g := (f⁻¹ • f) • g)]; rw [smul_assoc]
    · exact (h₁f.inv h₂f).fun_smul hprod
    · filter_upwards [h₁f.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.2 h₂f)]
      intro y hy
      rw [Set.preimage_compl]; rw [Set.mem_compl_iff]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hy
      simp [hy]

/--
theorem `analyticAt_iff_analytic_smul` / 定理 `analyticAt_iff_analytic_smul`

English:
theorem analyticAt_iff_analytic_smul
  statement: [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
  proof: analyticAt_iff_analytic_fun_smul h₁f h₂f

中文:
定理 analyticAt_iff_analytic_smul
  结论: [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
  证明: analyticAt_iff_analytic_fun_smul h₁f h₂f

Depends on / 依赖: analyticAt_iff_analytic_fun_smul
-/
theorem analyticAt_iff_analytic_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E -> 𝕝} {g : E -> F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z != 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f • g) z :=
  analyticAt_iff_analytic_fun_smul h₁f h₂f

/-- A function is analytic at a point iff it is analytic after multiplication
with a non-vanishing analytic function. -/
@[to_fun analyticAt_iff_analytic_fun_mul]
/--
theorem `analyticAt_iff_analytic_mul` / 定理 `analyticAt_iff_analytic_mul`

English:
theorem analyticAt_iff_analytic_mul
  statement: {f g : E -> 𝕝} {z : E} (h₁f : AnalyticAt 𝕜 f z)
  proof: by
  simp_rw [← smul_eq_mul]
  exact analyticAt_iff_analytic_smul h₁f h₂f

中文:
定理 analyticAt_iff_analytic_mul
  结论: {f g : E -> 𝕝} {z : E} (h₁f : AnalyticAt 𝕜 f z)
  证明: by
  simp_rw [← smul_eq_mul]
  exact analyticAt_iff_analytic_smul h₁f h₂f

Depends on / 依赖: analyticAt_iff_analytic_smul, simp_rw, smul_eq_mul
-/
theorem analyticAt_iff_analytic_mul {f g : E -> 𝕝} {z : E} (h₁f : AnalyticAt 𝕜 f z)
    (h₂f : f z != 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f * g) z := by
  simp_rw [← smul_eq_mul]
  exact analyticAt_iff_analytic_smul h₁f h₂f

/--
theorem `AnalyticWithinAt.div` / 定理 `AnalyticWithinAt.div`

English:
theorem AnalyticWithinAt.div
  statement: {f g : E -> 𝕝} {s : Set E} {x : E}
  proof: by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

中文:
定理 AnalyticWithinAt.div
  结论: {f g : E -> 𝕝} {s : Set E} {x : E}
  证明: by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

Depends on / 依赖: div_eq_mul_inv, fa.mul, ga.inv, simp_rw
-/
theorem AnalyticWithinAt.div {f g : E -> 𝕝} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (ga : AnalyticWithinAt 𝕜 g s x) (g0 : g x != 0) :
    AnalyticWithinAt 𝕜 (fun x => f x / g x) s x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- `f x / g x` is analytic away from `g x = 0` -/
@[to_fun (attr := fun_prop)]
/--
theorem `AnalyticAt.div` / 定理 `AnalyticAt.div`

English:
theorem AnalyticAt.div
  statement: {f g : E -> 𝕝} {x : E}
  proof: by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

中文:
定理 AnalyticAt.div
  结论: {f g : E -> 𝕝} {x : E}
  证明: by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

Depends on / 依赖: div_eq_mul_inv, fa.mul, ga.inv, simp_rw
-/
theorem AnalyticAt.div {f g : E -> 𝕝} {x : E}
    (fa : AnalyticAt 𝕜 f x) (ga : AnalyticAt 𝕜 g x) (g0 : g x != 0) :
    AnalyticAt 𝕜 (f / g) x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/--
theorem `AnalyticOn.div` / 定理 `AnalyticOn.div`

English:
theorem AnalyticOn.div
  statement: {f g : E -> 𝕝} {s : Set E}
  proof: fun x m =>
  (fa x m).div (ga x m) (g0 x m)

中文:
定理 AnalyticOn.div
  结论: {f g : E -> 𝕝} {s : Set E}
  证明: fun x m =>
  (fa x m).div (ga x m) (g0 x m)
-/
theorem AnalyticOn.div {f g : E -> 𝕝} {s : Set E}
    (fa : AnalyticOn 𝕜 f s) (ga : AnalyticOn 𝕜 g s) (g0 : forall x in s, g x != 0) :
    AnalyticOn 𝕜 (fun x => f x / g x) s := fun x m =>
  (fa x m).div (ga x m) (g0 x m)

/--
theorem `AnalyticOnNhd.div` / 定理 `AnalyticOnNhd.div`

English:
theorem AnalyticOnNhd.div
  statement: {f g : E -> 𝕝} {s : Set E}
  proof: fun x m =>
  (fa x m).div (ga x m) (g0 x m)

中文:
定理 AnalyticOnNhd.div
  结论: {f g : E -> 𝕝} {s : Set E}
  证明: fun x m =>
  (fa x m).div (ga x m) (g0 x m)
-/
theorem AnalyticOnNhd.div {f g : E -> 𝕝} {s : Set E}
    (fa : AnalyticOnNhd 𝕜 f s) (ga : AnalyticOnNhd 𝕜 g s) (g0 : forall x in s, g x != 0) :
    AnalyticOnNhd 𝕜 (fun x => f x / g x) s := fun x m =>
  (fa x m).div (ga x m) (g0 x m)

/-!
### Finite sums and products of analytic functions
-/

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticWithinAt_fun_sum]
/--
theorem `Finset.analyticWithinAt_sum` / 定理 `Finset.analyticWithinAt_sum`

English:
theorem Finset.analyticWithinAt_sum
  statement: {f : α -> E -> F} {c : E} {s : Set E}
  proof: by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.sum_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).add (hB fun b m => h b (Or.inr m))

中文:
定理 Finset.analyticWithinAt_sum
  结论: {f : α -> E -> F} {c : E} {s : Set E}
  证明: by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.sum_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).add (hB fun b m => h b (Or.inr m))

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert, Finset.sum_empty, Finset.sum_insert, Or.inl, Or.inr, analyticWithinAt_const, classical, insert, mem_insert, simp_rw, sum_empty, sum_insert
-/
theorem Finset.analyticWithinAt_sum {f : α -> E -> F} {c : E} {s : Set E}
    (N : Finset α) (h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (∑ n in N, f n) s c := by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.sum_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).add (hB fun b m => h b (Or.inr m))

/-- Finite sums of analytic functions are analytic -/
@[to_fun (attr := fun_prop) Finset.analyticAt_fun_sum]
/--
theorem `Finset.analyticAt_sum` / 定理 `Finset.analyticAt_sum`

English:
theorem Finset.analyticAt_sum
  statement: {f : α -> E -> F} {c : E}
  proof: by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_sum h

中文:
定理 Finset.analyticAt_sum
  结论: {f : α -> E -> F} {c : E}
  证明: by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_sum h

Depends on / 依赖: N.analyticWithinAt_sum, analyticWithinAt_sum, analyticWithinAt_univ, simp_rw
-/
theorem Finset.analyticAt_sum {f : α -> E -> F} {c : E}
    (N : Finset α) (h : forall n in N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (∑ n in N, f n) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_sum h

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticOn_fun_sum]
/--
theorem `Finset.analyticOn_sum` / 定理 `Finset.analyticOn_sum`

English:
theorem Finset.analyticOn_sum
  statement: {f : α -> E -> F} {s : Set E}
  proof: fun z zs => N.analyticWithinAt_sum (fun n m => h n m z zs)

中文:
定理 Finset.analyticOn_sum
  结论: {f : α -> E -> F} {s : Set E}
  证明: fun z zs => N.analyticWithinAt_sum (fun n m => h n m z zs)

Depends on / 依赖: N.analyticWithinAt_sum, analyticWithinAt_sum
-/
theorem Finset.analyticOn_sum {f : α -> E -> F} {s : Set E}
    (N : Finset α) (h : forall n in N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (∑ n in N, f n) s :=
  fun z zs => N.analyticWithinAt_sum (fun n m => h n m z zs)

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticOnNhd_fun_sum]
/--
theorem `Finset.analyticOnNhd_sum` / 定理 `Finset.analyticOnNhd_sum`

English:
theorem Finset.analyticOnNhd_sum
  statement: {f : α -> E -> F} {s : Set E}
  proof: fun z zs => N.analyticAt_sum (fun n m => h n m z zs)

中文:
定理 Finset.analyticOnNhd_sum
  结论: {f : α -> E -> F} {s : Set E}
  证明: fun z zs => N.analyticAt_sum (fun n m => h n m z zs)

Depends on / 依赖: N.analyticAt_sum, analyticAt_sum
-/
theorem Finset.analyticOnNhd_sum {f : α -> E -> F} {s : Set E}
    (N : Finset α) (h : forall n in N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (∑ n in N, f n) s :=
  fun z zs => N.analyticAt_sum (fun n m => h n m z zs)

/--
theorem `Finset.analyticWithinAt_fun_prod` / 定理 `Finset.analyticWithinAt_fun_prod`

English:
theorem Finset.analyticWithinAt_fun_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.prod_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).mul (hB fun b m => h b (Or.inr m))

中文:
定理 Finset.analyticWithinAt_fun_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.prod_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).mul (hB fun b m => h b (Or.inr m))

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert, Finset.prod_empty, Finset.prod_insert, Or.inl, Or.inr, analyticWithinAt_const, classical, insert, mem_insert, prod_empty, prod_insert, simp_rw
-/
theorem Finset.analyticWithinAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {c : E} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (fun z => ∏ n in N, f n z) s c := by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.prod_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).mul (hB fun b m => h b (Or.inr m))

/--
theorem `Finset.analyticWithinAt_prod` / 定理 `Finset.analyticWithinAt_prod`

English:
theorem Finset.analyticWithinAt_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: by
  convert! N.analyticWithinAt_fun_prod h
  simp

中文:
定理 Finset.analyticWithinAt_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: by
  convert! N.analyticWithinAt_fun_prod h
  simp

Depends on / 依赖: N.analyticWithinAt_fun_prod, analyticWithinAt_fun_prod, convert
-/
theorem Finset.analyticWithinAt_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {c : E} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (∏ n in N, f n) s c := by
  convert! N.analyticWithinAt_fun_prod h
  simp

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
/--
theorem `Finset.analyticAt_fun_prod` / 定理 `Finset.analyticAt_fun_prod`

English:
theorem Finset.analyticAt_fun_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_fun_prod h

中文:
定理 Finset.analyticAt_fun_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_fun_prod h

Depends on / 依赖: N.analyticWithinAt_fun_prod, analyticWithinAt_fun_prod, analyticWithinAt_univ, simp_rw
-/
theorem Finset.analyticAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {c : E} (N : Finset α) (h : forall n in N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (fun z => ∏ n in N, f n z) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_fun_prod h

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
/--
theorem `Finset.analyticAt_prod` / 定理 `Finset.analyticAt_prod`

English:
theorem Finset.analyticAt_prod
  statement: {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: by
  convert! N.analyticAt_fun_prod h
  simp

中文:
定理 Finset.analyticAt_prod
  结论: {α : 类型} {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: by
  convert! N.analyticAt_fun_prod h
  simp

Depends on / 依赖: N.analyticAt_fun_prod, analyticAt_fun_prod, convert
-/
theorem Finset.analyticAt_prod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {c : E} (N : Finset α) (h : forall n in N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (∏ n in N, f n) c := by
  convert! N.analyticAt_fun_prod h
  simp

/--
theorem `Finset.analyticOn_fun_prod` / 定理 `Finset.analyticOn_fun_prod`

English:
theorem Finset.analyticOn_fun_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: fun z zs => N.analyticWithinAt_fun_prod (fun n m => h n m z zs)

中文:
定理 Finset.analyticOn_fun_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: fun z zs => N.analyticWithinAt_fun_prod (fun n m => h n m z zs)

Depends on / 依赖: N.analyticWithinAt_fun_prod, analyticWithinAt_fun_prod
-/
theorem Finset.analyticOn_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (fun z => ∏ n in N, f n z) s :=
  fun z zs => N.analyticWithinAt_fun_prod (fun n m => h n m z zs)

/--
theorem `Finset.analyticOn_prod` / 定理 `Finset.analyticOn_prod`

English:
theorem Finset.analyticOn_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: fun z zs => N.analyticWithinAt_prod (fun n m => h n m z zs)

中文:
定理 Finset.analyticOn_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: fun z zs => N.analyticWithinAt_prod (fun n m => h n m z zs)

Depends on / 依赖: N.analyticWithinAt_prod, analyticWithinAt_prod
-/
theorem Finset.analyticOn_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (∏ n in N, f n) s :=
  fun z zs => N.analyticWithinAt_prod (fun n m => h n m z zs)

/--
theorem `Finset.analyticOnNhd_fun_prod` / 定理 `Finset.analyticOnNhd_fun_prod`

English:
theorem Finset.analyticOnNhd_fun_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: fun z zs => N.analyticAt_fun_prod (fun n m => h n m z zs)

中文:
定理 Finset.analyticOnNhd_fun_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: fun z zs => N.analyticAt_fun_prod (fun n m => h n m z zs)

Depends on / 依赖: N.analyticAt_fun_prod, analyticAt_fun_prod
-/
theorem Finset.analyticOnNhd_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (fun z => ∏ n in N, f n z) s :=
  fun z zs => N.analyticAt_fun_prod (fun n m => h n m z zs)

/--
theorem `Finset.analyticOnNhd_prod` / 定理 `Finset.analyticOnNhd_prod`

English:
theorem Finset.analyticOnNhd_prod
  statement: {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: fun z zs => N.analyticAt_prod (fun n m => h n m z zs)

中文:
定理 Finset.analyticOnNhd_prod
  结论: {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: fun z zs => N.analyticAt_prod (fun n m => h n m z zs)

Depends on / 依赖: N.analyticAt_prod, analyticAt_prod
-/
theorem Finset.analyticOnNhd_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {s : Set E} (N : Finset α) (h : forall n in N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (∏ n in N, f n) s :=
  fun z zs => N.analyticAt_prod (fun n m => h n m z zs)

/-- Finproducts of analytic functions are analytic -/
@[fun_prop]
/--
theorem `analyticAt_finprod` / 定理 `analyticAt_finprod`

English:
theorem analyticAt_finprod
  statement: {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  proof: by
  by_cases hf : (Function.mulSupport f).Finite
  · simp_all [finprod_eq_prod _ hf, Finset.analyticAt_prod]
  · rw [finprod_of_infinite_mulSupport hf]
    apply analyticAt_const

中文:
定理 analyticAt_finprod
  结论: {α : 类型} {A : 类型} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  证明: by
  by_cases hf : (Function.mulSupport f).Finite
  · simp_all [finprod_eq_prod _ hf, Finset.analyticAt_prod]
  · rw [finprod_of_infinite_mulSupport hf]
    apply analyticAt_const

Depends on / 依赖: Finite, Finset, Finset.analyticAt_prod, Function, Function.mulSupport, analyticAt_const, analyticAt_prod, finprod_eq_prod, finprod_of_infinite_mulSupport, mulSupport
-/
theorem analyticAt_finprod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α -> E -> A} {c : E} (h : forall a, AnalyticAt 𝕜 (f a) c) :
    AnalyticAt 𝕜 (∏ᶠ n, f n) c := by
  by_cases hf : (Function.mulSupport f).Finite
  · simp_all [finprod_eq_prod _ hf, Finset.analyticAt_prod]
  · rw [finprod_of_infinite_mulSupport hf]
    apply analyticAt_const

/-!
### Unshifting
-/

section

variable {f : E -> (E ->L[𝕜] F)} {pf : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)} {s : Set E} {x : E}
  {r : Real>=0∞} {z : F}

/--
theorem `HasFPowerSeriesWithinOnBall.unshift` / 定理 `HasFPowerSeriesWithinOnBall.unshift`

English:
theorem HasFPowerSeriesWithinOnBall.unshift
  given: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  proof: by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy h'y
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    e

中文:
定理 HasFPowerSeriesWithinOnBall.unshift
  条件: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  证明: by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy h'y
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    e

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, FormalMultilinearSeries, FormalMultilinearSeries.radius_unshift, FormalMultilinearSeries.unshift, HasSum, HasSum.zero_add, Nat.succ_eq_add_one, add_sub_cancel_left, continuousMultilinearCurryRightEquiv_symm_apply, hasSum, hf.hasSum, hf.r_le, hf.r_pos, r_le, r_pos, radius_unshift, succ_eq_add_one, unshift, zero_add
-/
theorem HasFPowerSeriesWithinOnBall.unshift (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (fun y => z + f y (y - x)) (pf.unshift z) s x r where
  r_le := by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy h'y
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    exact (ContinuousLinearMap.apply 𝕜 F y).hasSum (hf.hasSum hy h'y)

/--
theorem `HasFPowerSeriesOnBall.unshift` / 定理 `HasFPowerSeriesOnBall.unshift`

English:
theorem HasFPowerSeriesOnBall.unshift
  given: (hf : HasFPowerSeriesOnBall f pf x r)
  proof: by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    exact

中文:
定理 HasFPowerSeriesOnBall.unshift
  条件: (hf : HasFPowerSeriesOnBall f pf x r)
  证明: by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    exact

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, FormalMultilinearSeries, FormalMultilinearSeries.radius_unshift, FormalMultilinearSeries.unshift, HasSum, HasSum.zero_add, Nat.succ_eq_add_one, add_sub_cancel_left, continuousMultilinearCurryRightEquiv_symm_apply, hasSum, hf.hasSum, hf.r_le, hf.r_pos, r_le, r_pos, radius_unshift, succ_eq_add_one, unshift, zero_add
-/
theorem HasFPowerSeriesOnBall.unshift (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (fun y => z + f y (y - x)) (pf.unshift z) x r where
  r_le := by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply', add_sub_cancel_left]
    exact (ContinuousLinearMap.apply 𝕜 F y).hasSum (hf.hasSum hy)

/--
theorem `HasFPowerSeriesWithinAt.unshift` / 定理 `HasFPowerSeriesWithinAt.unshift`

English:
theorem HasFPowerSeriesWithinAt.unshift
  given: (hf : HasFPowerSeriesWithinAt f pf s x)
  proof: let ⟨_, hrf⟩ := hf
  hrf.unshift.hasFPowerSeriesWithinAt

中文:
定理 HasFPowerSeriesWithinAt.unshift
  条件: (hf : HasFPowerSeriesWithinAt f pf s x)
  证明: let ⟨_, hrf⟩ := hf
  hrf.unshift.hasFPowerSeriesWithinAt

Depends on / 依赖: hasFPowerSeriesWithinAt, hrf.unshift.hasFPowerSeriesWithinAt, unshift
-/
theorem HasFPowerSeriesWithinAt.unshift (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (fun y => z + f y (y - x)) (pf.unshift z) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.unshift.hasFPowerSeriesWithinAt

end
