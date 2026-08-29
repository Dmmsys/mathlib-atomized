/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Derivatives on `WithLp`
-/

public section

open scoped ENNReal

section PiLp

open ContinuousLinearMap WithLp

variable {𝕜 ι : Type*} {E : ι -> Type*} {H : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [forall i, NormedAddCommGroup (E i)]
  [forall i, NormedSpace 𝕜 (E i)] [NormedSpace 𝕜 H] [Fintype ι] (p) [Fact (1 <= p)]
  {n : WithTop Nat∞} {f : H -> PiLp p E} {f' : H ->L[𝕜] PiLp p E} {t : Set H} {y : H}

/--
theorem `contDiffWithinAt_piLp` / 定理 `contDiffWithinAt_piLp`

English:
theorem contDiffWithinAt_piLp
  proof: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffWithinAt_iff]; rw [contDiffWithinAt_pi]
  rfl

@[fun_prop]

中文:
定理 contDiffWithinAt_piLp
  证明: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffWithinAt_iff]; rw [contDiffWithinAt_pi]
  rfl

@[fun_prop]

Depends on / 依赖: PiLp.continuousLinearEquiv, comp_contDiffWithinAt_iff, contDiffWithinAt_pi, continuousLinearEquiv
-/
theorem contDiffWithinAt_piLp :
    ContDiffWithinAt 𝕜 n f t y ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffWithinAt_iff]; rw [contDiffWithinAt_pi]
  rfl

@[fun_prop]
/--
theorem `contDiffWithinAt_piLp'` / 定理 `contDiffWithinAt_piLp'`

English:
theorem contDiffWithinAt_piLp'
  given: (hf : forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y)
  proof: (contDiffWithinAt_piLp p).2 hf

@[fun_prop]

中文:
定理 contDiffWithinAt_piLp'
  条件: (hf : 对任意 i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y)
  证明: (contDiffWithinAt_piLp p).2 hf

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_piLp
-/
theorem contDiffWithinAt_piLp' (hf : forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y) :
    ContDiffWithinAt 𝕜 n f t y :=
  (contDiffWithinAt_piLp p).2 hf

@[fun_prop]
/--
theorem `contDiffWithinAt_piLp_apply` / 定理 `contDiffWithinAt_piLp_apply`

English:
theorem contDiffWithinAt_piLp_apply
  given: {i : ι} {t : Set (PiLp p E)} {y : PiLp p E}
  proof: (contDiffWithinAt_piLp p).1 contDiffWithinAt_id i

中文:
定理 contDiffWithinAt_piLp_apply
  条件: {i : ι} {t : Set (PiLp p E)} {y : PiLp p E}
  证明: (contDiffWithinAt_piLp p).1 contDiffWithinAt_id i

Depends on / 依赖: contDiffWithinAt_id, contDiffWithinAt_piLp
-/
theorem contDiffWithinAt_piLp_apply {i : ι} {t : Set (PiLp p E)} {y : PiLp p E} :
    ContDiffWithinAt 𝕜 n (fun f : PiLp p E => f i) t y :=
  (contDiffWithinAt_piLp p).1 contDiffWithinAt_id i

/--
theorem `contDiffAt_piLp` / 定理 `contDiffAt_piLp`

English:
theorem contDiffAt_piLp
  proof: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffAt_iff]; rw [contDiffAt_pi]
  rfl

@[fun_prop]

中文:
定理 contDiffAt_piLp
  证明: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffAt_iff]; rw [contDiffAt_pi]
  rfl

@[fun_prop]

Depends on / 依赖: PiLp.continuousLinearEquiv, comp_contDiffAt_iff, contDiffAt_pi, continuousLinearEquiv
-/
theorem contDiffAt_piLp :
    ContDiffAt 𝕜 n f y ↔ forall i, ContDiffAt 𝕜 n (fun x => f x i) y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffAt_iff]; rw [contDiffAt_pi]
  rfl

@[fun_prop]
/--
theorem `contDiffAt_piLp'` / 定理 `contDiffAt_piLp'`

English:
theorem contDiffAt_piLp'
  given: (hf : forall i, ContDiffAt 𝕜 n (fun x => f x i) y)
  proof: (contDiffAt_piLp p).2 hf

@[fun_prop]

中文:
定理 contDiffAt_piLp'
  条件: (hf : 对任意 i, ContDiffAt 𝕜 n (fun x => f x i) y)
  证明: (contDiffAt_piLp p).2 hf

@[fun_prop]

Depends on / 依赖: contDiffAt_piLp
-/
theorem contDiffAt_piLp' (hf : forall i, ContDiffAt 𝕜 n (fun x => f x i) y) :
    ContDiffAt 𝕜 n f y :=
  (contDiffAt_piLp p).2 hf

@[fun_prop]
/--
theorem `contDiffAt_piLp_apply` / 定理 `contDiffAt_piLp_apply`

English:
theorem contDiffAt_piLp_apply
  given: {i : ι} {y : PiLp p E}
  proof: (contDiffAt_piLp p).1 contDiffAt_id i

中文:
定理 contDiffAt_piLp_apply
  条件: {i : ι} {y : PiLp p E}
  证明: (contDiffAt_piLp p).1 contDiffAt_id i

Depends on / 依赖: contDiffAt_id, contDiffAt_piLp
-/
theorem contDiffAt_piLp_apply {i : ι} {y : PiLp p E} :
    ContDiffAt 𝕜 n (fun f : PiLp p E => f i) y :=
  (contDiffAt_piLp p).1 contDiffAt_id i

/--
theorem `contDiffOn_piLp` / 定理 `contDiffOn_piLp`

English:
theorem contDiffOn_piLp
  proof: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffOn_iff]; rw [contDiffOn_pi]
  rfl

@[fun_prop]

中文:
定理 contDiffOn_piLp
  证明: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffOn_iff]; rw [contDiffOn_pi]
  rfl

@[fun_prop]

Depends on / 依赖: PiLp.continuousLinearEquiv, comp_contDiffOn_iff, contDiffOn_pi, continuousLinearEquiv
-/
theorem contDiffOn_piLp :
    ContDiffOn 𝕜 n f t ↔ forall i, ContDiffOn 𝕜 n (fun x => f x i) t := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffOn_iff]; rw [contDiffOn_pi]
  rfl

@[fun_prop]
/--
theorem `contDiffOn_piLp'` / 定理 `contDiffOn_piLp'`

English:
theorem contDiffOn_piLp'
  given: (hf : forall i, ContDiffOn 𝕜 n (fun x => f x i) t)
  proof: (contDiffOn_piLp p).2 hf

@[fun_prop]

中文:
定理 contDiffOn_piLp'
  条件: (hf : 对任意 i, ContDiffOn 𝕜 n (fun x => f x i) t)
  证明: (contDiffOn_piLp p).2 hf

@[fun_prop]

Depends on / 依赖: contDiffOn_piLp
-/
theorem contDiffOn_piLp' (hf : forall i, ContDiffOn 𝕜 n (fun x => f x i) t) :
    ContDiffOn 𝕜 n f t :=
  (contDiffOn_piLp p).2 hf

@[fun_prop]
/--
theorem `contDiffOn_piLp_apply` / 定理 `contDiffOn_piLp_apply`

English:
theorem contDiffOn_piLp_apply
  given: {i : ι} {t : Set (PiLp p E)}
  proof: (contDiffOn_piLp p).1 contDiffOn_id i

中文:
定理 contDiffOn_piLp_apply
  条件: {i : ι} {t : Set (PiLp p E)}
  证明: (contDiffOn_piLp p).1 contDiffOn_id i

Depends on / 依赖: contDiffOn_id, contDiffOn_piLp
-/
theorem contDiffOn_piLp_apply {i : ι} {t : Set (PiLp p E)} :
    ContDiffOn 𝕜 n (fun f : PiLp p E => f i) t :=
  (contDiffOn_piLp p).1 contDiffOn_id i

/--
theorem `contDiff_piLp` / 定理 `contDiff_piLp`

English:
theorem contDiff_piLp
  statement: ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n fun x => f x i
  proof: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiff_iff]; rw [contDiff_pi]
  rfl

@[fun_prop]

中文:
定理 contDiff_piLp
  结论: ContDiff 𝕜 n f ↔ 对任意 i, ContDiff 𝕜 n fun x => f x i
  证明: by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiff_iff]; rw [contDiff_pi]
  rfl

@[fun_prop]

Depends on / 依赖: PiLp.continuousLinearEquiv, comp_contDiff_iff, contDiff_pi, continuousLinearEquiv
-/
theorem contDiff_piLp : ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n fun x => f x i := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiff_iff]; rw [contDiff_pi]
  rfl

@[fun_prop]
/--
theorem `contDiff_piLp'` / 定理 `contDiff_piLp'`

English:
theorem contDiff_piLp'
  given: (hf : forall i, ContDiff 𝕜 n (fun x => f x i))
  proof: (contDiff_piLp p).2 hf

@[fun_prop]

中文:
定理 contDiff_piLp'
  条件: (hf : 对任意 i, ContDiff 𝕜 n (fun x => f x i))
  证明: (contDiff_piLp p).2 hf

@[fun_prop]

Depends on / 依赖: contDiff_piLp
-/
theorem contDiff_piLp' (hf : forall i, ContDiff 𝕜 n (fun x => f x i)) :
    ContDiff 𝕜 n f :=
  (contDiff_piLp p).2 hf

@[fun_prop]
/--
theorem `contDiff_piLp_apply` / 定理 `contDiff_piLp_apply`

English:
theorem contDiff_piLp_apply
  given: {i : ι}
  proof: (contDiff_piLp p).1 contDiff_id i

中文:
定理 contDiff_piLp_apply
  条件: {i : ι}
  证明: (contDiff_piLp p).1 contDiff_id i

Depends on / 依赖: contDiff_id, contDiff_piLp
-/
theorem contDiff_piLp_apply {i : ι} :
    ContDiff 𝕜 n (fun f : PiLp p E => f i) :=
  (contDiff_piLp p).1 contDiff_id i

variable {p}

/--
lemma `PiLp.contDiff_ofLp` / 引理 `PiLp.contDiff_ofLp`

English:
lemma PiLp.contDiff_ofLp
  statement: ContDiff 𝕜 n (@ofLp p (Π i, E i))
  proof: (continuousLinearEquiv p 𝕜 E).contDiff

中文:
引理 PiLp.contDiff_ofLp
  结论: ContDiff 𝕜 n (@ofLp p (Π i, E i))
  证明: (continuousLinearEquiv p 𝕜 E).contDiff

Depends on / 依赖: contDiff, continuousLinearEquiv
-/
lemma PiLp.contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (Π i, E i)) :=
  (continuousLinearEquiv p 𝕜 E).contDiff

/--
lemma `PiLp.contDiff_toLp` / 引理 `PiLp.contDiff_toLp`

English:
lemma PiLp.contDiff_toLp
  statement: ContDiff 𝕜 n (@toLp p (Π i, E i))
  proof: (continuousLinearEquiv p 𝕜 E).symm.contDiff

中文:
引理 PiLp.contDiff_toLp
  结论: ContDiff 𝕜 n (@toLp p (Π i, E i))
  证明: (continuousLinearEquiv p 𝕜 E).symm.contDiff

Depends on / 依赖: contDiff, continuousLinearEquiv, symm.contDiff
-/
lemma PiLp.contDiff_toLp : ContDiff 𝕜 n (@toLp p (Π i, E i)) :=
  (continuousLinearEquiv p 𝕜 E).symm.contDiff

end PiLp

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {p : Real>=0∞} [Fact (1 <= p)] {n : WithTop Nat∞}

/--
lemma `contDiff_ofLp` / 引理 `contDiff_ofLp`

English:
lemma contDiff_ofLp
  statement: ContDiff 𝕜 n (@ofLp p (E × F))
  proof: (prodContinuousLinearEquiv p 𝕜 E F).contDiff

中文:
引理 contDiff_ofLp
  结论: ContDiff 𝕜 n (@ofLp p (E × F))
  证明: (prodContinuousLinearEquiv p 𝕜 E F).contDiff

Depends on / 依赖: contDiff, prodContinuousLinearEquiv
-/
lemma contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (E × F)) :=
  (prodContinuousLinearEquiv p 𝕜 E F).contDiff

/--
lemma `contDiff_toLp` / 引理 `contDiff_toLp`

English:
lemma contDiff_toLp
  statement: ContDiff 𝕜 n (@toLp p (E × F))
  proof: (prodContinuousLinearEquiv p 𝕜 E F).symm.contDiff

中文:
引理 contDiff_toLp
  结论: ContDiff 𝕜 n (@toLp p (E × F))
  证明: (prodContinuousLinearEquiv p 𝕜 E F).symm.contDiff

Depends on / 依赖: contDiff, prodContinuousLinearEquiv, symm.contDiff
-/
lemma contDiff_toLp : ContDiff 𝕜 n (@toLp p (E × F)) :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.contDiff

end WithLp
