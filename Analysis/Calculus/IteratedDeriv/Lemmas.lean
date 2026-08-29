/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# One-dimensional iterated derivatives

This file contains a number of further results on `iteratedDerivWithin` that need more imports
than are available in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : Nat} {x : 𝕜} {s : Set 𝕜} (hx : x in s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 -> F}
  -- For maximum generality, results about `smul` involve a second type besides `𝕜`,
  -- with varying hypotheses.
  -- * `R`: general type.
  {R : Type*} [DistribSMul R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- * `𝕝`: division semiring. (Addition in `𝕝` is not used, so the results would work with a
  -- `GroupWithZero` if we had a `DistribSMulWithZero` typeclass.)
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]
  -- * `𝔸`: normed `𝕜`-algebra.
  {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Module 𝔸 F] [IsBoundedSMul 𝔸 F]
    [IsScalarTower 𝕜 𝔸 F]
  -- * `𝕜'`: normed `𝕜`-division algebra.
  {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [ContinuousSMul 𝕜' F]

section one_dimensional

open scoped Topology

section

/--
theorem `Filter.EventuallyEq.iteratedDerivWithin_eq` / 定理 `Filter.EventuallyEq.iteratedDerivWithin_eq`

English:
theorem Filter.EventuallyEq.iteratedDerivWithin_eq
  given: (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x)
  proof: congr($(hfg.iteratedFDerivWithin_eq hfg' n) _)

中文:
定理 滤子.EventuallyEq.iteratedDerivWithin_eq
  条件: (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x)
  证明: congr($(hfg.iteratedFDerivWithin_eq hfg' n) _)

Depends on / 依赖: hfg.iteratedFDerivWithin_eq, iteratedFDerivWithin_eq
-/
theorem Filter.EventuallyEq.iteratedDerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  congr($(hfg.iteratedFDerivWithin_eq hfg' n) _)

/--
theorem `Filter.EventuallyEq.iteratedDerivWithin'` / 定理 `Filter.EventuallyEq.iteratedDerivWithin'`

English:
theorem Filter.EventuallyEq.iteratedDerivWithin'
  statement: {s t : Set 𝕜}
  proof: by
  unfold iteratedDerivWithin
.fun_comp (fun a => a fun _ => 1) exact h.iteratedFDerivWithin' ht n

中文:
定理 滤子.EventuallyEq.iteratedDerivWithin'
  结论: {s t : 集合 𝕜}
  证明: by
  unfold iteratedDerivWithin
.fun_comp (fun a => a fun _ => 1) exact h.iteratedFDerivWithin' ht n

Depends on / 依赖: fun_comp, h.iteratedFDerivWithin, iteratedDerivWithin, iteratedFDerivWithin
-/
theorem Filter.EventuallyEq.iteratedDerivWithin' {s t : Set 𝕜}
    (h : f =ᶠ[𝓝[s] x] g) (ht : t subseteq s) (n : Nat) :
    iteratedDerivWithin n f t =ᶠ[𝓝[s] x] iteratedDerivWithin n g t := by
  unfold iteratedDerivWithin
.fun_comp (fun a => a fun _ => 1) exact h.iteratedFDerivWithin' ht n

/--
lemma `Filter.EventuallyEq.iteratedDerivWithin` / 引理 `Filter.EventuallyEq.iteratedDerivWithin`

English:
lemma Filter.EventuallyEq.iteratedDerivWithin
  given: {s : Set 𝕜} (h : f =ᶠ[𝓝[s] x] g) (n : Nat)
  proof: h.iteratedDerivWithin' Set.Subset.rfl n

中文:
引理 滤子.EventuallyEq.iteratedDerivWithin
  条件: {s : 集合 𝕜} (h : f =ᶠ[𝓝[s] x] g) (n : 自然数)
  证明: h.iteratedDerivWithin' Set.Subset.rfl n
-/
protected lemma Filter.EventuallyEq.iteratedDerivWithin {s : Set 𝕜} (h : f =ᶠ[𝓝[s] x] g) (n : Nat) :
    iteratedDerivWithin n f s =ᶠ[𝓝[s] x] iteratedDerivWithin n g s :=
  h.iteratedDerivWithin' Set.Subset.rfl n

/--
theorem `Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert` / 定理 `Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert`

English:
theorem Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
  proof: (hfg.filter_mono (by simp)).iteratedDerivWithin_eq (hfg.eq_of_nhdsWithin (by simp))

中文:
定理 滤子.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
  证明: (hfg.filter_mono (by simp)).iteratedDerivWithin_eq (hfg.eq_of_nhdsWithin (by simp))

Depends on / 依赖: eq_of_nhdsWithin, filter_mono, hfg.eq_of_nhdsWithin, hfg.filter_mono, iteratedDerivWithin_eq
-/
theorem Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : Nat) {f g : 𝕜 -> F} {x : 𝕜} {s : Set 𝕜}
    (hfg : f =ᶠ[𝓝[insert x s] x] g) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  (hfg.filter_mono (by simp)).iteratedDerivWithin_eq (hfg.eq_of_nhdsWithin (by simp))

/--
theorem `iteratedDerivWithin_congr` / 定理 `iteratedDerivWithin_congr`

English:
theorem iteratedDerivWithin_congr
  given: (hfg : Set.EqOn f g s)
  proof: fun _ hx => hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq (hfg hx)

include h hx in

中文:
定理 iteratedDerivWithin_congr
  条件: (hfg : 集合.EqOn f g s)
  证明: fun _ hx => hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq (hfg hx)

include h hx in

Depends on / 依赖: eventuallyEq_nhdsWithin, hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq, iteratedDerivWithin_eq
-/
theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s :=
  fun _ hx => hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq (hfg hx)

include h hx in
/--
theorem `iteratedDerivWithin_add` / 定理 `iteratedDerivWithin_add`

English:
theorem iteratedDerivWithin_add
  proof: by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx, add_apply]

include h hx in

中文:
定理 iteratedDerivWithin_add
  证明: by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx, add_apply]

include h hx in

Depends on / 依赖: add_apply, iteratedDerivWithin, iteratedFDerivWithin_add_apply, simp_rw
-/
theorem iteratedDerivWithin_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx, add_apply]

include h hx in
/--
theorem `iteratedDerivWithin_fun_add` / 定理 `iteratedDerivWithin_fun_add`

English:
theorem iteratedDerivWithin_fun_add
  proof: by
  simpa using! iteratedDerivWithin_add hx h hf hg

中文:
定理 iteratedDerivWithin_fun_add
  证明: by
  simpa using! iteratedDerivWithin_add hx h hf hg

Depends on / 依赖: iteratedDerivWithin_add
-/
theorem iteratedDerivWithin_fun_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun z => f z + g z) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simpa using! iteratedDerivWithin_add hx h hf hg

/--
theorem `iteratedDerivWithin_const_add` / 定理 `iteratedDerivWithin_const_add`

English:
theorem iteratedDerivWithin_const_add
  given: (hn : 0 < n) (c : F)
  proof: by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ']; rw [iteratedDerivWithin_succ']
  congr 1 with y
  exact derivWithin_const_add _

中文:
定理 iteratedDerivWithin_const_add
  条件: (hn : 0 < n) (c : F)
  证明: by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ']; rw [iteratedDerivWithin_succ']
  congr 1 with y
  exact derivWithin_const_add _

Depends on / 依赖: derivWithin_const_add, exists_eq_succ_of_ne_zero, hn.ne, iteratedDerivWithin_succ, n.exists_eq_succ_of_ne_zero
-/
theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ']; rw [iteratedDerivWithin_succ']
  congr 1 with y
  exact derivWithin_const_add _

/--
theorem `iteratedDerivWithin_const_sub` / 定理 `iteratedDerivWithin_const_sub`

English:
theorem iteratedDerivWithin_const_sub
  given: (hn : 0 < n) (c : F)
  proof: by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ']; rw [iteratedDerivWithin_succ']
  congr 1 with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in

中文:
定理 iteratedDerivWithin_const_sub
  条件: (hn : 0 < n) (c : F)
  证明: by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ']; rw [iteratedDerivWithin_succ']
  congr 1 with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in

Depends on / 依赖: derivWithin, derivWithin.fun_neg, derivWithin_const_sub, exists_eq_succ_of_ne_zero, fun_neg, hn.ne, iteratedDerivWithin_succ, n.exists_eq_succ_of_ne_zero
-/
theorem iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ']; rw [iteratedDerivWithin_succ']
  congr 1 with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in
/--
theorem `iteratedDerivWithin_const_smul` / 定理 `iteratedDerivWithin_const_smul`

English:
theorem iteratedDerivWithin_const_smul
  given: (c : R) (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: by
  simp [iteratedDerivWithin, iteratedFDerivWithin_const_smul_apply hf h hx]

include h hx in

中文:
定理 iteratedDerivWithin_const_smul
  条件: (c : R) (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: by
  simp [iteratedDerivWithin, iteratedFDerivWithin_const_smul_apply hf h hx]

include h hx in

Depends on / 依赖: iteratedDerivWithin, iteratedFDerivWithin_const_smul_apply
-/
theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_const_smul_apply hf h hx]

include h hx in
/--
theorem `iteratedDerivWithin_fun_const_smul` / 定理 `iteratedDerivWithin_fun_const_smul`

English:
theorem iteratedDerivWithin_fun_const_smul
  given: (c : R) (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: iteratedDerivWithin_const_smul hx h c hf

中文:
定理 iteratedDerivWithin_fun_const_smul
  条件: (c : R) (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: iteratedDerivWithin_const_smul hx h c hf

Depends on / 依赖: iteratedDerivWithin_const_smul
-/
theorem iteratedDerivWithin_fun_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun w => c • f w) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul hx h c hf

/-- A variant of `iteratedDerivWithin_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/--
theorem `iteratedDerivWithin_const_smul_field` / 定理 `iteratedDerivWithin_const_smul_field`

English:
theorem iteratedDerivWithin_const_smul_field
  given: (c : 𝕝) (f : 𝕜 -> F)
  proof: by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), ← Pi.smul_def,
      derivWithin_const_smul_field]

include h hx in

中文:
定理 iteratedDerivWithin_const_smul_field
  条件: (c : 𝕝) (f : 𝕜 -> F)
  证明: by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), ← Pi.smul_def,
      derivWithin_const_smul_field]

include h hx in

Depends on / 依赖: Pi.smul_def, derivWithin_const_smul_field, generalizing, iteratedDerivWithin_succ, simp_rw, smul_def
-/
theorem iteratedDerivWithin_const_smul_field (c : 𝕝) (f : 𝕜 -> F) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), ← Pi.smul_def,
      derivWithin_const_smul_field]

include h hx in
/--
theorem `iteratedDerivWithin_const_mul` / 定理 `iteratedDerivWithin_const_mul`

English:
theorem iteratedDerivWithin_const_mul
  given: (c : 𝔸) {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: iteratedDerivWithin_fun_const_smul hx h c hf

中文:
定理 iteratedDerivWithin_const_mul
  条件: (c : 𝔸) {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: iteratedDerivWithin_fun_const_smul hx h c hf

Depends on / 依赖: iteratedDerivWithin_fun_const_smul
-/
theorem iteratedDerivWithin_const_mul (c : 𝔸) {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x :=
  iteratedDerivWithin_fun_const_smul hx h c hf

/-- A variant of `iteratedDerivWithin_fun_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/--
theorem `iteratedDerivWithin_fun_const_smul_field` / 定理 `iteratedDerivWithin_fun_const_smul_field`

English:
theorem iteratedDerivWithin_fun_const_smul_field
  given: (c : 𝕝) (f : 𝕜 -> F)
  proof: iteratedDerivWithin_const_smul_field c f

@[simp]

中文:
定理 iteratedDerivWithin_fun_const_smul_field
  条件: (c : 𝕝) (f : 𝕜 -> F)
  证明: iteratedDerivWithin_const_smul_field c f

@[simp]

Depends on / 依赖: iteratedDerivWithin_const_smul_field
-/
theorem iteratedDerivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 -> F) :
    iteratedDerivWithin n (fun z => c • f z) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul_field c f

@[simp]
/--
theorem `iteratedDerivWithin_const_mul_field` / 定理 `iteratedDerivWithin_const_mul_field`

English:
theorem iteratedDerivWithin_const_mul_field
  given: (c : 𝕜') (f : 𝕜 -> 𝕜')
  proof: iteratedDerivWithin_fun_const_smul_field c f

include h hx in

中文:
定理 iteratedDerivWithin_const_mul_field
  条件: (c : 𝕜') (f : 𝕜 -> 𝕜')
  证明: iteratedDerivWithin_fun_const_smul_field c f

include h hx in

Depends on / 依赖: iteratedDerivWithin_fun_const_smul_field
-/
theorem iteratedDerivWithin_const_mul_field (c : 𝕜') (f : 𝕜 -> 𝕜') :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x :=
  iteratedDerivWithin_fun_const_smul_field c f

include h hx in
/--
theorem `iteratedDerivWithin_smul_const` / 定理 `iteratedDerivWithin_smul_const`

English:
theorem iteratedDerivWithin_smul_const
  given: {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F)
  proof: by
  simp [iteratedDerivWithin, iteratedFDerivWithin_smul_const_apply hf h hx]

include h hx in
@[simp]

中文:
定理 iteratedDerivWithin_smul_const
  条件: {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F)
  证明: by
  simp [iteratedDerivWithin, iteratedFDerivWithin_smul_const_apply hf h hx]

include h hx in
@[simp]

Depends on / 依赖: iteratedDerivWithin, iteratedFDerivWithin_smul_const_apply
-/
theorem iteratedDerivWithin_smul_const {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) :
    iteratedDerivWithin n (fun y => f y • v) s x = iteratedDerivWithin n f s x • v := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_smul_const_apply hf h hx]

include h hx in
@[simp]
/--
theorem `iteratedDerivWithin_mul_const` / 定理 `iteratedDerivWithin_mul_const`

English:
theorem iteratedDerivWithin_mul_const
  given: {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (d : 𝔸)
  proof: iteratedDerivWithin_smul_const hx h hf d

中文:
定理 iteratedDerivWithin_mul_const
  条件: {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (d : 𝔸)
  证明: iteratedDerivWithin_smul_const hx h hf d

Depends on / 依赖: iteratedDerivWithin_smul_const
-/
theorem iteratedDerivWithin_mul_const {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (d : 𝔸) :
    iteratedDerivWithin n (fun z => f z * d) s x = iteratedDerivWithin n f s x * d :=
  iteratedDerivWithin_smul_const hx h hf d

/-- A variant of `iteratedDerivWithin_mul_const` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/--
theorem `iteratedDerivWithin_mul_const_field` / 定理 `iteratedDerivWithin_mul_const_field`

English:
theorem iteratedDerivWithin_mul_const_field
  given: (f : 𝕜 -> 𝕜') (d : 𝕜')
  proof: by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), derivWithin_mul_const_field]

中文:
定理 iteratedDerivWithin_mul_const_field
  条件: (f : 𝕜 -> 𝕜') (d : 𝕜')
  证明: by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), derivWithin_mul_const_field]

Depends on / 依赖: derivWithin_mul_const_field, generalizing, iteratedDerivWithin_succ, simp_rw
-/
theorem iteratedDerivWithin_mul_const_field (f : 𝕜 -> 𝕜') (d : 𝕜') :
    iteratedDerivWithin n (fun z => f z * d) s x = iteratedDerivWithin n f s x * d := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), derivWithin_mul_const_field]

variable (f) in
omit h hx in
@[simp]
/--
theorem `iteratedDerivWithin_neg` / 定理 `iteratedDerivWithin_neg`

English:
theorem iteratedDerivWithin_neg
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [iteratedDerivWithin_succ]
    rw [← derivWithin.neg]
    congr with y
    exact IH

中文:
定理 iteratedDerivWithin_neg
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [iteratedDerivWithin_succ]
    rw [← derivWithin.neg]
    congr with y
    exact IH

Depends on / 依赖: derivWithin, derivWithin.neg, generalizing, iteratedDerivWithin_succ
-/
theorem iteratedDerivWithin_neg :
    iteratedDerivWithin n (-f) s x = -iteratedDerivWithin n f s x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [iteratedDerivWithin_succ]
    rw [← derivWithin.neg]
    congr with y
    exact IH

variable (f) in
/--
theorem `iteratedDerivWithin_fun_neg` / 定理 `iteratedDerivWithin_fun_neg`

English:
theorem iteratedDerivWithin_fun_neg
  proof: iteratedDerivWithin_neg f

include h hx

中文:
定理 iteratedDerivWithin_fun_neg
  证明: iteratedDerivWithin_neg f

include h hx

Depends on / 依赖: iteratedDerivWithin_neg
-/
theorem iteratedDerivWithin_fun_neg :
    iteratedDerivWithin n (fun z => -f z) s x = -iteratedDerivWithin n f s x :=
  iteratedDerivWithin_neg f

include h hx

/--
theorem `iteratedDerivWithin_sub` / 定理 `iteratedDerivWithin_sub`

English:
theorem iteratedDerivWithin_sub
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [Pi.neg_def]; rw [iteratedDerivWithin_add hx h hf hg.neg]; rw [iteratedDerivWithin_fun_neg]

中文:
定理 iteratedDerivWithin_sub
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [Pi.neg_def]; rw [iteratedDerivWithin_add hx h hf hg.neg]; rw [iteratedDerivWithin_fun_neg]

Depends on / 依赖: Pi.neg_def, hg.neg, iteratedDerivWithin_add, iteratedDerivWithin_fun_neg, neg_def, sub_eq_add_neg
-/
theorem iteratedDerivWithin_sub
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f - g) s x =
      iteratedDerivWithin n f s x - iteratedDerivWithin n g s x := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [Pi.neg_def]; rw [iteratedDerivWithin_add hx h hf hg.neg]; rw [iteratedDerivWithin_fun_neg]

/--
theorem `iteratedDerivWithin_comp_const_smul` / 定理 `iteratedDerivWithin_comp_const_smul`

English:
theorem iteratedDerivWithin_comp_const_smul
  statement: (hf : ContDiffOn 𝕜 n f s) (c : 𝕜)
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x in s := hs hx
    have h₀ : s.EqOn
        (iteratedDerivWithin n (fun x => f (c * x)) s)
        (fun x => c ^ n • iteratedDerivWithin n f s (c * x)) :=
      fun x hx => ih hx hf.of_succ
    have h₁ : DifferentiableWithinAt 𝕜 (iteratedDerivWithin n f s) s (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    have h₂ : DifferentiableWithinAt 𝕜 (fun x => iteratedDerivWithin n f s (c * x)) s x := by
      rw [← Function.comp_def]
      apply DifferentiableWithinAt.comp _ ?_ (by fun_prop) hs
      exact hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    rw [iteratedDerivWithin_succ]; rw [derivWithin_congr h₀ (ih hx hf.of_succ)]; rw [derivWithin_fun_const_smul (c ^ n) h₂]; rw [iteratedDerivWithin_succ]; rw [← Function.comp_def]; rw [derivWithin.scomp x h₁ (by fun_prop) hs]; rw [derivWithin_const_mul _ differentiableWithinAt_id]; rw [derivWithin_id' _ _ (h _ hx)]; rw [smul_smul]; rw [mul_one]; rw [pow_succ]

中文:
定理 iteratedDerivWithin_comp_const_smul
  结论: (hf : ContDiffOn 𝕜 n f s) (c : 𝕜)
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x in s := hs hx
    have h₀ : s.EqOn
        (iteratedDerivWithin n (fun x => f (c * x)) s)
        (fun x => c ^ n • iteratedDerivWithin n f s (c * x)) :=
      fun x hx => ih hx hf.of_succ
    have h₁ : DifferentiableWithinAt 𝕜 (iteratedDerivWithin n f s) s (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    have h₂ : DifferentiableWithinAt 𝕜 (fun x => iteratedDerivWithin n f s (c * x)) s x := by
      rw [← Function.comp_def]
      apply DifferentiableWithinAt.comp _ ?_ (by fun_prop) hs
      exact hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    rw [iteratedDerivWithin_succ]; rw [derivWithin_congr h₀ (ih hx hf.of_succ)]; rw [derivWithin_fun_const_smul (c ^ n) h₂]; rw [iteratedDerivWithin_succ]; rw [← Function.comp_def]; rw [derivWithin.scomp x h₁ (by fun_prop) hs]; rw [derivWithin_const_mul _ differentiableWithinAt_id]; rw [derivWithin_id' _ _ (h _ hx)]; rw [smul_smul]; rw [mul_one]; rw [pow_succ]

Depends on / 依赖: DifferentiableWithinAt, Nat.cast_lt.mpr, cast_lt, differentiableOn_iteratedDerivWithin, generalizing, hf.differentiableOn_iteratedDerivWithin, hf.of_succ, iteratedDerivWithin, lt_succ_self, n.lt_succ_self, of_succ, s.EqOn
-/
theorem iteratedDerivWithin_comp_const_smul (hf : ContDiffOn 𝕜 n f s) (c : 𝕜)
    (hs : Set.MapsTo (c * ·) s s) :
    iteratedDerivWithin n (fun x => f (c * x)) s x = c ^ n • iteratedDerivWithin n f s (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x in s := hs hx
    have h₀ : s.EqOn
        (iteratedDerivWithin n (fun x => f (c * x)) s)
        (fun x => c ^ n • iteratedDerivWithin n f s (c * x)) :=
      fun x hx => ih hx hf.of_succ
    have h₁ : DifferentiableWithinAt 𝕜 (iteratedDerivWithin n f s) s (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    have h₂ : DifferentiableWithinAt 𝕜 (fun x => iteratedDerivWithin n f s (c * x)) s x := by
      rw [← Function.comp_def]
      apply DifferentiableWithinAt.comp _ ?_ (by fun_prop) hs
      exact hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    rw [iteratedDerivWithin_succ]; rw [derivWithin_congr h₀ (ih hx hf.of_succ)]; rw [derivWithin_fun_const_smul (c ^ n) h₂]; rw [iteratedDerivWithin_succ]; rw [← Function.comp_def]; rw [derivWithin.scomp x h₁ (by fun_prop) hs]; rw [derivWithin_const_mul _ differentiableWithinAt_id]; rw [derivWithin_id' _ _ (h _ hx)]; rw [smul_smul]; rw [mul_one]; rw [pow_succ]

open scoped Pointwise

omit hx h in
/--
lemma `iteratedDerivWithin_comp_neg` / 引理 `iteratedDerivWithin_comp_neg`

English:
lemma iteratedDerivWithin_comp_neg
  given: (a : 𝕜)
  statement: iteratedDerivWithin n (fun x => f (-x)) s a
  proof: by
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_neg n a]

omit hx h in

中文:
引理 iteratedDerivWithin_comp_neg
  条件: (a : 𝕜)
  结论: iteratedDerivWithin n (fun x => f (-x)) s a
  证明: by
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_neg n a]

omit hx h in

Depends on / 依赖: iteratedDerivWithin, iteratedFDerivWithin_comp_neg
-/
lemma iteratedDerivWithin_comp_neg (a : 𝕜) : iteratedDerivWithin n (fun x => f (-x)) s a
    = (-1 : 𝕜) ^ n • iteratedDerivWithin n f (-s) (-a) := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_neg n a]

omit hx h in
/--
theorem `iteratedDerivWithin_comp_const_add` / 定理 `iteratedDerivWithin_comp_const_add`

English:
theorem iteratedDerivWithin_comp_const_add
  given: (c : 𝕜)
  proof: by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_left n c x]

omit hx h in

中文:
定理 iteratedDerivWithin_comp_const_add
  条件: (c : 𝕜)
  证明: by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_left n c x]

omit hx h in

Depends on / 依赖: iteratedDerivWithin, iteratedFDerivWithin_comp_add_left
-/
theorem iteratedDerivWithin_comp_const_add (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (c + z)) s =
      fun x => iteratedDerivWithin n f (c +ᵥ s) (c + x) := by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_left n c x]

omit hx h in
/--
theorem `iteratedDerivWithin_comp_add_const` / 定理 `iteratedDerivWithin_comp_add_const`

English:
theorem iteratedDerivWithin_comp_add_const
  given: (c : 𝕜)
  proof: by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_right n c x]

omit hx h in

中文:
定理 iteratedDerivWithin_comp_add_const
  条件: (c : 𝕜)
  证明: by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_right n c x]

omit hx h in

Depends on / 依赖: iteratedDerivWithin, iteratedFDerivWithin_comp_add_right
-/
theorem iteratedDerivWithin_comp_add_const (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (z + c)) s =
      fun x => iteratedDerivWithin n f (c +ᵥ s) (x + c) := by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_right n c x]

omit hx h in
/--
theorem `iteratedDerivWithin_comp_sub_const` / 定理 `iteratedDerivWithin_comp_sub_const`

English:
theorem iteratedDerivWithin_comp_sub_const
  given: (c : 𝕜)
  proof: by
  simpa only [sub_eq_add_neg] using iteratedDerivWithin_comp_add_const (-c)

omit hx h in

中文:
定理 iteratedDerivWithin_comp_sub_const
  条件: (c : 𝕜)
  证明: by
  simpa only [sub_eq_add_neg] using iteratedDerivWithin_comp_add_const (-c)

omit hx h in

Depends on / 依赖: iteratedDerivWithin_comp_add_const, sub_eq_add_neg
-/
theorem iteratedDerivWithin_comp_sub_const (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (z - c)) s =
      fun x => iteratedDerivWithin n f (-c +ᵥ s) (x - c) := by
  simpa only [sub_eq_add_neg] using iteratedDerivWithin_comp_add_const (-c)

omit hx h in
/--
theorem `iteratedDerivWithin_comp_const_sub` / 定理 `iteratedDerivWithin_comp_const_sub`

English:
theorem iteratedDerivWithin_comp_const_sub
  given: (c : 𝕜)
  proof: by
  ext a
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_const_sub]

@[to_fun iteratedDerivWithin_fun_id]

中文:
定理 iteratedDerivWithin_comp_const_sub
  条件: (c : 𝕜)
  证明: by
  ext a
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_const_sub]

@[to_fun iteratedDerivWithin_fun_id]

Depends on / 依赖: iteratedDerivWithin, iteratedFDerivWithin_comp_const_sub
-/
theorem iteratedDerivWithin_comp_const_sub (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (c - z)) s =
      fun x => (-1 : 𝕜) ^ n • iteratedDerivWithin n f (c +ᵥ -s) (c - x) := by
  ext a
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_const_sub]

@[to_fun iteratedDerivWithin_fun_id]
/--
lemma `iteratedDerivWithin_id` / 引理 `iteratedDerivWithin_id`

English:
lemma iteratedDerivWithin_id
  proof: by
  obtain (_ | n) := n
  · simp
  · rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr (g := fun _ => 1) _ hx]
    · simp [iteratedDerivWithin_const]
    · exact fun y hy => derivWithin_id _ _ (h.uniqueDiffWithinAt hy)

中文:
引理 iteratedDerivWithin_id
  证明: by
  obtain (_ | n) := n
  · simp
  · rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr (g := fun _ => 1) _ hx]
    · simp [iteratedDerivWithin_const]
    · exact fun y hy => derivWithin_id _ _ (h.uniqueDiffWithinAt hy)

Depends on / 依赖: derivWithin_id, h.uniqueDiffWithinAt, iteratedDerivWithin_congr, iteratedDerivWithin_const, iteratedDerivWithin_succ, uniqueDiffWithinAt
-/
lemma iteratedDerivWithin_id :
    iteratedDerivWithin n id s x = if n = 0 then x else if n = 1 then 1 else 0 := by
  obtain (_ | n) := n
  · simp
  · rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr (g := fun _ => 1) _ hx]
    · simp [iteratedDerivWithin_const]
    · exact fun y hy => derivWithin_id _ _ (h.uniqueDiffWithinAt hy)

/--
lemma `iteratedDerivWithin_smul` / 引理 `iteratedDerivWithin_smul`

English:
lemma iteratedDerivWithin_smul
  statement: {f : 𝕜 -> 𝔸} {g : 𝕜 -> F}
  proof: by
  induction n generalizing f g with
  | zero => simp
  | succ n IH =>
    obtain ⟨U, hU, H⟩ := ((hf.eventually (by simp)).and (hg.eventually (by simp))).exists_mem
    rw [iteratedDerivWithin_succ']; rw [Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := f • derivWithin g s + derivWithin f s • g)]
    · rw [Finset.sum_range_succ', iteratedDerivWithin_add hx h, IH, Finset.sum_range_succ', IH]
      · simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
        nth_rw 3 [Finset.sum_range_succ]
        have : forall i in Finset.range n, 1 <= n - i := by simp; lia
        simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub, Nat.sub_add_cancel, this]
        abel
      all_goals clear IH H U hU; fun_prop (disch := simp_all)
    · filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
      rw [derivWithin_smul (hfy.differentiableWithinAt _) (hgy.differentiableWithinAt _)]
      all_goals simp

中文:
引理 iteratedDerivWithin_smul
  结论: {f : 𝕜 -> 𝔸} {g : 𝕜 -> F}
  证明: by
  induction n generalizing f g with
  | zero => simp
  | succ n IH =>
    obtain ⟨U, hU, H⟩ := ((hf.eventually (by simp)).and (hg.eventually (by simp))).exists_mem
    rw [iteratedDerivWithin_succ']; rw [Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := f • derivWithin g s + derivWithin f s • g)]
    · rw [Finset.sum_range_succ', iteratedDerivWithin_add hx h, IH, Finset.sum_range_succ', IH]
      · simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
        nth_rw 3 [Finset.sum_range_succ]
        have : forall i in Finset.range n, 1 <= n - i := by simp; lia
        simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub, Nat.sub_add_cancel, this]
        abel
      all_goals clear IH H U hU; fun_prop (disch := simp_all)
    · filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
      rw [derivWithin_smul (hfy.differentiableWithinAt _) (hgy.differentiableWithinAt _)]
      all_goals simp

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert, Finset, Finset.sum_add_distrib, Finset.sum_range_succ, Nat.choose_succ_succ, add_smul, choose_succ_succ, derivWithin, eventually, exists_mem, generalizing, hf.eventually, hg.eventually, iteratedDerivWithin_add, iteratedDerivWithin_eq_of_nhds_insert, iteratedDerivWithin_succ, nth_rw, sum_add_distrib
-/
lemma iteratedDerivWithin_smul {f : 𝕜 -> 𝔸} {g : 𝕜 -> F}
    (hf : ContDiffWithinAt 𝕜 (↑n) f s x) (hg : ContDiffWithinAt 𝕜 (↑n) g s x) :
    iteratedDerivWithin n (f • g) s x = ∑ i in .range (n + 1),
      n.choose i • iteratedDerivWithin i f s x • iteratedDerivWithin (n - i) g s x := by
  induction n generalizing f g with
  | zero => simp
  | succ n IH =>
    obtain ⟨U, hU, H⟩ := ((hf.eventually (by simp)).and (hg.eventually (by simp))).exists_mem
    rw [iteratedDerivWithin_succ']; rw [Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := f • derivWithin g s + derivWithin f s • g)]
    · rw [Finset.sum_range_succ', iteratedDerivWithin_add hx h, IH, Finset.sum_range_succ', IH]
      · simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
        nth_rw 3 [Finset.sum_range_succ]
        have : forall i in Finset.range n, 1 <= n - i := by simp; lia
        simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub, Nat.sub_add_cancel, this]
        abel
      all_goals clear IH H U hU; fun_prop (disch := simp_all)
    · filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
      rw [derivWithin_smul (hfy.differentiableWithinAt _) (hgy.differentiableWithinAt _)]
      all_goals simp

/--
lemma `iteratedDerivWithin_mul` / 引理 `iteratedDerivWithin_mul`

English:
lemma iteratedDerivWithin_mul
  statement: {f g : 𝕜 -> 𝔸}
  proof: by
  simp [← smul_eq_mul, iteratedDerivWithin_smul hx h hf hg]

中文:
引理 iteratedDerivWithin_mul
  结论: {f g : 𝕜 -> 𝔸}
  证明: by
  simp [← smul_eq_mul, iteratedDerivWithin_smul hx h hf hg]

Depends on / 依赖: iteratedDerivWithin_smul, smul_eq_mul
-/
lemma iteratedDerivWithin_mul {f g : 𝕜 -> 𝔸}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f * g) s x = ∑ i in .range (n + 1),
      n.choose i * iteratedDerivWithin i f s x * iteratedDerivWithin (n - i) g s x := by
  simp [← smul_eq_mul, iteratedDerivWithin_smul hx h hf hg]

/--
theorem `iteratedDerivWithin_pow` / 定理 `iteratedDerivWithin_pow`

English:
theorem iteratedDerivWithin_pow
  given: (m : Nat) (k : Nat)
  proof: by
  induction m generalizing k with
  | zero => cases k <;> simp [iteratedDerivWithin_const]
  | succ i IH =>
    obtain (_ | k) := k
    · simp
    simp only [pow_succ]
    refine (iteratedDerivWithin_mul hx h (by fun_prop) (by fun_prop)).trans ?_
    have : ((i + 1).descFactorial (k + 1)) =
        (k + 1) * (i.descFactorial k) + (i.descFactorial (k + 1)) := by
      rw [Nat.succ_descFactorial_succ]
      cases le_or_gt k i <;> simp [Nat.descFactorial, ← add_mul, *]; lia
    obtain hik | hik := le_or_gt i k <;>
      simp +contextual [IH, iteratedDerivWithin_fun_id, h, hx, Finset.sum_range_succ,
        show forall x in Finset.range k, k + 1 - x != 0 by simp; lia, -Nat.descFactorial_succ,
        show forall x in Finset.range k, k + 1 - x != 1 by simp; lia, this,
        Nat.descFactorial_eq_zero_iff_lt.mpr, hik,
        show k < i -> i - k = (i - (k + 1) + 1) by lia]; ring

中文:
定理 iteratedDerivWithin_pow
  条件: (m : 自然数) (k : 自然数)
  证明: by
  induction m generalizing k with
  | zero => cases k <;> simp [iteratedDerivWithin_const]
  | succ i IH =>
    obtain (_ | k) := k
    · simp
    simp only [pow_succ]
    refine (iteratedDerivWithin_mul hx h (by fun_prop) (by fun_prop)).trans ?_
    have : ((i + 1).descFactorial (k + 1)) =
        (k + 1) * (i.descFactorial k) + (i.descFactorial (k + 1)) := by
      rw [Nat.succ_descFactorial_succ]
      cases le_or_gt k i <;> simp [Nat.descFactorial, ← add_mul, *]; lia
    obtain hik | hik := le_or_gt i k <;>
      simp +contextual [IH, iteratedDerivWithin_fun_id, h, hx, Finset.sum_range_succ,
        show forall x in Finset.range k, k + 1 - x != 0 by simp; lia, -Nat.descFactorial_succ,
        show forall x in Finset.range k, k + 1 - x != 1 by simp; lia, this,
        Nat.descFactorial_eq_zero_iff_lt.mpr, hik,
        show k < i -> i - k = (i - (k + 1) + 1) by lia]; ring

Depends on / 依赖: Nat.descFactorial, Nat.succ_descFactorial_succ, add_mul, contextual, descFactorial, fun_prop, generalizing, i.descFactorial, iterated, iteratedDerivWithin_const, iteratedDerivWithin_mul, le_or_gt, pow_succ, succ_descFactorial_succ
-/
theorem iteratedDerivWithin_pow (m : Nat) (k : Nat) :
    iteratedDerivWithin k (· ^ m) s x = m.descFactorial k * x ^ (m - k) := by
  induction m generalizing k with
  | zero => cases k <;> simp [iteratedDerivWithin_const]
  | succ i IH =>
    obtain (_ | k) := k
    · simp
    simp only [pow_succ]
    refine (iteratedDerivWithin_mul hx h (by fun_prop) (by fun_prop)).trans ?_
    have : ((i + 1).descFactorial (k + 1)) =
        (k + 1) * (i.descFactorial k) + (i.descFactorial (k + 1)) := by
      rw [Nat.succ_descFactorial_succ]
      cases le_or_gt k i <;> simp [Nat.descFactorial, ← add_mul, *]; lia
    obtain hik | hik := le_or_gt i k <;>
      simp +contextual [IH, iteratedDerivWithin_fun_id, h, hx, Finset.sum_range_succ,
        show forall x in Finset.range k, k + 1 - x != 0 by simp; lia, -Nat.descFactorial_succ,
        show forall x in Finset.range k, k + 1 - x != 1 by simp; lia, this,
        Nat.descFactorial_eq_zero_iff_lt.mpr, hik,
        show k < i -> i - k = (i - (k + 1) + 1) by lia]; ring

end

/--
lemma `Filter.EventuallyEq.iteratedDeriv` / 引理 `Filter.EventuallyEq.iteratedDeriv`

English:
lemma Filter.EventuallyEq.iteratedDeriv
  proof: by
  simp_all [← nhdsWithin_univ, ← iteratedDerivWithin_univ, EventuallyEq.iteratedDerivWithin]

@[to_fun iteratedDeriv_fun_add]

中文:
引理 滤子.EventuallyEq.iteratedDeriv
  证明: by
  simp_all [← nhdsWithin_univ, ← iteratedDerivWithin_univ, EventuallyEq.iteratedDerivWithin]

@[to_fun iteratedDeriv_fun_add]
-/
protected lemma Filter.EventuallyEq.iteratedDeriv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : 𝕜 -> F} {x : 𝕜} (h : f₁ =ᶠ[𝓝 x] f₂) (n : Nat) :
    iteratedDeriv n f₁ =ᶠ[𝓝 x] iteratedDeriv n f₂ := by
  simp_all [← nhdsWithin_univ, ← iteratedDerivWithin_univ, EventuallyEq.iteratedDerivWithin]

@[to_fun iteratedDeriv_fun_add]
/--
lemma `iteratedDeriv_add` / 引理 `iteratedDeriv_add`

English:
lemma iteratedDeriv_add
  given: (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ hf hg

中文:
引理 iteratedDeriv_add
  条件: (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ hf hg

Depends on / 依赖: Set.mem_univ, iteratedDerivWithin_add, iteratedDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
lemma iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ hf hg

/--
theorem `iteratedDeriv_const_add` / 定理 `iteratedDeriv_const_add`

English:
theorem iteratedDeriv_const_add
  given: (hn : 0 < n) (c : F)
  proof: by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_add hn c

中文:
定理 iteratedDeriv_const_add
  条件: (hn : 0 < n) (c : F)
  证明: by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_add hn c

Depends on / 依赖: iteratedDerivWithin_const_add, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_const_add (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c + f z) x = iteratedDeriv n f x := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_add hn c

/--
theorem `iteratedDeriv_const_sub` / 定理 `iteratedDeriv_const_sub`

English:
theorem iteratedDeriv_const_sub
  given: (hn : 0 < n) (c : F)
  proof: by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_const_sub hn c

@[simp]

中文:
定理 iteratedDeriv_const_sub
  条件: (hn : 0 < n) (c : F)
  证明: by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_const_sub hn c

@[simp]

Depends on / 依赖: iteratedDerivWithin_const_sub, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_const_sub (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c - f z) x = iteratedDeriv n (-f) x := by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_const_sub hn c

@[simp]
/--
lemma `iteratedDeriv_fun_neg` / 引理 `iteratedDeriv_fun_neg`

English:
lemma iteratedDeriv_fun_neg
  given: (n : Nat) (f : 𝕜 -> F) (a : 𝕜)
  proof: by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_neg f

@[simp]

中文:
引理 iteratedDeriv_fun_neg
  条件: (n : 自然数) (f : 𝕜 -> F) (a : 𝕜)
  证明: by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_neg f

@[simp]

Depends on / 依赖: iteratedDerivWithin_neg, iteratedDerivWithin_univ
-/
lemma iteratedDeriv_fun_neg (n : Nat) (f : 𝕜 -> F) (a : 𝕜) :
    iteratedDeriv n (fun x => -(f x)) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_neg f

@[simp]
/--
lemma `iteratedDeriv_neg` / 引理 `iteratedDeriv_neg`

English:
lemma iteratedDeriv_neg
  given: (n : Nat) (f : 𝕜 -> F) (a : 𝕜)
  proof: by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

中文:
引理 iteratedDeriv_neg
  条件: (n : 自然数) (f : 𝕜 -> F) (a : 𝕜)
  证明: by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

Depends on / 依赖: attribute, iteratedDerivWithin_neg, iteratedDerivWithin_univ, iteratedDeriv_fun_neg
-/
lemma iteratedDeriv_neg (n : Nat) (f : 𝕜 -> F) (a : 𝕜) :
    iteratedDeriv n (-f) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f
attribute [simp] iteratedDeriv_fun_neg

@[to_fun iteratedDeriv_fun_sub]
/--
lemma `iteratedDeriv_sub` / 引理 `iteratedDeriv_sub`

English:
lemma iteratedDeriv_sub
  given: (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ hf hg

@[to_fun iteratedDeriv_fun_const_smul]

中文:
引理 iteratedDeriv_sub
  条件: (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ hf hg

@[to_fun iteratedDeriv_fun_const_smul]

Depends on / 依赖: Set.mem_univ, iteratedDerivWithin_sub, iteratedDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
lemma iteratedDeriv_sub (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ hf hg

@[to_fun iteratedDeriv_fun_const_smul]
/--
theorem `iteratedDeriv_const_smul` / 定理 `iteratedDeriv_const_smul`

English:
theorem iteratedDeriv_const_smul
  given: {n : Nat} {f : 𝕜 -> F} (h : ContDiffAt 𝕜 n f x) (c : R)
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

中文:
定理 iteratedDeriv_const_smul
  条件: {n : 自然数} {f : 𝕜 -> F} (h : ContDiffAt 𝕜 n f x) (c : R)
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

Depends on / 依赖: Set.mem_univ, contDiffWithinAt_univ, contDiffWithinAt_univ.mpr, iteratedDerivWithin_const_smul, iteratedDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_const_smul {n : Nat} {f : 𝕜 -> F} (h : ContDiffAt 𝕜 n f x) (c : R) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

/-- A variant of `iteratedDeriv_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/--
theorem `iteratedDeriv_const_smul_field` / 定理 `iteratedDeriv_const_smul_field`

English:
theorem iteratedDeriv_const_smul_field
  given: {n : Nat} (c : 𝕝) (f : 𝕜 -> F)
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul_field (s := Set.univ) c f

中文:
定理 iteratedDeriv_const_smul_field
  条件: {n : 自然数} (c : 𝕝) (f : 𝕜 -> F)
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul_field (s := Set.univ) c f

Depends on / 依赖: Set.univ, iteratedDerivWithin_const_smul_field, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_const_smul_field {n : Nat} (c : 𝕝) (f : 𝕜 -> F) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul_field (s := Set.univ) c f

/-- A variant of `iteratedDeriv_fun_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/--
theorem `iteratedDeriv_fun_const_smul_field` / 定理 `iteratedDeriv_fun_const_smul_field`

English:
theorem iteratedDeriv_fun_const_smul_field
  given: {n : Nat} (c : 𝕝) (f : 𝕜 -> F)
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_fun_const_smul_field (s := Set.univ) c f

中文:
定理 iteratedDeriv_fun_const_smul_field
  条件: {n : 自然数} (c : 𝕝) (f : 𝕜 -> F)
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_fun_const_smul_field (s := Set.univ) c f

Depends on / 依赖: Set.univ, iteratedDerivWithin_fun_const_smul_field, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_fun_const_smul_field {n : Nat} (c : 𝕝) (f : 𝕜 -> F) :
    iteratedDeriv n (c • f ·) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_fun_const_smul_field (s := Set.univ) c f

/--
theorem `iteratedDeriv_smul_const` / 定理 `iteratedDeriv_smul_const`

English:
theorem iteratedDeriv_smul_const
  given: {f : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (v : F)
  proof: by
  simp [iteratedDeriv, iteratedFDeriv_smul_const_apply hf]

中文:
定理 iteratedDeriv_smul_const
  条件: {f : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (v : F)
  证明: by
  simp [iteratedDeriv, iteratedFDeriv_smul_const_apply hf]

Depends on / 依赖: iteratedDeriv, iteratedFDeriv_smul_const_apply
-/
theorem iteratedDeriv_smul_const {f : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (v : F) :
    iteratedDeriv n (fun y => f y • v) x = iteratedDeriv n f x • v := by
  simp [iteratedDeriv, iteratedFDeriv_smul_const_apply hf]

/--
theorem `iteratedDeriv_const_mul` / 定理 `iteratedDeriv_const_mul`

English:
theorem iteratedDeriv_const_mul
  given: {n : Nat} {f : 𝕜 -> 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 n f x)
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ c hf

中文:
定理 iteratedDeriv_const_mul
  条件: {n : 自然数} {f : 𝕜 -> 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 n f x)
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ c hf

Depends on / 依赖: Set.mem_univ, iteratedDerivWithin_const_mul, iteratedDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_const_mul {n : Nat} {f : 𝕜 -> 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 n f x) :
    iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ c hf

/-- A variant of `iteratedDeriv_const_mul` without differentiability assumption when
the multiplication is in a division ring. -/
@[simp]
/--
theorem `iteratedDeriv_const_mul_field` / 定理 `iteratedDeriv_const_mul_field`

English:
theorem iteratedDeriv_const_mul_field
  given: {n : Nat} (c : 𝕜') (f : 𝕜 -> 𝕜')
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul_field (s := .univ) c f

中文:
定理 iteratedDeriv_const_mul_field
  条件: {n : 自然数} (c : 𝕜') (f : 𝕜 -> 𝕜')
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul_field (s := .univ) c f

Depends on / 依赖: iteratedDerivWithin_const_mul_field, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_const_mul_field {n : Nat} (c : 𝕜') (f : 𝕜 -> 𝕜') :
    iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul_field (s := .univ) c f

/-- A variant of `iteratedDeriv_mul_const` without differentiability assumption when
the multiplication is in a division ring. -/
@[simp]
/--
theorem `iteratedDeriv_mul_const_field` / 定理 `iteratedDeriv_mul_const_field`

English:
theorem iteratedDeriv_mul_const_field
  given: {n : Nat} (f : 𝕜 -> 𝕜') (c : 𝕜')
  proof: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_mul_const_field (s := .univ) f c

@[simp]

中文:
定理 iteratedDeriv_mul_const_field
  条件: {n : 自然数} (f : 𝕜 -> 𝕜') (c : 𝕜')
  证明: by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_mul_const_field (s := .univ) f c

@[simp]

Depends on / 依赖: iteratedDerivWithin_mul_const_field, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_mul_const_field {n : Nat} (f : 𝕜 -> 𝕜') (c : 𝕜') :
    iteratedDeriv n (f · * c) x = iteratedDeriv n f x * c := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_mul_const_field (s := .univ) f c

@[simp]
/--
theorem `iteratedDeriv_div_const` / 定理 `iteratedDeriv_div_const`

English:
theorem iteratedDeriv_div_const
  given: {n : Nat} (f : 𝕜 -> 𝕜') (c : 𝕜')
  proof: by
  simp [div_eq_mul_inv]

中文:
定理 iteratedDeriv_div_const
  条件: {n : 自然数} (f : 𝕜 -> 𝕜') (c : 𝕜')
  证明: by
  simp [div_eq_mul_inv]

Depends on / 依赖: ContinuousStar, NormedStarGroup, NormedStarGroup.to_continuousStar, div_eq_mul_inv, to_continuousStar
-/
theorem iteratedDeriv_div_const {n : Nat} (f : 𝕜 -> 𝕜') (c : 𝕜') :
    iteratedDeriv n (f · / c) x = iteratedDeriv n f x / c := by
  simp [div_eq_mul_inv]

/--
theorem `iteratedDeriv_comp_const_smul` / 定理 `iteratedDeriv_comp_const_smul`

English:
theorem iteratedDeriv_comp_const_smul
  given: {n : Nat} {f : 𝕜 -> F} (h : ContDiff 𝕜 n f) (c : 𝕜)
  proof: by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)

中文:
定理 iteratedDeriv_comp_const_smul
  条件: {n : 自然数} {f : 𝕜 -> F} (h : 连续可微 𝕜 n f) (c : 𝕜)
  证明: by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)

Depends on / 依赖: Set.mapsTo_univ, Set.mem_univ, contDiffOn_univ, contDiffOn_univ.mpr, iteratedDerivWithin_comp_const_smul, iteratedDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_comp_const_smul {n : Nat} {f : 𝕜 -> F} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n • iteratedDeriv n f (c * x) := by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)

/--
theorem `iteratedDeriv_comp_const_mul` / 定理 `iteratedDeriv_comp_const_mul`

English:
theorem iteratedDeriv_comp_const_mul
  given: {n : Nat} {f : 𝕜 -> 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜)
  proof: by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c

中文:
定理 iteratedDeriv_comp_const_mul
  条件: {n : 自然数} {f : 𝕜 -> 𝕜} (h : 连续可微 𝕜 n f) (c : 𝕜)
  证明: by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c

Depends on / 依赖: iteratedDeriv_comp_const_smul, smul_eq_mul
-/
theorem iteratedDeriv_comp_const_mul {n : Nat} {f : 𝕜 -> 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n * iteratedDeriv n f (c * x) := by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c

/--
lemma `iteratedDeriv_comp_neg` / 引理 `iteratedDeriv_comp_neg`

English:
lemma iteratedDeriv_comp_neg
  given: (n : Nat) (f : 𝕜 -> F) (a : 𝕜)
  proof: by
  simp [iteratedDeriv, ← iteratedFDerivWithin_univ, iteratedFDerivWithin_comp_neg]

@[to_fun iteratedDeriv_fun_id]

中文:
引理 iteratedDeriv_comp_neg
  条件: (n : 自然数) (f : 𝕜 -> F) (a : 𝕜)
  证明: by
  simp [iteratedDeriv, ← iteratedFDerivWithin_univ, iteratedFDerivWithin_comp_neg]

@[to_fun iteratedDeriv_fun_id]

Depends on / 依赖: iteratedDeriv, iteratedFDerivWithin_comp_neg, iteratedFDerivWithin_univ
-/
lemma iteratedDeriv_comp_neg (n : Nat) (f : 𝕜 -> F) (a : 𝕜) :
    iteratedDeriv n (fun x => f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  simp [iteratedDeriv, ← iteratedFDerivWithin_univ, iteratedFDerivWithin_comp_neg]

@[to_fun iteratedDeriv_fun_id]
/--
lemma `iteratedDeriv_id` / 引理 `iteratedDeriv_id`

English:
lemma iteratedDeriv_id
  given: {n : Nat} {x : 𝕜}
  proof: by
  obtain (_ | _ | n) := n <;>
    simp [iteratedDeriv_succ', iteratedDeriv_const]

中文:
引理 iteratedDeriv_id
  条件: {n : 自然数} {x : 𝕜}
  证明: by
  obtain (_ | _ | n) := n <;>
    simp [iteratedDeriv_succ', iteratedDeriv_const]

Depends on / 依赖: iteratedDeriv_const, iteratedDeriv_succ
-/
lemma iteratedDeriv_id {n : Nat} {x : 𝕜} :
    iteratedDeriv n id x = if n = 0 then x else if n = 1 then 1 else 0 := by
  obtain (_ | _ | n) := n <;>
    simp [iteratedDeriv_succ', iteratedDeriv_const]

/--
lemma `iteratedDeriv_fun_id_zero` / 引理 `iteratedDeriv_fun_id_zero`

English:
lemma iteratedDeriv_fun_id_zero
  proof: by
  simp +contextual [iteratedDeriv_fun_id]

@[to_fun iteratedDeriv_fun_mul]

中文:
引理 iteratedDeriv_fun_id_zero
  证明: by
  simp +contextual [iteratedDeriv_fun_id]

@[to_fun iteratedDeriv_fun_mul]

Depends on / 依赖: NormedStarGroup, contextual, iteratedDeriv_fun_id, to_normedStarGroup
-/
lemma iteratedDeriv_fun_id_zero :
    iteratedDeriv n (fun a => a) (0 : 𝕜) = if n = 1 then 1 else 0 := by
  simp +contextual [iteratedDeriv_fun_id]

@[to_fun iteratedDeriv_fun_mul]
/--
lemma `iteratedDeriv_mul` / 引理 `iteratedDeriv_mul`

English:
lemma iteratedDeriv_mul
  given: {f g : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  proof: by
  simpa using iteratedDerivWithin_mul
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

@[simp]

中文:
引理 iteratedDeriv_mul
  条件: {f g : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
  证明: by
  simpa using iteratedDerivWithin_mul
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

@[simp]

Depends on / 依赖: Set.mem_univ, contDiffWithinAt, hf.contDiffWithinAt, hg.contDiffWithinAt, iteratedDerivWithin_mul, mem_univ, uniqueDiffOn_univ
-/
lemma iteratedDeriv_mul {f g : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f * g) x = ∑ i in .range (n + 1),
      n.choose i * iteratedDeriv i f x * iteratedDeriv (n - i) g x := by
  simpa using iteratedDerivWithin_mul
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

@[simp]
/--
theorem `iteratedDeriv_pow` / 定理 `iteratedDeriv_pow`

English:
theorem iteratedDeriv_pow
  given: (m : Nat) (k : Nat)
  proof: by
  simpa using iteratedDerivWithin_pow (Set.mem_univ x) uniqueDiffOn_univ m k

中文:
定理 iteratedDeriv_pow
  条件: (m : 自然数) (k : 自然数)
  证明: by
  simpa using iteratedDerivWithin_pow (Set.mem_univ x) uniqueDiffOn_univ m k

Depends on / 依赖: Set.mem_univ, iteratedDerivWithin_pow, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_pow (m : Nat) (k : Nat) :
    iteratedDeriv k (· ^ m) x = m.descFactorial k * x ^ (m - k) := by
  simpa using iteratedDerivWithin_pow (Set.mem_univ x) uniqueDiffOn_univ m k

/--
lemma `iteratedDeriv_fun_pow_zero` / 引理 `iteratedDeriv_fun_pow_zero`

English:
lemma iteratedDeriv_fun_pow_zero
  given: {n m : Nat}
  proof: by
  obtain h | h | h := lt_trichotomy n m <;>
    simp_all [Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt.mpr, ne_of_lt, ne_of_gt]

中文:
引理 iteratedDeriv_fun_pow_zero
  条件: {n m : 自然数}
  证明: by
  obtain h | h | h := lt_trichotomy n m <;>
    simp_all [Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt.mpr, ne_of_lt, ne_of_gt]

Depends on / 依赖: Nat.descFactorial_eq_zero_iff_lt.mpr, Nat.descFactorial_self, descFactorial_eq_zero_iff_lt, descFactorial_self, lt_trichotomy, ne_of_gt, ne_of_lt
-/
lemma iteratedDeriv_fun_pow_zero {n m : Nat} :
    iteratedDeriv n (· ^ m) (0 : 𝕜) = if n = m then m.factorial else 0 := by
  obtain h | h | h := lt_trichotomy n m <;>
    simp_all [Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt.mpr, ne_of_lt, ne_of_gt]

/--
lemma `Filter.EventuallyEq.iteratedDeriv_eq` / 引理 `Filter.EventuallyEq.iteratedDeriv_eq`

English:
lemma Filter.EventuallyEq.iteratedDeriv_eq
  given: (n : Nat) {f g : 𝕜 -> F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g)
  proof: by
  simp only [← iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [(hfg.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hfg.eq_of_nhds n]

中文:
引理 滤子.EventuallyEq.iteratedDeriv_eq
  条件: (n : 自然数) {f g : 𝕜 -> F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g)
  证明: by
  simp only [← iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [(hfg.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hfg.eq_of_nhds n]

Depends on / 依赖: eq_of_nhds, filter_mono, hfg.eq_of_nhds, hfg.filter_mono, iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_univ, iteratedFDerivWithin_eq, nhdsWithin_le_nhds
-/
lemma Filter.EventuallyEq.iteratedDeriv_eq (n : Nat) {f g : 𝕜 -> F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  simp only [← iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [(hfg.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hfg.eq_of_nhds n]

/--
lemma `Set.EqOn.iteratedDeriv_of_isOpen` / 引理 `Set.EqOn.iteratedDeriv_of_isOpen`

English:
lemma Set.EqOn.iteratedDeriv_of_isOpen
  given: (hfg : Set.EqOn f g s) (hs : IsOpen s) (n : Nat)
  proof: by
  refine fun x hx => Filter.EventuallyEq.iteratedDeriv_eq n ?_
  filter_upwards [IsOpen.mem_nhds hs hx] with a ha
  exact hfg ha

中文:
引理 集合.EqOn.iteratedDeriv_of_isOpen
  条件: (hfg : 集合.EqOn f g s) (hs : 是开集 s) (n : 自然数)
  证明: by
  refine fun x hx => Filter.EventuallyEq.iteratedDeriv_eq n ?_
  filter_upwards [IsOpen.mem_nhds hs hx] with a ha
  exact hfg ha

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.iteratedDeriv_eq, IsOpen, IsOpen.mem_nhds, filter_upwards, iteratedDeriv_eq, mem_nhds
-/
lemma Set.EqOn.iteratedDeriv_of_isOpen (hfg : Set.EqOn f g s) (hs : IsOpen s) (n : Nat) :
    Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) s := by
  refine fun x hx => Filter.EventuallyEq.iteratedDeriv_eq n ?_
  filter_upwards [IsOpen.mem_nhds hs hx] with a ha
  exact hfg ha

end one_dimensional

/-!
### Invariance of iterated derivatives under translation
-/

section shift_invariance

variable (n : Nat) (f : 𝕜 -> F) (s : 𝕜)

/--
lemma `iteratedDeriv_comp_const_add` / 引理 `iteratedDeriv_comp_const_add`

English:
lemma iteratedDeriv_comp_const_add
  proof: by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
simpa only [iteratedDeriv_succ, IH] using funext deriv_comp_const_add _ s

中文:
引理 iteratedDeriv_comp_const_add
  证明: by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
simpa only [iteratedDeriv_succ, IH] using funext deriv_comp_const_add _ s

Depends on / 依赖: deriv_comp_const_add, iteratedDeriv_succ, iteratedDeriv_zero
-/
lemma iteratedDeriv_comp_const_add :
    iteratedDeriv n (fun z => f (s + z)) = fun t => iteratedDeriv n f (s + t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
simpa only [iteratedDeriv_succ, IH] using funext deriv_comp_const_add _ s

/--
lemma `iteratedDeriv_comp_add_const` / 引理 `iteratedDeriv_comp_add_const`

English:
lemma iteratedDeriv_comp_add_const
  proof: by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
simpa only [iteratedDeriv_succ, IH] using funext deriv_comp_add_const _ s

中文:
引理 iteratedDeriv_comp_add_const
  证明: by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
simpa only [iteratedDeriv_succ, IH] using funext deriv_comp_add_const _ s

Depends on / 依赖: deriv_comp_add_const, iteratedDeriv_succ, iteratedDeriv_zero
-/
lemma iteratedDeriv_comp_add_const :
    iteratedDeriv n (fun z => f (z + s)) = fun t => iteratedDeriv n f (t + s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
simpa only [iteratedDeriv_succ, IH] using funext deriv_comp_add_const _ s

/--
lemma `iteratedDeriv_comp_sub_const` / 引理 `iteratedDeriv_comp_sub_const`

English:
lemma iteratedDeriv_comp_sub_const
  proof: by
  simp [sub_eq_add_neg, iteratedDeriv_comp_add_const]

中文:
引理 iteratedDeriv_comp_sub_const
  证明: by
  simp [sub_eq_add_neg, iteratedDeriv_comp_add_const]

Depends on / 依赖: iteratedDeriv_comp_add_const, sub_eq_add_neg
-/
lemma iteratedDeriv_comp_sub_const :
    iteratedDeriv n (fun z => f (z - s)) = fun t => iteratedDeriv n f (t - s) := by
  simp [sub_eq_add_neg, iteratedDeriv_comp_add_const]

/--
lemma `iteratedDeriv_comp_const_sub` / 引理 `iteratedDeriv_comp_const_sub`

English:
lemma iteratedDeriv_comp_const_sub
  proof: by
  simpa [funext_iff, neg_add_eq_sub, iteratedDeriv_comp_add_const] using
    iteratedDeriv_comp_neg n (fun z => f (z + s))

中文:
引理 iteratedDeriv_comp_const_sub
  证明: by
  simpa [funext_iff, neg_add_eq_sub, iteratedDeriv_comp_add_const] using
    iteratedDeriv_comp_neg n (fun z => f (z + s))

Depends on / 依赖: funext_iff, iteratedDeriv_comp_add_const, iteratedDeriv_comp_neg, neg_add_eq_sub
-/
lemma iteratedDeriv_comp_const_sub :
    iteratedDeriv n (fun z => f (s - z)) = fun t => (-1 : 𝕜) ^ n • iteratedDeriv n f (s - t) := by
  simpa [funext_iff, neg_add_eq_sub, iteratedDeriv_comp_add_const] using
    iteratedDeriv_comp_neg n (fun z => f (z + s))

end shift_invariance

section sums

/-!
### Iterated derivatives of sums
-/
open Finset
variable {ι : Type*} {n : Nat} {x : 𝕜} {f : ι -> 𝕜 -> F} {I : Finset ι}

/--
lemma `iteratedDerivWithin_sum` / 引理 `iteratedDerivWithin_sum`

English:
lemma iteratedDerivWithin_sum
  statement: {s : Set 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s)
  proof: by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    rw [forall_mem_insert] at hf
    simp only [sum_insert hi, sum_fn] at IH ⊢
    rw [iteratedDerivWithin_add hx hs hf.1 (.sum hf.2)]; rw [IH hf.2]

中文:
引理 iteratedDerivWithin_sum
  结论: {s : 集合 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s)
  证明: by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    rw [forall_mem_insert] at hf
    simp only [sum_insert hi, sum_fn] at IH ⊢
    rw [iteratedDerivWithin_add hx hs hf.1 (.sum hf.2)]; rw [IH hf.2]

Depends on / 依赖: Finset, Finset.induction_on, classical, forall_mem_insert, induction_on, insert, iteratedDerivWithin_add, sum_fn, sum_insert
-/
lemma iteratedDerivWithin_sum {s : Set 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s)
    (hf : forall i in I, ContDiffWithinAt 𝕜 n (f i) s x) :
    iteratedDerivWithin n (∑ i in I, f i) s x =
      ∑ i in I, iteratedDerivWithin n (f i) s x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    rw [forall_mem_insert] at hf
    simp only [sum_insert hi, sum_fn] at IH ⊢
    rw [iteratedDerivWithin_add hx hs hf.1 (.sum hf.2)]; rw [IH hf.2]

/--
lemma `iteratedDerivWithin_fun_sum` / 引理 `iteratedDerivWithin_fun_sum`

English:
lemma iteratedDerivWithin_fun_sum
  statement: {s : Set 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s)
  proof: by
  simpa [sum_fn] using iteratedDerivWithin_sum hx hs hf

中文:
引理 iteratedDerivWithin_fun_sum
  结论: {s : 集合 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s)
  证明: by
  simpa [sum_fn] using iteratedDerivWithin_sum hx hs hf

Depends on / 依赖: iteratedDerivWithin_sum, sum_fn
-/
lemma iteratedDerivWithin_fun_sum {s : Set 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s)
    (hf : forall i in I, ContDiffWithinAt 𝕜 n (f i) s x) :
    iteratedDerivWithin n (∑ i in I, f i ·) s x = ∑ i in I, iteratedDerivWithin n (f i) s x := by
  simpa [sum_fn] using iteratedDerivWithin_sum hx hs hf

/--
lemma `iteratedDeriv_sum` / 引理 `iteratedDeriv_sum`

English:
lemma iteratedDeriv_sum
  given: (hf : forall i in I, ContDiffAt 𝕜 n (f i) x)
  proof: by
  simpa using iteratedDerivWithin_sum (Set.mem_univ x) uniqueDiffOn_univ hf

中文:
引理 iteratedDeriv_sum
  条件: (hf : 对任意 i in I, ContDiffAt 𝕜 n (f i) x)
  证明: by
  simpa using iteratedDerivWithin_sum (Set.mem_univ x) uniqueDiffOn_univ hf

Depends on / 依赖: Set.mem_univ, iteratedDerivWithin_sum, mem_univ, uniqueDiffOn_univ
-/
lemma iteratedDeriv_sum (hf : forall i in I, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (∑ i in I, f i) x = ∑ i in I, iteratedDeriv n (f i) x := by
  simpa using iteratedDerivWithin_sum (Set.mem_univ x) uniqueDiffOn_univ hf

/--
lemma `iteratedDeriv_fun_sum` / 引理 `iteratedDeriv_fun_sum`

English:
lemma iteratedDeriv_fun_sum
  given: (hf : forall i in I, ContDiffAt 𝕜 n (f i) x)
  proof: by
  simpa [sum_fn] using iteratedDeriv_sum hf

中文:
引理 iteratedDeriv_fun_sum
  条件: (hf : 对任意 i in I, ContDiffAt 𝕜 n (f i) x)
  证明: by
  simpa [sum_fn] using iteratedDeriv_sum hf

Depends on / 依赖: iteratedDeriv_sum, sum_fn
-/
lemma iteratedDeriv_fun_sum (hf : forall i in I, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (fun z => ∑ i in I, f i z) x = ∑ i in I, iteratedDeriv n (f i) x := by
  simpa [sum_fn] using iteratedDeriv_sum hf

end sums
