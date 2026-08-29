/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Fréchet Derivative of `f x ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n • f x ^ (n - 1)) • f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `fderiv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i`.

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

variable {𝕜 𝔸 E : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E -> 𝔸} {f' : E ->L[𝕜] 𝔸} {x : E} {s : Set E}

open scoped RightActions

/--
theorem `aux` / 定理 `aux`

English:
theorem aux
  given: (f : E -> 𝔸) (f' : E ->L[𝕜] 𝔸) (x : E) (n : Nat)
  proof: by
  rw [Finset.sum_range_succ _ (n + 1)]; rw [Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
  rw [ts

中文:
定理 aux
  条件: (f : E -> 𝔸) (f' : E ->L[𝕜] 𝔸) (x : E) (n : 自然数)
  证明: by
  rw [Finset.sum_range_succ _ (n + 1)]; rw [Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
  rw [ts
-/
private theorem aux (f : E -> 𝔸) (f' : E ->L[𝕜] 𝔸) (x : E) (n : Nat) :
    f x •> ∑ i in Finset.range (n + 1), f x ^ ((n + 1).pred - i) •> f' <• f x ^ i
      + f' <• (f x ^ (n + 1)) =
    ∑ i in Finset.range (n + 1 + 1), f x ^ ((n + 1 + 1).pred - i) •> f' <• f x ^ i := by
  rw [Finset.sum_range_succ _ (n + 1)]; rw [Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
  rw [tsub_add_eq_add_tsub hx]

@[to_fun]
/--
theorem `HasStrictFDerivAt.pow'` / 定理 `HasStrictFDerivAt.pow'`

English:
theorem HasStrictFDerivAt.pow'
  given: (h : HasStrictFDerivAt f f' x) (n : Nat)
  proof: match n with
  | 0 => by simpa using! hasStrictFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
refine this.congr_fderiv aux _ _ _ _

中文:
定理 HasStrictFDerivAt.pow'
  条件: (h : HasStrictFDerivAt f f' x) (n : 自然数)
  证明: match n with
  | 0 => by simpa using! hasStrictFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
refine this.congr_fderiv aux _ _ _ _

Depends on / 依赖: congr_fderiv, h.mul, h.pow, hasStrictFDerivAt_const, pow_succ, simp_rw, this.congr_fderiv
-/
theorem HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f f' x) (n : Nat) :
    HasStrictFDerivAt (f ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using! hasStrictFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
refine this.congr_fderiv aux _ _ _ _

/--
theorem `hasStrictFDerivAt_pow'` / 定理 `hasStrictFDerivAt_pow'`

English:
theorem hasStrictFDerivAt_pow'
  given: (n : Nat) {x : 𝔸}
  proof: .pow' n hasStrictFDerivAt_id _

@[to_fun]

中文:
定理 hasStrictFDerivAt_pow'
  条件: (n : 自然数) {x : 𝔸}
  证明: .pow' n hasStrictFDerivAt_id _

@[to_fun]
-/
theorem hasStrictFDerivAt_pow' (n : Nat) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => x ^ n)
      (∑ i in Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
.pow' n hasStrictFDerivAt_id _

@[to_fun]
/--
theorem `HasFDerivWithinAt.pow'` / 定理 `HasFDerivWithinAt.pow'`

English:
theorem HasFDerivWithinAt.pow'
  given: (h : HasFDerivWithinAt f f' s x) (n : Nat)
  proof: match n with
  | 0 => by simpa using! hasFDerivWithinAt_const 1 x s
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
exact this.congr_fderiv aux _ _ _ _

中文:
定理 HasFDerivWithinAt.pow'
  条件: (h : HasFDerivWithinAt f f' s x) (n : 自然数)
  证明: match n with
  | 0 => by simpa using! hasFDerivWithinAt_const 1 x s
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
exact this.congr_fderiv aux _ _ _ _

Depends on / 依赖: congr_fderiv, h.mul, h.pow, hasFDerivWithinAt_const, pow_succ, simp_rw, this.congr_fderiv
-/
theorem HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f f' s x) (n : Nat) :
    HasFDerivWithinAt (f ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) s x :=
  match n with
  | 0 => by simpa using! hasFDerivWithinAt_const 1 x s
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
exact this.congr_fderiv aux _ _ _ _

/--
theorem `hasFDerivWithinAt_pow'` / 定理 `hasFDerivWithinAt_pow'`

English:
theorem hasFDerivWithinAt_pow'
  given: (n : Nat) {x : 𝔸} {s : Set 𝔸}
  proof: .pow' n hasFDerivWithinAt_id _ _

@[to_fun]

中文:
定理 hasFDerivWithinAt_pow'
  条件: (n : 自然数) {x : 𝔸} {s : 集合 𝔸}
  证明: .pow' n hasFDerivWithinAt_id _ _

@[to_fun]
-/
theorem hasFDerivWithinAt_pow' (n : Nat) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun x => x ^ n)
      (∑ i in Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) s x :=
.pow' n hasFDerivWithinAt_id _ _

@[to_fun]
/--
theorem `HasFDerivAt.pow'` / 定理 `HasFDerivAt.pow'`

English:
theorem HasFDerivAt.pow'
  given: (h : HasFDerivAt f f' x) (n : Nat)
  proof: match n with
  | 0 => by simpa using! hasFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
exact this.congr_fderiv aux _ _ _ _

中文:
定理 在点处Fréchet可导.pow'
  条件: (h : 在点处Fréchet可导 f f' x) (n : 自然数)
  证明: match n with
  | 0 => by simpa using! hasFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
exact this.congr_fderiv aux _ _ _ _

Depends on / 依赖: congr_fderiv, h.mul, h.pow, hasFDerivAt_const, pow_succ, simp_rw, this.congr_fderiv
-/
theorem HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : Nat) :
    HasFDerivAt (f ^ n) (∑ i in Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using! hasFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
exact this.congr_fderiv aux _ _ _ _

/--
theorem `hasFDerivAt_pow'` / 定理 `hasFDerivAt_pow'`

English:
theorem hasFDerivAt_pow'
  given: (n : Nat) {x : 𝔸}
  proof: .pow' n hasFDerivAt_id _

@[fun_prop]

中文:
定理 hasFDerivAt_pow'
  条件: (n : 自然数) {x : 𝔸}
  证明: .pow' n hasFDerivAt_id _

@[fun_prop]
-/
theorem hasFDerivAt_pow' (n : Nat) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x => x ^ n)
      (∑ i in Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
.pow' n hasFDerivAt_id _

@[fun_prop]
/--
theorem `DifferentiableWithinAt.fun_pow` / 定理 `DifferentiableWithinAt.fun_pow`

English:
theorem DifferentiableWithinAt.fun_pow
  given: (hf : DifferentiableWithinAt 𝕜 f s x) (n : Nat)
  proof: let ⟨_, hf'⟩ := hf; ⟨_, hf'.pow' n⟩

@[fun_prop]

中文:
定理 DifferentiableWithinAt.fun_pow
  条件: (hf : DifferentiableWithinAt 𝕜 f s x) (n : 自然数)
  证明: let ⟨_, hf'⟩ := hf; ⟨_, hf'.pow' n⟩

@[fun_prop]
-/
theorem DifferentiableWithinAt.fun_pow (hf : DifferentiableWithinAt 𝕜 f s x) (n : Nat) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ n) s x :=
  let ⟨_, hf'⟩ := hf; ⟨_, hf'.pow' n⟩

@[fun_prop]
/--
theorem `DifferentiableWithinAt.pow` / 定理 `DifferentiableWithinAt.pow`

English:
theorem DifferentiableWithinAt.pow
  given: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: hf.fun_pow

中文:
定理 DifferentiableWithinAt.pow
  条件: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: hf.fun_pow

Depends on / 依赖: fun_pow, hf.fun_pow
-/
theorem DifferentiableWithinAt.pow (hf : DifferentiableWithinAt 𝕜 f s x) :
    forall n : Nat, DifferentiableWithinAt 𝕜 (f ^ n) s x :=
  hf.fun_pow

/--
theorem `differentiableWithinAt_pow` / 定理 `differentiableWithinAt_pow`

English:
theorem differentiableWithinAt_pow
  given: (n : Nat) {x : 𝔸} {s : Set 𝔸}
  proof: differentiableWithinAt_id.pow _

@[to_fun (attr := simp, fun_prop)]

中文:
定理 differentiableWithinAt_pow
  条件: (n : 自然数) {x : 𝔸} {s : 集合 𝔸}
  证明: differentiableWithinAt_id.pow _

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: differentiableWithinAt_id, differentiableWithinAt_id.pow
-/
theorem differentiableWithinAt_pow (n : Nat) {x : 𝔸} {s : Set 𝔸} :
    DifferentiableWithinAt 𝕜 (fun x : 𝔸 => x ^ n) s x :=
  differentiableWithinAt_id.pow _

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.pow` / 定理 `DifferentiableAt.pow`

English:
theorem DifferentiableAt.pow
  given: (hf : DifferentiableAt 𝕜 f x) (n : Nat)
  proof: differentiableWithinAt_univ.mp hf.differentiableWithinAt.pow n

中文:
定理 DifferentiableAt.pow
  条件: (hf : DifferentiableAt 𝕜 f x) (n : 自然数)
  证明: differentiableWithinAt_univ.mp hf.differentiableWithinAt.pow n

Depends on / 依赖: differentiableWithinAt, differentiableWithinAt_univ, differentiableWithinAt_univ.mp, hf.differentiableWithinAt.pow
-/
theorem DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x) (n : Nat) :
    DifferentiableAt 𝕜 (f ^ n) x :=
differentiableWithinAt_univ.mp hf.differentiableWithinAt.pow n

/--
theorem `differentiableAt_pow` / 定理 `differentiableAt_pow`

English:
theorem differentiableAt_pow
  given: (n : Nat) {x : 𝔸}
  statement: DifferentiableAt 𝕜 (fun x : 𝔸 => x ^ n) x
  proof: differentiableAt_id.pow _

@[to_fun (attr := fun_prop)]

中文:
定理 differentiableAt_pow
  条件: (n : 自然数) {x : 𝔸}
  结论: DifferentiableAt 𝕜 (fun x : 𝔸 => x ^ n) x
  证明: differentiableAt_id.pow _

@[to_fun (attr := fun_prop)]

Depends on / 依赖: differentiableAt_id, differentiableAt_id.pow
-/
theorem differentiableAt_pow (n : Nat) {x : 𝔸} : DifferentiableAt 𝕜 (fun x : 𝔸 => x ^ n) x :=
  differentiableAt_id.pow _

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.pow` / 定理 `DifferentiableOn.pow`

English:
theorem DifferentiableOn.pow
  given: (hf : DifferentiableOn 𝕜 f s) (n : Nat)
  proof: fun x h => (hf x h).pow n

中文:
定理 DifferentiableOn.pow
  条件: (hf : DifferentiableOn 𝕜 f s) (n : 自然数)
  证明: fun x h => (hf x h).pow n
-/
theorem DifferentiableOn.pow (hf : DifferentiableOn 𝕜 f s) (n : Nat) :
    DifferentiableOn 𝕜 (f ^ n) s := fun x h => (hf x h).pow n

/--
theorem `differentiableOn_pow` / 定理 `differentiableOn_pow`

English:
theorem differentiableOn_pow
  given: (n : Nat) {s : Set 𝔸}
  statement: DifferentiableOn 𝕜 (fun x : 𝔸 => x ^ n) s
  proof: differentiableOn_id.pow n

@[to_fun (attr := simp, fun_prop)]

中文:
定理 differentiableOn_pow
  条件: (n : 自然数) {s : 集合 𝔸}
  结论: DifferentiableOn 𝕜 (fun x : 𝔸 => x ^ n) s
  证明: differentiableOn_id.pow n

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: differentiableOn_id, differentiableOn_id.pow
-/
theorem differentiableOn_pow (n : Nat) {s : Set 𝔸} : DifferentiableOn 𝕜 (fun x : 𝔸 => x ^ n) s :=
  differentiableOn_id.pow n

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.pow` / 定理 `Differentiable.pow`

English:
theorem Differentiable.pow
  given: (hf : Differentiable 𝕜 f) (n : Nat)
  statement: Differentiable 𝕜 (f ^ n)
  proof: fun x => (hf x).pow n

中文:
定理 可微.pow
  条件: (hf : 可微 𝕜 f) (n : 自然数)
  结论: 可微 𝕜 (f ^ n)
  证明: fun x => (hf x).pow n
-/
theorem Differentiable.pow (hf : Differentiable 𝕜 f) (n : Nat) : Differentiable 𝕜 (f ^ n) :=
  fun x => (hf x).pow n

/--
theorem `differentiable_pow` / 定理 `differentiable_pow`

English:
theorem differentiable_pow
  given: (n : Nat)
  statement: Differentiable 𝕜 fun x : 𝔸 => x ^ n
  proof: differentiable_id.pow _

@[to_fun fderiv_fun_pow']

中文:
定理 differentiable_pow
  条件: (n : 自然数)
  结论: 可微 𝕜 fun x : 𝔸 => x ^ n
  证明: differentiable_id.pow _

@[to_fun fderiv_fun_pow']

Depends on / 依赖: differentiable_id, differentiable_id.pow
-/
theorem differentiable_pow (n : Nat) : Differentiable 𝕜 fun x : 𝔸 => x ^ n :=
  differentiable_id.pow _

@[to_fun fderiv_fun_pow']
/--
theorem `fderiv_pow'` / 定理 `fderiv_pow'`

English:
theorem fderiv_pow'
  given: (n : Nat) (hf : DifferentiableAt 𝕜 f x)
  proof: .fderiv hf.hasFDerivAt.pow' n

中文:
定理 fderiv_pow'
  条件: (n : 自然数) (hf : DifferentiableAt 𝕜 f x)
  证明: .fderiv hf.hasFDerivAt.pow' n

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.pow
-/
theorem fderiv_pow' (n : Nat) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (f ^ n) x
      = (∑ i in Finset.range n, f x ^ (n.pred - i) •> fderiv 𝕜 f x <• f x ^ i) :=
.fderiv hf.hasFDerivAt.pow' n

/--
theorem `fderiv_pow_ring'` / 定理 `fderiv_pow_ring'`

English:
theorem fderiv_pow_ring'
  given: {x : 𝔸} (n : Nat)
  proof: by
  rw [fderiv_fun_pow' n differentiableAt_fun_id]; rw [fderiv_fun_id]

@[to_fun fderivWithin_fun_pow']

中文:
定理 fderiv_pow_ring'
  条件: {x : 𝔸} (n : 自然数)
  证明: by
  rw [fderiv_fun_pow' n differentiableAt_fun_id]; rw [fderiv_fun_id]

@[to_fun fderivWithin_fun_pow']

Depends on / 依赖: differentiableAt_fun_id, fderiv_fun_id, fderiv_fun_pow
-/
theorem fderiv_pow_ring' {x : 𝔸} (n : Nat) :
    fderiv 𝕜 (fun x : 𝔸 => x ^ n) x
      = (∑ i in Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i) := by
  rw [fderiv_fun_pow' n differentiableAt_fun_id]; rw [fderiv_fun_id]

@[to_fun fderivWithin_fun_pow']
/--
theorem `fderivWithin_pow'` / 定理 `fderivWithin_pow'`

English:
theorem fderivWithin_pow'
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: .fderivWithin hxs hf.hasFDerivWithinAt.pow' n

中文:
定理 fderivWithin_pow'
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: .fderivWithin hxs hf.hasFDerivWithinAt.pow' n

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.pow
-/
theorem fderivWithin_pow' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : Nat) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (f ^ n) s x
      = (∑ i in Finset.range n, f x ^ (n.pred - i) •> fderivWithin 𝕜 f s x <• f x ^ i) :=
.fderivWithin hxs hf.hasFDerivWithinAt.pow' n

/--
theorem `fderivWithin_pow_ring'` / 定理 `fderivWithin_pow_ring'`

English:
theorem fderivWithin_pow_ring'
  given: {s : Set 𝔸} {x : 𝔸} (n : Nat) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [fderivWithin_fun_pow' hxs n differentiableAt_fun_id.differentiableWithinAt]; rw [fderivWithin_fun_id hxs]

中文:
定理 fderivWithin_pow_ring'
  条件: {s : 集合 𝔸} {x : 𝔸} (n : 自然数) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [fderivWithin_fun_pow' hxs n differentiableAt_fun_id.differentiableWithinAt]; rw [fderivWithin_fun_id hxs]

Depends on / 依赖: differentiableAt_fun_id, differentiableAt_fun_id.differentiableWithinAt, differentiableWithinAt, fderivWithin_fun_id, fderivWithin_fun_pow
-/
theorem fderivWithin_pow_ring' {s : Set 𝔸} {x : 𝔸} (n : Nat) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : 𝔸 => x ^ n) s x
      = (∑ i in Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i) := by
  rw [fderivWithin_fun_pow' hxs n differentiableAt_fun_id.differentiableWithinAt]; rw [fderivWithin_fun_id hxs]

end NormedRing

section NormedCommRing
variable [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E -> 𝔸} {f' : E ->L[𝕜] 𝔸} {x : E} {s : Set E}

/--
theorem `aux_sum_eq_pow` / 定理 `aux_sum_eq_pow`

English:
theorem aux_sum_eq_pow
  given: (n : Nat)
  proof: by
  simp_rw [op_smul_eq_smul, smul_smul, ← pow_add, ← Finset.sum_smul]
  rw [Finset.sum_eq_card_nsmul]; rw [Finset.card_range]; rw [smul_assoc]
  intro a ha
  congr
  exact add_tsub_cancel_of_le (Nat.le_pred_of_lt <| Finset.mem_range.1 ha)

中文:
定理 aux_sum_eq_pow
  条件: (n : 自然数)
  证明: by
  simp_rw [op_smul_eq_smul, smul_smul, ← pow_add, ← Finset.sum_smul]
  rw [Finset.sum_eq_card_nsmul]; rw [Finset.card_range]; rw [smul_assoc]
  intro a ha
  congr
  exact add_tsub_cancel_of_le (Nat.le_pred_of_lt <| Finset.mem_range.1 ha)
-/
private theorem aux_sum_eq_pow (n : Nat) :
    ∑ i in Finset.range n, MulOpposite.op (f x ^ i) • f x ^ (n.pred - i) • f' =
      (n • f x ^ (n - 1)) • f' := by
  simp_rw [op_smul_eq_smul, smul_smul, ← pow_add, ← Finset.sum_smul]
  rw [Finset.sum_eq_card_nsmul]; rw [Finset.card_range]; rw [smul_assoc]
  intro a ha
  congr
  exact add_tsub_cancel_of_le (Nat.le_pred_of_lt <| Finset.mem_range.1 ha)

/--
theorem `HasStrictFDerivAt.pow` / 定理 `HasStrictFDerivAt.pow`

English:
theorem HasStrictFDerivAt.pow
  given: (h : HasStrictFDerivAt f f' x) (n : Nat)
  proof: .congr_fderiv aux_sum_eq_pow _ h.pow' n

中文:
定理 HasStrictFDerivAt.pow
  条件: (h : HasStrictFDerivAt f f' x) (n : 自然数)
  证明: .congr_fderiv aux_sum_eq_pow _ h.pow' n

Depends on / 依赖: aux_sum_eq_pow, congr_fderiv, h.pow
-/
theorem HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f' x) (n : Nat) :
    HasStrictFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') x :=
.congr_fderiv aux_sum_eq_pow _ h.pow' n

/--
theorem `hasStrictFDerivAt_pow` / 定理 `hasStrictFDerivAt_pow`

English:
theorem hasStrictFDerivAt_pow
  given: (n : Nat) {x : 𝔸}
  proof: .pow n hasStrictFDerivAt_id _

中文:
定理 hasStrictFDerivAt_pow
  条件: (n : 自然数) {x : 𝔸}
  证明: .pow n hasStrictFDerivAt_id _
-/
theorem hasStrictFDerivAt_pow (n : Nat) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜)
      (fun x : 𝔸 => x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) x :=
.pow n hasStrictFDerivAt_id _

/--
theorem `HasFDerivWithinAt.pow` / 定理 `HasFDerivWithinAt.pow`

English:
theorem HasFDerivWithinAt.pow
  given: (h : HasFDerivWithinAt f f' s x) (n : Nat)
  proof: .congr_fderiv aux_sum_eq_pow _ h.pow' n

中文:
定理 HasFDerivWithinAt.pow
  条件: (h : HasFDerivWithinAt f f' s x) (n : 自然数)
  证明: .congr_fderiv aux_sum_eq_pow _ h.pow' n

Depends on / 依赖: aux_sum_eq_pow, congr_fderiv, h.pow
-/
theorem HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f' s x) (n : Nat) :
    HasFDerivWithinAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') s x :=
.congr_fderiv aux_sum_eq_pow _ h.pow' n

/--
theorem `hasFDerivWithinAt_pow` / 定理 `hasFDerivWithinAt_pow`

English:
theorem hasFDerivWithinAt_pow
  given: (n : Nat) {x : 𝔸} {s : Set 𝔸}
  proof: .pow n hasFDerivWithinAt_id _ _

中文:
定理 hasFDerivWithinAt_pow
  条件: (n : 自然数) {x : 𝔸} {s : 集合 𝔸}
  证明: .pow n hasFDerivWithinAt_id _ _
-/
theorem hasFDerivWithinAt_pow (n : Nat) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜)
      (fun x : 𝔸 => x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) s x :=
.pow n hasFDerivWithinAt_id _ _

/--
theorem `HasFDerivAt.pow` / 定理 `HasFDerivAt.pow`

English:
theorem HasFDerivAt.pow
  given: (h : HasFDerivAt f f' x) (n : Nat)
  proof: .congr_fderiv aux_sum_eq_pow _ h.pow' n

中文:
定理 在点处Fréchet可导.pow
  条件: (h : 在点处Fréchet可导 f f' x) (n : 自然数)
  证明: .congr_fderiv aux_sum_eq_pow _ h.pow' n

Depends on / 依赖: aux_sum_eq_pow, congr_fderiv, h.pow
-/
theorem HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : Nat) :
    HasFDerivAt (fun x => f x ^ n) ((n • f x ^ (n - 1)) • f') x :=
.congr_fderiv aux_sum_eq_pow _ h.pow' n

/--
theorem `hasFDerivAt_pow` / 定理 `hasFDerivAt_pow`

English:
theorem hasFDerivAt_pow
  given: (n : Nat) {x : 𝔸}
  proof: .pow n hasFDerivAt_id _

@[to_fun fderiv_fun_pow]

中文:
定理 hasFDerivAt_pow
  条件: (n : 自然数) {x : 𝔸}
  证明: .pow n hasFDerivAt_id _

@[to_fun fderiv_fun_pow]
-/
theorem hasFDerivAt_pow (n : Nat) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜)
      (fun x : 𝔸 => x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) x :=
.pow n hasFDerivAt_id _

@[to_fun fderiv_fun_pow]
/--
theorem `fderiv_pow` / 定理 `fderiv_pow`

English:
theorem fderiv_pow
  given: (n : Nat) (hf : DifferentiableAt 𝕜 f x)
  proof: .fderiv hf.hasFDerivAt.pow n

中文:
定理 fderiv_pow
  条件: (n : 自然数) (hf : DifferentiableAt 𝕜 f x)
  证明: .fderiv hf.hasFDerivAt.pow n

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.pow
-/
theorem fderiv_pow (n : Nat) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (f ^ n) x = (n • f x ^ (n - 1)) • fderiv 𝕜 f x :=
.fderiv hf.hasFDerivAt.pow n

/--
theorem `fderiv_pow_ring` / 定理 `fderiv_pow_ring`

English:
theorem fderiv_pow_ring
  given: {x : 𝔸} (n : Nat)
  proof: by
  rw [fderiv_fun_pow n differentiableAt_fun_id]; rw [fderiv_fun_id]

@[to_fun fderivWithin_fun_pow]

中文:
定理 fderiv_pow_ring
  条件: {x : 𝔸} (n : 自然数)
  证明: by
  rw [fderiv_fun_pow n differentiableAt_fun_id]; rw [fderiv_fun_id]

@[to_fun fderivWithin_fun_pow]

Depends on / 依赖: differentiableAt_fun_id, fderiv_fun_id, fderiv_fun_pow
-/
theorem fderiv_pow_ring {x : 𝔸} (n : Nat) :
    fderiv 𝕜 (fun x : 𝔸 => x ^ n) x = (n • x ^ (n - 1)) • .id _ _ := by
  rw [fderiv_fun_pow n differentiableAt_fun_id]; rw [fderiv_fun_id]

@[to_fun fderivWithin_fun_pow]
/--
theorem `fderivWithin_pow` / 定理 `fderivWithin_pow`

English:
theorem fderivWithin_pow
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: .fderivWithin hxs hf.hasFDerivWithinAt.pow n

中文:
定理 fderivWithin_pow
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: .fderivWithin hxs hf.hasFDerivWithinAt.pow n

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.pow
-/
theorem fderivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : Nat) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (f ^ n) s x = (n • f x ^ (n - 1)) • fderivWithin 𝕜 f s x :=
.fderivWithin hxs hf.hasFDerivWithinAt.pow n

/--
theorem `fderivWithin_pow_ring` / 定理 `fderivWithin_pow_ring`

English:
theorem fderivWithin_pow_ring
  given: {s : Set 𝔸} {x : 𝔸} (n : Nat) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [fderivWithin_fun_pow hxs n differentiableAt_fun_id.differentiableWithinAt]; rw [fderivWithin_fun_id hxs]

中文:
定理 fderivWithin_pow_ring
  条件: {s : 集合 𝔸} {x : 𝔸} (n : 自然数) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [fderivWithin_fun_pow hxs n differentiableAt_fun_id.differentiableWithinAt]; rw [fderivWithin_fun_id hxs]

Depends on / 依赖: differentiableAt_fun_id, differentiableAt_fun_id.differentiableWithinAt, differentiableWithinAt, fderivWithin_fun_id, fderivWithin_fun_pow
-/
theorem fderivWithin_pow_ring {s : Set 𝔸} {x : 𝔸} (n : Nat) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : 𝔸 => x ^ n) s x = (n • x ^ (n - 1)) • .id _ _ := by
  rw [fderivWithin_fun_pow hxs n differentiableAt_fun_id.differentiableWithinAt]; rw [fderivWithin_fun_id hxs]

end NormedCommRing
