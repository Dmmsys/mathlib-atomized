/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n * f x ^ (n - 1) * f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `deriv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

variable {𝕜 𝔸 : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸]
variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 -> 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

/--
theorem `HasStrictDerivAt.fun_pow'` / 定理 `HasStrictDerivAt.fun_pow'`

English:
theorem HasStrictDerivAt.fun_pow'
  given: (h : HasStrictDerivAt f f' x) (n : Nat)
  proof: by
.hasStrictDerivAt simpa using! h.hasStrictFDerivAt.pow' n

中文:
定理 HasStrictDerivAt.fun_pow'
  条件: (h : HasStrictDerivAt f f' x) (n : 自然数)
  证明: by
.hasStrictDerivAt simpa using! h.hasStrictFDerivAt.pow' n

Depends on / 依赖: h.hasStrictFDerivAt.pow, hasStrictDerivAt, hasStrictFDerivAt
-/
theorem HasStrictDerivAt.fun_pow' (h : HasStrictDerivAt f f' x) (n : Nat) :
    HasStrictDerivAt (fun x => f x ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
.hasStrictDerivAt simpa using! h.hasStrictFDerivAt.pow' n

/--
theorem `HasStrictDerivAt.pow'` / 定理 `HasStrictDerivAt.pow'`

English:
theorem HasStrictDerivAt.pow'
  given: (h : HasStrictDerivAt f f' x) (n : Nat)
  proof: h.fun_pow' n

中文:
定理 HasStrictDerivAt.pow'
  条件: (h : HasStrictDerivAt f f' x) (n : 自然数)
  证明: h.fun_pow' n

Depends on / 依赖: fun_pow, h.fun_pow
-/
theorem HasStrictDerivAt.pow' (h : HasStrictDerivAt f f' x) (n : Nat) :
    HasStrictDerivAt (f ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x :=
  h.fun_pow' n

/--
theorem `HasDerivWithinAt.fun_pow'` / 定理 `HasDerivWithinAt.fun_pow'`

English:
theorem HasDerivWithinAt.fun_pow'
  given: (h : HasDerivWithinAt f f' s x) (n : Nat)
  proof: by
.hasDerivWithinAt simpa using! h.hasFDerivWithinAt.pow' n

中文:
定理 HasDerivWithinAt.fun_pow'
  条件: (h : HasDerivWithinAt f f' s x) (n : 自然数)
  证明: by
.hasDerivWithinAt simpa using! h.hasFDerivWithinAt.pow' n

Depends on / 依赖: h.hasFDerivWithinAt.pow, hasDerivWithinAt, hasFDerivWithinAt
-/
theorem HasDerivWithinAt.fun_pow' (h : HasDerivWithinAt f f' s x) (n : Nat) :
    HasDerivWithinAt (fun x => f x ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x := by
.hasDerivWithinAt simpa using! h.hasFDerivWithinAt.pow' n

/--
theorem `HasDerivWithinAt.pow'` / 定理 `HasDerivWithinAt.pow'`

English:
theorem HasDerivWithinAt.pow'
  given: (h : HasDerivWithinAt f f' s x) (n : Nat)
  proof: h.fun_pow' n

中文:
定理 HasDerivWithinAt.pow'
  条件: (h : HasDerivWithinAt f f' s x) (n : 自然数)
  证明: h.fun_pow' n

Depends on / 依赖: fun_pow, h.fun_pow
-/
theorem HasDerivWithinAt.pow' (h : HasDerivWithinAt f f' s x) (n : Nat) :
    HasDerivWithinAt (f ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x := h.fun_pow' n

/--
theorem `HasDerivAt.fun_pow'` / 定理 `HasDerivAt.fun_pow'`

English:
theorem HasDerivAt.fun_pow'
  given: (h : HasDerivAt f f' x) (n : Nat)
  proof: by
.hasDerivAt simpa using! h.hasFDerivAt.pow' n

中文:
定理 在点处可导.fun_pow'
  条件: (h : 在点处可导 f f' x) (n : 自然数)
  证明: by
.hasDerivAt simpa using! h.hasFDerivAt.pow' n

Depends on / 依赖: h.hasFDerivAt.pow, hasDerivAt, hasFDerivAt
-/
theorem HasDerivAt.fun_pow' (h : HasDerivAt f f' x) (n : Nat) :
    HasDerivAt (fun x => f x ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
.hasDerivAt simpa using! h.hasFDerivAt.pow' n

/--
theorem `HasDerivAt.pow'` / 定理 `HasDerivAt.pow'`

English:
theorem HasDerivAt.pow'
  given: (h : HasDerivAt f f' x) (n : Nat)
  proof: h.fun_pow' n

@[simp low]

中文:
定理 在点处可导.pow'
  条件: (h : 在点处可导 f f' x) (n : 自然数)
  证明: h.fun_pow' n

@[simp low]

Depends on / 依赖: fun_pow, h.fun_pow
-/
theorem HasDerivAt.pow' (h : HasDerivAt f f' x) (n : Nat) :
    HasDerivAt (f ^ n)
      (∑ i in Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := h.fun_pow' n

@[simp low]
/--
theorem `derivWithin_fun_pow'` / 定理 `derivWithin_fun_pow'`

English:
theorem derivWithin_fun_pow'
  given: (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow' n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp low]

中文:
定理 derivWithin_fun_pow'
  条件: (h : DifferentiableWithinAt 𝕜 f s x) (n : 自然数)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow' n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp low]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, h.hasDerivWithinAt.pow, hasDerivWithinAt
-/
theorem derivWithin_fun_pow' (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat) :
    derivWithin (fun x => f x ^ n) s x =
      ∑ i in Finset.range n, f x ^ (n.pred - i) * derivWithin f s x * f x ^ i := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow' n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp low]
/--
theorem `derivWithin_pow'` / 定理 `derivWithin_pow'`

English:
theorem derivWithin_pow'
  given: (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat)
  proof: derivWithin_fun_pow' h n

@[simp low]

中文:
定理 derivWithin_pow'
  条件: (h : DifferentiableWithinAt 𝕜 f s x) (n : 自然数)
  证明: derivWithin_fun_pow' h n

@[simp low]

Depends on / 依赖: derivWithin_fun_pow
-/
theorem derivWithin_pow' (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat) :
    derivWithin (f ^ n) s x =
      ∑ i in Finset.range n, f x ^ (n.pred - i) * derivWithin f s x * f x ^ i :=
  derivWithin_fun_pow' h n

@[simp low]
/--
theorem `deriv_fun_pow'` / 定理 `deriv_fun_pow'`

English:
theorem deriv_fun_pow'
  given: (h : DifferentiableAt 𝕜 f x) (n : Nat)
  proof: (h.hasDerivAt.pow' n).deriv

@[simp low]

中文:
定理 deriv_fun_pow'
  条件: (h : DifferentiableAt 𝕜 f x) (n : 自然数)
  证明: (h.hasDerivAt.pow' n).deriv

@[simp low]

Depends on / 依赖: h.hasDerivAt.pow, hasDerivAt
-/
theorem deriv_fun_pow' (h : DifferentiableAt 𝕜 f x) (n : Nat) :
    deriv (fun x => f x ^ n) x = ∑ i in Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i :=
  (h.hasDerivAt.pow' n).deriv

@[simp low]
/--
theorem `deriv_pow'` / 定理 `deriv_pow'`

English:
theorem deriv_pow'
  given: (h : DifferentiableAt 𝕜 f x) (n : Nat)
  proof: deriv_fun_pow' h n

中文:
定理 deriv_pow'
  条件: (h : DifferentiableAt 𝕜 f x) (n : 自然数)
  证明: deriv_fun_pow' h n

Depends on / 依赖: deriv_fun_pow
-/
theorem deriv_pow' (h : DifferentiableAt 𝕜 f x) (n : Nat) :
    deriv (f ^ n) x = ∑ i in Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i :=
  deriv_fun_pow' h n

end NormedRing

section NormedCommRing
variable [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸]
variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 -> 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

open scoped RightActions

/--
theorem `HasStrictDerivAt.fun_pow` / 定理 `HasStrictDerivAt.fun_pow`

English:
theorem HasStrictDerivAt.fun_pow
  given: (h : HasStrictDerivAt f f' x) (n : Nat)
  proof: by
.hasStrictDerivAt simpa using h.hasStrictFDerivAt.pow n

中文:
定理 HasStrictDerivAt.fun_pow
  条件: (h : HasStrictDerivAt f f' x) (n : 自然数)
  证明: by
.hasStrictDerivAt simpa using h.hasStrictFDerivAt.pow n

Depends on / 依赖: h.hasStrictFDerivAt.pow, hasStrictDerivAt, hasStrictFDerivAt
-/
theorem HasStrictDerivAt.fun_pow (h : HasStrictDerivAt f f' x) (n : Nat) :
    HasStrictDerivAt (fun x => f x ^ n) (n * f x ^ (n - 1) * f') x := by
.hasStrictDerivAt simpa using h.hasStrictFDerivAt.pow n

/--
theorem `HasStrictDerivAt.pow` / 定理 `HasStrictDerivAt.pow`

English:
theorem HasStrictDerivAt.pow
  given: (h : HasStrictDerivAt f f' x) (n : Nat)
  proof: h.fun_pow n

中文:
定理 HasStrictDerivAt.pow
  条件: (h : HasStrictDerivAt f f' x) (n : 自然数)
  证明: h.fun_pow n

Depends on / 依赖: fun_pow, h.fun_pow
-/
theorem HasStrictDerivAt.pow (h : HasStrictDerivAt f f' x) (n : Nat) :
    HasStrictDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x := h.fun_pow n

/--
theorem `HasDerivWithinAt.fun_pow` / 定理 `HasDerivWithinAt.fun_pow`

English:
theorem HasDerivWithinAt.fun_pow
  given: (h : HasDerivWithinAt f f' s x) (n : Nat)
  proof: by
.hasDerivWithinAt simpa using h.hasFDerivWithinAt.pow n

中文:
定理 HasDerivWithinAt.fun_pow
  条件: (h : HasDerivWithinAt f f' s x) (n : 自然数)
  证明: by
.hasDerivWithinAt simpa using h.hasFDerivWithinAt.pow n

Depends on / 依赖: h.hasFDerivWithinAt.pow, hasDerivWithinAt, hasFDerivWithinAt
-/
theorem HasDerivWithinAt.fun_pow (h : HasDerivWithinAt f f' s x) (n : Nat) :
    HasDerivWithinAt (fun x => f x ^ n) (n * f x ^ (n - 1) * f') s x := by
.hasDerivWithinAt simpa using h.hasFDerivWithinAt.pow n

/--
theorem `HasDerivWithinAt.pow` / 定理 `HasDerivWithinAt.pow`

English:
theorem HasDerivWithinAt.pow
  given: (h : HasDerivWithinAt f f' s x) (n : Nat)
  proof: h.fun_pow n

@[to_fun]

中文:
定理 HasDerivWithinAt.pow
  条件: (h : HasDerivWithinAt f f' s x) (n : 自然数)
  证明: h.fun_pow n

@[to_fun]

Depends on / 依赖: fun_pow, h.fun_pow
-/
theorem HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s x) (n : Nat) :
    HasDerivWithinAt (f ^ n) (n * f x ^ (n - 1) * f') s x := h.fun_pow n

@[to_fun]
/--
theorem `HasDerivAt.pow` / 定理 `HasDerivAt.pow`

English:
theorem HasDerivAt.pow
  given: (h : HasDerivAt f f' x) (n : Nat)
  proof: by
.hasDerivAt simpa using! h.hasFDerivAt.pow n

@[to_fun (attr := simp) derivWithin_fun_pow]

中文:
定理 在点处可导.pow
  条件: (h : 在点处可导 f f' x) (n : 自然数)
  证明: by
.hasDerivAt simpa using! h.hasFDerivAt.pow n

@[to_fun (attr := simp) derivWithin_fun_pow]

Depends on / 依赖: h.hasFDerivAt.pow, hasDerivAt, hasFDerivAt
-/
theorem HasDerivAt.pow (h : HasDerivAt f f' x) (n : Nat) :
    HasDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x := by
.hasDerivAt simpa using! h.hasFDerivAt.pow n

@[to_fun (attr := simp) derivWithin_fun_pow]
/--
theorem `derivWithin_pow` / 定理 `derivWithin_pow`

English:
theorem derivWithin_pow
  given: (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun (attr := simp) deriv_fun_pow]

中文:
定理 derivWithin_pow
  条件: (h : DifferentiableWithinAt 𝕜 f s x) (n : 自然数)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun (attr := simp) deriv_fun_pow]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, h.hasDerivWithinAt.pow, hasDerivWithinAt
-/
theorem derivWithin_pow (h : DifferentiableWithinAt 𝕜 f s x) (n : Nat) :
    derivWithin (f ^ n) s x = n * f x ^ (n - 1) * derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (h.hasDerivWithinAt.pow n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun (attr := simp) deriv_fun_pow]
/--
theorem `deriv_pow` / 定理 `deriv_pow`

English:
theorem deriv_pow
  given: (h : DifferentiableAt 𝕜 f x) (n : Nat)
  proof: (h.hasDerivAt.pow n).deriv

中文:
定理 deriv_pow
  条件: (h : DifferentiableAt 𝕜 f x) (n : 自然数)
  证明: (h.hasDerivAt.pow n).deriv

Depends on / 依赖: h.hasDerivAt.pow, hasDerivAt
-/
theorem deriv_pow (h : DifferentiableAt 𝕜 f x) (n : Nat) :
    deriv (f ^ n) x = n * f x ^ (n - 1) * deriv f x := (h.hasDerivAt.pow n).deriv

end NormedCommRing

section NontriviallyNormedField
variable [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} {c : 𝕜 -> 𝕜}

/--
theorem `hasStrictDerivAt_pow` / 定理 `hasStrictDerivAt_pow`

English:
theorem hasStrictDerivAt_pow
  given: (n : Nat) (x : 𝕜)
  proof: by
  simpa using! (hasStrictDerivAt_id x).pow n

中文:
定理 hasStrictDerivAt_pow
  条件: (n : 自然数) (x : 𝕜)
  证明: by
  simpa using! (hasStrictDerivAt_id x).pow n

Depends on / 依赖: hasStrictDerivAt_id
-/
theorem hasStrictDerivAt_pow (n : Nat) (x : 𝕜) :
    HasStrictDerivAt (fun x : 𝕜 => x ^ n) (n * x ^ (n - 1)) x := by
  simpa using! (hasStrictDerivAt_id x).pow n

/--
theorem `hasDerivWithinAt_pow` / 定理 `hasDerivWithinAt_pow`

English:
theorem hasDerivWithinAt_pow
  given: (n : Nat) (x : 𝕜)
  proof: by
  simpa using! (hasDerivWithinAt_id x s).pow n

中文:
定理 hasDerivWithinAt_pow
  条件: (n : 自然数) (x : 𝕜)
  证明: by
  simpa using! (hasDerivWithinAt_id x s).pow n

Depends on / 依赖: hasDerivWithinAt_id
-/
theorem hasDerivWithinAt_pow (n : Nat) (x : 𝕜) :
    HasDerivWithinAt (fun x : 𝕜 => x ^ n) (n * x ^ (n - 1)) s x := by
  simpa using! (hasDerivWithinAt_id x s).pow n

/--
theorem `hasDerivAt_pow` / 定理 `hasDerivAt_pow`

English:
theorem hasDerivAt_pow
  given: (n : Nat) (x : 𝕜)
  proof: by
  simpa using (hasStrictDerivAt_pow n x).hasDerivAt

中文:
定理 hasDerivAt_pow
  条件: (n : 自然数) (x : 𝕜)
  证明: by
  simpa using (hasStrictDerivAt_pow n x).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_pow
-/
theorem hasDerivAt_pow (n : Nat) (x : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x := by
  simpa using (hasStrictDerivAt_pow n x).hasDerivAt

/--
theorem `derivWithin_pow_field` / 定理 `derivWithin_pow_field`

English:
theorem derivWithin_pow_field
  given: (h : UniqueDiffWithinAt 𝕜 s x) (n : Nat)
  proof: by
  rw [derivWithin_fun_pow (differentiableWithinAt_fun_id) n]; rw [derivWithin_id' _ _ h]; rw [mul_one]

中文:
定理 derivWithin_pow_field
  条件: (h : UniqueDiffWithinAt 𝕜 s x) (n : 自然数)
  证明: by
  rw [derivWithin_fun_pow (differentiableWithinAt_fun_id) n]; rw [derivWithin_id' _ _ h]; rw [mul_one]

Depends on / 依赖: derivWithin_fun_pow, derivWithin_id, differentiableWithinAt_fun_id, mul_one
-/
theorem derivWithin_pow_field (h : UniqueDiffWithinAt 𝕜 s x) (n : Nat) :
    derivWithin (fun x => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) := by
  rw [derivWithin_fun_pow (differentiableWithinAt_fun_id) n]; rw [derivWithin_id' _ _ h]; rw [mul_one]

/--
theorem `deriv_pow_field` / 定理 `deriv_pow_field`

English:
theorem deriv_pow_field
  given: (n : Nat)
  statement: deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1)
  proof: by
  simp

中文:
定理 deriv_pow_field
  条件: (n : 自然数)
  结论: deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1)
  证明: by
  simp
-/
theorem deriv_pow_field (n : Nat) : deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1) := by
  simp

end NontriviallyNormedField
