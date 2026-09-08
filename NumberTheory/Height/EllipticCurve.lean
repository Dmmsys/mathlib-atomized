/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# The naïve height and the approximate parallelogram law

This file defines the *naïve height* on an elliptic curve (over a field `K` with a theory of
heights, i.e., satisfying `[Height.AdmissibleAbsValues K]`).

The final goal of this file is to prove the *approximate parallelogram law* for (affine) points
on elliptic curves,
```
  |h(P+Q) + h(P-Q) - 2*(h(P) + h(Q))| ≤ C
```
where `h` is the naïve height, `P` and `Q` are affine points on a `WeierstrassCurve` and `C`
is some real constant depending only on the Weierstrass model.

### TODO

* Define the naïve height
* Add the further ingredients needed for the approximate parallelogram law
* Add the statement and proof of the approximate parallelogram law
-/

public section

namespace WeierstrassCurve

open Height MvPolynomial

variable {K : Type*} [Field K] [AdmissibleAbsValues K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- If `W` is a Weierstrass curve over `K`, then the map `F : ℙ² → ℙ²` given by `addSubMap W`
is a morphism.

This implies that `|logHeight (F x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `F` acts on the coordinate vector. -/
/-
**WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le** 是 Mathlib 
中的一个定理，位于命名空间 `WeierstrassCurve`。
形式化陈述：abs_logHeight_addSubMap_sub_two_mul_logHeight_le : exists C, forall x : Fi
n 3 -> K, |logHeight (fun i => (addSubMap W i).eval x) - 2 * logHeight x| <= C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Height.logHeight_eval_le'`：logHeight_eval_le' {N : Nat} {p : ι' -> MvPol
ynomial ι K} (hp : forall i, (p i).IsHomogeneous N) : exists C, forall (x : ι ->
 K), logHeight …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `WeierstrassCurve.isHomogeneous_addSubMap`：isHomogeneous_addSubMap (i : F
in 3) : (addSubMap W i).IsHomogeneous 2
· 使用定理 `Height.logHeight_eval_ge'`：logHeight_eval_ge' {M N : Nat} {q : ι × ι' ->
 MvPolynomial ι K} (hq : forall a, (q a).IsHomogeneous M) : exists C, forall (p 
: ι' -> MvPolyn…
· 使用引理 `MvPolynomial.IsHomogeneous.C_mul`：C_mul (hφ : φ.IsHomogeneous m) (r : R)
 : (C r * φ).IsHomogeneous m
· 使用引理 `WeierstrassCurve.isHomogeneous_addSubMapCoeff`：isHomogeneous_addSubMapCo
eff (ij : Fin 3 × Fin 3) : (addSubMapCoeff W ij).IsHomogeneous 2
· 使用引理 `WeierstrassCurve.addSubMapCoeff_condition`：addSubMapCoeff_condition (x :
 Fin 3 -> R) (i : Fin 3) : ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, 
j)).eval x * (addSubMap W j).ev…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c

--- 原说明 ---
If `W` is a Weierstrass curve over `K`, then the map `F : ℙ² → ℙ²` given by `add
SubMap W`
is a morphism.

This implies that `|logHeight (F x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `F` acts on the coordinate vector.
-/
theorem abs_logHeight_addSubMap_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → K,
      |logHeight (fun i ↦ (addSubMap W i).eval x) - 2 * logHeight x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' <| isHomogeneous_addSubMap W
  obtain ⟨C₂, h⟩ := logHeight_eval_ge' (N := 2)
    fun ij ↦ (isHomogeneous_addSubMapCoeff W ij).C_mul ↑W.Δ'⁻¹
  have hC₂ := fun x ↦ h _ <| addSubMapCoeff_condition W x
  refine ⟨max C₁ (-C₂), fun x ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩ <;> grind

end WeierstrassCurve

end

