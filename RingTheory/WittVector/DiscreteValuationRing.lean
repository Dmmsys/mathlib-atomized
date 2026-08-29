/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth, Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.MulCoeff
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.LinearCombination

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `WittVector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `WittVector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `WittVector.isDiscreteValuationRing`: `𝕎 k` is a discrete valuation ring if `k` is a perfect field

-/

@[expose] public section


noncomputable section

namespace WittVector

variable {p : Nat} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

/--
Definition of `succNthValUnits` / `succNthValUnits` 的定义

English:
definition succNthValUnits
  signature: (n : Nat) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) -> k)
  body: -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)

中文:
定义 succNthValUnits
  签名: (n : 自然数) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) -> k)
  定义体: -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)

Depends on / 依赖: A.coeff, nthRemainder, truncateFun
-/
def succNthValUnits (n : Nat) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) -> k) : k :=
  -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)

/--
Definition of `inverseCoeff` / `inverseCoeff` 的定义

English:
definition inverseCoeff
  signature: (a : Units k) (A : 𝕎 k)

中文:
定义 inverseCoeff
  签名: (a : Units k) (A : 𝕎 k)
-/
noncomputable def inverseCoeff (a : Units k) (A : 𝕎 k) : Nat -> k
  | 0 => ↑a⁻¹
  | n + 1 => succNthValUnits n a A fun i => inverseCoeff a A i.val

/--
Definition of `mkUnit` / `mkUnit` 的定义

English:
definition mkUnit
  signature: {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a)
  body: Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    induction n with
    | zero => simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
    | succ n => ?_
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin 

中文:
定义 mkUnit
  签名: {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a)
  定义体: Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    induction n with
    | zero => simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
    | succ n => ?_
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin 

Depends on / 依赖: A.coeff, H_coeff, Units.mkOfMulEqOne, Units.mul_inv, WittVector, WittVector.mk, WittVector.mul_coeff_zero, ha_inv, inverseCoeff, linear_combination, mkOfMulEqOne, mul_coeff_zero, mul_inv, nthRemainder, truncateFun
-/
def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    induction n with
    | zero => simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
    | succ n => ?_
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin (n + 1) => inverseCoeff a A i
    have H := Units.mul_inv (a ^ p ^ (n + 1))
    linear_combination (norm := skip) -H_coeff * H
    have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by norm_cast
    have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by norm_cast
    simp only [nthRemainder_spec, inverseCoeff, succNthValUnits, hA,
      one_coeff_eq_of_pos, Nat.succ_pos', ha_inv, ha, inv_pow]
    ring!)

@[simp]
/--
theorem `coe_mkUnit` / 定理 `coe_mkUnit`

English:
theorem coe_mkUnit
  given: {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a)
  statement: (mkUnit hA : 𝕎 k) = A
  proof: rfl

中文:
定理 coe_mkUnit
  条件: {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a)
  结论: (mkUnit hA : 𝕎 k) = A
  证明: rfl
-/
theorem coe_mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k) = A :=
  rfl

end CommRing

section Field

variable {k : Type*} [Field k] [CharP k p]

/--
theorem `isUnit_of_coeff_zero_ne_zero` / 定理 `isUnit_of_coeff_zero_ne_zero`

English:
theorem isUnit_of_coeff_zero_ne_zero
  given: (x : 𝕎 k) (hx : x.coeff 0 != 0)
  statement: IsUnit x
  proof: by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mkUnit hy).isUnit

中文:
定理 isUnit_of_coeff_zero_ne_zero
  条件: (x : 𝕎 k) (hx : x.coeff 0 != 0)
  结论: IsUnit x
  证明: by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mkUnit hy).isUnit

Depends on / 依赖: Units.mk0, isUnit, mkUnit, x.coeff
-/
theorem isUnit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 != 0) : IsUnit x := by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mkUnit hy).isUnit

variable (p)

/--
theorem `irreducible` / 定理 `irreducible`

English:
theorem irreducible
  statement: Irreducible (p : 𝕎 k)
  proof: by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constantCoeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constantCoeff : WittVector p k ->+* _).isUnit_map hp
  refine ⟨hp, fun a b hab => ?_⟩
  obtain ⟨ha0, hb0⟩ : a != 0 ∧ b != 0 := by
    rw [← mul_ne_zero_iff]; intro h; 

中文:
定理 irreducible
  结论: Irreducible (p : 𝕎 k)
  证明: by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constantCoeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constantCoeff : WittVector p k ->+* _).isUnit_map hp
  refine ⟨hp, fun a b hab => ?_⟩
  obtain ⟨ha0, hb0⟩ : a != 0 ∧ b != 0 := by
    rw [← mul_ne_zero_iff]; intro h; 

Depends on / 依赖: IsUnit, Or.inl, WittVector, coeff_p_zero, constantCoeff, constantCoeff_apply, isUnit_map, isUnit_of_coeff_zero_ne_zero, mul_ne_zero_iff, not_isUnit_zero, p_nonzero, verschiebung_nonzero
-/
theorem irreducible : Irreducible (p : 𝕎 k) := by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constantCoeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constantCoeff : WittVector p k ->+* _).isUnit_map hp
  refine ⟨hp, fun a b hab => ?_⟩
  obtain ⟨ha0, hb0⟩ : a != 0 ∧ b != 0 := by
    rw [← mul_ne_zero_iff]; intro h; rw [h] at hab; exact p_nonzero p k hab
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0
  cases m; · exact Or.inl (isUnit_of_coeff_zero_ne_zero a ha)
  rcases n with - | n; · exact Or.inr (isUnit_of_coeff_zero_ne_zero b hb)
  rw [iterate_verschiebung_mul] at hab
  apply_fun fun x => coeff x 1 at hab
  simp only [coeff_p_one, Nat.add_succ, add_comm _ n, Function.iterate_succ', Function.comp_apply,
    verschiebung_coeff_add_one, verschiebung_coeff_zero] at hab
  exact (one_ne_zero hab).elim

end Field

section PerfectRing

variable {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

/--
theorem `exists_eq_pow_p_mul` / 定理 `exists_eq_pow_p_mul`

English:
theorem exists_eq_pow_p_mul
  given: (a : 𝕎 k) (ha : a != 0)
  proof: by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc
  have := congr_fun (WittVector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [Function.comp_apply] at t

中文:
定理 exists_eq_pow_p_mul
  条件: (a : 𝕎 k) (ha : a != 0)
  证明: by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc
  have := congr_fun (WittVector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [Function.comp_apply] at t

Depends on / 依赖: Function, Function.comp_apply, WittVector, WittVector.iterate_frobenius_coeff, WittVector.verschiebung_frobenius_comm.comp_iterate, WittVector.verschiebung_nonzero, comp_apply, comp_iterate, congr_fun, contrapose, convert, frobenius_bijective, hp.out.ne_zero, iterate, iterate_frobenius_coeff, mul_comm, mul_left_iterate, ne_zero, pow_ne_zero, simp_rw
-/
theorem exists_eq_pow_p_mul (a : 𝕎 k) (ha : a != 0) :
    exists (m : Nat) (b : 𝕎 k), b.coeff 0 != 0 ∧ a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc
  have := congr_fun (WittVector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [Function.comp_apply] at this
  rw [← this] at hcm
  refine ⟨m, b, ?_, ?_⟩
  · contrapose hc
    simp [hc, zero_pow <| pow_ne_zero _ hp.out.ne_zero]
  · simp_rw [← mul_left_iterate (p : 𝕎 k) m]
    convert! hcm using 2
    ext1 x
    rw [mul_comm]; rw [← WittVector.verschiebung_frobenius x]; rfl

end PerfectRing

section PerfectField

variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p]

/--
theorem `exists_eq_pow_p_mul'` / 定理 `exists_eq_pow_p_mul'`

English:
theorem exists_eq_pow_p_mul'
  given: (a : 𝕎 k) (ha : a != 0)
  proof: by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mkUnit hb₀, h₂⟩

中文:
定理 exists_eq_pow_p_mul'
  条件: (a : 𝕎 k) (ha : a != 0)
  证明: by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mkUnit hb₀, h₂⟩

Depends on / 依赖: Units.mk0, b.coeff, exists_eq_pow_p_mul, mkUnit
-/
theorem exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a != 0) :
    exists (m : Nat) (b : Units (𝕎 k)), a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mkUnit hb₀, h₂⟩

/--
Instance `isDiscreteValuationRing` / 实例 `isDiscreteValuationRing`

English:
instance isDiscreteValuationRing
  signature: : IsDiscreteValuationRing (𝕎 k)
  body: IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (by
    refine ⟨p, irreducible p, fun {x} hx => ?_⟩
    obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
    exact ⟨n, b, hb.symm⟩)

中文:
实例 isDiscreteValuationRing
  签名: : IsDiscreteValuationRing (𝕎 k)
  定义体: IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (by
    refine ⟨p, irreducible p, fun {x} hx => ?_⟩
    obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
    exact ⟨n, b, hb.symm⟩)

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization, exists_eq_pow_p_mul, hb.symm, irreducible, ofHasUnitMulPowIrreducibleFactorization
-/
instance isDiscreteValuationRing : IsDiscreteValuationRing (𝕎 k) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (by
    refine ⟨p, irreducible p, fun {x} hx => ?_⟩
    obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
    exact ⟨n, b, hb.symm⟩)

end PerfectField

end WittVector
