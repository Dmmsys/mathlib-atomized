/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.Identities

/-!

# Witt vectors over a domain

This file builds to the proof `WittVector.instIsDomain`,
an instance that says if `R` is an integral domain, then so is `𝕎 R`.
It depends on the API around iterated applications
of `WittVector.verschiebung` and `WittVector.frobenius`
found in `Identities.lean`.

The [proof sketch](https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723)
goes as follows:
any nonzero $x$ is an iterated application of $V$
to some vector $w_x$ whose 0th component is nonzero (`WittVector.verschiebung_nonzero`).
Known identities (`WittVector.iterate_verschiebung_mul`) allow us to transform
the product of two such $x$ and $y$
to the form $V^{m+n}\left(F^n(w_x) \cdot F^m(w_y)\right)$,
the 0th component of which must be nonzero.

## Main declarations

* `WittVector.iterate_verschiebung_mul_coeff` : an identity from [Haze09]
* `WittVector.instIsDomain`

-/

@[expose] public section


noncomputable section

namespace WittVector

open Function

variable {p : Nat} {R : Type*}

local notation "𝕎" => WittVector p -- type as `\bbW`

/-!
## The `shift` operator
-/


/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: (x : 𝕎 R) (n : Nat)
  body: @mk' p R fun i => x.coeff (n + i)

中文:
定义 shift
  签名: (x : 𝕎 R) (n : 自然数)
  定义体: @mk' p R fun i => x.coeff (n + i)

Depends on / 依赖: x.coeff
-/
def shift (x : 𝕎 R) (n : Nat) : 𝕎 R :=
  @mk' p R fun i => x.coeff (n + i)

/--
theorem `shift_coeff` / 定理 `shift_coeff`

English:
theorem shift_coeff
  given: (x : 𝕎 R) (n k : Nat)
  statement: (x.shift n).coeff k = x.coeff (n + k)
  proof: rfl

中文:
定理 shift_coeff
  条件: (x : 𝕎 R) (n k : 自然数)
  结论: (x.shift n).coeff k = x.coeff (n + k)
  证明: rfl
-/
theorem shift_coeff (x : 𝕎 R) (n k : Nat) : (x.shift n).coeff k = x.coeff (n + k) :=
  rfl

variable [hp : Fact p.Prime] [CommRing R]

/--
theorem `verschiebung_shift` / 定理 `verschiebung_shift`

English:
theorem verschiebung_shift
  given: (x : 𝕎 R) (k : Nat) (h : forall i < k + 1, x.coeff i = 0)
  proof: by
  ext ⟨j⟩
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_self
  · simp only [verschiebung_coeff_succ, shift]
    congr 1
    rw [Nat.add_succ]; rw [add_comm]; rw [Nat.add_succ]; rw [add_comm]

中文:
定理 verschiebung_shift
  条件: (x : 𝕎 R) (k : 自然数) (h : 对任意 i < k + 1, x.coeff i = 0)
  证明: by
  ext ⟨j⟩
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_self
  · simp only [verschiebung_coeff_succ, shift]
    congr 1
    rw [Nat.add_succ]; rw [add_comm]; rw [Nat.add_succ]; rw [add_comm]

Depends on / 依赖: Nat.add_succ, Nat.lt_succ_self, add_comm, add_succ, lt_succ_self, shift_coeff, verschiebung_coeff_succ, verschiebung_coeff_zero
-/
theorem verschiebung_shift (x : 𝕎 R) (k : Nat) (h : forall i < k + 1, x.coeff i = 0) :
    verschiebung (x.shift k.succ) = x.shift k := by
  ext ⟨j⟩
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_self
  · simp only [verschiebung_coeff_succ, shift]
    congr 1
    rw [Nat.add_succ]; rw [add_comm]; rw [Nat.add_succ]; rw [add_comm]

/--
theorem `eq_iterate_verschiebung` / 定理 `eq_iterate_verschiebung`

English:
theorem eq_iterate_verschiebung
  given: {x : 𝕎 R} {n : Nat} (h : forall i < n, x.coeff i = 0)
  proof: by
  induction n with
  | zero => cases x; simp [shift]
  | succ k ih =>
    dsimp; rw [verschiebung_shift]
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
    · exact h

中文:
定理 eq_iterate_verschiebung
  条件: {x : 𝕎 R} {n : 自然数} (h : 对任意 i < n, x.coeff i = 0)
  证明: by
  induction n with
  | zero => cases x; simp [shift]
  | succ k ih =>
    dsimp; rw [verschiebung_shift]
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
    · exact h

Depends on / 依赖: Nat.lt_succ_self, hi.trans, lt_succ_self, verschiebung_shift
-/
theorem eq_iterate_verschiebung {x : 𝕎 R} {n : Nat} (h : forall i < n, x.coeff i = 0) :
    x = verschiebung^[n] (x.shift n) := by
  induction n with
  | zero => cases x; simp [shift]
  | succ k ih =>
    dsimp; rw [verschiebung_shift]
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
    · exact h

/--
theorem `verschiebung_nonzero` / 定理 `verschiebung_nonzero`

English:
theorem verschiebung_nonzero
  given: {x : 𝕎 R} (hx : x != 0)
  proof: by
  classical
  have hex : exists k : Nat, x.coeff k != 0 := by
    by_contra! hall
    apply hx
    ext i
    simp only [hall, zero_coeff]
  let n := Nat.find hex
  use n, x.shift n
  refine ⟨Nat.find_spec hex, eq_iterate_verschiebung fun i hi => not_not.mp ?_⟩
  exact Nat.find_min hex hi

中文:
定理 verschiebung_nonzero
  条件: {x : 𝕎 R} (hx : x != 0)
  证明: by
  classical
  have hex : exists k : Nat, x.coeff k != 0 := by
    by_contra! hall
    apply hx
    ext i
    simp only [hall, zero_coeff]
  let n := Nat.find hex
  use n, x.shift n
  refine ⟨Nat.find_spec hex, eq_iterate_verschiebung fun i hi => not_not.mp ?_⟩
  exact Nat.find_min hex hi

Depends on / 依赖: Nat.find, Nat.find_min, Nat.find_spec, classical, eq_iterate_verschiebung, find_min, find_spec, not_not, not_not.mp, x.coeff, x.shift, zero_coeff
-/
theorem verschiebung_nonzero {x : 𝕎 R} (hx : x != 0) :
    exists n : Nat, exists x' : 𝕎 R, x'.coeff 0 != 0 ∧ x = verschiebung^[n] x' := by
  classical
  have hex : exists k : Nat, x.coeff k != 0 := by
    by_contra! hall
    apply hx
    ext i
    simp only [hall, zero_coeff]
  let n := Nat.find hex
  use n, x.shift n
  refine ⟨Nat.find_spec hex, eq_iterate_verschiebung fun i hi => not_not.mp ?_⟩
  exact Nat.find_min hex hi



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharP
  signature: R p] [NoZeroDivisors R] : NoZeroDivisors (𝕎 R)
  body: ⟨fun {x y} => by
    contrapose!
    rintro ⟨ha, hb⟩
    rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, rfl⟩
    rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, rfl⟩
    refine ne_of_apply_ne (fun x => x.coeff (na + nb)) ?_
    rw [iterate_verschiebung_mul_coeff]; rw [zero_coeff]
    exact mu

中文:
实例 [CharP
  签名: R p] [NoZeroDivisors R] : NoZeroDivisors (𝕎 R)
  定义体: ⟨fun {x y} => by
    contrapose!
    rintro ⟨ha, hb⟩
    rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, rfl⟩
    rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, rfl⟩
    refine ne_of_apply_ne (fun x => x.coeff (na + nb)) ?_
    rw [iterate_verschiebung_mul_coeff]; rw [zero_coeff]
    exact mu

Depends on / 依赖: contrapose, iterate_verschiebung_mul_coeff, mul_ne_zero, ne_of_apply_ne, pow_ne_zero, verschiebung_nonzero, x.coeff, zero_coeff
-/
instance [CharP R p] [NoZeroDivisors R] : NoZeroDivisors (𝕎 R) :=
  ⟨fun {x y} => by
    contrapose!
    rintro ⟨ha, hb⟩
    rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, rfl⟩
    rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, rfl⟩
    refine ne_of_apply_ne (fun x => x.coeff (na + nb)) ?_
    rw [iterate_verschiebung_mul_coeff]; rw [zero_coeff]
    exact mul_ne_zero (pow_ne_zero _ hwa0) (pow_ne_zero _ hwb0)⟩

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: [CharP R p] [IsDomain R]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 instIsDomain
  签名: [CharP R p] [IsDomain R]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance instIsDomain [CharP R p] [IsDomain R] : IsDomain (𝕎 R) :=
  NoZeroDivisors.to_isDomain _

end WittVector
