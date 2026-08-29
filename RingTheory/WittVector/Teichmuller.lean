/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Basic

/-!
# Teichmüller lifts

This file defines `WittVector.teichmuller`, a monoid hom `R →* 𝕎 R`, which embeds `r : R` as the
`0`-th component of a Witt vector whose other coefficients are `0`.

## Main declarations

- `WittVector.teichmuller`: the Teichmuller map.
- `WittVector.map_teichmuller`: `WittVector.teichmuller` is a natural transformation.
- `WittVector.ghostComponent_teichmuller`:
  the `n`-th ghost component of `WittVector.teichmuller p r` is `r ^ p ^ n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

open MvPolynomial

variable (p : Nat) {R S : Type*} [hp : Fact p.Prime] [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

/--
Definition of `teichmullerFun` / `teichmullerFun` 的定义

English:
definition teichmullerFun
  signature: (r : R)
  body: ⟨fun n => if n = 0 then r else 0⟩

中文:
定义 teichmullerFun
  签名: (r : R)
  定义体: ⟨fun n => if n = 0 then r else 0⟩
-/
def teichmullerFun (r : R) : 𝕎 R :=
  ⟨fun n => if n = 0 then r else 0⟩



/--
theorem `ghostComponent_teichmullerFun` / 定理 `ghostComponent_teichmullerFun`

English:
theorem ghostComponent_teichmullerFun
  given: (r : R) (n : Nat)
  proof: by
  rw [ghostComponent_apply]; rw [aeval_wittPolynomial]; rw [Finset.sum_eq_single 0]; rw [pow_zero]; rw [one_mul]; rw [tsub_zero]
  · rfl
  · intro i _ h0
    simp [teichmullerFun, h0, hp.1.ne_zero]
  · rw [Finset.mem_range]; intro h; exact (h (Nat.succ_pos n)).elim

中文:
定理 ghostComponent_teichmullerFun
  条件: (r : R) (n : 自然数)
  证明: by
  rw [ghostComponent_apply]; rw [aeval_wittPolynomial]; rw [Finset.sum_eq_single 0]; rw [pow_zero]; rw [one_mul]; rw [tsub_zero]
  · rfl
  · intro i _ h0
    simp [teichmullerFun, h0, hp.1.ne_zero]
  · rw [Finset.mem_range]; intro h; exact (h (Nat.succ_pos n)).elim
-/
private theorem ghostComponent_teichmullerFun (r : R) (n : Nat) :
    ghostComponent n (teichmullerFun p r) = r ^ p ^ n := by
  rw [ghostComponent_apply]; rw [aeval_wittPolynomial]; rw [Finset.sum_eq_single 0]; rw [pow_zero]; rw [one_mul]; rw [tsub_zero]
  · rfl
  · intro i _ h0
    simp [teichmullerFun, h0, hp.1.ne_zero]
  · rw [Finset.mem_range]; intro h; exact (h (Nat.succ_pos n)).elim

/--
theorem `map_teichmullerFun` / 定理 `map_teichmullerFun`

English:
theorem map_teichmullerFun
  given: (f : R ->+* S) (r : R)
  proof: by
  ext n; cases n
  · rfl
  · exact f.map_zero

中文:
定理 map_teichmullerFun
  条件: (f : R ->+* S) (r : R)
  证明: by
  ext n; cases n
  · rfl
  · exact f.map_zero
-/
private theorem map_teichmullerFun (f : R ->+* S) (r : R) :
    map f (teichmullerFun p r) = teichmullerFun p (f r) := by
  ext n; cases n
  · rfl
  · exact f.map_zero

/--
theorem `teichmuller_mul_aux₁` / 定理 `teichmuller_mul_aux₁`

English:
theorem teichmuller_mul_aux₁
  given: {R : Type*} (x y : MvPolynomial R Rat)
  proof: by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R Rat)).1
  rw [map_mul]
  ext1 n
  simp only [Pi.mul_apply, ghostMap_apply, ghostComponent_teichmullerFun, mul_pow]

中文:
定理 teichmuller_mul_aux₁
  条件: {R : 类型} (x y : MvPolynomial R Rat)
  证明: by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R Rat)).1
  rw [map_mul]
  ext1 n
  simp only [Pi.mul_apply, ghostMap_apply, ghostComponent_teichmullerFun, mul_pow]
-/
private theorem teichmuller_mul_aux₁ {R : Type*} (x y : MvPolynomial R Rat) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R Rat)).1
  rw [map_mul]
  ext1 n
  simp only [Pi.mul_apply, ghostMap_apply, ghostComponent_teichmullerFun, mul_pow]

/--
theorem `teichmuller_mul_aux₂` / 定理 `teichmuller_mul_aux₂`

English:
theorem teichmuller_mul_aux₂
  given: {R : Type*} (x y : MvPolynomial R Int)
  proof: by
  refine map_injective (MvPolynomial.map (Int.castRingHom Rat))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  simp only [teichmuller_mul_aux₁, map_teichmullerFun, map_mul]

中文:
定理 teichmuller_mul_aux₂
  条件: {R : 类型} (x y : MvPolynomial R 整数)
  证明: by
  refine map_injective (MvPolynomial.map (Int.castRingHom Rat))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  simp only [teichmuller_mul_aux₁, map_teichmullerFun, map_mul]
-/
private theorem teichmuller_mul_aux₂ {R : Type*} (x y : MvPolynomial R Int) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  refine map_injective (MvPolynomial.map (Int.castRingHom Rat))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  simp only [teichmuller_mul_aux₁, map_teichmullerFun, map_mul]

/--
Definition of `teichmuller` / `teichmuller` 的定义

English:
definition teichmuller
  signature: : R ->* 𝕎 R where
  body: teichmullerFun p
  map_one' := by
    ext ⟨⟩
    · rw [one_coeff_zero]; rfl
    · rw [one_coeff_eq_of_pos _ _ _ (Nat.succ_pos _)]; rfl
  map_mul' := by
    intro x y
    rcases counit_surjective R x with ⟨x, rfl⟩
    rcases counit_surjective R y with ⟨y, rfl⟩
    simp only [← map_teichmullerFun, ← m

中文:
定义 teichmuller
  签名: : R ->* 𝕎 R where
  定义体: teichmullerFun p
  map_one' := by
    ext ⟨⟩
    · rw [one_coeff_zero]; rfl
    · rw [one_coeff_eq_of_pos _ _ _ (Nat.succ_pos _)]; rfl
  map_mul' := by
    intro x y
    rcases counit_surjective R x with ⟨x, rfl⟩
    rcases counit_surjective R y with ⟨y, rfl⟩
    simp only [← map_teichmullerFun, ← m

Depends on / 依赖: teichmullerFun
-/
def teichmuller : R ->* 𝕎 R where
  toFun := teichmullerFun p
  map_one' := by
    ext ⟨⟩
    · rw [one_coeff_zero]; rfl
    · rw [one_coeff_eq_of_pos _ _ _ (Nat.succ_pos _)]; rfl
  map_mul' := by
    intro x y
    rcases counit_surjective R x with ⟨x, rfl⟩
    rcases counit_surjective R y with ⟨y, rfl⟩
    simp only [← map_teichmullerFun, ← map_mul, teichmuller_mul_aux₂]

@[simp]
/--
theorem `teichmuller_coeff_zero` / 定理 `teichmuller_coeff_zero`

English:
theorem teichmuller_coeff_zero
  given: (r : R)
  statement: (teichmuller p r).coeff 0 = r
  proof: rfl

@[simp]

中文:
定理 teichmuller_coeff_zero
  条件: (r : R)
  结论: (teichmuller p r).coeff 0 = r
  证明: rfl

@[simp]
-/
theorem teichmuller_coeff_zero (r : R) : (teichmuller p r).coeff 0 = r :=
  rfl

@[simp]
/--
theorem `teichmuller_coeff_pos` / 定理 `teichmuller_coeff_pos`

English:
theorem teichmuller_coeff_pos
  given: (r : R)
  statement: forall (n : Nat) (_ : 0 < n), (teichmuller p r).coeff n = 0

中文:
定理 teichmuller_coeff_pos
  条件: (r : R)
  结论: 对任意 (n : 自然数) (_ : 0 < n), (teichmuller p r).coeff n = 0
-/
theorem teichmuller_coeff_pos (r : R) : forall (n : Nat) (_ : 0 < n), (teichmuller p r).coeff n = 0
  | _ + 1, _ => rfl

@[simp]
/--
theorem `teichmuller_zero` / 定理 `teichmuller_zero`

English:
theorem teichmuller_zero
  statement: teichmuller p (0 : R) = 0
  proof: by
  ext ⟨⟩ <;> · rw [zero_coeff]; rfl

中文:
定理 teichmuller_zero
  结论: teichmuller p (0 : R) = 0
  证明: by
  ext ⟨⟩ <;> · rw [zero_coeff]; rfl

Depends on / 依赖: zero_coeff
-/
theorem teichmuller_zero : teichmuller p (0 : R) = 0 := by
  ext ⟨⟩ <;> · rw [zero_coeff]; rfl

/-- `teichmuller` is a natural transformation. -/
@[simp]
/--
theorem `map_teichmuller` / 定理 `map_teichmuller`

English:
theorem map_teichmuller
  given: (f : R ->+* S) (r : R)
  statement: map f (teichmuller p r) = teichmuller p (f r)
  proof: map_teichmullerFun _ _ _

中文:
定理 map_teichmuller
  条件: (f : R ->+* S) (r : R)
  结论: map f (teichmuller p r) = teichmuller p (f r)
  证明: map_teichmullerFun _ _ _

Depends on / 依赖: map_teichmullerFun
-/
theorem map_teichmuller (f : R ->+* S) (r : R) : map f (teichmuller p r) = teichmuller p (f r) :=
  map_teichmullerFun _ _ _

/-- The `n`-th ghost component of `teichmuller p r` is `r ^ p ^ n`. -/
@[simp]
/--
theorem `ghostComponent_teichmuller` / 定理 `ghostComponent_teichmuller`

English:
theorem ghostComponent_teichmuller
  given: (r : R) (n : Nat)
  proof: ghostComponent_teichmullerFun _ _ _

中文:
定理 ghostComponent_teichmuller
  条件: (r : R) (n : 自然数)
  证明: ghostComponent_teichmullerFun _ _ _

Depends on / 依赖: ghostComponent_teichmullerFun
-/
theorem ghostComponent_teichmuller (r : R) (n : Nat) :
    ghostComponent n (teichmuller p r) = r ^ p ^ n :=
  ghostComponent_teichmullerFun _ _ _

/--
lemma `constantCoeff_surjective` / 引理 `constantCoeff_surjective`

English:
lemma constantCoeff_surjective
  statement: Function.Surjective (constantCoeff : 𝕎 R -> R)
  proof: fun r => ⟨teichmuller p r, rfl⟩

中文:
引理 constantCoeff_surjective
  结论: Function.Surjective (constantCoeff : 𝕎 R -> R)
  证明: fun r => ⟨teichmuller p r, rfl⟩

Depends on / 依赖: teichmuller
-/
lemma constantCoeff_surjective : Function.Surjective (constantCoeff : 𝕎 R -> R) :=
  fun r => ⟨teichmuller p r, rfl⟩

end WittVector
