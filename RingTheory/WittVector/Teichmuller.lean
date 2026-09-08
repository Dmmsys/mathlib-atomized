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

variable (p : ℕ) {R S : Type*} [hp : Fact p.Prime] [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

/-- The underlying function of the monoid hom `WittVector.teichmuller`.
The `0`-th coefficient of `teichmullerFun p r` is `r`, and all others are `0`.
-/
/-
**WittVector.teichmullerFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：teichmullerFun (r : R) : 𝕎 R
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function of the monoid hom `WittVector.teichmuller`.
The `0`-th coefficient of `teichmullerFun p r` is `r`, and all others are `0`.
-/
def teichmullerFun (r : R) : 𝕎 R :=
  ⟨fun n => if n = 0 then r else 0⟩

/-!
## `teichmuller` is a monoid homomorphism

On ghost components, it is clear that `teichmullerFun` is a monoid homomorphism.
But in general the ghost map is not injective.
We follow the same strategy as for proving that the ring operations on `𝕎 R`
satisfy the ring axioms.

1. We first prove it for rings `R` where `p` is invertible,
   because then the ghost map is in fact an isomorphism.
2. After that, we derive the result for `MvPolynomial R ℤ`,
3. and from that we can prove the result for arbitrary `R`.
-/


/-
**WittVector.ghostComponent_teichmullerFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## `teichmuller` is a monoid homomorphism

On ghost components, it is clear that `teichmullerFun` is a monoid homomorphism.
But in general the ghost map is not injective.
We follow the same strategy as for proving that the ring operations on `𝕎 R`
satisfy the ring axioms.

1. We first prove it for rings `R` where `p` is invertible,
   because then the ghost map is in fact an isomorphism.
2. After that, we derive the result for `MvPolynomial R ℤ`,
3. and from that we can prove the result for arbitrary `R`.
-/
private theorem ghostComponent_teichmullerFun (r : R) (n : ℕ) :
    ghostComponent n (teichmullerFun p r) = r ^ p ^ n := by
  rw [ghostComponent_apply, aeval_wittPolynomial, Finset.sum_eq_single 0, pow_zero, one_mul,
    tsub_zero]
  · rfl
  · intro i _ h0
    simp [teichmullerFun, h0, hp.1.ne_zero]
  · rw [Finset.mem_range]; intro h; exact (h (Nat.succ_pos n)).elim
/-
**WittVector.map_teichmullerFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem map_teichmullerFun (f : R →+* S) (r : R) :
    map f (teichmullerFun p r) = teichmullerFun p (f r) := by
  ext n; cases n
  · rfl
  · exact f.map_zero
/-
**WittVector.teichmuller_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem teichmuller_mul_aux₁ {R : Type*} (x y : MvPolynomial R ℚ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R ℚ)).1
  rw [map_mul]
  ext1 n
  simp only [Pi.mul_apply, ghostMap_apply, ghostComponent_teichmullerFun, mul_pow]
/-
**WittVector.teichmuller_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem teichmuller_mul_aux₂ {R : Type*} (x y : MvPolynomial R ℤ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  refine map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  simp only [teichmuller_mul_aux₁, map_teichmullerFun, map_mul]

/-- The Teichmüller lift of an element of `R` to `𝕎 R`.
The `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.
This is a monoid homomorphism. -/
/-
**WittVector.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：teichmuller : R ->* 𝕎 R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Teichmüller lift of an element of `R` to `𝕎 R`.
The `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.
This is a monoid homomorphism.
-/
def teichmuller : R →* 𝕎 R where
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
/-
**WittVector.teichmuller_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：teichmuller_coeff_zero (r : R) : (teichmuller p r).coeff 0 = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem teichmuller_coeff_zero (r : R) : (teichmuller p r).coeff 0 = r :=
  rfl

@[simp]
/-
**WittVector.teichmuller_coeff_pos** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：∀ (p : ℕ) {R : Type u_1} [hp : Fact (Nat.Prime p)] [inst : CommRing R] (r 
: R) (n : ℕ),   0 < n → ((WittVector.teichmuller p) r).coeff n = 0
参数：p : ℕ；Nat.Prime p；r : R；n : ℕ；(WittVector.teichmuller p) r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem teichmuller_coeff_pos (r : R) : ∀ (n : ℕ) (_ : 0 < n), (teichmuller p r).coeff n = 0
  | _ + 1, _ => rfl

@[simp]
/-
**WittVector.teichmuller_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：teichmuller_zero : teichmuller p (0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
-/
theorem teichmuller_zero : teichmuller p (0 : R) = 0 := by
  ext ⟨⟩ <;> · rw [zero_coeff]; rfl

/-- `teichmuller` is a natural transformation. -/
@[simp]
/-
**WittVector.map_teichmuller** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_teichmuller (f : R ->+* S) (r : R) : map f (teichmuller p r) = teichmu
ller p (f r)
参数：f : R ->+* S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.WittVector.Teichmuller.0.WittVector.map_teic
hmullerFun`：∀ (p : ℕ) {R : Type u_1} {S : Type u_2} [hp : Fact (Nat.Prime p)] [i
nst : CommRing R] [inst_1 : CommRing S]   (f : R →+* S) (r : R), (WittVe…

--- 原说明 ---
`teichmuller` is a natural transformation.
-/
theorem map_teichmuller (f : R →+* S) (r : R) : map f (teichmuller p r) = teichmuller p (f r) :=
  map_teichmullerFun _ _ _

/-- The `n`-th ghost component of `teichmuller p r` is `r ^ p ^ n`. -/
@[simp]
/-
**WittVector.ghostComponent_teichmuller** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostComponent_teichmuller (r : R) (n : Nat) : ghostComponent n (teichmull
er p r) = r ^ p ^ n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.WittVector.Teichmuller.0.WittVector.ghostCom
ponent_teichmullerFun`：∀ (p : ℕ) {R : Type u_1} [hp : Fact (Nat.Prime p)] [inst 
: CommRing R] (r : R) (n : ℕ),   (WittVector.ghostComponent n) (WittVector.teich
mul…

--- 原说明 ---
The `n`-th ghost component of `teichmuller p r` is `r ^ p ^ n`.
-/
theorem ghostComponent_teichmuller (r : R) (n : ℕ) :
    ghostComponent n (teichmuller p r) = r ^ p ^ n :=
  ghostComponent_teichmullerFun _ _ _

/-- The Teichmüller lift is set-theoretically right inverse to the constant coefficient map,
showing that the latter is surjective. -/
/-
**WittVector.constantCoeff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_surjective : Function.Surjective (constantCoeff : 𝕎 R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Teichmüller lift is set-theoretically right inverse to the constant coeffici
ent map,
showing that the latter is surjective.
-/
lemma constantCoeff_surjective : Function.Surjective (constantCoeff : 𝕎 R → R) :=
  fun r ↦ ⟨teichmuller p r, rfl⟩

end WittVector

