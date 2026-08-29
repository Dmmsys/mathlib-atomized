/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.LinearAlgebra.SModEq.Pow
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Perfection

/-! # Teichmüller map

Let `R` be an `I`-adically complete ring, and `p` be a prime number with `p ∈ I`.

Then there is a canonical map `Perfection (R ⧸ I) p →*₀ R` that we shall call
`Perfection.teichmuller`, such that it composed with the quotient map `R →+* R ⧸ I` is the
"0-th coefficient" map `Perfection (R ⧸ I) p →+* R ⧸ I`.

-/

@[expose] public section

variable {p : Nat} [Fact p.Prime] {R : Type*} [CommRing R] {I : Ideal R} [CharP (R ⧸ I) p]

namespace Perfection

/--
Definition of `teichmullerAux` / `teichmullerAux` 的定义

English:
definition teichmullerAux
  signature: (x : Perfection (R ⧸ I) p)

中文:
定义 teichmullerAux
  签名: (x : Perfection (R ⧸ I) p)
-/
noncomputable def teichmullerAux (x : Perfection (R ⧸ I) p) : Nat -> R
  | 0 => 1
  | n + 1 => (coeff _ p n x).out ^ p ^ n

/--
theorem `teichmullerAux_sModEq` / 定理 `teichmullerAux_sModEq`

English:
theorem teichmullerAux_sModEq
  given: (x : Perfection (R ⧸ I) p) (m : Nat)
  proof: by
  obtain _ | m := m
  · simp
  symm
  rw [teichmullerAux]; rw [pow_succ' p]; rw [pow_mul]
exact .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := m) by
    simp [SModEq.idealQuotientMk, coeff_pow_p']

中文:
定理 teichmullerAux_sModEq
  条件: (x : Perfection (R ⧸ I) p) (m : 自然数)
  证明: by
  obtain _ | m := m
  · simp
  symm
  rw [teichmullerAux]; rw [pow_succ' p]; rw [pow_mul]
exact .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := m) by
    simp [SModEq.idealQuotientMk, coeff_pow_p']

Depends on / 依赖: I.natCast_mem_of_charP_quotient, SModEq, SModEq.idealQuotientMk, coeff_pow_p, idealQuotientMk, natCast_mem_of_charP_quotient, pow_mul, pow_pow_add_one, pow_succ, teichmullerAux
-/
theorem teichmullerAux_sModEq (x : Perfection (R ⧸ I) p) (m : Nat) :
    teichmullerAux x m ≡ teichmullerAux x (m + 1) [SMOD I ^ m] := by
  obtain _ | m := m
  · simp
  symm
  rw [teichmullerAux]; rw [pow_succ' p]; rw [pow_mul]
exact .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := m) by
    simp [SModEq.idealQuotientMk, coeff_pow_p']

/--
Definition of `teichmullerCauchy` / `teichmullerCauchy` 的定义

English:
definition teichmullerCauchy
  signature: (x : Perfection (R ⧸ I) p)
  body: .mk _ _ (teichmullerAux x) by simpa using teichmullerAux_sModEq x

中文:
定义 teichmullerCauchy
  签名: (x : Perfection (R ⧸ I) p)
  定义体: .mk _ _ (teichmullerAux x) by simpa using teichmullerAux_sModEq x

Depends on / 依赖: teichmullerAux, teichmullerAux_sModEq
-/
noncomputable def teichmullerCauchy (x : Perfection (R ⧸ I) p) :
    AdicCompletion.AdicCauchySequence I R :=
.mk _ _ (teichmullerAux x) by simpa using teichmullerAux_sModEq x

section IsPrecomplete
variable [IsPrecomplete I R]

/--
theorem `exists_teichmullerFun` / 定理 `exists_teichmullerFun`

English:
theorem exists_teichmullerFun
  given: (x : Perfection (R ⧸ I) p)
  proof: IsPrecomplete.prec' _ (teichmullerCauchy x).2

中文:
定理 存在_teichmullerFun
  条件: (x : Perfection (R ⧸ I) p)
  证明: IsPrecomplete.prec' _ (teichmullerCauchy x).2

Depends on / 依赖: IsPrecomplete, IsPrecomplete.prec, teichmullerCauchy
-/
theorem exists_teichmullerFun (x : Perfection (R ⧸ I) p) :
    exists y : R, forall n, teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : Ideal R)] :=
  IsPrecomplete.prec' _ (teichmullerCauchy x).2

/--
Definition of `teichmullerFun` / `teichmullerFun` 的定义

English:
definition teichmullerFun
  signature: (x : Perfection (R ⧸ I) p)
  body: (exists_teichmullerFun x).choose

中文:
定义 teichmullerFun
  签名: (x : Perfection (R ⧸ I) p)
  定义体: (exists_teichmullerFun x).choose

Depends on / 依赖: exists_teichmullerFun
-/
noncomputable def teichmullerFun (x : Perfection (R ⧸ I) p) : R :=
  (exists_teichmullerFun x).choose

/--
theorem `teichmullerFun_sModEq` / 定理 `teichmullerFun_sModEq`

English:
theorem teichmullerFun_sModEq
  statement: {x : Perfection (R ⧸ I) p} {y : R} {n : Nat}
  proof: by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul]; rw [Ideal.mul_top] at this
exact this.symm.trans .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := n) by
    simp [SModEq.idealQuotientMk, h]

中文:
定理 teichmullerFun_sModEq
  结论: {x : Perfection (R ⧸ I) p} {y : R} {n : 自然数}
  证明: by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul]; rw [Ideal.mul_top] at this
exact this.symm.trans .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := n) by
    simp [SModEq.idealQuotientMk, h]

Depends on / 依赖: I.natCast_mem_of_charP_quotient, Ideal.mul_top, SModEq, SModEq.idealQuotientMk, choose_spec, exists_teichmullerFun, idealQuotientMk, mul_top, natCast_mem_of_charP_quotient, pow_pow_add_one, smul_eq_mul, this.symm.trans
-/
theorem teichmullerFun_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : Nat}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmullerFun x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] := by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul]; rw [Ideal.mul_top] at this
exact this.symm.trans .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := n) by
    simp [SModEq.idealQuotientMk, h]

end IsPrecomplete

variable [IsAdicComplete I R]

/--
theorem `teichmullerFun_spec'` / 定理 `teichmullerFun_spec'`

English:
theorem teichmullerFun_spec'
  statement: {x : Perfection (R ⧸ I) p} {y : R}
  proof: by
  obtain ⟨N, h⟩ := h
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n => ?_
  rw [smul_eq_mul]; rw [Ideal.mul_top]
  obtain hn | hn := le_total n N
  · obtain ⟨z, hz₁, hz₂⟩ := h N le_rfl
exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono Ideal.pow_le_pow_right (by omega)
  · obtain ⟨z, hz₁

中文:
定理 teichmullerFun_spec'
  结论: {x : Perfection (R ⧸ I) p} {y : R}
  证明: by
  obtain ⟨N, h⟩ := h
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n => ?_
  rw [smul_eq_mul]; rw [Ideal.mul_top]
  obtain hn | hn := le_total n N
  · obtain ⟨z, hz₁, hz₂⟩ := h N le_rfl
exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono Ideal.pow_le_pow_right (by omega)
  · obtain ⟨z, hz₁

Depends on / 依赖: Ideal.mul_top, Ideal.pow_le_pow_right, IsHausdorff, IsHausdorff.eq_iff_smodEq, eq_iff_smodEq, le_rfl, le_total, mul_top, pow_le_pow_right, smul_eq_mul, teichmullerFun_sModEq
-/
theorem teichmullerFun_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y := by
  obtain ⟨N, h⟩ := h
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n => ?_
  rw [smul_eq_mul]; rw [Ideal.mul_top]
  obtain hn | hn := le_total n N
  · obtain ⟨z, hz₁, hz₂⟩ := h N le_rfl
exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono Ideal.pow_le_pow_right (by omega)
  · obtain ⟨z, hz₁, hz₂⟩ := h n hn
exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono Ideal.pow_le_pow_right (by omega)

/--
theorem `teichmullerFun_spec` / 定理 `teichmullerFun_spec`

English:
theorem teichmullerFun_spec
  statement: {x : Perfection (R ⧸ I) p} {y : R}
  proof: teichmullerFun_spec' ⟨0, fun n _ => h n⟩

中文:
定理 teichmullerFun_spec
  结论: {x : Perfection (R ⧸ I) p} {y : R}
  证明: teichmullerFun_spec' ⟨0, fun n _ => h n⟩

Depends on / 依赖: teichmullerFun_spec
-/
theorem teichmullerFun_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y :=
  teichmullerFun_spec' ⟨0, fun n _ => h n⟩

variable (p I) in
/--
Definition of `teichmuller` / `teichmuller` 的定义

English:
definition teichmuller
  signature: : Perfection (R ⧸ I) p ->* R where
  body: teichmullerFun
  map_one' := teichmullerFun_spec fun _ => ⟨1, by simp⟩
  map_mul' x y := by
    refine teichmullerFun_spec fun n => ?_
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <

中文:
定义 teichmuller
  签名: : Perfection (R ⧸ I) p ->* R where
  定义体: teichmullerFun
  map_one' := teichmullerFun_spec fun _ => ⟨1, by simp⟩
  map_mul' x y := by
    refine teichmullerFun_spec fun n => ?_
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <

Depends on / 依赖: teichmullerFun
-/
noncomputable def teichmuller : Perfection (R ⧸ I) p ->* R where
  toFun := teichmullerFun
  map_one' := teichmullerFun_spec fun _ => ⟨1, by simp⟩
  map_mul' x y := by
    refine teichmullerFun_spec fun n => ?_
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <;> simp

/--
theorem `teichmuller_sModEq` / 定理 `teichmuller_sModEq`

English:
theorem teichmuller_sModEq
  statement: {x : Perfection (R ⧸ I) p} {y : R} {n : Nat}
  proof: teichmullerFun_sModEq h

中文:
定理 teichmuller_sModEq
  结论: {x : Perfection (R ⧸ I) p} {y : R} {n : 自然数}
  证明: teichmullerFun_sModEq h

Depends on / 依赖: teichmullerFun_sModEq
-/
theorem teichmuller_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : Nat}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h

/--
theorem `teichmuller_spec'` / 定理 `teichmuller_spec'`

English:
theorem teichmuller_spec'
  statement: {x : Perfection (R ⧸ I) p} {y : R}
  proof: teichmullerFun_spec' h

中文:
定理 teichmuller_spec'
  结论: {x : Perfection (R ⧸ I) p} {y : R}
  证明: teichmullerFun_spec' h

Depends on / 依赖: teichmullerFun_spec
-/
theorem teichmuller_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec' h

/--
theorem `teichmuller_spec` / 定理 `teichmuller_spec`

English:
theorem teichmuller_spec
  statement: {x : Perfection (R ⧸ I) p} {y : R}
  proof: teichmullerFun_spec h

中文:
定理 teichmuller_spec
  结论: {x : Perfection (R ⧸ I) p} {y : R}
  证明: teichmullerFun_spec h

Depends on / 依赖: teichmullerFun_spec
-/
theorem teichmuller_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec h

/--
theorem `teichmuller_zero` / 定理 `teichmuller_zero`

English:
theorem teichmuller_zero
  statement: teichmuller p I 0 = 0
  proof: have : p != 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec fun n => ⟨0, by simp [zero_pow (pow_ne_zero n this)]⟩

中文:
定理 teichmuller_zero
  结论: teichmuller p I 0 = 0
  证明: have : p != 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec fun n => ⟨0, by simp [zero_pow (pow_ne_zero n this)]⟩

Depends on / 依赖: Fact.out, Nat.Prime.ne_zero, ne_zero, pow_ne_zero, teichmuller_spec, zero_pow
-/
theorem teichmuller_zero : teichmuller p I 0 = 0 :=
  have : p != 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec fun n => ⟨0, by simp [zero_pow (pow_ne_zero n this)]⟩

variable (p I) in
/--
Definition of `teichmuller₀` / `teichmuller₀` 的定义

English:
definition teichmuller₀
  signature: : Perfection (R ⧸ I) p ->*₀ R where
  body: teichmuller p I
  map_zero' := teichmuller_zero

中文:
定义 teichmuller₀
  签名: : Perfection (R ⧸ I) p ->*₀ R where
  定义体: teichmuller p I
  map_zero' := teichmuller_zero

Depends on / 依赖: teichmuller
-/
noncomputable def teichmuller₀ : Perfection (R ⧸ I) p ->*₀ R where
  __ := teichmuller p I
  map_zero' := teichmuller_zero

/--
lemma `teichmuller_eq_teichmuller₀_toMonoidHom` / 引理 `teichmuller_eq_teichmuller₀_toMonoidHom`

English:
lemma teichmuller_eq_teichmuller₀_toMonoidHom
  proof: rfl

中文:
引理 teichmuller_eq_teichmuller₀_toMonoidHom
  证明: rfl
-/
@[simp] lemma teichmuller_eq_teichmuller₀_toMonoidHom :
    teichmuller p I = (teichmuller₀ p I).toMonoidHom := rfl

/--
lemma `coe_teichmuller_eq_teichmuller₀` / 引理 `coe_teichmuller_eq_teichmuller₀`

English:
lemma coe_teichmuller_eq_teichmuller₀
  proof: rfl

中文:
引理 coe_teichmuller_eq_teichmuller₀
  证明: rfl
-/
@[simp] lemma coe_teichmuller_eq_teichmuller₀ :
    ⇑(teichmuller p I) = teichmuller₀ p I := rfl

/--
lemma `teichmullerFun_eq_teichmuller₀` / 引理 `teichmullerFun_eq_teichmuller₀`

English:
lemma teichmullerFun_eq_teichmuller₀
  proof: rfl

中文:
引理 teichmullerFun_eq_teichmuller₀
  证明: rfl
-/
@[simp] lemma teichmullerFun_eq_teichmuller₀ :
    teichmullerFun = teichmuller₀ p I := rfl

/--
theorem `teichmuller₀_sModEq` / 定理 `teichmuller₀_sModEq`

English:
theorem teichmuller₀_sModEq
  statement: {x : Perfection (R ⧸ I) p} {y : R} {n : Nat}
  proof: teichmullerFun_sModEq h

中文:
定理 teichmuller₀_sModEq
  结论: {x : Perfection (R ⧸ I) p} {y : R} {n : 自然数}
  证明: teichmullerFun_sModEq h

Depends on / 依赖: teichmullerFun_sModEq
-/
theorem teichmuller₀_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : Nat}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller₀ p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h

/--
theorem `teichmuller₀_spec'` / 定理 `teichmuller₀_spec'`

English:
theorem teichmuller₀_spec'
  statement: {x : Perfection (R ⧸ I) p} {y : R}
  proof: teichmullerFun_spec' h

中文:
定理 teichmuller₀_spec'
  结论: {x : Perfection (R ⧸ I) p} {y : R}
  证明: teichmullerFun_spec' h

Depends on / 依赖: teichmullerFun_spec
-/
theorem teichmuller₀_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller₀ p I x = y :=
  teichmullerFun_spec' h

/--
theorem `teichmuller₀_spec` / 定理 `teichmuller₀_spec`

English:
theorem teichmuller₀_spec
  statement: {x : Perfection (R ⧸ I) p} {y : R}
  proof: teichmullerFun_spec h

中文:
定理 teichmuller₀_spec
  结论: {x : Perfection (R ⧸ I) p} {y : R}
  证明: teichmullerFun_spec h

Depends on / 依赖: teichmullerFun_spec
-/
theorem teichmuller₀_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller₀ p I x = y :=
  teichmullerFun_spec h

/--
theorem `teichmuller₀_mapMonoidHom_idealQuotientMk` / 定理 `teichmuller₀_mapMonoidHom_idealQuotientMk`

English:
theorem teichmuller₀_mapMonoidHom_idealQuotientMk
  given: {x : Perfection R p}
  proof: teichmuller₀_spec fun n => ⟨coeffMonoidHom R p n x, by simp⟩

中文:
定理 teichmuller₀_mapMonoidHom_idealQuotientMk
  条件: {x : Perfection R p}
  证明: teichmuller₀_spec fun n => ⟨coeffMonoidHom R p n x, by simp⟩
-/
@[simp] theorem teichmuller₀_mapMonoidHom_idealQuotientMk {x : Perfection R p} :
    teichmuller₀ p I (mapMonoidHom p (Ideal.Quotient.mk I) x) = coeffMonoidHom R p 0 x :=
  teichmuller₀_spec fun n => ⟨coeffMonoidHom R p n x, by simp⟩

/--
theorem `mk_teichmuller` / 定理 `mk_teichmuller`

English:
theorem mk_teichmuller
  given: (x : Perfection (R ⧸ I) p)
  proof: by
have := teichmuller_sModEq Ideal.Quotient.mk_out coeff _ p 0 x
  simp_rw [zero_add, pow_one] at this
  simpa [SModEq.idealQuotientMk] using this

中文:
定理 mk_teichmuller
  条件: (x : Perfection (R ⧸ I) p)
  证明: by
have := teichmuller_sModEq Ideal.Quotient.mk_out coeff _ p 0 x
  simp_rw [zero_add, pow_one] at this
  simpa [SModEq.idealQuotientMk] using this

Depends on / 依赖: Ideal.Quotient.mk_out, Quotient, SModEq, SModEq.idealQuotientMk, idealQuotientMk, mk_out, pow_one, simp_rw, teichmuller_sModEq, zero_add
-/
theorem mk_teichmuller (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x := by
have := teichmuller_sModEq Ideal.Quotient.mk_out coeff _ p 0 x
  simp_rw [zero_add, pow_one] at this
  simpa [SModEq.idealQuotientMk] using this

/--
theorem `mk_teichmuller₀` / 定理 `mk_teichmuller₀`

English:
theorem mk_teichmuller₀
  given: (x : Perfection (R ⧸ I) p)
  proof: mk_teichmuller _

中文:
定理 mk_teichmuller₀
  条件: (x : Perfection (R ⧸ I) p)
  证明: mk_teichmuller _
-/
@[simp] theorem mk_teichmuller₀ (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller₀ p I x) = coeff _ p 0 x := mk_teichmuller _

variable (p I) in
/--
theorem `mk_comp_teichmuller` / 定理 `mk_comp_teichmuller`

English:
theorem mk_comp_teichmuller
  proof: MonoidHom.ext mk_teichmuller

中文:
定理 mk_comp_teichmuller
  证明: MonoidHom.ext mk_teichmuller

Depends on / 依赖: MonoidHom, MonoidHom.ext, mk_teichmuller
-/
theorem mk_comp_teichmuller :
    (Ideal.Quotient.mk I : _ ->* _).comp (teichmuller p I) =
      (coeff (R ⧸ I) p 0 : Perfection (R ⧸ I) p ->* R ⧸ I) :=
  MonoidHom.ext mk_teichmuller

variable (p I) in
/--
theorem `mk_comp_teichmuller₀` / 定理 `mk_comp_teichmuller₀`

English:
theorem mk_comp_teichmuller₀
  proof: MonoidWithZeroHom.ext mk_teichmuller

中文:
定理 mk_comp_teichmuller₀
  证明: MonoidWithZeroHom.ext mk_teichmuller

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.ext, mk_teichmuller
-/
theorem mk_comp_teichmuller₀ :
    (MonoidWithZeroHom.ofClass (Ideal.Quotient.mk I)).comp (teichmuller₀ p I) =
      .ofClass (coeff (R ⧸ I) p 0) :=
  MonoidWithZeroHom.ext mk_teichmuller

variable (p I) in
/--
theorem `mk_comp_teichmuller'` / 定理 `mk_comp_teichmuller'`

English:
theorem mk_comp_teichmuller'
  proof: funext mk_teichmuller

中文:
定理 mk_comp_teichmuller'
  证明: funext mk_teichmuller

Depends on / 依赖: mk_teichmuller
-/
theorem mk_comp_teichmuller' :
    Ideal.Quotient.mk I ∘ (teichmuller p I) = coeff (R ⧸ I) p 0 :=
  funext mk_teichmuller

/--
Definition of `quotientMulEquiv` / `quotientMulEquiv` 的定义

English:
definition quotientMulEquiv
  signature: (p : Nat) [Fact p.Prime]
  body: MonoidHom.toMulEquiv
  (mapMonoidHom _ <| Ideal.Quotient.mk I)
  (liftMonoidHom p _ _ <| teichmuller p I)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)

中文:
定义 quotientMulEquiv
  签名: (p : 自然数) [Fact p.素]
  定义体: MonoidHom.toMulEquiv
  (mapMonoidHom _ <| Ideal.Quotient.mk I)
  (liftMonoidHom p _ _ <| teichmuller p I)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, toMulEquiv
-/
noncomputable def quotientMulEquiv (p : Nat) [Fact p.Prime]
    {R : Type*} [CommRing R] (I : Ideal R) [CharP (R ⧸ I) p] [IsAdicComplete I R] :
    Perfection R p ≃* Perfection (R ⧸ I) p := MonoidHom.toMulEquiv
  (mapMonoidHom _ <| Ideal.Quotient.mk I)
  (liftMonoidHom p _ _ <| teichmuller p I)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)

/--
theorem `coeff_quotientMulEquiv` / 定理 `coeff_quotientMulEquiv`

English:
theorem coeff_quotientMulEquiv
  given: (x : Perfection R p) (n : Nat)
  proof: rfl

中文:
定理 coeff_quotientMulEquiv
  条件: (x : Perfection R p) (n : 自然数)
  证明: rfl
-/
@[simp] theorem coeff_quotientMulEquiv (x : Perfection R p) (n : Nat) :
    coeff (R ⧸ I) p n (quotientMulEquiv p I x) = Ideal.Quotient.mk I (coeffMonoidHom R p n x) := rfl

/--
theorem `coeff_zero_symm_quotientMulEquiv` / 定理 `coeff_zero_symm_quotientMulEquiv`

English:
theorem coeff_zero_symm_quotientMulEquiv
  given: (x : Perfection (R ⧸ I) p)
  proof: by
  simp [quotientMulEquiv]

中文:
定理 coeff_zero_symm_quotientMulEquiv
  条件: (x : Perfection (R ⧸ I) p)
  证明: by
  simp [quotientMulEquiv]
-/
@[simp] theorem coeff_zero_symm_quotientMulEquiv (x : Perfection (R ⧸ I) p) :
    coeffMonoidHom R p 0 (quotientMulEquiv p I |>.symm x) = teichmuller₀ p I x := by
  simp [quotientMulEquiv]

end Perfection
