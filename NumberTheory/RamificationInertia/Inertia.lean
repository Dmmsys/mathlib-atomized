/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **inertia degree** `Ideal.inertiaDeg' p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `f` stands for the inertia degree of `P` over `p`, leaving `p` and `P` implicit.

-/

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

/--
Definition of `inertiaDeg'` / `inertiaDeg'` 的定义

English:
definition inertiaDeg'
  signature: : Nat
  body: if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

中文:
定义 inertiaDeg'
  签名: : 自然数
  定义体: if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

Depends on / 依赖: Algebra, Quotient, Quotient.algebraQuotientOfLEComap, algebraQuotientOfLEComap, finrank, hPp.ge
-/
noncomputable def inertiaDeg' : Nat :=
  if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
/--
theorem `inertiaDeg'_of_subsingleton` / 定理 `inertiaDeg'_of_subsingleton`

English:
theorem inertiaDeg'_of_subsingleton
  given: [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)]
  proof: by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
exact dif_neg fun h => hp.ne_top h.symm.trans comap_top

@[deprecated (since := "2026-07-03")] alias inertiaDeg_of_subsingleton :=
  inertiaDeg'_of_subsingleton

@[simp]

中文:
定理 inertiaDeg'_of_subsingleton
  条件: [hp : p.是极大] [hQ : 子单例 (S ⧸ P)]
  证明: by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
exact dif_neg fun h => hp.ne_top h.symm.trans comap_top

@[deprecated (since := "2026-07-03")] alias inertiaDeg_of_subsingleton :=
  inertiaDeg'_of_subsingleton

@[simp]
-/
theorem inertiaDeg'_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg' p P = 0 := by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
exact dif_neg fun h => hp.ne_top h.symm.trans comap_top

@[deprecated (since := "2026-07-03")] alias inertiaDeg_of_subsingleton :=
  inertiaDeg'_of_subsingleton

@[simp]
/--
theorem `inertiaDeg'_algebraMap` / 定理 `inertiaDeg'_algebraMap`

English:
theorem inertiaDeg'_algebraMap
  given: [P.LiesOver p]
  proof: by
  rw [inertiaDeg']; rw [dif_pos (over_def P p).symm]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebraMap := inertiaDeg'_algebraMap

中文:
定理 inertiaDeg'_algebraMap
  条件: [P.LiesOver p]
  证明: by
  rw [inertiaDeg']; rw [dif_pos (over_def P p).symm]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebraMap := inertiaDeg'_algebraMap
-/
theorem inertiaDeg'_algebraMap [P.LiesOver p] :
    inertiaDeg' p P = finrank (R ⧸ p) (S ⧸ P) := by
  rw [inertiaDeg']; rw [dif_pos (over_def P p).symm]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebraMap := inertiaDeg'_algebraMap

/--
theorem `inertiaDeg'_pos` / 定理 `inertiaDeg'_pos`

English:
theorem inertiaDeg'_pos
  given: [p.IsMaximal] [Module.Finite R S] [P.LiesOver p]
  statement: 0 < inertiaDeg' p P
  proof: have : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

中文:
定理 inertiaDeg'_pos
  条件: [p.是极大] [模.有限 R S] [P.LiesOver p]
  结论: 0 < inertiaDeg' p P
  证明: have : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm
-/
theorem inertiaDeg'_pos [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg' p P :=
  have : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

/--
theorem `inertiaDeg'_pos'` / 定理 `inertiaDeg'_pos'`

English:
theorem inertiaDeg'_pos'
  given: [P.IsPrime] [Module.Finite R S] [P.LiesOver p]
  statement: 0 < inertiaDeg' p P
  proof: have : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  Module.finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_pos' := inertiaDeg'_pos'

中文:
定理 inertiaDeg'_pos'
  条件: [P.是素] [模.有限 R S] [P.LiesOver p]
  结论: 0 < inertiaDeg' p P
  证明: have : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  Module.finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_pos' := inertiaDeg'_pos'
-/
theorem inertiaDeg'_pos' [P.IsPrime] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg' p P :=
  have : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  Module.finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_pos' := inertiaDeg'_pos'

/--
theorem `inertiaDeg'_ne_zero` / 定理 `inertiaDeg'_ne_zero`

English:
theorem inertiaDeg'_ne_zero
  given: [p.IsMaximal] [Module.Finite R S] [P.LiesOver p]
  proof: (Nat.ne_of_lt (inertiaDeg'_pos p P)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_ne_zero := inertiaDeg'_ne_zero

中文:
定理 inertiaDeg'_ne_zero
  条件: [p.是极大] [模.有限 R S] [P.LiesOver p]
  证明: (Nat.ne_of_lt (inertiaDeg'_pos p P)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_ne_zero := inertiaDeg'_ne_zero
-/
theorem inertiaDeg'_ne_zero [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] :
    inertiaDeg' p P != 0 :=
  (Nat.ne_of_lt (inertiaDeg'_pos p P)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_ne_zero := inertiaDeg'_ne_zero

/--
lemma `inertiaDeg'_comap_eq` / 引理 `inertiaDeg'_comap_eq`

English:
lemma inertiaDeg'_comap_eq
  given: (e : S ≃ₐ[R] S₁) (P : Ideal S₁)
  proof: by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e]; rw [comap_comap]; rw [← e.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
    exact (Quotient.algEq

中文:
引理 inertiaDeg'_comap_eq
  条件: (e : S ≃ₐ[R] S₁) (P : 理想 S₁)
  证明: by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e]; rw [comap_comap]; rw [← e.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
    exact (Quotient.algEq
-/
lemma inertiaDeg'_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    inertiaDeg' p (P.comap e) = inertiaDeg' p P := by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e]; rw [comap_comap]; rw [← e.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
    exact (Quotient.algEquivOfEqComap p e rfl).toLinearEquiv.finrank_eq
  · rw [inertiaDeg', dif_neg (fun eq => h ⟨(he.mp eq).symm⟩)]
    rw [inertiaDeg']; rw [dif_neg (fun eq => h ⟨eq.symm⟩)]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_comap_eq := inertiaDeg'_comap_eq

/--
lemma `inertiaDeg'_map_eq` / 引理 `inertiaDeg'_map_eq`

English:
lemma inertiaDeg'_map_eq
  statement: (P : Ideal S)
  proof: by
  rw [show P.map e = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.inertiaDeg'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-03")] alias inertiaDeg_map_eq := inertiaDeg'_map_eq

中文:
引理 inertiaDeg'_map_eq
  结论: (P : 理想 S)
  证明: by
  rw [show P.map e = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.inertiaDeg'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-03")] alias inertiaDeg_map_eq := inertiaDeg'_map_eq
-/
lemma inertiaDeg'_map_eq (P : Ideal S)
    {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁] (e : E) :
    inertiaDeg' p (P.map e) = inertiaDeg' p P := by
  rw [show P.map e = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.inertiaDeg'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-03")] alias inertiaDeg_map_eq := inertiaDeg'_map_eq

/--
theorem `inertiaDeg'_bot` / 定理 `inertiaDeg'_bot`

English:
theorem inertiaDeg'_bot
  statement: [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
  proof: by
  rw [inertiaDeg']; rw [dif_pos (over_def P (⊥ : Ideal R)).symm]
  replace hP : P = ⊥ := eq_bot_of_liesOver_bot R P
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
    ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
  rfl

@[deprecated (since := "2026-07-03")] al

中文:
定理 inertiaDeg'_bot
  结论: [非平凡 R] [是整环 S] [代数.是整 R S]
  证明: by
  rw [inertiaDeg']; rw [dif_pos (over_def P (⊥ : Ideal R)).symm]
  replace hP : P = ⊥ := eq_bot_of_liesOver_bot R P
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
    ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
  rfl

@[deprecated (since := "2026-07-03")] al
-/
theorem inertiaDeg'_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    [hP : P.LiesOver (⊥ : Ideal R)] :
    (⊥ : Ideal R).inertiaDeg' P = finrank R S := by
  rw [inertiaDeg']; rw [dif_pos (over_def P (⊥ : Ideal R)).symm]
  replace hP : P = ⊥ := eq_bot_of_liesOver_bot R P
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
    ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
  rfl

@[deprecated (since := "2026-07-03")] alias inertiaDeg_bot := inertiaDeg'_bot

/--
theorem `inertiaDeg'_le_inertiaDeg'` / 定理 `inertiaDeg'_le_inertiaDeg'`

English:
theorem inertiaDeg'_le_inertiaDeg'
  statement: {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
  proof: by
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDeg'_algebraMap]; rw [inertiaDeg'_algebraMap]
have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq by
    rintro ⟨x⟩
    simp [Submodule.Quotient.quot_mk_eq_mk, IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
 

中文:
定理 inertiaDeg'_le_inertiaDeg'
  结论: {T : 类型} [交换环 T] [代数 R T] [代数 S T]
  证明: by
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDeg'_algebraMap]; rw [inertiaDeg'_algebraMap]
have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq by
    rintro ⟨x⟩
    simp [Submodule.Quotient.quot_mk_eq_mk, IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
 
-/
theorem inertiaDeg'_le_inertiaDeg' {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.Finite R T] (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P]
    [p.IsPrime] : inertiaDeg' P Q <= inertiaDeg' p Q := by
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDeg'_algebraMap]; rw [inertiaDeg'_algebraMap]
have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq by
    rintro ⟨x⟩
    simp [Submodule.Quotient.quot_mk_eq_mk, IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
  exact finrank_top_le_finrank_of_isScalarTower ..

@[deprecated (since := "2026-07-03")] alias inertiaDeg_le_inertiaDeg := inertiaDeg'_le_inertiaDeg'

end DecEq

section absNorm

/--
lemma `absNorm_eq_pow_inertiaDeg'_of_liesOver` / 引理 `absNorm_eq_pow_inertiaDeg'_of_liesOver`

English:
lemma absNorm_eq_pow_inertiaDeg'_of_liesOver
  statement: {S : Type*} [CommRing S] [IsDedekindDomain S]
  proof: by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  simpa [absNorm_apply, Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K := S ⧸ p)

@[deprecated (since := "2026-07-03")] alias absNorm_eq_pow_inertiaDeg_of_liesOver :=
  absNorm_eq_pow_inertiaDeg'_of_liesOver

中文:
引理 absNorm_eq_pow_inertiaDeg'_of_liesOver
  结论: {S : 类型} [交换环 S] [是Dedekind整环 S]
  证明: by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  simpa [absNorm_apply, Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K := S ⧸ p)

@[deprecated (since := "2026-07-03")] alias absNorm_eq_pow_inertiaDeg_of_liesOver :=
  absNorm_eq_pow_inertiaDeg'_of_liesOver

Depends on / 依赖: IsMaximal, Module, Module.natCard_eq_pow_finrank, Submodule, Submodule.cardQuot_apply, absNorm_apply, cardQuot_apply, hp.isMaximal, hp_ne_bot, isMaximal, natCard_eq_pow_finrank, p.IsMaximal
-/
lemma absNorm_eq_pow_inertiaDeg'_of_liesOver {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free Int S] [IsDedekindDomain R] [Module.Free Int R] [Algebra S R] [Module.Finite S R]
    (P : Ideal R) (p : Ideal S) [P.LiesOver p] (hp : p.IsPrime) (hp_ne_bot : p != ⊥) :
    absNorm P = absNorm p ^ (p.inertiaDeg' P) := by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  simpa [absNorm_apply, Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K := S ⧸ p)

@[deprecated (since := "2026-07-03")] alias absNorm_eq_pow_inertiaDeg_of_liesOver :=
  absNorm_eq_pow_inertiaDeg'_of_liesOver

/--
lemma `absNorm_eq_pow_inertiaDeg` / 引理 `absNorm_eq_pow_inertiaDeg`

English:
lemma absNorm_eq_pow_inertiaDeg
  statement: [IsDedekindDomain R] [Module.Free Int R] [Module.Finite Int R] {p : Int}
  proof: by
  simpa using absNorm_eq_pow_inertiaDeg'_of_liesOver P (span {p})
    (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)

中文:
引理 absNorm_eq_pow_inertiaDeg
  结论: [是Dedekind整环 R] [模.自由 整数 R] [模.有限 整数 R] {p : 整数}
  证明: by
  simpa using absNorm_eq_pow_inertiaDeg'_of_liesOver P (span {p})
    (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)

Depends on / 依赖: _of_liesOver, absNorm_eq_pow_inertiaDeg, hp.ne_zero, ne_zero, span_singleton_prime
-/
lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free Int R] [Module.Finite Int R] {p : Int}
    (P : Ideal R) [P.LiesOver (span {p})] (hp : Prime p) :
    absNorm P = p.natAbs ^ ((span {p}).inertiaDeg' P) := by
  simpa using absNorm_eq_pow_inertiaDeg'_of_liesOver P (span {p})
    (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)

/--
lemma `absNorm_eq_pow_inertiaDeg'` / 引理 `absNorm_eq_pow_inertiaDeg'`

English:
lemma absNorm_eq_pow_inertiaDeg'
  statement: [IsDedekindDomain R] [Module.Free Int R] [Module.Finite Int R] {p : Nat}
  proof: absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)

中文:
引理 absNorm_eq_pow_inertiaDeg'
  结论: [是Dedekind整环 R] [模.自由 整数 R] [模.有限 整数 R] {p : 自然数}
  证明: absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
-/
lemma absNorm_eq_pow_inertiaDeg' [IsDedekindDomain R] [Module.Free Int R] [Module.Finite Int R] {p : Nat}
    (P : Ideal R) [P.LiesOver (span {(p : Int)})] (hp : p.Prime) :
    absNorm P = p ^ ((span {(p : Int)}).inertiaDeg' P) :=
  absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)

end absNorm

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/--
theorem `inertiaDeg'_algebra_tower` / 定理 `inertiaDeg'_algebra_tower`

English:
theorem inertiaDeg'_algebra_tower
  statement: (p : Ideal R) (P : Ideal S) (I : Ideal T) [p.IsMaximal]
  proof: by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg', dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  let : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  let : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quoti

中文:
定理 inertiaDeg'_algebra_tower
  结论: (p : 理想 R) (P : 理想 S) (I : 理想 T) [p.是极大]
  证明: by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg', dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  let : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  let : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quoti
-/
theorem inertiaDeg'_algebra_tower (p : Ideal R) (P : Ideal S) (I : Ideal T) [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] : inertiaDeg' p I =
    inertiaDeg' p P * inertiaDeg' P I := by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg', dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  let : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  let : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₂.le
  let : Algebra (R ⧸ p) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₃.le
let : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) := IsScalarTower.of_algebraMap_eq by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact (finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebra_tower := inertiaDeg'_algebra_tower

end tower

end Ideal
