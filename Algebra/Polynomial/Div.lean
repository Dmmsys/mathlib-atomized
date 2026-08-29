/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Multiplicity

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : Nat}

section Semiring

variable [Semiring R]

/--
theorem `X_dvd_iff` / 定理 `X_dvd_iff`

English:
theorem X_dvd_iff
  given: {f : R[X]}
  statement: X ∣ f ↔ f.coeff 0 = 0
  proof: ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩

中文:
定理 X_dvd_iff
  条件: {f : R[X]}
  结论: X ∣ f ↔ f.coeff 0 = 0
  证明: ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩

Depends on / 依赖: X_mul_divX_add, add_zero, coeff_X_mul_zero, f.divX
-/
theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩

/--
theorem `X_pow_dvd_iff` / 定理 `X_pow_dvd_iff`

English:
theorem X_pow_dvd_iff
  given: {f : R[X]} {n : Nat}
  statement: X ^ n ∣ f ↔ forall d < n, f.coeff d = 0
  proof: ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : Nat => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      h

中文:
定理 X_pow_dvd_iff
  条件: {f : R[X]} {n : 自然数}
  结论: X ^ n ∣ f ↔ 对任意 d < n, f.coeff d = 0
  证明: ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : Nat => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      h

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, Nat.lt_succ_of_lt, Nat.lt_succ_self, Polynomial, Polynomial.X_dvd_iff.mpr, X_dvd_iff, coeff_X_pow_mul, forall_iff, ite_eq_right_iff, lt_succ_of_lt, lt_succ_self, mul_assoc, not_le_of_gt, pow_succ, pow_zero, this.symm, zero_add
-/
theorem X_pow_dvd_iff {f : R[X]} {n : Nat} : X ^ n ∣ f ↔ forall d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : Nat => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      have := coeff_X_pow_mul g n 0
      rw [zero_add]; rw [← hgf]; rw [hd n (Nat.lt_succ_self n)] at this
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      use k
      rwa [pow_succ, mul_assoc, ← hgk]⟩

variable {p q : R[X]}

/--
theorem `finiteMultiplicity_of_degree_pos_of_monic` / 定理 `finiteMultiplicity_of_degree_pos_of_monic`

English:
theorem finiteMultiplicity_of_degree_pos_of_monic
  statement: (hp : (0 : WithBot Nat) < degree p) (hmp : Monic p)
  proof: have zn0 : (0 : R) != 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p != 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r != 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 :=

中文:
定理 finiteMultiplicity_of_degree_pos_of_monic
  结论: (hp : (0 : WithBot 自然数) < degree p) (hmp : Monic p)
  证明: have zn0 : (0 : R) != 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p != 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r != 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 :=

Depends on / 依赖: Nontrivial, Nontrivial.of_polynomial_ne, hpn1.symm, leadingCoeff, leadingCoeff_pow, natDegree, of_polynomial_ne, zero_ne_one, zn0.symm
-/
theorem finiteMultiplicity_of_degree_pos_of_monic (hp : (0 : WithBot Nat) < degree p) (hmp : Monic p)
    (hq : q != 0) : FiniteMultiplicity p q :=
  have zn0 : (0 : R) != 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p != 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r != 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 := by simp [show _ = _ from hmp]
    have hpn0' : leadingCoeff p ^ (natDegree q + 1) != 0 := hpn1.symm ▸ zn0.symm
    have hpnr0 : leadingCoeff (p ^ (natDegree q + 1)) * leadingCoeff r != 0 := by
      simp only [leadingCoeff_pow' hpn0', leadingCoeff_eq_zero, hpn1, one_mul, Ne,
          hr0, not_false_eq_true]
have hnp : 0 < natDegree p := Nat.cast_lt.1 by
      rw [← degree_eq_natDegree hp0]; exact hp
    have := congr_arg natDegree hr
    rw [natDegree_mul' hpnr0]; rw [natDegree_pow' hpn0']; rw [add_mul]; rw [add_assoc] at this
    exact
      ne_of_lt
        (lt_add_of_le_of_pos (le_mul_of_one_le_right (Nat.zero_le _) hnp)
          (add_pos_of_pos_of_nonneg (by rwa [one_mul]) (Nat.zero_le _)))
        this⟩

/--
lemma `eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le` / 引理 `eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le`

English:
lemma eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
  statement: {p q : R[X]}
  proof: by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp
  have : r.natDegree = 0 := by simpa [hp.natDegree_mul' hr] using hdeg
  rw [eq_C_of_natDegree_eq_zero this]
  simp [leadingCoeff_monic_mul hp]

中文:
引理 eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
  结论: {p q : R[X]}
  证明: by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp
  have : r.natDegree = 0 := by simpa [hp.natDegree_mul' hr] using hdeg
  rw [eq_C_of_natDegree_eq_zero this]
  simp [leadingCoeff_monic_mul hp]

Depends on / 依赖: eq_C_of_natDegree_eq_zero, eq_or_ne, hp.natDegree_mul, leadingCoeff_monic_mul, natDegree, natDegree_mul, r.natDegree
-/
lemma eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p.natDegree) :
    q = p * C q.leadingCoeff := by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp
  have : r.natDegree = 0 := by simpa [hp.natDegree_mul' hr] using hdeg
  rw [eq_C_of_natDegree_eq_zero this]
  simp [leadingCoeff_monic_mul hp]

/--
lemma `eq_of_monic_of_dvd_of_natDegree_le` / 引理 `eq_of_monic_of_dvd_of_natDegree_le`

English:
lemma eq_of_monic_of_dvd_of_natDegree_le
  statement: {p q : R[X]} (hp : p.Monic)
  proof: by
  rw [eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]
  simp [hq]

中文:
引理 eq_of_monic_of_dvd_of_natDegree_le
  结论: {p q : R[X]} (hp : p.Monic)
  证明: by
  rw [eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]
  simp [hq]

Depends on / 依赖: eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
-/
lemma eq_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p.natDegree) : q = p := by
  rw [eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]
  simp [hq]

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

/--
theorem `div_wf_lemma` / 定理 `div_wf_lemma`

English:
theorem div_wf_lemma
  given: (h : degree q <= degree p ∧ p != 0) (hq : Monic q)
  proof: have hp : leadingCoeff p != 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q != 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q <= natDegree p :=
    (Nat.cast_le (α := WithBot Nat)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt_left

中文:
定理 div_wf_lemma
  条件: (h : degree q <= degree p ∧ p != 0) (hq : Monic q)
  证明: have hp : leadingCoeff p != 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q != 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q <= natDegree p :=
    (Nat.cast_le (α := WithBot Nat)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt_left

Depends on / 依赖: Nat.cast_add, Nat.cast_le, WithBot, cast_add, cast_le, degree_C_mul_X_pow, degree_eq_natDegree, degree_mul, degree_mul_comm, degree_sub_lt_left, hq.degree_mul, hq.degree_mul_comm, hq.ne_zero_of_polynomial_ne, leadingCoef, leadingCoeff, leadingCoeff_eq_zero, natDegree, ne_zero_of_polynomial_ne, tsub_add_cancel_of_le
-/
theorem div_wf_lemma (h : degree q <= degree p ∧ p != 0) (hq : Monic q) :
    degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) < degree p :=
  have hp : leadingCoeff p != 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q != 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q <= natDegree p :=
    (Nat.cast_le (α := WithBot Nat)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt_left
    (by
      rw [hq.degree_mul_comm]; rw [hq.degree_mul]; rw [degree_C_mul_X_pow _ hp]; rw [degree_eq_natDegree h.2]; rw [degree_eq_natDegree hq0]; rw [← Nat.cast_add]; rw [tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_monic_mul hq, leadingCoeff_mul_X_pow, leadingCoeff_C])

/--
Definition of `divModByMonicAux` / `divModByMonicAux` 的定义

English:
definition divModByMonicAux
  signature: : forall (_p : R[X]) {q : R[X]}, Monic q -> R[X] × R[X]
  body: Classical.decEq R
    if h : degree q <= degree p ∧ p != 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

中文:
定义 divModByMonicAux
  签名: : 对任意 (_p : R[X]) {q : R[X]}, Monic q -> R[X] × R[X]
  定义体: Classical.decEq R
    if h : degree q <= degree p ∧ p != 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

Depends on / 依赖: Classical, Classical.decEq
-/
noncomputable def divModByMonicAux : forall (_p : R[X]) {q : R[X]}, Monic q -> R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q <= degree p ∧ p != 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

/--
Definition of `divByMonic` / `divByMonic` 的定义

English:
definition divByMonic
  signature: (p q : R[X])
  body: letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

中文:
定义 divByMonic
  签名: (p q : R[X])
  定义体: letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

Depends on / 依赖: Classical, Classical.decEq, divModByMonicAux
-/
def divByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

/--
Definition of `modByMonic` / `modByMonic` 的定义

English:
definition modByMonic
  signature: (p q : R[X])
  body: letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

中文:
定义 modByMonic
  签名: (p q : R[X])
  定义体: letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

Depends on / 依赖: Classical, Classical.decEq, divModByMonicAux
-/
def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

/--
theorem `degree_modByMonic_lt` / 定理 `degree_modByMonic_lt`

English:
theorem degree_modByMonic_lt
  given: [Nontrivial R]
  proof: Classical.decEq R
    if h : degree q <= degree p ∧ p != 0 then by
      have _wf := div_wf_lemma ⟨h.1, h.2⟩ hq
      have :=
        degree_modByMonic_lt (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) hq
      grind [divModByMonicAux, modByMonic]
    else
      Or.casesOn (not_and

中文:
定理 degree_modByMonic_lt
  条件: [Nontrivial R]
  证明: Classical.decEq R
    if h : degree q <= degree p ∧ p != 0 then by
      have _wf := div_wf_lemma ⟨h.1, h.2⟩ hq
      have :=
        degree_modByMonic_lt (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) hq
      grind [divModByMonicAux, modByMonic]
    else
      Or.casesOn (not_and

Depends on / 依赖: Classical, Classical.decEq
-/
theorem degree_modByMonic_lt [Nontrivial R] :
    forall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q <= degree p ∧ p != 0 then by
      have _wf := div_wf_lemma ⟨h.1, h.2⟩ hq
      have :=
        degree_modByMonic_lt (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) hq
      grind [divModByMonicAux, modByMonic]
    else
      Or.casesOn (not_and_or.1 h)
        (by
          unfold modByMonic divModByMonicAux
          dsimp
          rw [dif_pos hq]; rw [if_neg h]
          exact lt_of_not_ge)
        (by
          intro hp
          unfold modByMonic divModByMonicAux
          dsimp
          rw [dif_pos hq]; rw [if_neg h]; rw [Classical.not_not.1 hp]
          exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 hq.ne_zero)))
  termination_by p => p

/--
theorem `natDegree_modByMonic_lt` / 定理 `natDegree_modByMonic_lt`

English:
theorem natDegree_modByMonic_lt
  given: (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q != 1)
  proof: by
  by_cases hpq : p %ₘ q = 0
  · rw [hpq, natDegree_zero, Nat.pos_iff_ne_zero]
    contrapose hq
    exact eq_one_of_monic_natDegree_zero hmq hq
  · have := Nontrivial.of_polynomial_ne hpq
    exact natDegree_lt_natDegree hpq (degree_modByMonic_lt p hmq)

@[simp]

中文:
定理 natDegree_modByMonic_lt
  条件: (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q != 1)
  证明: by
  by_cases hpq : p %ₘ q = 0
  · rw [hpq, natDegree_zero, Nat.pos_iff_ne_zero]
    contrapose hq
    exact eq_one_of_monic_natDegree_zero hmq hq
  · have := Nontrivial.of_polynomial_ne hpq
    exact natDegree_lt_natDegree hpq (degree_modByMonic_lt p hmq)

@[simp]

Depends on / 依赖: Nat.pos_iff_ne_zero, Nontrivial, Nontrivial.of_polynomial_ne, contrapose, degree_modByMonic_lt, eq_one_of_monic_natDegree_zero, natDegree_lt_natDegree, natDegree_zero, of_polynomial_ne, pos_iff_ne_zero
-/
theorem natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q != 1) :
    natDegree (p %ₘ q) < q.natDegree := by
  by_cases hpq : p %ₘ q = 0
  · rw [hpq, natDegree_zero, Nat.pos_iff_ne_zero]
    contrapose hq
    exact eq_one_of_monic_natDegree_zero hmq hq
  · have := Nontrivial.of_polynomial_ne hpq
    exact natDegree_lt_natDegree hpq (degree_modByMonic_lt p hmq)

@[simp]
/--
theorem `zero_modByMonic` / 定理 `zero_modByMonic`

English:
theorem zero_modByMonic
  given: (p : R[X])
  statement: 0 %ₘ p = 0
  proof: by
  grind [modByMonic, divModByMonicAux]

@[simp]

中文:
定理 zero_modByMonic
  条件: (p : R[X])
  结论: 0 %ₘ p = 0
  证明: by
  grind [modByMonic, divModByMonicAux]

@[simp]

Depends on / 依赖: divModByMonicAux, modByMonic
-/
theorem zero_modByMonic (p : R[X]) : 0 %ₘ p = 0 := by
  grind [modByMonic, divModByMonicAux]

@[simp]
/--
theorem `zero_divByMonic` / 定理 `zero_divByMonic`

English:
theorem zero_divByMonic
  given: (p : R[X])
  statement: 0 /ₘ p = 0
  proof: by
  grind [divByMonic, divModByMonicAux]

@[simp]

中文:
定理 zero_divByMonic
  条件: (p : R[X])
  结论: 0 /ₘ p = 0
  证明: by
  grind [divByMonic, divModByMonicAux]

@[simp]

Depends on / 依赖: divByMonic, divModByMonicAux
-/
theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by
  grind [divByMonic, divModByMonicAux]

@[simp]
/--
theorem `modByMonic_zero` / 定理 `modByMonic_zero`

English:
theorem modByMonic_zero
  given: (p : R[X])
  statement: p %ₘ 0 = p
  proof: letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]

@[simp]

中文:
定理 modByMonic_zero
  条件: (p : R[X])
  结论: p %ₘ 0 = p
  证明: letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]

@[simp]

Depends on / 依赖: Classical, Classical.decEq, dif_neg, divModByMonicAux, eq_iff_true_of_subsingleton, modByMonic, monic_zero_iff_subsingleton, monic_zero_iff_subsingleton.mp
-/
theorem modByMonic_zero (p : R[X]) : p %ₘ 0 = p :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]

@[simp]
/--
theorem `divByMonic_zero` / 定理 `divByMonic_zero`

English:
theorem divByMonic_zero
  given: (p : R[X])
  statement: p /ₘ 0 = 0
  proof: letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]

中文:
定理 divByMonic_zero
  条件: (p : R[X])
  结论: p /ₘ 0 = 0
  证明: letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]

Depends on / 依赖: Classical, Classical.decEq, dif_neg, divByMonic, divModByMonicAux, eq_iff_true_of_subsingleton, monic_zero_iff_subsingleton, monic_zero_iff_subsingleton.mp
-/
theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    have := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]

/--
theorem `divByMonic_eq_of_not_monic` / 定理 `divByMonic_eq_of_not_monic`

English:
theorem divByMonic_eq_of_not_monic
  given: (p : R[X]) (hq : ¬Monic q)
  statement: p /ₘ q = 0
  proof: dif_neg hq

中文:
定理 divByMonic_eq_of_not_monic
  条件: (p : R[X]) (hq : ¬Monic q)
  结论: p /ₘ q = 0
  证明: dif_neg hq

Depends on / 依赖: dif_neg
-/
theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0 :=
  dif_neg hq

/--
theorem `modByMonic_eq_of_not_monic` / 定理 `modByMonic_eq_of_not_monic`

English:
theorem modByMonic_eq_of_not_monic
  given: (p : R[X]) (hq : ¬Monic q)
  statement: p %ₘ q = p
  proof: dif_neg hq

中文:
定理 modByMonic_eq_of_not_monic
  条件: (p : R[X]) (hq : ¬Monic q)
  结论: p %ₘ q = p
  证明: dif_neg hq

Depends on / 依赖: dif_neg
-/
theorem modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p :=
  dif_neg hq

/--
theorem `modByMonic_eq_self_iff` / 定理 `modByMonic_eq_self_iff`

English:
theorem modByMonic_eq_self_iff
  given: [Nontrivial R] (hq : Monic q)
  statement: p %ₘ q = p ↔ degree p < degree q
  proof: ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    have : ¬degree q <= degree p := not_le_of_gt h
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

中文:
定理 modByMonic_eq_self_iff
  条件: [Nontrivial R] (hq : Monic q)
  结论: p %ₘ q = p ↔ degree p < degree q
  证明: ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    have : ¬degree q <= degree p := not_le_of_gt h
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

Depends on / 依赖: And.left, degree, degree_modByMonic_lt, dif_pos, divModByMonicAux, if_neg, modByMonic, not_le_of_gt
-/
theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    have : ¬degree q <= degree p := not_le_of_gt h
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

/--
theorem `degree_modByMonic_le` / 定理 `degree_modByMonic_le`

English:
theorem degree_modByMonic_le
  given: (p : R[X]) {q : R[X]} (hq : Monic q)
  statement: degree (p %ₘ q) <= degree q
  proof: by
  nontriviality R
  exact (degree_modByMonic_lt _ hq).le

中文:
定理 degree_modByMonic_le
  条件: (p : R[X]) {q : R[X]} (hq : Monic q)
  结论: degree (p %ₘ q) <= degree q
  证明: by
  nontriviality R
  exact (degree_modByMonic_lt _ hq).le

Depends on / 依赖: degree_modByMonic_lt, nontriviality
-/
theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q) <= degree q := by
  nontriviality R
  exact (degree_modByMonic_lt _ hq).le

/--
theorem `degree_modByMonic_le_left` / 定理 `degree_modByMonic_le_left`

English:
theorem degree_modByMonic_le_left
  statement: degree (p %ₘ q) <= degree p
  proof: by
  nontriviality R
  by_cases hq : q.Monic
  · cases lt_or_ge (degree p) (degree q)
    · rw [(modByMonic_eq_self_iff hq).mpr ‹_›]
    · exact (degree_modByMonic_le p hq).trans ‹_›
  · rw [modByMonic_eq_of_not_monic p hq]

中文:
定理 degree_modByMonic_le_left
  结论: degree (p %ₘ q) <= degree p
  证明: by
  nontriviality R
  by_cases hq : q.Monic
  · cases lt_or_ge (degree p) (degree q)
    · rw [(modByMonic_eq_self_iff hq).mpr ‹_›]
    · exact (degree_modByMonic_le p hq).trans ‹_›
  · rw [modByMonic_eq_of_not_monic p hq]

Depends on / 依赖: degree, degree_modByMonic_le, lt_or_ge, modByMonic_eq_of_not_monic, modByMonic_eq_self_iff, nontriviality, q.Monic
-/
theorem degree_modByMonic_le_left : degree (p %ₘ q) <= degree p := by
  nontriviality R
  by_cases hq : q.Monic
  · cases lt_or_ge (degree p) (degree q)
    · rw [(modByMonic_eq_self_iff hq).mpr ‹_›]
    · exact (degree_modByMonic_le p hq).trans ‹_›
  · rw [modByMonic_eq_of_not_monic p hq]

/--
theorem `natDegree_modByMonic_le` / 定理 `natDegree_modByMonic_le`

English:
theorem natDegree_modByMonic_le
  given: (p : Polynomial R) {g : Polynomial R} (hg : g.Monic)
  proof: natDegree_le_natDegree (degree_modByMonic_le p hg)

中文:
定理 natDegree_modByMonic_le
  条件: (p : Polynomial R) {g : Polynomial R} (hg : g.Monic)
  证明: natDegree_le_natDegree (degree_modByMonic_le p hg)

Depends on / 依赖: degree_modByMonic_le, natDegree_le_natDegree
-/
theorem natDegree_modByMonic_le (p : Polynomial R) {g : Polynomial R} (hg : g.Monic) :
    natDegree (p %ₘ g) <= g.natDegree :=
  natDegree_le_natDegree (degree_modByMonic_le p hg)

/--
theorem `natDegree_modByMonic_le_left` / 定理 `natDegree_modByMonic_le_left`

English:
theorem natDegree_modByMonic_le_left
  statement: natDegree (p %ₘ q) <= natDegree p
  proof: natDegree_le_natDegree degree_modByMonic_le_left

中文:
定理 natDegree_modByMonic_le_left
  结论: natDegree (p %ₘ q) <= natDegree p
  证明: natDegree_le_natDegree degree_modByMonic_le_left

Depends on / 依赖: degree_modByMonic_le_left, natDegree_le_natDegree
-/
theorem natDegree_modByMonic_le_left : natDegree (p %ₘ q) <= natDegree p :=
  natDegree_le_natDegree degree_modByMonic_le_left

/--
theorem `X_dvd_sub_C` / 定理 `X_dvd_sub_C`

English:
theorem X_dvd_sub_C
  statement: X ∣ p - C (p.coeff 0)
  proof: by
  simp [X_dvd_iff, coeff_C]

中文:
定理 X_dvd_sub_C
  结论: X ∣ p - C (p.coeff 0)
  证明: by
  simp [X_dvd_iff, coeff_C]

Depends on / 依赖: X_dvd_iff, coeff_C
-/
theorem X_dvd_sub_C : X ∣ p - C (p.coeff 0) := by
  simp [X_dvd_iff, coeff_C]

/--
theorem `modByMonic_eq_sub_mul_div` / 定理 `modByMonic_eq_sub_mul_div`

English:
theorem modByMonic_eq_sub_mul_div
  proof: Classical.decEq R
    if hq : q.Monic then
      if h : degree q <= degree p ∧ p != 0 then by
        have _wf := div_wf_lemma h hq
        have ih := modByMonic_eq_sub_mul_div
          (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) q
        unfold modByMonic divByMonic divModByM

中文:
定理 modByMonic_eq_sub_mul_div
  证明: Classical.decEq R
    if hq : q.Monic then
      if h : degree q <= degree p ∧ p != 0 then by
        have _wf := div_wf_lemma h hq
        have ih := modByMonic_eq_sub_mul_div
          (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) q
        unfold modByMonic divByMonic divModByM

Depends on / 依赖: Classical, Classical.decEq
-/
theorem modByMonic_eq_sub_mul_div :
    forall p q : R[X], p %ₘ q = p - q * (p /ₘ q)
  | p, q =>
    letI := Classical.decEq R
    if hq : q.Monic then
      if h : degree q <= degree p ∧ p != 0 then by
        have _wf := div_wf_lemma h hq
        have ih := modByMonic_eq_sub_mul_div
          (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) q
        unfold modByMonic divByMonic divModByMonicAux
        rw [dif_pos hq]; rw [dif_pos h]
        rw [modByMonic]; rw [dif_pos hq] at ih
        refine ih.trans ?_
        rw [divByMonic]; rw [dif_pos hq]; rw [dif_pos hq]; rw [dif_pos h]; rw [mul_add]; rw [sub_add_eq_sub_sub]
      else by
        unfold modByMonic divByMonic divModByMonicAux
        dsimp
        rw [dif_pos hq]; rw [if_neg h]; rw [dif_pos hq]; rw [if_neg h]; rw [mul_zero]; rw [sub_zero]
    else by
      rw [modByMonic_eq_of_not_monic _ hq]; rw [divByMonic_eq_of_not_monic _ hq]; rw [mul_zero]; rw [sub_zero]
  termination_by p => p

/--
theorem `modByMonic_add_div` / 定理 `modByMonic_add_div`

English:
theorem modByMonic_add_div
  given: (p q : R[X])
  statement: p %ₘ q + q * (p /ₘ q) = p
  proof: eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p q)

中文:
定理 modByMonic_add_div
  条件: (p q : R[X])
  结论: p %ₘ q + q * (p /ₘ q) = p
  证明: eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p q)

Depends on / 依赖: eq_sub_iff_add_eq, modByMonic_eq_sub_mul_div
-/
theorem modByMonic_add_div (p q : R[X]) : p %ₘ q + q * (p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p q)

/--
theorem `dvd_modByMonic_sub` / 定理 `dvd_modByMonic_sub`

English:
theorem dvd_modByMonic_sub
  given: (p q : R[X])
  statement: q ∣ (p %ₘ q - p)
  proof: by
  by_cases h : q.Monic
  · simp [modByMonic_eq_sub_mul_div]
  · simp [modByMonic_eq_of_not_monic, h]

中文:
定理 dvd_modByMonic_sub
  条件: (p q : R[X])
  结论: q ∣ (p %ₘ q - p)
  证明: by
  by_cases h : q.Monic
  · simp [modByMonic_eq_sub_mul_div]
  · simp [modByMonic_eq_of_not_monic, h]

Depends on / 依赖: modByMonic_eq_of_not_monic, modByMonic_eq_sub_mul_div, q.Monic
-/
theorem dvd_modByMonic_sub (p q : R[X]) : q ∣ (p %ₘ q - p) := by
  by_cases h : q.Monic
  · simp [modByMonic_eq_sub_mul_div]
  · simp [modByMonic_eq_of_not_monic, h]

/--
theorem `dvd_modByMonic_iff_dvd` / 定理 `dvd_modByMonic_iff_dvd`

English:
theorem dvd_modByMonic_iff_dvd
  statement: q ∣ p %ₘ q ↔ q ∣ p
  proof: by
simpa using dvd_iff_dvd_of_dvd_sub dvd_modByMonic_sub p q

中文:
定理 dvd_modByMonic_iff_dvd
  结论: q ∣ p %ₘ q ↔ q ∣ p
  证明: by
simpa using dvd_iff_dvd_of_dvd_sub dvd_modByMonic_sub p q
-/
@[simp] theorem dvd_modByMonic_iff_dvd : q ∣ p %ₘ q ↔ q ∣ p := by
simpa using dvd_iff_dvd_of_dvd_sub dvd_modByMonic_sub p q

/--
theorem `divByMonic_eq_zero_iff` / 定理 `divByMonic_eq_zero_iff`

English:
theorem divByMonic_eq_zero_iff
  given: [Nontrivial R] (hq : Monic q)
  statement: p /ₘ q = 0 ↔ degree p < degree q
  proof: ⟨fun h => by
    have := modByMonic_add_div p q
    rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
  fun h => by
    have : ¬degree q <= degree p := not_le_of_gt h
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

中文:
定理 divByMonic_eq_zero_iff
  条件: [Nontrivial R] (hq : Monic q)
  结论: p /ₘ q = 0 ↔ degree p < degree q
  证明: ⟨fun h => by
    have := modByMonic_add_div p q
    rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
  fun h => by
    have : ¬degree q <= degree p := not_le_of_gt h
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

Depends on / 依赖: And.left, add_zero, degree, dif_pos, divByMonic, divModByMonicAux, if_neg, modByMonic_add_div, modByMonic_eq_self_iff, mul_zero, not_le_of_gt
-/
theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := modByMonic_add_div p q
    rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
  fun h => by
    have : ¬degree q <= degree p := not_le_of_gt h
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

/--
theorem `degree_add_divByMonic` / 定理 `degree_add_divByMonic`

English:
theorem degree_add_divByMonic
  given: (hq : Monic q) (h : degree q <= degree p)
  proof: by
  nontriviality R
  have hdiv0 : p /ₘ q != 0 := by rwa [Ne, divByMonic_eq_zero_iff hq, not_lt]
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) != 0 := by
    rwa [Monic.def.1 hq, one_mul, Ne, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree 

中文:
定理 degree_add_divByMonic
  条件: (hq : Monic q) (h : degree q <= degree p)
  证明: by
  nontriviality R
  have hdiv0 : p /ₘ q != 0 := by rwa [Ne, divByMonic_eq_zero_iff hq, not_lt]
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) != 0 := by
    rwa [Monic.def.1 hq, one_mul, Ne, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree 

Depends on / 依赖: Monic.def, Nat.cast_add, Nat.cast_le, Nat.le_add_right, cast_add, cast_le, degree, degree_eq_natDegree, degree_modByMonic_lt, degree_mul, divByMonic_eq_zero_iff, hq.ne_zero, le_add_right, leadingCoeff, leadingCoeff_eq_zero, ne_zero, nontriviality, not_lt, one_mul
-/
theorem degree_add_divByMonic (hq : Monic q) (h : degree q <= degree p) :
    degree q + degree (p /ₘ q) = degree p := by
  nontriviality R
  have hdiv0 : p /ₘ q != 0 := by rwa [Ne, divByMonic_eq_zero_iff hq, not_lt]
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) != 0 := by
    rwa [Monic.def.1 hq, one_mul, Ne, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree (p %ₘ q) < degree q := degree_modByMonic_lt _ hq
      _ <= _ := by
        rw [degree_mul' hlc]; rw [degree_eq_natDegree hq.ne_zero]; rw [degree_eq_natDegree hdiv0]; rw [←
            Nat.cast_add]; rw [Nat.cast_le]
        exact Nat.le_add_right _ _
  calc
    degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) := Eq.symm (degree_mul' hlc)
    _ = degree (p %ₘ q + q * (p /ₘ q)) := (degree_add_eq_right_of_degree_lt hmod).symm
    _ = _ := congr_arg _ (modByMonic_add_div _ _)

/--
theorem `degree_divByMonic_le` / 定理 `degree_divByMonic_le`

English:
theorem degree_divByMonic_le
  given: (p q : R[X])
  statement: degree (p /ₘ q) <= degree p
  proof: letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q <= degree p then by
        have := Nontrivial.of_polynomial_ne hp0
        rw [← degree_add_divByMonic hq h]; rw [degree_eq_natDegree hq.ne_zero]; rw [d

中文:
定理 degree_divByMonic_le
  条件: (p q : R[X])
  结论: degree (p /ₘ q) <= degree p
  证明: letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q <= degree p then by
        have := Nontrivial.of_polynomial_ne hp0
        rw [← degree_add_divByMonic hq h]; rw [degree_eq_natDegree hq.ne_zero]; rw [d

Depends on / 依赖: Classical, Classical.decEq, Nat.le_add_left, Nontrivial, Nontrivial.of_polynomial_ne, WithBot, WithBot.coe_le_coe, bot_le, coe_le_coe, degree, degree_add_divByMonic, degree_eq_natDegree, degree_zero, dif_pos, divByMonic, divByMonic_eq_of_not_m, divByMonic_eq_zero_iff, divModByMonicAux, hq.ne_zero, le_add_left
-/
theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) <= degree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q <= degree p then by
        have := Nontrivial.of_polynomial_ne hp0
        rw [← degree_add_divByMonic hq h]; rw [degree_eq_natDegree hq.ne_zero]; rw [degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 (not_lt.2 h))]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
      else by
        unfold divByMonic divModByMonicAux
        simp [dif_pos hq, h, degree_zero, bot_le]
    else (divByMonic_eq_of_not_monic p hq).symm ▸ bot_le

/--
theorem `degree_divByMonic_lt` / 定理 `degree_divByMonic_lt`

English:
theorem degree_divByMonic_lt
  statement: (p q : R[X]) (hp0 : p != 0)
  proof: letI := Classical.decEq R
  if hq : q.Monic then
    if hpq : degree p < degree q then by
      have := Nontrivial.of_polynomial_ne hp0
      rw [(divByMonic_eq_zero_iff hq).2 hpq]; rw [degree_eq_natDegree hp0]
      exact WithBot.bot_lt_coe _
    else by
      have := Nontrivial.of_polynomial_ne hp

中文:
定理 degree_divByMonic_lt
  结论: (p q : R[X]) (hp0 : p != 0)
  证明: letI := Classical.decEq R
  if hq : q.Monic then
    if hpq : degree p < degree q then by
      have := Nontrivial.of_polynomial_ne hp0
      rw [(divByMonic_eq_zero_iff hq).2 hpq]; rw [degree_eq_natDegree hp0]
      exact WithBot.bot_lt_coe _
    else by
      have := Nontrivial.of_polynomial_ne hp

Depends on / 依赖: Classical, Classical.decEq, Nat.cast_lt, Nat.lt_add_of_pos_left, Nontrivial, Nontrivial.of_polynomial_ne, WithBot, WithBot.bot_lt_coe, bot_lt_coe, cast_lt, degree, degree_add_divByMonic, degree_eq_n, degree_eq_natDegree, divByMonic_eq_zero_iff, hq.ne_zero, lt_add_of_pos_left, ne_zero, not_lt, of_polynomial_ne
-/
theorem degree_divByMonic_lt (p q : R[X]) (hp0 : p != 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  letI := Classical.decEq R
  if hq : q.Monic then
    if hpq : degree p < degree q then by
      have := Nontrivial.of_polynomial_ne hp0
      rw [(divByMonic_eq_zero_iff hq).2 hpq]; rw [degree_eq_natDegree hp0]
      exact WithBot.bot_lt_coe _
    else by
      have := Nontrivial.of_polynomial_ne hp0
      rw [← degree_add_divByMonic hq (not_lt.1 hpq)]; rw [degree_eq_natDegree hq.ne_zero]; rw [degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 hpq)]
      exact
        Nat.cast_lt.2
          (Nat.lt_add_of_pos_left (Nat.cast_lt.1 <|
            by simpa [degree_eq_natDegree hq.ne_zero] using! h0q))
  else by
    rwa [divByMonic_eq_of_not_monic _ hq, degree_zero, bot_lt_iff_ne_bot, degree_ne_bot]

/--
theorem `natDegree_divByMonic` / 定理 `natDegree_divByMonic`

English:
theorem natDegree_divByMonic
  given: (f : R[X]) {g : R[X]} (hg : g.Monic)
  proof: by
  nontriviality R
  by_cases hfg : f /ₘ g = 0
  · rw [hfg, natDegree_zero]
    rw [divByMonic_eq_zero_iff hg] at hfg
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
  have hgf := hfg
  rw [divByMonic_eq_zero_iff hg] at hgf
  push Not at hgf
  have := degree_add_divByMoni

中文:
定理 natDegree_divByMonic
  条件: (f : R[X]) {g : R[X]} (hg : g.Monic)
  证明: by
  nontriviality R
  by_cases hfg : f /ₘ g = 0
  · rw [hfg, natDegree_zero]
    rw [divByMonic_eq_zero_iff hg] at hfg
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
  have hgf := hfg
  rw [divByMonic_eq_zero_iff hg] at hgf
  push Not at hgf
  have := degree_add_divByMoni

Depends on / 依赖: Nat.cast_add, Nat.cast_inj, cast_add, cast_inj, degree_add_divByMonic, degree_eq_natDegree, divByMonic_eq_zero_iff, hg.ne_zero, le_of_lt, natDegree_le_natDegree, natDegree_zero, ne_zero, nontriviality, tsub_eq_zero_iff_le, tsub_eq_zero_iff_le.mpr, zero_divByMonic
-/
theorem natDegree_divByMonic (f : R[X]) {g : R[X]} (hg : g.Monic) :
    natDegree (f /ₘ g) = natDegree f - natDegree g := by
  nontriviality R
  by_cases hfg : f /ₘ g = 0
  · rw [hfg, natDegree_zero]
    rw [divByMonic_eq_zero_iff hg] at hfg
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
  have hgf := hfg
  rw [divByMonic_eq_zero_iff hg] at hgf
  push Not at hgf
  have := degree_add_divByMonic hg hgf
  have hf : f != 0 := by
    intro hf
    apply hfg
    rw [hf]; rw [zero_divByMonic]
  rw [degree_eq_natDegree hf]; rw [degree_eq_natDegree hg.ne_zero]; rw [degree_eq_natDegree hfg]; rw [← Nat.cast_add]; rw [Nat.cast_inj] at this
  rw [← this]; rw [add_tsub_cancel_left]

/--
theorem `div_modByMonic_unique` / 定理 `div_modByMonic_unique`

English:
theorem div_modByMonic_unique
  statement: {f g} (q r : R[X]) (hg : Monic g)
  proof: by
  nontriviality R
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f g).symm)]
        simp [mul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q -

中文:
定理 div_modByMonic_unique
  结论: {f g} (q r : R[X]) (hg : Monic g)
  证明: by
  nontriviality R
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f g).symm)]
        simp [mul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q -

Depends on / 依赖: add_assoc, add_comm, add_left_comm, degree, degree_modByMonic_lt, degree_sub_le, eq_of_sub_eq_zero, max_lt_iff, modByMonic_add_div, mul_add, nontriviality, sub_eq_add_neg, sub_eq_zero_of_eq
-/
theorem div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g)
    (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r := by
  nontriviality R
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f g).symm)]
        simp [mul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)) := by simp [h₁]
  have h₄ : degree (r - f %ₘ g) < degree g :=
    calc
      degree (r - f %ₘ g) <= max (degree r) (degree (f %ₘ g)) := degree_sub_le _ _
      _ < degree g := max_lt_iff.2 ⟨h.2, degree_modByMonic_lt _ hg⟩
  have h₅ : q - f /ₘ g = 0 :=
    _root_.by_contradiction fun hqf =>
not_le_of_gt h₄
        calc
          degree g <= degree g + degree (q - f /ₘ g) := by
            rw [degree_eq_natDegree hg.ne_zero]; rw [degree_eq_natDegree hqf]
            norm_cast
            exact Nat.le_add_right _ _
          _ = degree (r - f %ₘ g) := by rw [h₂, degree_mul']; simpa [Monic.def.1 hg]
exact ⟨Eq.symm eq_of_sub_eq_zero h₅, Eq.symm eq_of_sub_eq_zero by simpa [h₅] using h₁⟩

/--
theorem `map_mod_divByMonic` / 定理 `map_mod_divByMonic`

English:
theorem map_mod_divByMonic
  given: [Ring S] (f : R ->+* S) (hq : Monic q)
  proof: by
  nontriviality S
  have : Nontrivial R := f.domain_nontrivial
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q) :=
    div_modByMonic_unique ((p /ₘ q).map f) _ (hq.map f)
⟨Eq.symm by rw [← Polynomial.map_mul, ← Polynomial.map_add, modByMonic_add_div],
        cal

中文:
定理 map_mod_divByMonic
  条件: [Ring S] (f : R ->+* S) (hq : Monic q)
  证明: by
  nontriviality S
  have : Nontrivial R := f.domain_nontrivial
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q) :=
    div_modByMonic_unique ((p /ₘ q).map f) _ (hq.map f)
⟨Eq.symm by rw [← Polynomial.map_mul, ← Polynomial.map_add, modByMonic_add_div],
        cal

Depends on / 依赖: Eq.symm, Monic.def, Nontrivial, Polynomial, Polynomial.map_add, Polynomial.map_mul, degree, degree_map_eq_of_leadingCoeff_ne_zero, degree_map_le, degree_modByMonic_lt, div_modByMonic_unique, domain_nontrivial, f.domain_nontrivial, f.map_one, hq.map, map_add, map_mul, map_one, modByMonic_add_div, nontriviality
-/
theorem map_mod_divByMonic [Ring S] (f : R ->+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f := by
  nontriviality S
  have : Nontrivial R := f.domain_nontrivial
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q) :=
    div_modByMonic_unique ((p /ₘ q).map f) _ (hq.map f)
⟨Eq.symm by rw [← Polynomial.map_mul, ← Polynomial.map_add, modByMonic_add_div],
        calc
          _ <= degree (p %ₘ q) := degree_map_le
          _ < degree q := degree_modByMonic_lt _ hq
          _ = _ :=
Eq.symm
              degree_map_eq_of_leadingCoeff_ne_zero _
                (by rw [Monic.def.1 hq, f.map_one]; exact one_ne_zero)⟩
  exact ⟨this.1.symm, this.2.symm⟩

/--
theorem `map_divByMonic` / 定理 `map_divByMonic`

English:
theorem map_divByMonic
  given: [Ring S] (f : R ->+* S) (hq : Monic q)
  proof: (map_mod_divByMonic f hq).1

中文:
定理 map_divByMonic
  条件: [Ring S] (f : R ->+* S) (hq : Monic q)
  证明: (map_mod_divByMonic f hq).1

Depends on / 依赖: map_mod_divByMonic
-/
theorem map_divByMonic [Ring S] (f : R ->+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f :=
  (map_mod_divByMonic f hq).1

/--
theorem `map_modByMonic` / 定理 `map_modByMonic`

English:
theorem map_modByMonic
  given: [Ring S] (f : R ->+* S) (hq : Monic q)
  proof: (map_mod_divByMonic f hq).2

中文:
定理 map_modByMonic
  条件: [Ring S] (f : R ->+* S) (hq : Monic q)
  证明: (map_mod_divByMonic f hq).2

Depends on / 依赖: map_mod_divByMonic, odd_mul, odd_mul.mp
-/
theorem map_modByMonic [Ring S] (f : R ->+* S) (hq : Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_divByMonic f hq).2

/--
theorem `modByMonic_eq_zero_iff_dvd` / 定理 `modByMonic_eq_zero_iff_dvd`

English:
theorem modByMonic_eq_zero_iff_dvd
  given: (hq : Monic q)
  statement: p %ₘ q = 0 ↔ q ∣ p
  proof: ⟨fun h => by rw [← modByMonic_add_div p q, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div, mul_sub, ← hr]
    have : degree (q *

中文:
定理 modByMonic_eq_zero_iff_dvd
  条件: (hq : Monic q)
  结论: p %ₘ q = 0 ↔ q ∣ p
  证明: ⟨fun h => by rw [← modByMonic_add_div p q, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div, mul_sub, ← hr]
    have : degree (q *

Depends on / 依赖: degree, degree_modByMonic_lt, dvd_mul_right, exists_eq_mul_right_of_dvd, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_zero, modByMonic_add_div, modByMonic_eq_sub_mul_div, mul_sub, mul_zero, nontriviality, odd_mul, odd_mul.mp, zero_add
-/
theorem modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  ⟨fun h => by rw [← modByMonic_add_div p q, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div, mul_sub, ← hr]
    have : degree (q * (r - p /ₘ q)) < degree q := hmod ▸ degree_modByMonic_lt _ hq
    have hrpq0 : leadingCoeff (r - p /ₘ q) != 0 := fun h =>
hpq0
        leadingCoeff_eq_zero.1
          (by rw [hmod, leadingCoeff_eq_zero.1 h, mul_zero, leadingCoeff_zero])
    have hlc : leadingCoeff q * leadingCoeff (r - p /ₘ q) != 0 := by rwa [Monic.def.1 hq, one_mul]
    rw [degree_mul' hlc]; rw [degree_eq_natDegree hq.ne_zero]; rw [degree_eq_natDegree (mt leadingCoeff_eq_zero.2 hrpq0)] at this
    exact not_lt_of_ge (Nat.le_add_right _ _) (WithBot.coe_lt_coe.1 this)⟩

@[simp]
/--
theorem `modByMonic_self` / 定理 `modByMonic_self`

English:
theorem modByMonic_self
  given: (hp : p.Monic)
  statement: p %ₘ p = 0
  proof: by rw [modByMonic_eq_zero_iff_dvd hp]

中文:
定理 modByMonic_self
  条件: (hp : p.Monic)
  结论: p %ₘ p = 0
  证明: by rw [modByMonic_eq_zero_iff_dvd hp]

Depends on / 依赖: modByMonic_eq_zero_iff_dvd
-/
theorem modByMonic_self (hp : p.Monic) : p %ₘ p = 0 := by rw [modByMonic_eq_zero_iff_dvd hp]

/-- See `Polynomial.mul_self_modByMonic` for the other multiplication order. That version, unlike
this one, requires commutativity. -/
@[simp]
/--
lemma `self_mul_modByMonic` / 引理 `self_mul_modByMonic`

English:
lemma self_mul_modByMonic
  given: (hq : q.Monic)
  statement: (q * p) %ₘ q = 0
  proof: by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_right q p

中文:
引理 self_mul_modByMonic
  条件: (hq : q.Monic)
  结论: (q * p) %ₘ q = 0
  证明: by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_right q p

Depends on / 依赖: dvd_mul_right, modByMonic_eq_zero_iff_dvd
-/
lemma self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_right q p

/--
theorem `map_dvd_map` / 定理 `map_dvd_map`

English:
theorem map_dvd_map
  statement: [Ring S] (f : R ->+* S) (hf : Function.Injective f) {x y : R[X]}
  proof: by
  rw [← modByMonic_eq_zero_iff_dvd hx]; rw [← modByMonic_eq_zero_iff_dvd (hx.map f)]; rw [←
    map_modByMonic f hx]
  exact
⟨fun H => map_injective f hf by rw [H, Polynomial.map_zero], fun H => by
      rw [H]; rw [Polynomial.map_zero]⟩

@[simp]

中文:
定理 map_dvd_map
  结论: [Ring S] (f : R ->+* S) (hf : Function.Injective f) {x y : R[X]}
  证明: by
  rw [← modByMonic_eq_zero_iff_dvd hx]; rw [← modByMonic_eq_zero_iff_dvd (hx.map f)]; rw [←
    map_modByMonic f hx]
  exact
⟨fun H => map_injective f hf by rw [H, Polynomial.map_zero], fun H => by
      rw [H]; rw [Polynomial.map_zero]⟩

@[simp]

Depends on / 依赖: Polynomial, Polynomial.map_zero, hx.map, map_injective, map_modByMonic, map_zero, modByMonic_eq_zero_iff_dvd
-/
theorem map_dvd_map [Ring S] (f : R ->+* S) (hf : Function.Injective f) {x y : R[X]}
    (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y := by
  rw [← modByMonic_eq_zero_iff_dvd hx]; rw [← modByMonic_eq_zero_iff_dvd (hx.map f)]; rw [←
    map_modByMonic f hx]
  exact
⟨fun H => map_injective f hf by rw [H, Polynomial.map_zero], fun H => by
      rw [H]; rw [Polynomial.map_zero]⟩

@[simp]
/--
theorem `modByMonic_one` / 定理 `modByMonic_one`

English:
theorem modByMonic_one
  given: (p : R[X])
  statement: p %ₘ 1 = 0
  proof: (modByMonic_eq_zero_iff_dvd (by convert! monic_one (R := R))).2 (one_dvd _)

@[simp]

中文:
定理 modByMonic_one
  条件: (p : R[X])
  结论: p %ₘ 1 = 0
  证明: (modByMonic_eq_zero_iff_dvd (by convert! monic_one (R := R))).2 (one_dvd _)

@[simp]

Depends on / 依赖: convert, modByMonic_eq_zero_iff_dvd, monic_one, one_dvd
-/
theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 :=
  (modByMonic_eq_zero_iff_dvd (by convert! monic_one (R := R))).2 (one_dvd _)

@[simp]
/--
theorem `divByMonic_one` / 定理 `divByMonic_one`

English:
theorem divByMonic_one
  given: (p : R[X])
  statement: p /ₘ 1 = p
  proof: by
  conv_rhs => rw [← modByMonic_add_div p 1]; simp

中文:
定理 divByMonic_one
  条件: (p : R[X])
  结论: p /ₘ 1 = p
  证明: by
  conv_rhs => rw [← modByMonic_add_div p 1]; simp

Depends on / 依赖: conv_rhs, modByMonic_add_div
-/
theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by
  conv_rhs => rw [← modByMonic_add_div p 1]; simp

/--
theorem `sum_modByMonic_coeff` / 定理 `sum_modByMonic_coeff`

English:
theorem sum_modByMonic_coeff
  given: (hq : q.Monic) {n : Nat} (hn : q.degree <= n)
  proof: by
  nontriviality R
  exact
    (sum_fin (fun i c => monomial i c) (by simp) ((degree_modByMonic_lt _ hq).trans_le hn)).trans
      (sum_monomial_eq _)

中文:
定理 sum_modByMonic_coeff
  条件: (hq : q.Monic) {n : 自然数} (hn : q.degree <= n)
  证明: by
  nontriviality R
  exact
    (sum_fin (fun i c => monomial i c) (by simp) ((degree_modByMonic_lt _ hq).trans_le hn)).trans
      (sum_monomial_eq _)

Depends on / 依赖: degree_modByMonic_lt, monomial, nontriviality, sum_fin, sum_monomial_eq, trans_le
-/
theorem sum_modByMonic_coeff (hq : q.Monic) {n : Nat} (hn : q.degree <= n) :
    (∑ i : Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q := by
  nontriviality R
  exact
    (sum_fin (fun i c => monomial i c) (by simp) ((degree_modByMonic_lt _ hq).trans_le hn)).trans
      (sum_monomial_eq _)

/--
theorem `mul_divByMonic_cancel_left` / 定理 `mul_divByMonic_cancel_left`

English:
theorem mul_divByMonic_cancel_left
  given: (p : R[X]) {q : R[X]} (hmo : q.Monic)
  proof: by
  nontriviality R
  refine (div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], ?_⟩).1
  rw [degree_zero]
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)

中文:
定理 mul_divByMonic_cancel_left
  条件: (p : R[X]) {q : R[X]} (hmo : q.Monic)
  证明: by
  nontriviality R
  refine (div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], ?_⟩).1
  rw [degree_zero]
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)

Depends on / 依赖: Ne.bot_lt, bot_lt, degree_eq_bot, degree_zero, div_modByMonic_unique, hmo.ne_zero, ne_zero, nontriviality, zero_add
-/
theorem mul_divByMonic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by
  nontriviality R
  refine (div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], ?_⟩).1
  rw [degree_zero]
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)

/--
lemma `coeff_divByMonic_X_sub_C_rec` / 引理 `coeff_divByMonic_X_sub_C_rec`

English:
lemma coeff_divByMonic_X_sub_C_rec
  given: (p : R[X]) (a : R) (n : Nat)
  proof: by
  nontriviality R
  have := monic_X_sub_C a
  set q := p /ₘ (X - C a)
  rw [← p.modByMonic_add_div (X - C a)]
  have : degree (p %ₘ (X - C a)) < ↑(n + 1) := degree_X_sub_C a ▸ p.degree_modByMonic_lt this
.trans_le WithBot.coe_le_coe.mpr le_add_self
  simp [q, sub_mul, add_sub, coeff_eq_zero_of_de

中文:
引理 coeff_divByMonic_X_sub_C_rec
  条件: (p : R[X]) (a : R) (n : 自然数)
  证明: by
  nontriviality R
  have := monic_X_sub_C a
  set q := p /ₘ (X - C a)
  rw [← p.modByMonic_add_div (X - C a)]
  have : degree (p %ₘ (X - C a)) < ↑(n + 1) := degree_X_sub_C a ▸ p.degree_modByMonic_lt this
.trans_le WithBot.coe_le_coe.mpr le_add_self
  simp [q, sub_mul, add_sub, coeff_eq_zero_of_de

Depends on / 依赖: WithBot, WithBot.coe_le_coe.mpr, add_sub, coe_le_coe, coeff_eq_zero_of_degree_lt, degree, degree_X_sub_C, degree_modByMonic_lt, le_add_self, modByMonic_add_div, monic_X_sub_C, nontriviality, p.degree_modByMonic_lt, p.modByMonic_add_div, sub_mul, trans_le
-/
lemma coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : Nat) :
    (p /ₘ (X - C a)).coeff n = coeff p (n + 1) + a * (p /ₘ (X - C a)).coeff (n + 1) := by
  nontriviality R
  have := monic_X_sub_C a
  set q := p /ₘ (X - C a)
  rw [← p.modByMonic_add_div (X - C a)]
  have : degree (p %ₘ (X - C a)) < ↑(n + 1) := degree_X_sub_C a ▸ p.degree_modByMonic_lt this
.trans_le WithBot.coe_le_coe.mpr le_add_self
  simp [q, sub_mul, add_sub, coeff_eq_zero_of_degree_lt this]

/--
theorem `coeff_divByMonic_X_sub_C` / 定理 `coeff_divByMonic_X_sub_C`

English:
theorem coeff_divByMonic_X_sub_C
  given: (p : R[X]) (a : R) (n : Nat)
  proof: by
  wlog h : p.natDegree <= n generalizing n
  · refine Nat.decreasingInduction' (fun n hn _ ih => ?_) (le_of_not_ge h) ?_
    · rw [coeff_divByMonic_X_sub_C_rec, ih, eq_comm, Icc_eq_cons_Ioc (Nat.succ_le_iff.mpr hn),
          sum_cons, Nat.sub_self, pow_zero, one_mul, mul_sum]
      congr 1; refi

中文:
定理 coeff_divByMonic_X_sub_C
  条件: (p : R[X]) (a : R) (n : 自然数)
  证明: by
  wlog h : p.natDegree <= n generalizing n
  · refine Nat.decreasingInduction' (fun n hn _ ih => ?_) (le_of_not_ge h) ?_
    · rw [coeff_divByMonic_X_sub_C_rec, ih, eq_comm, Icc_eq_cons_Ioc (Nat.succ_le_iff.mpr hn),
          sum_cons, Nat.sub_self, pow_zero, one_mul, mul_sum]
      congr 1; refi

Depends on / 依赖: Icc_eq_cons_Ioc, Nat.decreasingInduction, Nat.le_sub_of_add_le, Nat.sub_add_cancel, Nat.sub_self, Nat.succ_le_iff.mpr, add_comm, coeff_divByMonic_X_sub_C_rec, decreasingInduction, eq_comm, generalizing, i.sub_succ, le_of_not_ge, le_rfl, le_sub_of_add_le, mem_Icc, mem_Icc.mp, mul_assoc, mul_sum, natDegree
-/
theorem coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : Nat) :
    (p /ₘ (X - C a)).coeff n = ∑ i in Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i := by
  wlog h : p.natDegree <= n generalizing n
  · refine Nat.decreasingInduction' (fun n hn _ ih => ?_) (le_of_not_ge h) ?_
    · rw [coeff_divByMonic_X_sub_C_rec, ih, eq_comm, Icc_eq_cons_Ioc (Nat.succ_le_iff.mpr hn),
          sum_cons, Nat.sub_self, pow_zero, one_mul, mul_sum]
      congr 1; refine sum_congr ?_ fun i hi => ?_
      · ext; simp
      rw [← mul_assoc]; rw [← pow_succ']; rw [eq_comm]; rw [i.sub_succ']; rw [Nat.sub_add_cancel]
      apply Nat.le_sub_of_add_le
      rw [add_comm]; exact (mem_Icc.mp hi).1
    · exact this _ le_rfl
  rw [Icc_eq_empty (Nat.lt_succ_iff.mpr h).not_ge]; rw [sum_empty]
  nontriviality R
  by_cases hp : p.natDegree = 0
  · rw [(divByMonic_eq_zero_iff <| monic_X_sub_C a).mpr, coeff_zero]
    apply degree_lt_degree; rw [hp, natDegree_X_sub_C]; simp
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_divByMonic p (monic_X_sub_C a)]; rw [natDegree_X_sub_C]
    exact (Nat.pred_lt hp).trans_le h

section multiplicity

/-- An algorithm for deciding polynomial divisibility.
Prefer `Classical.dec`, as the algorithm relies on `%ₘ` and so is `noncomputable`.
-/
@[deprecated Classical.dec (since := "2026-02-07")]
/--
Definition of `decidableDvdMonic` / `decidableDvdMonic` 的定义

English:
definition decidableDvdMonic
  signature: [DecidableEq R] (p : R[X]) (hq : Monic q)
  body: decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)

中文:
定义 decidableDvdMonic
  签名: [DecidableEq R] (p : R[X]) (hq : Monic q)
  定义体: decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)

Depends on / 依赖: decidable_of_iff, modByMonic_eq_zero_iff_dvd
-/
def decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)

/--
theorem `finiteMultiplicity_X_sub_C` / 定理 `finiteMultiplicity_X_sub_C`

English:
theorem finiteMultiplicity_X_sub_C
  given: (a : R) (h0 : p != 0)
  statement: FiniteMultiplicity (X - C a) p
  proof: by
  have := Nontrivial.of_polynomial_ne h0
  refine finiteMultiplicity_of_degree_pos_of_monic ?_ (monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide

中文:
定理 finiteMultiplicity_X_sub_C
  条件: (a : R) (h0 : p != 0)
  结论: FiniteMultiplicity (X - C a) p
  证明: by
  have := Nontrivial.of_polynomial_ne h0
  refine finiteMultiplicity_of_degree_pos_of_monic ?_ (monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide

Depends on / 依赖: Nontrivial, Nontrivial.of_polynomial_ne, degree_X_sub_C, finiteMultiplicity_of_degree_pos_of_monic, monic_X_sub_C, of_polynomial_ne
-/
theorem finiteMultiplicity_X_sub_C (a : R) (h0 : p != 0) : FiniteMultiplicity (X - C a) p := by
  have := Nontrivial.of_polynomial_ne h0
  refine finiteMultiplicity_of_degree_pos_of_monic ?_ (monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide

/- TODO: stripping out classical for decidability instance parameter might
make for better ergonomics -/
/--
Definition of `rootMultiplicity` / `rootMultiplicity` 的定义

English:
definition rootMultiplicity
  signature: (a : R) (p : R[X])
  body: letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : Nat => ¬(X - C a) ^ (n + 1) ∣ p := Classical.decPred _
    Nat.find (finiteMultiplicity_X_sub_C a h0)

中文:
定义 rootMultiplicity
  签名: (a : R) (p : R[X])
  定义体: letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : Nat => ¬(X - C a) ^ (n + 1) ∣ p := Classical.decPred _
    Nat.find (finiteMultiplicity_X_sub_C a h0)

Depends on / 依赖: Classical, Classical.decEq, Classical.decPred, DecidablePred, Nat.find, decPred, finiteMultiplicity_X_sub_C
-/
def rootMultiplicity (a : R) (p : R[X]) : Nat :=
  letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : Nat => ¬(X - C a) ^ (n + 1) ∣ p := Classical.decPred _
    Nat.find (finiteMultiplicity_X_sub_C a h0)

/--
theorem `rootMultiplicity_eq_natFind_of_ne_zero` / 定理 `rootMultiplicity_eq_natFind_of_ne_zero`

English:
theorem rootMultiplicity_eq_natFind_of_ne_zero
  statement: {p : R[X]} (p0 : p != 0) {a : R}
  proof: by
  dsimp [rootMultiplicity]
  rw [dif_neg p0]
  congr

@[deprecated (since := "2026-02-12")]
alias rootMultiplicity_eq_nat_find_of_nonzero := rootMultiplicity_eq_natFind_of_ne_zero

中文:
定理 rootMultiplicity_eq_natFind_of_ne_zero
  结论: {p : R[X]} (p0 : p != 0) {a : R}
  证明: by
  dsimp [rootMultiplicity]
  rw [dif_neg p0]
  congr

@[deprecated (since := "2026-02-12")]
alias rootMultiplicity_eq_nat_find_of_nonzero := rootMultiplicity_eq_natFind_of_ne_zero

Depends on / 依赖: dif_neg, rootMultiplicity
-/
theorem rootMultiplicity_eq_natFind_of_ne_zero {p : R[X]} (p0 : p != 0) {a : R}
    [DecidablePred fun n : Nat => ¬(X - C a) ^ (n + 1) ∣ p] :
    rootMultiplicity a p = Nat.find (finiteMultiplicity_X_sub_C a p0) := by
  dsimp [rootMultiplicity]
  rw [dif_neg p0]
  congr

@[deprecated (since := "2026-02-12")]
alias rootMultiplicity_eq_nat_find_of_nonzero := rootMultiplicity_eq_natFind_of_ne_zero

/--
theorem `rootMultiplicity_eq_multiplicity` / 定理 `rootMultiplicity_eq_multiplicity`

English:
theorem rootMultiplicity_eq_multiplicity
  statement: [DecidableEq R]
  proof: by
  simp only [rootMultiplicity, multiplicity, emultiplicity]
  split
  · rfl
  rename_i h
  simp only [finiteMultiplicity_X_sub_C a h, ↓reduceDIte]
  rw [untopD_coe_enat]
  congr

@[simp]

中文:
定理 rootMultiplicity_eq_multiplicity
  结论: [DecidableEq R]
  证明: by
  simp only [rootMultiplicity, multiplicity, emultiplicity]
  split
  · rfl
  rename_i h
  simp only [finiteMultiplicity_X_sub_C a h, ↓reduceDIte]
  rw [untopD_coe_enat]
  congr

@[simp]

Depends on / 依赖: emultiplicity, finiteMultiplicity_X_sub_C, multiplicity, reduceDIte, rename_i, rootMultiplicity, untopD_coe_enat
-/
theorem rootMultiplicity_eq_multiplicity [DecidableEq R]
    (p : R[X]) (a : R) :
    rootMultiplicity a p =
      if p = 0 then 0 else multiplicity (X - C a) p := by
  simp only [rootMultiplicity, multiplicity, emultiplicity]
  split
  · rfl
  rename_i h
  simp only [finiteMultiplicity_X_sub_C a h, ↓reduceDIte]
  rw [untopD_coe_enat]
  congr

@[simp]
/--
theorem `rootMultiplicity_zero` / 定理 `rootMultiplicity_zero`

English:
theorem rootMultiplicity_zero
  given: {x : R}
  statement: rootMultiplicity x 0 = 0
  proof: dif_pos rfl

@[simp]

中文:
定理 rootMultiplicity_zero
  条件: {x : R}
  结论: rootMultiplicity x 0 = 0
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0 :=
  dif_pos rfl

@[simp]
/--
theorem `rootMultiplicity_C` / 定理 `rootMultiplicity_C`

English:
theorem rootMultiplicity_C
  given: (r a : R)
  statement: rootMultiplicity a (C r) = 0
  proof: by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (C r) 0, rootMultiplicity_zero]
  classical
  rw [rootMultiplicity_eq_multiplicity]
  split_ifs with hr
  · rfl
  have h : natDegree (C r) < natDegree (X - C a) := by simp
  simp_rw [multiplicity_eq_zero.mpr ((monic_X_sub_C a).not_dvd

中文:
定理 rootMultiplicity_C
  条件: (r a : R)
  结论: rootMultiplicity a (C r) = 0
  证明: by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (C r) 0, rootMultiplicity_zero]
  classical
  rw [rootMultiplicity_eq_multiplicity]
  split_ifs with hr
  · rfl
  have h : natDegree (C r) < natDegree (X - C a) := by simp
  simp_rw [multiplicity_eq_zero.mpr ((monic_X_sub_C a).not_dvd

Depends on / 依赖: Subsingleton, Subsingleton.elim, classical, monic_X_sub_C, multiplicity_eq_zero, multiplicity_eq_zero.mpr, natDegree, not_dvd_of_natDegree_lt, rootMultiplicity_eq_multiplicity, rootMultiplicity_zero, simp_rw, split_ifs, subsingleton_or_nontrivial
-/
theorem rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (C r) 0, rootMultiplicity_zero]
  classical
  rw [rootMultiplicity_eq_multiplicity]
  split_ifs with hr
  · rfl
  have h : natDegree (C r) < natDegree (X - C a) := by simp
  simp_rw [multiplicity_eq_zero.mpr ((monic_X_sub_C a).not_dvd_of_natDegree_lt hr h)]

/--
theorem `pow_rootMultiplicity_dvd` / 定理 `pow_rootMultiplicity_dvd`

English:
theorem pow_rootMultiplicity_dvd
  given: (p : R[X]) (a : R)
  statement: (X - C a) ^ rootMultiplicity a p ∣ p
  proof: letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    rw [rootMultiplicity_eq_multiplicity]; rw [if_neg h]; apply pow_multiplicity_dvd

中文:
定理 pow_rootMultiplicity_dvd
  条件: (p : R[X]) (a : R)
  结论: (X - C a) ^ rootMultiplicity a p ∣ p
  证明: letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    rw [rootMultiplicity_eq_multiplicity]; rw [if_neg h]; apply pow_multiplicity_dvd

Depends on / 依赖: Classical, Classical.decEq, if_neg, pow_multiplicity_dvd, rootMultiplicity_eq_multiplicity
-/
theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p :=
  letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    rw [rootMultiplicity_eq_multiplicity]; rw [if_neg h]; apply pow_multiplicity_dvd

/--
theorem `pow_mul_divByMonic_rootMultiplicity_eq` / 定理 `pow_mul_divByMonic_rootMultiplicity_eq`

English:
theorem pow_mul_divByMonic_rootMultiplicity_eq
  given: (p : R[X]) (a : R)
  proof: by
  have : Monic ((X - C a) ^ rootMultiplicity a p) := (monic_X_sub_C _).pow _
  conv_rhs =>
    rw [← modByMonic_add_div p]; rw [(modByMonic_eq_zero_iff_dvd this).2 (pow_rootMultiplicity_dvd _ _)]
  simp

中文:
定理 pow_mul_divByMonic_rootMultiplicity_eq
  条件: (p : R[X]) (a : R)
  证明: by
  have : Monic ((X - C a) ^ rootMultiplicity a p) := (monic_X_sub_C _).pow _
  conv_rhs =>
    rw [← modByMonic_add_div p]; rw [(modByMonic_eq_zero_iff_dvd this).2 (pow_rootMultiplicity_dvd _ _)]
  simp

Depends on / 依赖: conv_rhs, modByMonic_add_div, modByMonic_eq_zero_iff_dvd, monic_X_sub_C, pow_rootMultiplicity_dvd, rootMultiplicity
-/
theorem pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) :
    (X - C a) ^ rootMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p := by
  have : Monic ((X - C a) ^ rootMultiplicity a p) := (monic_X_sub_C _).pow _
  conv_rhs =>
    rw [← modByMonic_add_div p]; rw [(modByMonic_eq_zero_iff_dvd this).2 (pow_rootMultiplicity_dvd _ _)]
  simp

/--
theorem `exists_eq_pow_rootMultiplicity_mul_and_not_dvd` / 定理 `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`

English:
theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd
  given: (p : R[X]) (hp : p != 0) (a : R)
  proof: by
  classical
  rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp]
  apply (finiteMultiplicity_X_sub_C a hp).exists_eq_pow_mul_and_not_dvd

中文:
定理 exists_eq_pow_rootMultiplicity_mul_and_not_dvd
  条件: (p : R[X]) (hp : p != 0) (a : R)
  证明: by
  classical
  rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp]
  apply (finiteMultiplicity_X_sub_C a hp).exists_eq_pow_mul_and_not_dvd

Depends on / 依赖: classical, exists_eq_pow_mul_and_not_dvd, finiteMultiplicity_X_sub_C, if_neg, rootMultiplicity_eq_multiplicity
-/
theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) :
    exists q : R[X], p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) ∣ q := by
  classical
  rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp]
  apply (finiteMultiplicity_X_sub_C a hp).exists_eq_pow_mul_and_not_dvd

end multiplicity

end Ring

section CommRing

variable [CommRing R] {p p₁ p₂ q : R[X]}

@[simp]
/--
theorem `modByMonic_X_sub_C_eq_C_eval` / 定理 `modByMonic_X_sub_C_eq_C_eval`

English:
theorem modByMonic_X_sub_C_eq_C_eval
  given: (p : R[X]) (a : R)
  statement: p %ₘ (X - C a) = C (p.eval a)
  proof: by
  nontriviality R
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div]; rw [eval_sub]; rw [eval_mul]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_self]; rw [zero_mul]; rw [sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByM

中文:
定理 modByMonic_X_sub_C_eq_C_eval
  条件: (p : R[X]) (a : R)
  结论: p %ₘ (X - C a) = C (p.eval a)
  证明: by
  nontriviality R
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div]; rw [eval_sub]; rw [eval_mul]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_self]; rw [zero_mul]; rw [sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByM

Depends on / 依赖: Nat.le_of_lt_succ, WithBot, WithBot.coe_le_coe, WithBot.coe_lt_coe, bot_le, coe_le_coe, coe_lt_coe, degree, degree_X_sub_C, degree_modByMonic_lt, eval_C, eval_X, eval_mul, eval_sub, le_of_lt_succ, modByMonic_eq_sub_mul_div, monic_X_sub_C, nontriviality, p.eval, revert
-/
theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a) := by
  nontriviality R
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div]; rw [eval_sub]; rw [eval_mul]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_self]; rw [zero_mul]; rw [sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByMonic_lt p (monic_X_sub_C a)
  have : degree (p %ₘ (X - C a)) <= 0 := by
    revert this
    cases degree (p %ₘ (X - C a))
    · exact fun _ => bot_le
    · exact fun h => WithBot.coe_le_coe.2 (Nat.le_of_lt_succ (WithBot.coe_lt_coe.1 h))
  rw [eq_C_of_degree_le_zero this]; rw [eval_C] at h
  rw [eq_C_of_degree_le_zero this]; rw [h]

/--
theorem `mul_divByMonic_eq_iff_isRoot` / 定理 `mul_divByMonic_eq_iff_isRoot`

English:
theorem mul_divByMonic_eq_iff_isRoot
  statement: (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
  proof: .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs => rw [← modByMonic_add_div p, modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm

中文:
定理 mul_divByMonic_eq_iff_isRoot
  结论: (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
  证明: .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs => rw [← modByMonic_add_div p, modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm

Depends on / 依赖: IsRoot, IsRoot.def.symm, conv_rhs, eval_C, eval_X, eval_mul, eval_sub, modByMonic_X_sub_C_eq_C_eval, modByMonic_add_div, sub_self, zero_add, zero_mul
-/
theorem mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a :=
  .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs => rw [← modByMonic_add_div p, modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm

/--
theorem `dvd_iff_isRoot` / 定理 `dvd_iff_isRoot`

English:
theorem dvd_iff_isRoot
  statement: X - C a ∣ p ↔ IsRoot p a
  proof: ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩

中文:
定理 dvd_iff_isRoot
  结论: X - C a ∣ p ↔ IsRoot p a
  证明: ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩

Depends on / 依赖: C_inj, modByMonic_X_sub_C_eq_C_eval, modByMonic_eq_zero_iff_dvd, monic_X_sub_C, mul_divByMonic_eq_iff_isRoot
-/
theorem dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a :=
  ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩

/--
theorem `X_sub_C_dvd_sub_C_eval` / 定理 `X_sub_C_dvd_sub_C_eval`

English:
theorem X_sub_C_dvd_sub_C_eval
  statement: X - C a ∣ p - C (p.eval a)
  proof: by
  rw [dvd_iff_isRoot]; rw [IsRoot]; rw [eval_sub]; rw [eval_C]; rw [sub_self]

中文:
定理 X_sub_C_dvd_sub_C_eval
  结论: X - C a ∣ p - C (p.eval a)
  证明: by
  rw [dvd_iff_isRoot]; rw [IsRoot]; rw [eval_sub]; rw [eval_C]; rw [sub_self]

Depends on / 依赖: IsRoot, dvd_iff_isRoot, eval_C, eval_sub, sub_self
-/
theorem X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a) := by
  rw [dvd_iff_isRoot]; rw [IsRoot]; rw [eval_sub]; rw [eval_C]; rw [sub_self]

-- TODO: generalize this to Ring. In general, 0 can be replaced by any element in the center of R.
/--
theorem `modByMonic_X` / 定理 `modByMonic_X`

English:
theorem modByMonic_X
  given: (p : R[X])
  statement: p %ₘ X = C (p.eval 0)
  proof: by
  rw [← modByMonic_X_sub_C_eq_C_eval]; rw [C_0]; rw [sub_zero]

中文:
定理 modByMonic_X
  条件: (p : R[X])
  结论: p %ₘ X = C (p.eval 0)
  证明: by
  rw [← modByMonic_X_sub_C_eq_C_eval]; rw [C_0]; rw [sub_zero]

Depends on / 依赖: modByMonic_X_sub_C_eq_C_eval, sub_zero
-/
theorem modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0) := by
  rw [← modByMonic_X_sub_C_eq_C_eval]; rw [C_0]; rw [sub_zero]

/--
theorem `eval₂_modByMonic_eq_self_of_root` / 定理 `eval₂_modByMonic_eq_self_of_root`

English:
theorem eval₂_modByMonic_eq_self_of_root
  statement: [CommRing S] {f : R ->+* S} {p q : R[X]}
  proof: by
  rw [modByMonic_eq_sub_mul_div]; rw [eval₂_sub]; rw [eval₂_mul]; rw [hx]; rw [zero_mul]; rw [sub_zero]

中文:
定理 eval₂_modByMonic_eq_self_of_root
  结论: [CommRing S] {f : R ->+* S} {p q : R[X]}
  证明: by
  rw [modByMonic_eq_sub_mul_div]; rw [eval₂_sub]; rw [eval₂_mul]; rw [hx]; rw [zero_mul]; rw [sub_zero]

Depends on / 依赖: modByMonic_eq_sub_mul_div, sub_zero, zero_mul
-/
theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R ->+* S} {p q : R[X]}
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by
  rw [modByMonic_eq_sub_mul_div]; rw [eval₂_sub]; rw [eval₂_mul]; rw [hx]; rw [zero_mul]; rw [sub_zero]

/--
theorem `sub_dvd_eval_sub` / 定理 `sub_dvd_eval_sub`

English:
theorem sub_dvd_eval_sub
  given: (a b : R) (p : R[X])
  statement: a - b ∣ p.eval a - p.eval b
  proof: by
  suffices X - C b ∣ p - C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C]
      using (_root_.map_dvd (evalRingHom a)) this
  simp [dvd_iff_isRoot]

中文:
定理 sub_dvd_eval_sub
  条件: (a b : R) (p : R[X])
  结论: a - b ∣ p.eval a - p.eval b
  证明: by
  suffices X - C b ∣ p - C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C]
      using (_root_.map_dvd (evalRingHom a)) this
  simp [dvd_iff_isRoot]

Depends on / 依赖: _root_, _root_.map_dvd, coe_evalRingHom, dvd_iff_isRoot, evalRingHom, eval_C, eval_X, eval_sub, map_dvd, p.eval
-/
theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by
  suffices X - C b ∣ p - C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C]
      using (_root_.map_dvd (evalRingHom a)) this
  simp [dvd_iff_isRoot]

/--
lemma `IsRoot.dvd_coeff_zero` / 引理 `IsRoot.dvd_coeff_zero`

English:
lemma IsRoot.dvd_coeff_zero
  given: {p : R[X]} {x : R} (h : p.IsRoot x)
  statement: x ∣ p.coeff 0
  proof: by
  simpa [h.eq_zero, coeff_zero_eq_eval_zero] using sub_dvd_eval_sub 0 x p

@[simp]

中文:
引理 IsRoot.dvd_coeff_zero
  条件: {p : R[X]} {x : R} (h : p.IsRoot x)
  结论: x ∣ p.coeff 0
  证明: by
  simpa [h.eq_zero, coeff_zero_eq_eval_zero] using sub_dvd_eval_sub 0 x p

@[simp]

Depends on / 依赖: coeff_zero_eq_eval_zero, eq_zero, h.eq_zero, sub_dvd_eval_sub
-/
lemma IsRoot.dvd_coeff_zero {p : R[X]} {x : R} (h : p.IsRoot x) : x ∣ p.coeff 0 := by
  simpa [h.eq_zero, coeff_zero_eq_eval_zero] using sub_dvd_eval_sub 0 x p

@[simp]
/--
theorem `rootMultiplicity_eq_zero_iff` / 定理 `rootMultiplicity_eq_zero_iff`

English:
theorem rootMultiplicity_eq_zero_iff
  given: {p : R[X]} {x : R}
  proof: by
  classical
  simp only [rootMultiplicity_eq_multiplicity, ite_eq_left_iff, multiplicity_eq_zero,
    dvd_iff_isRoot, not_imp_not]

中文:
定理 rootMultiplicity_eq_zero_iff
  条件: {p : R[X]} {x : R}
  证明: by
  classical
  simp only [rootMultiplicity_eq_multiplicity, ite_eq_left_iff, multiplicity_eq_zero,
    dvd_iff_isRoot, not_imp_not]

Depends on / 依赖: classical, dvd_iff_isRoot, ite_eq_left_iff, multiplicity_eq_zero, not_imp_not, rootMultiplicity_eq_multiplicity
-/
theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    rootMultiplicity x p = 0 ↔ IsRoot p x -> p = 0 := by
  classical
  simp only [rootMultiplicity_eq_multiplicity, ite_eq_left_iff, multiplicity_eq_zero,
    dvd_iff_isRoot, not_imp_not]

/--
theorem `rootMultiplicity_eq_zero` / 定理 `rootMultiplicity_eq_zero`

English:
theorem rootMultiplicity_eq_zero
  given: {p : R[X]} {x : R} (h : ¬IsRoot p x)
  statement: rootMultiplicity x p = 0
  proof: rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim

@[simp]

中文:
定理 rootMultiplicity_eq_zero
  条件: {p : R[X]} {x : R} (h : ¬IsRoot p x)
  结论: rootMultiplicity x p = 0
  证明: rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim

@[simp]

Depends on / 依赖: rootMultiplicity_eq_zero_iff
-/
theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0 :=
  rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim

@[simp]
/--
theorem `rootMultiplicity_pos'` / 定理 `rootMultiplicity_pos'`

English:
theorem rootMultiplicity_pos'
  given: {p : R[X]} {x : R}
  proof: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [rootMultiplicity_eq_zero_iff]; rw [Classical.not_imp]; rw [and_comm]

中文:
定理 rootMultiplicity_pos'
  条件: {p : R[X]} {x : R}
  证明: by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [rootMultiplicity_eq_zero_iff]; rw [Classical.not_imp]; rw [and_comm]

Depends on / 依赖: Classical, Classical.not_imp, and_comm, not_imp, pos_iff_ne_zero, rootMultiplicity_eq_zero_iff
-/
theorem rootMultiplicity_pos' {p : R[X]} {x : R} :
    0 < rootMultiplicity x p ↔ p != 0 ∧ IsRoot p x := by
  rw [pos_iff_ne_zero]; rw [Ne]; rw [rootMultiplicity_eq_zero_iff]; rw [Classical.not_imp]; rw [and_comm]

/--
theorem `rootMultiplicity_pos` / 定理 `rootMultiplicity_pos`

English:
theorem rootMultiplicity_pos
  given: {p : R[X]} (hp : p != 0) {x : R}
  proof: rootMultiplicity_pos'.trans (and_iff_right hp)

中文:
定理 rootMultiplicity_pos
  条件: {p : R[X]} (hp : p != 0) {x : R}
  证明: rootMultiplicity_pos'.trans (and_iff_right hp)

Depends on / 依赖: CharZero, IsSemireal, NonAssocRing, and_iff_right, rootMultiplicity_pos
-/
theorem rootMultiplicity_pos {p : R[X]} (hp : p != 0) {x : R} :
    0 < rootMultiplicity x p ↔ IsRoot p x :=
  rootMultiplicity_pos'.trans (and_iff_right hp)

/--
theorem `eval_divByMonic_pow_rootMultiplicity_ne_zero` / 定理 `eval_divByMonic_pow_rootMultiplicity_ne_zero`

English:
theorem eval_divByMonic_pow_rootMultiplicity_ne_zero
  given: {p : R[X]} (a : R) (hp : p != 0)
  proof: by
  classical
  have : Nontrivial R := Nontrivial.of_polynomial_ne hp
  rw [Ne]; rw [← IsRoot]; rw [← dvd_iff_isRoot]
  rintro ⟨q, hq⟩
  have := pow_mul_divByMonic_rootMultiplicity_eq p a
  rw [hq]; rw [← mul_assoc]; rw [← pow_succ]; rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp] at this
  e

中文:
定理 eval_divByMonic_pow_rootMultiplicity_ne_zero
  条件: {p : R[X]} (a : R) (hp : p != 0)
  证明: by
  classical
  have : Nontrivial R := Nontrivial.of_polynomial_ne hp
  rw [Ne]; rw [← IsRoot]; rw [← dvd_iff_isRoot]
  rintro ⟨q, hq⟩
  have := pow_mul_divByMonic_rootMultiplicity_eq p a
  rw [hq]; rw [← mul_assoc]; rw [← pow_succ]; rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp] at this
  e

Depends on / 依赖: IsRoot, Nat.lt_succ_self, Nontrivial, Nontrivial.of_polynomial_ne, WithBot, classical, degree, degree_X_sub_C, dvd_iff_isRoot, dvd_of_mul_right, finiteMultiplicity_of_degree_pos_of_monic, if_neg, lt_succ_self, monic_X_sub_C, mul_assoc, not_pow_dvd_of_multiplicity_lt, of_polynomial_ne, pow_mul_divByMonic_rootMultiplicity_eq, pow_succ, rootMultiplicity_eq_multiplicity
-/
theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p != 0) :
    eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) != 0 := by
  classical
  have : Nontrivial R := Nontrivial.of_polynomial_ne hp
  rw [Ne]; rw [← IsRoot]; rw [← dvd_iff_isRoot]
  rintro ⟨q, hq⟩
  have := pow_mul_divByMonic_rootMultiplicity_eq p a
  rw [hq]; rw [← mul_assoc]; rw [← pow_succ]; rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp] at this
  exact
    (finiteMultiplicity_of_degree_pos_of_monic
      (show (0 : WithBot Nat) < degree (X - C a) by rw [degree_X_sub_C]; decide)
      (monic_X_sub_C _) hp).not_pow_dvd_of_multiplicity_lt
      (Nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)

/-- See `Polynomial.self_mul_modByMonic` for the other multiplication order. This version, unlike
that one, requires commutativity. -/
@[simp]
/--
lemma `mul_self_modByMonic` / 引理 `mul_self_modByMonic`

English:
lemma mul_self_modByMonic
  given: (hq : q.Monic)
  statement: (p * q) %ₘ q = 0
  proof: by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p

中文:
引理 mul_self_modByMonic
  条件: (hq : q.Monic)
  结论: (p * q) %ₘ q = 0
  证明: by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p

Depends on / 依赖: dvd_mul_left, modByMonic_eq_zero_iff_dvd
-/
lemma mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p

/--
lemma `modByMonic_eq_of_dvd_sub` / 引理 `modByMonic_eq_of_dvd_sub`

English:
lemma modByMonic_eq_of_dvd_sub
  given: (hq : q.Monic) (h : q ∣ p₁ - p₂)
  statement: p₁ %ₘ q = p₂ %ₘ q
  proof: by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq]; rw [mul_add]; rw [← add_assoc]; rw [modByMonic_add_div]; rw [add_comm]

中文:
引理 modByMonic_eq_of_dvd_sub
  条件: (hq : q.Monic) (h : q ∣ p₁ - p₂)
  结论: p₁ %ₘ q = p₂ %ₘ q
  证明: by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq]; rw [mul_add]; rw [← add_assoc]; rw [modByMonic_add_div]; rw [add_comm]

Depends on / 依赖: add_assoc, add_comm, degree_modByMonic_lt, div_modByMonic_unique, modByMonic_add_div, mul_add, nontriviality, sub_eq, sub_eq_iff_eq_add, sub_eq_iff_eq_add.mp
-/
lemma modByMonic_eq_of_dvd_sub (hq : q.Monic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq]; rw [mul_add]; rw [← add_assoc]; rw [modByMonic_add_div]; rw [add_comm]

/--
lemma `add_modByMonic` / 引理 `add_modByMonic`

English:
lemma add_modByMonic
  given: (p₁ p₂ : R[X])
  statement: (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q
  proof: by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add]; rw [add_left_comm]; rw [add_assoc]; rw [modByMonic_add_div]; rw [← a

中文:
引理 add_modByMonic
  条件: (p₁ p₂ : R[X])
  结论: (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q
  证明: by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add]; rw [add_left_comm]; rw [add_assoc]; rw [modByMonic_add_div]; rw [← a

Depends on / 依赖: add_assoc, add_comm, add_left_comm, degree_add_le, degree_modByMonic_lt, div_modByMonic_unique, eq_iff_true_of_subsingleton, max_lt, modByMonic_add_div, modByMonic_eq_of_not_monic, mul_add, q.Monic, simp_rw, subsingleton_or_nontrivial, trans_lt
-/
lemma add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add]; rw [add_left_comm]; rw [add_assoc]; rw [modByMonic_add_div]; rw [← add_assoc]; rw [add_comm (q * _)]; rw [modByMonic_add_div],
            (degree_add_le _ _).trans_lt
              (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]

/--
lemma `neg_modByMonic` / 引理 `neg_modByMonic`

English:
lemma neg_modByMonic
  given: (p q : R[X])
  statement: (-p) %ₘ q = -(p %ₘ q)
  proof: by
  rw [eq_neg_iff_add_eq_zero]; rw [← add_modByMonic]; rw [neg_add_cancel]; rw [zero_modByMonic]

中文:
引理 neg_modByMonic
  条件: (p q : R[X])
  结论: (-p) %ₘ q = -(p %ₘ q)
  证明: by
  rw [eq_neg_iff_add_eq_zero]; rw [← add_modByMonic]; rw [neg_add_cancel]; rw [zero_modByMonic]

Depends on / 依赖: add_modByMonic, eq_neg_iff_add_eq_zero, neg_add_cancel, zero_modByMonic
-/
lemma neg_modByMonic (p q : R[X]) : (-p) %ₘ q = -(p %ₘ q) := by
  rw [eq_neg_iff_add_eq_zero]; rw [← add_modByMonic]; rw [neg_add_cancel]; rw [zero_modByMonic]

/--
lemma `sub_modByMonic` / 引理 `sub_modByMonic`

English:
lemma sub_modByMonic
  given: (p₁ p₂ q : R[X])
  statement: (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q
  proof: by
  simp [sub_eq_add_neg, add_modByMonic, neg_modByMonic]

中文:
引理 sub_modByMonic
  条件: (p₁ p₂ q : R[X])
  结论: (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q
  证明: by
  simp [sub_eq_add_neg, add_modByMonic, neg_modByMonic]

Depends on / 依赖: add_modByMonic, neg_modByMonic, sub_eq_add_neg
-/
lemma sub_modByMonic (p₁ p₂ q : R[X]) : (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q := by
  simp [sub_eq_add_neg, add_modByMonic, neg_modByMonic]

/--
lemma `mul_modByMonic` / 引理 `mul_modByMonic`

English:
lemma mul_modByMonic
  given: (p₁ p₂ q : R[X])
  statement: (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q
  proof: by
  by_cases! h : ¬ q.Monic
  · simp [Polynomial.modByMonic_eq_of_not_monic _ h]
  apply Polynomial.modByMonic_eq_of_dvd_sub h
  have : p₁ * p₂ - p₁ %ₘ q * (p₂ %ₘ q) = (p₁ %ₘ q) * (p₂ - p₂ %ₘ q) + p₂ * (p₁ - p₁ %ₘ q) := by ring
  rw [this]
  apply dvd_add
  all_goals
  · apply dvd_mul_of_dvd_right


中文:
引理 mul_modByMonic
  条件: (p₁ p₂ q : R[X])
  结论: (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q
  证明: by
  by_cases! h : ¬ q.Monic
  · simp [Polynomial.modByMonic_eq_of_not_monic _ h]
  apply Polynomial.modByMonic_eq_of_dvd_sub h
  have : p₁ * p₂ - p₁ %ₘ q * (p₂ %ₘ q) = (p₁ %ₘ q) * (p₂ - p₂ %ₘ q) + p₂ * (p₁ - p₁ %ₘ q) := by ring
  rw [this]
  apply dvd_add
  all_goals
  · apply dvd_mul_of_dvd_right


Depends on / 依赖: Polynomial, Polynomial.modByMonic_eq_of_dvd_sub, Polynomial.modByMonic_eq_of_not_monic, Polynomial.modByMonic_eq_sub_mul_div, all_goals, dvd_add, dvd_mul_of_dvd_right, modByMonic_eq_of_dvd_sub, modByMonic_eq_of_not_monic, modByMonic_eq_sub_mul_div, q.Monic
-/
lemma mul_modByMonic (p₁ p₂ q : R[X]) : (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q := by
  by_cases! h : ¬ q.Monic
  · simp [Polynomial.modByMonic_eq_of_not_monic _ h]
  apply Polynomial.modByMonic_eq_of_dvd_sub h
  have : p₁ * p₂ - p₁ %ₘ q * (p₂ %ₘ q) = (p₁ %ₘ q) * (p₂ - p₂ %ₘ q) + p₂ * (p₁ - p₁ %ₘ q) := by ring
  rw [this]
  apply dvd_add
  all_goals
  · apply dvd_mul_of_dvd_right
    simp [Polynomial.modByMonic_eq_sub_mul_div]

/--
lemma `eval_divByMonic_eq_trailingCoeff_comp` / 引理 `eval_divByMonic_eq_trailingCoeff_comp`

English:
lemma eval_divByMonic_eq_trailingCoeff_comp
  given: {p : R[X]} {t : R}
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := p.pow_mul_divByMonic_rootMultiplicity_eq t
  set m := p.rootMultiplicity t
  set g := p /ₘ (X - C t) ^ m
  have : (g.comp (X + C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq

中文:
引理 eval_divByMonic_eq_trailingCoeff_comp
  条件: {p : R[X]} {t : R}
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := p.pow_mul_divByMonic_rootMultiplicity_eq t
  set m := p.rootMultiplicity t
  set g := p /ₘ (X - C t) ^ m
  have : (g.comp (X + C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq

Depends on / 依赖: C_comp, X_comp, add_sub_canc, coeff_zero_eq_eval_zero, congr_arg, eq_or_ne, eval_C, eval_X, eval_add, eval_comp, eval_zero, g.comp, g.eval, mul_comp, mul_eq, p.pow_mul_divByMonic_rootMultiplicity_eq, p.rootMultiplicity, pow_comp, pow_mul_divByMonic_rootMultiplicity_eq, rootMultiplicity
-/
lemma eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} :
    (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t = (p.comp (X + C t)).trailingCoeff := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := p.pow_mul_divByMonic_rootMultiplicity_eq t
  set m := p.rootMultiplicity t
  set g := p /ₘ (X - C t) ^ m
  have : (g.comp (X + C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq_eval_zero]; rw [eval_comp]; rw [eval_add]; rw [eval_X]; rw [eval_C]; rw [zero_add]
  rw [← congr_arg (comp · <| X + C t) mul_eq]; rw [mul_comp]; rw [pow_comp]; rw [sub_comp]; rw [X_comp]; rw [C_comp]; rw [add_sub_cancel_right]; rw [← reverse_leadingCoeff]; rw [reverse_X_pow_mul]; rw [reverse_leadingCoeff]; rw [trailingCoeff]; rw [Nat.le_zero.1 (natTrailingDegree_le_of_ne_zero <|
      this ▸ eval_divByMonic_pow_rootMultiplicity_ne_zero t hp)]; rw [this]

/--
lemma `le_rootMultiplicity_iff` / 引理 `le_rootMultiplicity_iff`

English:
lemma le_rootMultiplicity_iff
  given: (p0 : p != 0) {a : R} {n : Nat}
  proof: by
  simp_rw [rootMultiplicity, dif_neg p0, Nat.le_find_iff, not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  rcases n with - | n
  · rw [pow_zero]
    apply one_dvd
  · exact h n n.lt_succ_self

中文:
引理 le_rootMultiplicity_iff
  条件: (p0 : p != 0) {a : R} {n : 自然数}
  证明: by
  simp_rw [rootMultiplicity, dif_neg p0, Nat.le_find_iff, not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  rcases n with - | n
  · rw [pow_zero]
    apply one_dvd
  · exact h n n.lt_succ_self

Depends on / 依赖: Nat.le_find_iff, dif_neg, le_find_iff, lt_succ_self, n.lt_succ_self, not_not, one_dvd, pow_dvd_pow, pow_zero, rootMultiplicity, simp_rw
-/
lemma le_rootMultiplicity_iff (p0 : p != 0) {a : R} {n : Nat} :
    n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by
  simp_rw [rootMultiplicity, dif_neg p0, Nat.le_find_iff, not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  rcases n with - | n
  · rw [pow_zero]
    apply one_dvd
  · exact h n n.lt_succ_self

/--
lemma `rootMultiplicity_le_iff` / 引理 `rootMultiplicity_le_iff`

English:
lemma rootMultiplicity_le_iff
  given: (p0 : p != 0) (a : R) (n : Nat)
  proof: by
  rw [← (le_rootMultiplicity_iff p0).not]; rw [not_le]; rw [Nat.lt_add_one_iff]

中文:
引理 rootMultiplicity_le_iff
  条件: (p0 : p != 0) (a : R) (n : 自然数)
  证明: by
  rw [← (le_rootMultiplicity_iff p0).not]; rw [not_le]; rw [Nat.lt_add_one_iff]

Depends on / 依赖: Nat.lt_add_one_iff, le_rootMultiplicity_iff, lt_add_one_iff, not_le
-/
lemma rootMultiplicity_le_iff (p0 : p != 0) (a : R) (n : Nat) :
    rootMultiplicity a p <= n ↔ ¬(X - C a) ^ (n + 1) ∣ p := by
  rw [← (le_rootMultiplicity_iff p0).not]; rw [not_le]; rw [Nat.lt_add_one_iff]

/--
lemma `rootMultiplicity_add` / 引理 `rootMultiplicity_add`

English:
lemma rootMultiplicity_add
  given: {p q : R[X]} (a : R) (hzero : p + q != 0)
  proof: by
  rw [le_rootMultiplicity_iff hzero]
  exact min_pow_dvd_add (pow_rootMultiplicity_dvd p a) (pow_rootMultiplicity_dvd q a)

中文:
引理 rootMultiplicity_add
  条件: {p q : R[X]} (a : R) (hzero : p + q != 0)
  证明: by
  rw [le_rootMultiplicity_iff hzero]
  exact min_pow_dvd_add (pow_rootMultiplicity_dvd p a) (pow_rootMultiplicity_dvd q a)

Depends on / 依赖: le_rootMultiplicity_iff, min_pow_dvd_add, pow_rootMultiplicity_dvd
-/
lemma rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q != 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) <= rootMultiplicity a (p + q) := by
  rw [le_rootMultiplicity_iff hzero]
  exact min_pow_dvd_add (pow_rootMultiplicity_dvd p a) (pow_rootMultiplicity_dvd q a)

/--
lemma `le_rootMultiplicity_mul` / 引理 `le_rootMultiplicity_mul`

English:
lemma le_rootMultiplicity_mul
  given: {p q : R[X]} (x : R) (hpq : p * q != 0)
  proof: by
  rw [le_rootMultiplicity_iff hpq]; rw [pow_add]
  gcongr <;> apply pow_rootMultiplicity_dvd

中文:
引理 le_rootMultiplicity_mul
  条件: {p q : R[X]} (x : R) (hpq : p * q != 0)
  证明: by
  rw [le_rootMultiplicity_iff hpq]; rw [pow_add]
  gcongr <;> apply pow_rootMultiplicity_dvd

Depends on / 依赖: le_rootMultiplicity_iff, pow_add, pow_rootMultiplicity_dvd
-/
lemma le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q != 0) :
    rootMultiplicity x p + rootMultiplicity x q <= rootMultiplicity x (p * q) := by
  rw [le_rootMultiplicity_iff hpq]; rw [pow_add]
  gcongr <;> apply pow_rootMultiplicity_dvd

/--
lemma `rootMultiplicity_le_rootMultiplicity_of_dvd` / 引理 `rootMultiplicity_le_rootMultiplicity_of_dvd`

English:
lemma rootMultiplicity_le_rootMultiplicity_of_dvd
  given: {p q : R[X]} (hq : q != 0) (hpq : p ∣ q) (x : R)
  proof: by
  obtain ⟨_, rfl⟩ := hpq
exact Nat.le_of_add_right_le le_rootMultiplicity_mul x hq

中文:
引理 rootMultiplicity_le_rootMultiplicity_of_dvd
  条件: {p q : R[X]} (hq : q != 0) (hpq : p ∣ q) (x : R)
  证明: by
  obtain ⟨_, rfl⟩ := hpq
exact Nat.le_of_add_right_le le_rootMultiplicity_mul x hq

Depends on / 依赖: Nat.le_of_add_right_le, le_of_add_right_le, le_rootMultiplicity_mul
-/
lemma rootMultiplicity_le_rootMultiplicity_of_dvd {p q : R[X]} (hq : q != 0) (hpq : p ∣ q) (x : R) :
    p.rootMultiplicity x <= q.rootMultiplicity x := by
  obtain ⟨_, rfl⟩ := hpq
exact Nat.le_of_add_right_le le_rootMultiplicity_mul x hq

/--
lemma `pow_rootMultiplicity_not_dvd` / 引理 `pow_rootMultiplicity_not_dvd`

English:
lemma pow_rootMultiplicity_not_dvd
  given: (p0 : p != 0) (a : R)
  proof: by rw [← rootMultiplicity_le_iff p0]

中文:
引理 pow_rootMultiplicity_not_dvd
  条件: (p0 : p != 0) (a : R)
  证明: by rw [← rootMultiplicity_le_iff p0]

Depends on / 依赖: rootMultiplicity_le_iff
-/
lemma pow_rootMultiplicity_not_dvd (p0 : p != 0) (a : R) :
    ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p := by rw [← rootMultiplicity_le_iff p0]

/--
lemma `rootMultiplicity_eq_natTrailingDegree'` / 引理 `rootMultiplicity_eq_natTrailingDegree'`

English:
lemma rootMultiplicity_eq_natTrailingDegree'
  statement: p.rootMultiplicity 0 = p.natTrailingDegree
  proof: by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
fun h' => trailingCoeff_nonzero_iff_nonzero.2 h h' Nat.lt_add_one _⟩
 

中文:
引理 rootMultiplicity_eq_natTrailingDegree'
  结论: p.rootMultiplicity 0 = p.natTrailingDegree
  证明: by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
fun h' => trailingCoeff_nonzero_iff_nonzero.2 h h' Nat.lt_add_one _⟩
 

Depends on / 依赖: Nat.lt_add_one, X_pow_dvd_iff, coeff_eq_zero_of_lt_natTrailingDegree, le_antisymm, le_rootMultiplicity_iff, lt_add_one, map_zero, natTrailingDegree, natTrailingDegree_zero, not_forall, p.natTrailingDegree, rootMultiplicity_le_iff, rootMultiplicity_zero, sub_zero, trailingCoeff_nonzero_iff_nonzero
-/
lemma rootMultiplicity_eq_natTrailingDegree' : p.rootMultiplicity 0 = p.natTrailingDegree := by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
fun h' => trailingCoeff_nonzero_iff_nonzero.2 h h' Nat.lt_add_one _⟩
  · rw [le_rootMultiplicity_iff h, map_zero, sub_zero, X_pow_dvd_iff]
    exact fun _ => coeff_eq_zero_of_lt_natTrailingDegree

/--
lemma `leadingCoeff_divByMonic_of_monic` / 引理 `leadingCoeff_divByMonic_of_monic`

English:
lemma leadingCoeff_divByMonic_of_monic
  statement: (hmonic : q.Monic)
  proof: by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff != 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p q]
  rw [leadingCoeff_add_of_degree_lt]; rw [leadingCoeff_monic_mul hm

中文:
引理 leadingCoeff_divByMonic_of_monic
  结论: (hmonic : q.Monic)
  证明: by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff != 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p q]
  rw [leadingCoeff_add_of_degree_lt]; rw [leadingCoeff_monic_mul hm

Depends on / 依赖: Nat.WithBot.one_le_iff_zero_lt, WithBot, degree_add_divByMonic, degree_modByMonic_lt, degree_mul, divByMonic_eq_zero_iff, hdegree, hmonic, hmonic.leadingCoeff, leadingCoeff, leadingCoeff_add_of_degree_lt, leadingCoeff_monic_mul, modByMonic_add_div, nontriviality, nth_rw, one_le_iff_zero_lt, q.leadingCoeff, trans_le
-/
lemma leadingCoeff_divByMonic_of_monic (hmonic : q.Monic)
    (hdegree : q.degree <= p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff != 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p q]
  rw [leadingCoeff_add_of_degree_lt]; rw [leadingCoeff_monic_mul hmonic]
  rw [degree_mul' h]; rw [degree_add_divByMonic hmonic hdegree]
  exact (degree_modByMonic_lt p hmonic).trans_le hdegree

variable [IsDomain R]

/--
lemma `degree_eq_one_of_irreducible_of_root` / 引理 `degree_eq_one_of_irreducible_of_root`

English:
lemma degree_eq_one_of_irreducible_of_root
  given: (hi : Irreducible p) {x : R} (hx : IsRoot p x)
  proof: let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))

中文:
引理 degree_eq_one_of_irreducible_of_root
  条件: (hi : Irreducible p) {x : R} (hx : IsRoot p x)
  证明: let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))

Depends on / 依赖: IsUnit, absurd, add_zero, degree, degree_X_sub_C, degree_eq_zero_of_isUnit, degree_mul, dvd_iff_isRoot, hi.isUnit_or_isUnit, isUnit_or_isUnit, this.elim
-/
lemma degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_isUnit hgu, add_zero]

/--
lemma `_root_.Irreducible.not_isRoot_of_natDegree_ne_one` / 引理 `_root_.Irreducible.not_isRoot_of_natDegree_ne_one`

English:
lemma _root_.Irreducible.not_isRoot_of_natDegree_ne_one
  proof: fun hr => hdeg natDegree_eq_of_degree_eq_some degree_eq_one_of_irreducible_of_root hi hr

中文:
引理 _root_.Irreducible.not_isRoot_of_natDegree_ne_one
  证明: fun hr => hdeg natDegree_eq_of_degree_eq_some degree_eq_one_of_irreducible_of_root hi hr

Depends on / 依赖: degree_eq_one_of_irreducible_of_root, natDegree_eq_of_degree_eq_some
-/
lemma _root_.Irreducible.not_isRoot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree != 1) {x : R} : ¬p.IsRoot x :=
fun hr => hdeg natDegree_eq_of_degree_eq_some degree_eq_one_of_irreducible_of_root hi hr

/--
lemma `_root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one` / 引理 `_root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one`

English:
lemma _root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one
  proof: le_bot_iff.mp fun _ => hi.not_isRoot_of_natDegree_ne_one hdeg

中文:
引理 _root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one
  证明: le_bot_iff.mp fun _ => hi.not_isRoot_of_natDegree_ne_one hdeg

Depends on / 依赖: hi.not_isRoot_of_natDegree_ne_one, le_bot_iff, le_bot_iff.mp, not_isRoot_of_natDegree_ne_one
-/
lemma _root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree != 1) : p.IsRoot = ⊥ :=
  le_bot_iff.mp fun _ => hi.not_isRoot_of_natDegree_ne_one hdeg

/--
lemma `_root_.Irreducible.subsingleton_isRoot` / 引理 `_root_.Irreducible.subsingleton_isRoot`

English:
lemma _root_.Irreducible.subsingleton_isRoot
  proof: fun _ hx => (subsingleton_isRoot_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hi hx) hx

中文:
引理 _root_.Irreducible.subsingleton_isRoot
  证明: fun _ hx => (subsingleton_isRoot_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hi hx) hx

Depends on / 依赖: degree_eq_one_of_irreducible_of_root, natDegree_eq_of_degree_eq_some, subsingleton_isRoot_of_natDegree_eq_one
-/
lemma _root_.Irreducible.subsingleton_isRoot
    (hi : Irreducible p) : { x | p.IsRoot x }.Subsingleton :=
  fun _ hx => (subsingleton_isRoot_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hi hx) hx

/--
lemma `leadingCoeff_divByMonic_X_sub_C` / 引理 `leadingCoeff_divByMonic_X_sub_C`

English:
lemma leadingCoeff_divByMonic_X_sub_C
  given: (p : R[X]) (hp : degree p != 0) (a : R)
  proof: by
  nontriviality
  rcases hp.lt_or_gt with hd | hd
  · rw [degree_eq_bot.mp <| Nat.WithBot.lt_zero_iff.mp hd, zero_divByMonic]
  refine leadingCoeff_divByMonic_of_monic (monic_X_sub_C a) ?_
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]

中文:
引理 leadingCoeff_divByMonic_X_sub_C
  条件: (p : R[X]) (hp : degree p != 0) (a : R)
  证明: by
  nontriviality
  rcases hp.lt_or_gt with hd | hd
  · rw [degree_eq_bot.mp <| Nat.WithBot.lt_zero_iff.mp hd, zero_divByMonic]
  refine leadingCoeff_divByMonic_of_monic (monic_X_sub_C a) ?_
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]

Depends on / 依赖: Nat.WithBot.lt_zero_iff.mp, Nat.WithBot.one_le_iff_zero_lt, WithBot, degree_X_sub_C, degree_eq_bot, degree_eq_bot.mp, hp.lt_or_gt, leadingCoeff_divByMonic_of_monic, lt_or_gt, lt_zero_iff, monic_X_sub_C, nontriviality, one_le_iff_zero_lt, zero_divByMonic
-/
lemma leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p != 0) (a : R) :
    leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p := by
  nontriviality
  rcases hp.lt_or_gt with hd | hd
  · rw [degree_eq_bot.mp <| Nat.WithBot.lt_zero_iff.mp hd, zero_divByMonic]
  refine leadingCoeff_divByMonic_of_monic (monic_X_sub_C a) ?_
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]

/--
lemma `eq_of_dvd_of_natDegree_le_of_leadingCoeff` / 引理 `eq_of_dvd_of_natDegree_le_of_leadingCoeff`

English:
lemma eq_of_dvd_of_natDegree_le_of_leadingCoeff
  statement: {p q : R[X]} (hpq : p ∣ q)
  proof: by
  rcases eq_or_ne q 0 with rfl | hq
  · simpa using h₂
  replace h₁ := (natDegree_le_of_dvd hpq hq).antisymm h₁
  obtain ⟨u, rfl⟩ := hpq
  rw [mul_ne_zero_iff] at hq
  rw [natDegree_mul hq.1 hq.2]; rw [left_eq_add] at h₁
  rw [eq_C_of_natDegree_eq_zero h₁]; rw [leadingCoeff_mul]; rw [leadingCoeff

中文:
引理 eq_of_dvd_of_natDegree_le_of_leadingCoeff
  结论: {p q : R[X]} (hpq : p ∣ q)
  证明: by
  rcases eq_or_ne q 0 with rfl | hq
  · simpa using h₂
  replace h₁ := (natDegree_le_of_dvd hpq hq).antisymm h₁
  obtain ⟨u, rfl⟩ := hpq
  rw [mul_ne_zero_iff] at hq
  rw [natDegree_mul hq.1 hq.2]; rw [left_eq_add] at h₁
  rw [eq_C_of_natDegree_eq_zero h₁]; rw [leadingCoeff_mul]; rw [leadingCoeff

Depends on / 依赖: antisymm, eq_C_of_natDegree_eq_zero, eq_comm, eq_or_ne, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, left_eq_add, map_one, mul_ne_zero_iff, mul_one, natDegree_le_of_dvd, natDegree_mul, replace
-/
lemma eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree <= p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) :
    p = q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simpa using h₂
  replace h₁ := (natDegree_le_of_dvd hpq hq).antisymm h₁
  obtain ⟨u, rfl⟩ := hpq
  rw [mul_ne_zero_iff] at hq
  rw [natDegree_mul hq.1 hq.2]; rw [left_eq_add] at h₁
  rw [eq_C_of_natDegree_eq_zero h₁]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [eq_comm]; rw [mul_eq_left₀ (leadingCoeff_ne_zero.mpr hq.1)] at h₂
  rw [eq_C_of_natDegree_eq_zero h₁]; rw [h₂]; rw [map_one]; rw [mul_one]

/--
lemma `associated_of_dvd_of_natDegree_le_of_leadingCoeff` / 引理 `associated_of_dvd_of_natDegree_le_of_leadingCoeff`

English:
lemma associated_of_dvd_of_natDegree_le_of_leadingCoeff
  statement: {p q : R[X]} (hpq : p ∣ q)
  proof: have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

中文:
引理 associated_of_dvd_of_natDegree_le_of_leadingCoeff
  结论: {p q : R[X]} (hpq : p ∣ q)
  证明: have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

Depends on / 依赖: C.toMonoidHom, Units.map, Units.mul_right_dvd, associated_of_dvd_dvd, eq_of_dvd_of_natDegree_le_of_leadingCoeff, leadingCoeff, leadingCoeff_mul, mul_right_dvd, natDegree_mul_C, toMonoidHom
-/
lemma associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree <= p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) :
    Associated p q :=
  have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

/--
lemma `associated_of_dvd_of_natDegree_le` / 引理 `associated_of_dvd_of_natDegree_le`

English:
lemma associated_of_dvd_of_natDegree_le
  statement: {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q != 0)
  proof: associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))

中文:
引理 associated_of_dvd_of_natDegree_le
  结论: {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q != 0)
  证明: associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))

Depends on / 依赖: IsUnit, IsUnit.dvd, associated_of_dvd_of_natDegree_le_of_leadingCoeff, isUnit_iff_ne_zero, leadingCoeff_ne_zero
-/
lemma associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q != 0)
    (h₁ : q.natDegree <= p.natDegree) : Associated p q :=
  associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))

/--
lemma `associated_of_dvd_of_degree_eq` / 引理 `associated_of_dvd_of_degree_eq`

English:
lemma associated_of_dvd_of_degree_eq
  statement: {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
  proof: (Classical.em (q = 0)).elim (fun hq => (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

中文:
引理 associated_of_dvd_of_degree_eq
  结论: {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
  证明: (Classical.em (q = 0)).elim (fun hq => (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

Depends on / 依赖: Associated, Associated.refl, Classical, Classical.em, associated_of_dvd_of_natDegree_le, natDegree_le_natDegree
-/
lemma associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
    (h₁ : p.degree = q.degree) : Associated p q :=
  (Classical.em (q = 0)).elim (fun hq => (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

/--
lemma `eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le` / 引理 `eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le`

English:
lemma eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
  statement: {R} [CommSemiring R] {p q : R[X]}
  proof: by
  rw [mul_comm]; rw [← eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]

中文:
引理 eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
  结论: {R} [CommSemiring R] {p q : R[X]}
  证明: by
  rw [mul_comm]; rw [← eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]

Depends on / 依赖: eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le, mul_comm
-/
lemma eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommSemiring R] {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree <= p.natDegree) :
    q = C q.leadingCoeff * p := by
  rw [mul_comm]; rw [← eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]

end CommRing

end Polynomial
