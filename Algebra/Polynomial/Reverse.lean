/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`. Applying `reverse` to a polynomial `f : R[X]` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.natDegree * f(1/X)`.

The main result is that `reverse (f * g) = reverse f * reverse g`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

@[expose] public section


namespace Polynomial

open Finsupp Finset

open scoped Polynomial

section Semiring

variable {R : Type*} [Semiring R] {f : R[X]}

/--
Definition of `revAtFun` / `revAtFun` 的定义

English:
definition revAtFun
  signature: (N i : Nat)
  body: ite (i <= N) (N - i) i

中文:
定义 revAtFun
  签名: (N i : 自然数)
  定义体: ite (i <= N) (N - i) i
-/
def revAtFun (N i : Nat) : Nat :=
  ite (i <= N) (N - i) i

/--
theorem `revAtFun_invol` / 定理 `revAtFun_invol`

English:
theorem revAtFun_invol
  given: {N i : Nat}
  statement: revAtFun N (revAtFun N i) = i
  proof: by
  unfold revAtFun
  grind

中文:
定理 revAtFun_invol
  条件: {N i : 自然数}
  结论: revAtFun N (revAtFun N i) = i
  证明: by
  unfold revAtFun
  grind

Depends on / 依赖: revAtFun
-/
theorem revAtFun_invol {N i : Nat} : revAtFun N (revAtFun N i) = i := by
  unfold revAtFun
  grind

/--
theorem `revAtFun_inj` / 定理 `revAtFun_inj`

English:
theorem revAtFun_inj
  given: {N : Nat}
  statement: Function.Injective (revAtFun N)
  proof: by
  intro a b hab
  rw [← @revAtFun_invol N a]; rw [hab]; rw [revAtFun_invol]

中文:
定理 revAtFun_inj
  条件: {N : 自然数}
  结论: Function.Injective (revAtFun N)
  证明: by
  intro a b hab
  rw [← @revAtFun_invol N a]; rw [hab]; rw [revAtFun_invol]

Depends on / 依赖: revAtFun_invol
-/
theorem revAtFun_inj {N : Nat} : Function.Injective (revAtFun N) := by
  intro a b hab
  rw [← @revAtFun_invol N a]; rw [hab]; rw [revAtFun_invol]

/--
Definition of `revAt` / `revAt` 的定义

English:
definition revAt
  signature: (N : Nat)
  body: ite (i <= N) (N - i) i
  inj' := revAtFun_inj

中文:
定义 revAt
  签名: (N : 自然数)
  定义体: ite (i <= N) (N - i) i
  inj' := revAtFun_inj
-/
def revAt (N : Nat) : Function.Embedding Nat Nat where
  toFun i := ite (i <= N) (N - i) i
  inj' := revAtFun_inj

/-- We prefer to use the bundled `revAt` over unbundled `revAtFun`. -/
@[simp]
/--
theorem `revAtFun_eq` / 定理 `revAtFun_eq`

English:
theorem revAtFun_eq
  given: (N i : Nat)
  statement: revAtFun N i = revAt N i
  proof: rfl

@[simp, grind =]

中文:
定理 revAtFun_eq
  条件: (N i : 自然数)
  结论: revAtFun N i = revAt N i
  证明: rfl

@[simp, grind =]
-/
theorem revAtFun_eq (N i : Nat) : revAtFun N i = revAt N i :=
  rfl

@[simp, grind =]
/--
theorem `revAt_invol` / 定理 `revAt_invol`

English:
theorem revAt_invol
  given: {N i : Nat}
  statement: (revAt N) (revAt N i) = i
  proof: revAtFun_invol

@[simp]

中文:
定理 revAt_invol
  条件: {N i : 自然数}
  结论: (revAt N) (revAt N i) = i
  证明: revAtFun_invol

@[simp]

Depends on / 依赖: revAtFun_invol
-/
theorem revAt_invol {N i : Nat} : (revAt N) (revAt N i) = i :=
  revAtFun_invol

@[simp]
/--
theorem `revAt_le` / 定理 `revAt_le`

English:
theorem revAt_le
  given: {N i : Nat} (H : i <= N)
  statement: revAt N i = N - i
  proof: if_pos H

中文:
定理 revAt_le
  条件: {N i : 自然数} (H : i <= N)
  结论: revAt N i = N - i
  证明: if_pos H

Depends on / 依赖: if_pos
-/
theorem revAt_le {N i : Nat} (H : i <= N) : revAt N i = N - i :=
  if_pos H

set_option backward.isDefEq.respectTransparency false in
/--
lemma `revAt_eq_self_of_lt` / 引理 `revAt_eq_self_of_lt`

English:
lemma revAt_eq_self_of_lt
  given: {N i : Nat} (h : N < i)
  statement: revAt N i = i
  proof: by simp [revAt, Nat.not_le.mpr h]

中文:
引理 revAt_eq_self_of_lt
  条件: {N i : 自然数} (h : N < i)
  结论: revAt N i = i
  证明: by simp [revAt, Nat.not_le.mpr h]

Depends on / 依赖: Nat.not_le.mpr, not_le
-/
lemma revAt_eq_self_of_lt {N i : Nat} (h : N < i) : revAt N i = i := by simp [revAt, Nat.not_le.mpr h]

/--
theorem `revAt_add` / 定理 `revAt_add`

English:
theorem revAt_add
  given: {N O n o : Nat} (hn : n <= N) (ho : o <= O)
  proof: by
  rcases Nat.le.dest hn with ⟨n', rfl⟩
  rcases Nat.le.dest ho with ⟨o', rfl⟩
  repeat' rw [revAt_le (le_add_right rfl.le)]
  rw [add_assoc]; rw [add_left_comm n' o]; rw [← add_assoc]; rw [revAt_le (le_add_right rfl.le)]
  repeat' rw [add_tsub_cancel_left]

中文:
定理 revAt_add
  条件: {N O n o : 自然数} (hn : n <= N) (ho : o <= O)
  证明: by
  rcases Nat.le.dest hn with ⟨n', rfl⟩
  rcases Nat.le.dest ho with ⟨o', rfl⟩
  repeat' rw [revAt_le (le_add_right rfl.le)]
  rw [add_assoc]; rw [add_left_comm n' o]; rw [← add_assoc]; rw [revAt_le (le_add_right rfl.le)]
  repeat' rw [add_tsub_cancel_left]

Depends on / 依赖: Nat.le.dest, add_assoc, add_left_comm, add_tsub_cancel_left, le_add_right, repeat, revAt_le, rfl.le
-/
theorem revAt_add {N O n o : Nat} (hn : n <= N) (ho : o <= O) :
    revAt (N + O) (n + o) = revAt N n + revAt O o := by
  rcases Nat.le.dest hn with ⟨n', rfl⟩
  rcases Nat.le.dest ho with ⟨o', rfl⟩
  repeat' rw [revAt_le (le_add_right rfl.le)]
  rw [add_assoc]; rw [add_left_comm n' o]; rw [← add_assoc]; rw [revAt_le (le_add_right rfl.le)]
  repeat' rw [add_tsub_cancel_left]

/--
theorem `revAt_zero` / 定理 `revAt_zero`

English:
theorem revAt_zero
  given: (N : Nat)
  statement: revAt N 0 = N
  proof: by simp

中文:
定理 revAt_zero
  条件: (N : 自然数)
  结论: revAt N 0 = N
  证明: by simp
-/
theorem revAt_zero (N : Nat) : revAt N 0 = N := by simp

/--
Definition of `reflect` / `reflect` 的定义

English:
definition reflect
  signature: (N : Nat)

中文:
定义 reflect
  签名: (N : 自然数)
-/
noncomputable def reflect (N : Nat) : R[X] -> R[X]
| ⟨f⟩ => ⟨.ofCoeff f.coeff.embDomain (revAt N)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `reflect_support` / 定理 `reflect_support`

English:
theorem reflect_support
  given: (N : Nat) (f : R[X])
  proof: by cases f; ext1; simp [reflect]

@[simp, grind =]

中文:
定理 reflect_support
  条件: (N : 自然数) (f : R[X])
  证明: by cases f; ext1; simp [reflect]

@[simp, grind =]

Depends on / 依赖: reflect
-/
theorem reflect_support (N : Nat) (f : R[X]) :
    (reflect N f).support = Finset.image (revAt N) f.support := by cases f; ext1; simp [reflect]

@[simp, grind =]
/--
theorem `coeff_reflect` / 定理 `coeff_reflect`

English:
theorem coeff_reflect
  given: (N : Nat) (f : R[X]) (i : Nat)
  statement: coeff (reflect N f) i = f.coeff (revAt N i)
  proof: by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    f.coeff.embDomain (revAt N) i
      = f.coeff.embDomain (revAt N) (revAt N (revAt N i)) := by rw [revAt_invol]
    _ = f.coeff (revAt N i) := Finsupp.embDomain_apply_self _ _ _

中文:
定理 coeff_reflect
  条件: (N : 自然数) (f : R[X]) (i : 自然数)
  结论: coeff (reflect N f) i = f.coeff (revAt N i)
  证明: by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    f.coeff.embDomain (revAt N) i
      = f.coeff.embDomain (revAt N) (revAt N (revAt N i)) := by rw [revAt_invol]
    _ = f.coeff (revAt N i) := Finsupp.embDomain_apply_self _ _ _

Depends on / 依赖: Finsupp, Finsupp.embDomain_apply_self, embDomain, embDomain_apply_self, f.coeff, f.coeff.embDomain, reflect, revAt_invol
-/
theorem coeff_reflect (N : Nat) (f : R[X]) (i : Nat) : coeff (reflect N f) i = f.coeff (revAt N i) := by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    f.coeff.embDomain (revAt N) i
      = f.coeff.embDomain (revAt N) (revAt N (revAt N i)) := by rw [revAt_invol]
    _ = f.coeff (revAt N i) := Finsupp.embDomain_apply_self _ _ _

/--
lemma `reflect_reflect` / 引理 `reflect_reflect`

English:
lemma reflect_reflect
  given: {N : Nat} {p : R[X]}
  statement: (p.reflect N).reflect N = p
  proof: by ext; simp

@[simp]

中文:
引理 reflect_reflect
  条件: {N : 自然数} {p : R[X]}
  结论: (p.reflect N).reflect N = p
  证明: by ext; simp

@[simp]
-/
@[simp] lemma reflect_reflect {N : Nat} {p : R[X]} : (p.reflect N).reflect N = p := by ext; simp

@[simp]
/--
theorem `reflect_zero` / 定理 `reflect_zero`

English:
theorem reflect_zero
  given: {N : Nat}
  statement: reflect N (0 : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 reflect_zero
  条件: {N : 自然数}
  结论: reflect N (0 : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem reflect_zero {N : Nat} : reflect N (0 : R[X]) = 0 :=
  rfl

@[simp]
/--
lemma `reflect_eq_zero_iff` / 引理 `reflect_eq_zero_iff`

English:
lemma reflect_eq_zero_iff
  given: {N : Nat} {f : R[X]}
  statement: reflect N (f : R[X]) = 0 ↔ f = 0
  proof: by simp [reflect]

@[simp]

中文:
引理 reflect_eq_zero_iff
  条件: {N : 自然数} {f : R[X]}
  结论: reflect N (f : R[X]) = 0 ↔ f = 0
  证明: by simp [reflect]

@[simp]

Depends on / 依赖: reflect
-/
lemma reflect_eq_zero_iff {N : Nat} {f : R[X]} : reflect N (f : R[X]) = 0 ↔ f = 0 := by simp [reflect]

@[simp]
/--
theorem `reflect_add` / 定理 `reflect_add`

English:
theorem reflect_add
  given: (f g : R[X]) (N : Nat)
  statement: reflect N (f + g) = reflect N f + reflect N g
  proof: by
  ext
  simp only [coeff_add, coeff_reflect]

@[simp]

中文:
定理 reflect_add
  条件: (f g : R[X]) (N : 自然数)
  结论: reflect N (f + g) = reflect N f + reflect N g
  证明: by
  ext
  simp only [coeff_add, coeff_reflect]

@[simp]

Depends on / 依赖: coeff_add, coeff_reflect
-/
theorem reflect_add (f g : R[X]) (N : Nat) : reflect N (f + g) = reflect N f + reflect N g := by
  ext
  simp only [coeff_add, coeff_reflect]

@[simp]
/--
theorem `reflect_C_mul` / 定理 `reflect_C_mul`

English:
theorem reflect_C_mul
  given: (f : R[X]) (r : R) (N : Nat)
  statement: reflect N (C r * f) = C r * reflect N f
  proof: by
  ext
  simp only [coeff_reflect, coeff_C_mul]

中文:
定理 reflect_C_mul
  条件: (f : R[X]) (r : R) (N : 自然数)
  结论: reflect N (C r * f) = C r * reflect N f
  证明: by
  ext
  simp only [coeff_reflect, coeff_C_mul]

Depends on / 依赖: coeff_C_mul, coeff_reflect
-/
theorem reflect_C_mul (f : R[X]) (r : R) (N : Nat) : reflect N (C r * f) = C r * reflect N f := by
  ext
  simp only [coeff_reflect, coeff_C_mul]

/--
theorem `reflect_C_mul_X_pow` / 定理 `reflect_C_mul_X_pow`

English:
theorem reflect_C_mul_X_pow
  given: (N n : Nat) {c : R}
  statement: reflect N (C c * X ^ n) = C c * X ^ revAt N n
  proof: by
  ext
  grind

@[simp]

中文:
定理 reflect_C_mul_X_pow
  条件: (N n : 自然数) {c : R}
  结论: reflect N (C c * X ^ n) = C c * X ^ revAt N n
  证明: by
  ext
  grind

@[simp]
-/
theorem reflect_C_mul_X_pow (N n : Nat) {c : R} : reflect N (C c * X ^ n) = C c * X ^ revAt N n := by
  ext
  grind

@[simp]
/--
theorem `reflect_C` / 定理 `reflect_C`

English:
theorem reflect_C
  given: (r : R) (N : Nat)
  statement: reflect N (C r) = C r * X ^ N
  proof: by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, reflect_C_mul_X_pow, revAt_zero]

@[simp]

中文:
定理 reflect_C
  条件: (r : R) (N : 自然数)
  结论: reflect N (C r) = C r * X ^ N
  证明: by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, reflect_C_mul_X_pow, revAt_zero]

@[simp]

Depends on / 依赖: conv_lhs, mul_one, pow_zero, reflect_C_mul_X_pow, revAt_zero
-/
theorem reflect_C (r : R) (N : Nat) : reflect N (C r) = C r * X ^ N := by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, reflect_C_mul_X_pow, revAt_zero]

@[simp]
/--
theorem `reflect_monomial` / 定理 `reflect_monomial`

English:
theorem reflect_monomial
  given: (N n : Nat)
  statement: reflect N ((X : R[X]) ^ n) = X ^ revAt N n
  proof: by
  rw [← one_mul (X ^ n)]; rw [← one_mul (X ^ revAt N n)]; rw [← C_1]; rw [reflect_C_mul_X_pow]

中文:
定理 reflect_monomial
  条件: (N n : 自然数)
  结论: reflect N ((X : R[X]) ^ n) = X ^ revAt N n
  证明: by
  rw [← one_mul (X ^ n)]; rw [← one_mul (X ^ revAt N n)]; rw [← C_1]; rw [reflect_C_mul_X_pow]

Depends on / 依赖: one_mul, reflect_C_mul_X_pow
-/
theorem reflect_monomial (N n : Nat) : reflect N ((X : R[X]) ^ n) = X ^ revAt N n := by
  rw [← one_mul (X ^ n)]; rw [← one_mul (X ^ revAt N n)]; rw [← C_1]; rw [reflect_C_mul_X_pow]

/--
lemma `reflect_one_X` / 引理 `reflect_one_X`

English:
lemma reflect_one_X
  statement: reflect 1 (X : R[X]) = 1
  proof: by
  simpa using reflect_monomial 1 1 (R := R)

中文:
引理 reflect_one_X
  结论: reflect 1 (X : R[X]) = 1
  证明: by
  simpa using reflect_monomial 1 1 (R := R)
-/
@[simp] lemma reflect_one_X : reflect 1 (X : R[X]) = 1 := by
  simpa using reflect_monomial 1 1 (R := R)

/--
lemma `reflect_map` / 引理 `reflect_map`

English:
lemma reflect_map
  given: {S : Type*} [Semiring S] (f : R ->+* S) (p : R[X]) (n : Nat)
  proof: by
  ext; simp

@[simp]

中文:
引理 reflect_map
  条件: {S : 类型} [Semiring S] (f : R ->+* S) (p : R[X]) (n : 自然数)
  证明: by
  ext; simp

@[simp]
-/
lemma reflect_map {S : Type*} [Semiring S] (f : R ->+* S) (p : R[X]) (n : Nat) :
    (p.map f).reflect n = (p.reflect n).map f := by
  ext; simp

@[simp]
/--
lemma `reflect_one` / 引理 `reflect_one`

English:
lemma reflect_one
  given: (n : Nat)
  statement: (1 : R[X]).reflect n = Polynomial.X ^ n
  proof: by
  rw [← C.map_one]; rw [reflect_C]; rw [map_one]; rw [one_mul]

中文:
引理 reflect_one
  条件: (n : 自然数)
  结论: (1 : R[X]).reflect n = Polynomial.X ^ n
  证明: by
  rw [← C.map_one]; rw [reflect_C]; rw [map_one]; rw [one_mul]

Depends on / 依赖: C.map_one, map_one, one_mul, reflect_C
-/
lemma reflect_one (n : Nat) : (1 : R[X]).reflect n = Polynomial.X ^ n := by
  rw [← C.map_one]; rw [reflect_C]; rw [map_one]; rw [one_mul]

/--
theorem `reflect_mul_induction` / 定理 `reflect_mul_induction`

English:
theorem reflect_mul_induction
  statement: (cf cg : Nat) (N O : Nat) (f g : R[X]) (Cf : #f.support <= cf.succ)
  proof: by
  induction cf generalizing f with
  | zero =>
    induction cg generalizing g with
    | zero =>
      rw [← C_mul_X_pow_eq_self Cf]; rw [← C_mul_X_pow_eq_self Cg]
      simp_rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add (X : R[X]), reflect_C_mul,
        reflect_monomial, add_comm, revAt_add N

中文:
定理 reflect_mul_induction
  结论: (cf cg : 自然数) (N O : 自然数) (f g : R[X]) (Cf : #f.support <= cf.succ)
  证明: by
  induction cf generalizing f with
  | zero =>
    induction cg generalizing g with
    | zero =>
      rw [← C_mul_X_pow_eq_self Cf]; rw [← C_mul_X_pow_eq_self Cg]
      simp_rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add (X : R[X]), reflect_C_mul,
        reflect_monomial, add_comm, revAt_add N

Depends on / 依赖: C_mul_X_pow_eq_self, X_pow_mul, add_comm, eraseLead_add_C_mul_X_pow, generalizing, mul_add, mul_assoc, mul_zero, pow_add, reflect_C_mul, reflect_add, reflect_monomial, reflect_zero, revAt_add, simp_rw
-/
theorem reflect_mul_induction (cf cg : Nat) (N O : Nat) (f g : R[X]) (Cf : #f.support <= cf.succ)
    (Cg : #g.support <= cg.succ) (Nf : f.natDegree <= N) (Og : g.natDegree <= O) :
    reflect (N + O) (f * g) = reflect N f * reflect O g := by
  induction cf generalizing f with
  | zero =>
    induction cg generalizing g with
    | zero =>
      rw [← C_mul_X_pow_eq_self Cf]; rw [← C_mul_X_pow_eq_self Cg]
      simp_rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add (X : R[X]), reflect_C_mul,
        reflect_monomial, add_comm, revAt_add Nf Og, mul_assoc, X_pow_mul, mul_assoc, ←
        pow_add (X : R[X]), add_comm]
    | succ cg hcg =>
      by_cases g0 : g = 0
      · rw [g0, reflect_zero, mul_zero, mul_zero, reflect_zero]
      rw [← eraseLead_add_C_mul_X_pow g]; rw [mul_add]; rw [reflect_add]; rw [reflect_add]; rw [mul_add]; rw [hcg]; rw [hcg] <;>
        try assumption
      · exact le_add_left card_support_C_mul_X_pow_le_one
      · exact le_trans (natDegree_C_mul_X_pow_le g.leadingCoeff g.natDegree) Og
      · exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (eraseLead_support_card_lt g0) Cg)
      · exact le_trans eraseLead_natDegree_le_aux Og
  | succ cf hcf =>
    by_cases f0 : f = 0
    · rw [f0, reflect_zero, zero_mul, zero_mul, reflect_zero]
    rw [← eraseLead_add_C_mul_X_pow f]; rw [add_mul]; rw [reflect_add]; rw [reflect_add]; rw [add_mul]; rw [hcf]; rw [hcf] <;>
      try assumption
    · exact le_add_left card_support_C_mul_X_pow_le_one
    · exact le_trans (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree) Nf
    · exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (eraseLead_support_card_lt f0) Cf)
    · exact le_trans eraseLead_natDegree_le_aux Nf

@[simp]
/--
theorem `reflect_mul` / 定理 `reflect_mul`

English:
theorem reflect_mul
  given: (f g : R[X]) {F G : Nat} (Ff : f.natDegree <= F) (Gg : g.natDegree <= G)
  proof: reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

中文:
定理 reflect_mul
  条件: (f g : R[X]) {F G : 自然数} (Ff : f.natDegree <= F) (Gg : g.natDegree <= G)
  证明: reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

Depends on / 依赖: f.support.card.le_succ, g.support.card.le_succ, le_succ, reflect_mul_induction, support
-/
theorem reflect_mul (f g : R[X]) {F G : Nat} (Ff : f.natDegree <= F) (Gg : g.natDegree <= G) :
    reflect (F + G) (f * g) = reflect F f * reflect G g :=
  reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

set_option backward.isDefEq.respectTransparency false in
/--
lemma `natDegree_reflect_le` / 引理 `natDegree_reflect_le`

English:
lemma natDegree_reflect_le
  given: {N : Nat} {p : R[X]}
  proof: by
  simp +contextual [-le_sup_iff, natDegree_le_iff_coeff_eq_zero,
    revAt, not_le_of_gt, coeff_eq_zero_of_natDegree_lt]

中文:
引理 natDegree_reflect_le
  条件: {N : 自然数} {p : R[X]}
  证明: by
  simp +contextual [-le_sup_iff, natDegree_le_iff_coeff_eq_zero,
    revAt, not_le_of_gt, coeff_eq_zero_of_natDegree_lt]

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, contextual, le_sup_iff, natDegree_le_iff_coeff_eq_zero, not_le_of_gt
-/
lemma natDegree_reflect_le {N : Nat} {p : R[X]} :
    (p.reflect N).natDegree <= max N p.natDegree := by
  simp +contextual [-le_sup_iff, natDegree_le_iff_coeff_eq_zero,
    revAt, not_le_of_gt, coeff_eq_zero_of_natDegree_lt]

section Eval₂

variable {S : Type*} [CommSemiring S]

/--
theorem `eval₂_reflect_mul_pow` / 定理 `eval₂_reflect_mul_pow`

English:
theorem eval₂_reflect_mul_pow
  statement: (i : R ->+* S) (x : S) [Invertible x] (N : Nat) (f : R[X])
  proof: by
  refine
    induction_with_natDegree_le (fun f => eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f) _ ?_ ?_
      ?_ f hf
  · simp
  · intro n r _ hnN
    simp only [revAt_le hnN, reflect_C_mul_X_pow, eval₂_X_pow, eval₂_C, eval₂_mul]
    conv in x ^ N => rw [← Nat.sub_add_cancel hnN]
    rw [pow

中文:
定理 eval₂_reflect_mul_pow
  结论: (i : R ->+* S) (x : S) [Invertible x] (N : 自然数) (f : R[X])
  证明: by
  refine
    induction_with_natDegree_le (fun f => eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f) _ ?_ ?_
      ?_ f hf
  · simp
  · intro n r _ hnN
    simp only [revAt_le hnN, reflect_C_mul_X_pow, eval₂_X_pow, eval₂_C, eval₂_mul]
    conv in x ^ N => rw [← Nat.sub_add_cancel hnN]
    rw [pow

Depends on / 依赖: Nat.sub_add_cancel, add_mul, induction_with_natDegree_le, intros, invOf_mul_self, mul_assoc, mul_one, mul_pow, one_pow, pow_add, reflect, reflect_C_mul_X_pow, revAt_le, sub_add_cancel
-/
theorem eval₂_reflect_mul_pow (i : R ->+* S) (x : S) [Invertible x] (N : Nat) (f : R[X])
    (hf : f.natDegree <= N) : eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f := by
  refine
    induction_with_natDegree_le (fun f => eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f) _ ?_ ?_
      ?_ f hf
  · simp
  · intro n r _ hnN
    simp only [revAt_le hnN, reflect_C_mul_X_pow, eval₂_X_pow, eval₂_C, eval₂_mul]
    conv in x ^ N => rw [← Nat.sub_add_cancel hnN]
    rw [pow_add]; rw [← mul_assoc]; rw [mul_assoc (i r)]; rw [← mul_pow]; rw [invOf_mul_self]; rw [one_pow]; rw [mul_one]
  · intros
    simp [*, add_mul]

/--
theorem `eval₂_reflect_eq_zero_iff` / 定理 `eval₂_reflect_eq_zero_iff`

English:
theorem eval₂_reflect_eq_zero_iff
  statement: (i : R ->+* S) (x : S) [Invertible x] (N : Nat) (f : R[X])
  proof: by
  conv_rhs => rw [← eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h]; rw [zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟x) _)]; rw [← one_pow N]; rw [← mul_invOf_self x]; rw [mul_pow]; rw [← mul_assoc]; rw [h]; rw [zero_mul]

中文:
定理 eval₂_reflect_eq_zero_iff
  结论: (i : R ->+* S) (x : S) [Invertible x] (N : 自然数) (f : R[X])
  证明: by
  conv_rhs => rw [← eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h]; rw [zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟x) _)]; rw [← one_pow N]; rw [← mul_invOf_self x]; rw [mul_pow]; rw [← mul_assoc]; rw [h]; rw [zero_mul]

Depends on / 依赖: conv_rhs, mul_assoc, mul_invOf_self, mul_one, mul_pow, mul_zero, one_pow, zero_mul
-/
theorem eval₂_reflect_eq_zero_iff (i : R ->+* S) (x : S) [Invertible x] (N : Nat) (f : R[X])
    (hf : f.natDegree <= N) : eval₂ i (⅟x) (reflect N f) = 0 ↔ eval₂ i x f = 0 := by
  conv_rhs => rw [← eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h]; rw [zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟x) _)]; rw [← one_pow N]; rw [← mul_invOf_self x]; rw [mul_pow]; rw [← mul_assoc]; rw [h]; rw [zero_mul]

end Eval₂

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (f : R[X])
  body: reflect f.natDegree f

中文:
定义 reverse
  签名: (f : R[X])
  定义体: reflect f.natDegree f

Depends on / 依赖: f.natDegree, natDegree, reflect
-/
noncomputable def reverse (f : R[X]) : R[X] :=
  reflect f.natDegree f

/--
theorem `coeff_reverse` / 定理 `coeff_reverse`

English:
theorem coeff_reverse
  given: (f : R[X]) (n : Nat)
  statement: f.reverse.coeff n = f.coeff (revAt f.natDegree n)
  proof: by
  rw [reverse]; rw [coeff_reflect]

@[simp]

中文:
定理 coeff_reverse
  条件: (f : R[X]) (n : 自然数)
  结论: f.reverse.coeff n = f.coeff (revAt f.natDegree n)
  证明: by
  rw [reverse]; rw [coeff_reflect]

@[simp]

Depends on / 依赖: coeff_reflect, reverse
-/
theorem coeff_reverse (f : R[X]) (n : Nat) : f.reverse.coeff n = f.coeff (revAt f.natDegree n) := by
  rw [reverse]; rw [coeff_reflect]

@[simp]
/--
theorem `coeff_zero_reverse` / 定理 `coeff_zero_reverse`

English:
theorem coeff_zero_reverse
  given: (f : R[X])
  statement: coeff (reverse f) 0 = leadingCoeff f
  proof: by
  rw [coeff_reverse]; rw [revAt_le zero_le]; rw [tsub_zero]; rw [leadingCoeff]

@[simp]

中文:
定理 coeff_zero_reverse
  条件: (f : R[X])
  结论: coeff (reverse f) 0 = leadingCoeff f
  证明: by
  rw [coeff_reverse]; rw [revAt_le zero_le]; rw [tsub_zero]; rw [leadingCoeff]

@[simp]

Depends on / 依赖: coeff_reverse, leadingCoeff, revAt_le, tsub_zero, zero_le
-/
theorem coeff_zero_reverse (f : R[X]) : coeff (reverse f) 0 = leadingCoeff f := by
  rw [coeff_reverse]; rw [revAt_le zero_le]; rw [tsub_zero]; rw [leadingCoeff]

@[simp]
/--
theorem `reverse_zero` / 定理 `reverse_zero`

English:
theorem reverse_zero
  statement: reverse (0 : R[X]) = 0
  proof: rfl

@[simp]

中文:
定理 reverse_zero
  结论: reverse (0 : R[X]) = 0
  证明: rfl

@[simp]
-/
theorem reverse_zero : reverse (0 : R[X]) = 0 :=
  rfl

@[simp]
/--
theorem `reverse_eq_zero` / 定理 `reverse_eq_zero`

English:
theorem reverse_eq_zero
  statement: f.reverse = 0 ↔ f = 0
  proof: by simp [reverse]

中文:
定理 reverse_eq_zero
  结论: f.reverse = 0 ↔ f = 0
  证明: by simp [reverse]

Depends on / 依赖: reverse
-/
theorem reverse_eq_zero : f.reverse = 0 ↔ f = 0 := by simp [reverse]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `reverse_natDegree_le` / 定理 `reverse_natDegree_le`

English:
theorem reverse_natDegree_le
  given: (f : R[X])
  statement: f.reverse.natDegree <= f.natDegree
  proof: by
  rw [natDegree_le_iff_degree_le]; rw [degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [coeff_reverse]; rw [revAt]; rw [Function.Embedding.coeFn_mk]; rw [if_neg (not_le_of_gt hn)]; rw [coeff_eq_zero_of_natDegree_lt hn]

中文:
定理 reverse_natDegree_le
  条件: (f : R[X])
  结论: f.reverse.natDegree <= f.natDegree
  证明: by
  rw [natDegree_le_iff_degree_le]; rw [degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [coeff_reverse]; rw [revAt]; rw [Function.Embedding.coeFn_mk]; rw [if_neg (not_le_of_gt hn)]; rw [coeff_eq_zero_of_natDegree_lt hn]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, Nat.cast_lt, cast_lt, coeFn_mk, coeff_eq_zero_of_natDegree_lt, coeff_reverse, degree_le_iff_coeff_zero, if_neg, natDegree_le_iff_degree_le, not_le_of_gt
-/
theorem reverse_natDegree_le (f : R[X]) : f.reverse.natDegree <= f.natDegree := by
  rw [natDegree_le_iff_degree_le]; rw [degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [coeff_reverse]; rw [revAt]; rw [Function.Embedding.coeFn_mk]; rw [if_neg (not_le_of_gt hn)]; rw [coeff_eq_zero_of_natDegree_lt hn]

/--
theorem `natDegree_eq_reverse_natDegree_add_natTrailingDegree` / 定理 `natDegree_eq_reverse_natDegree_add_natTrailingDegree`

English:
theorem natDegree_eq_reverse_natDegree_add_natTrailingDegree
  given: (f : R[X])
  proof: by
  by_cases hf : f = 0
  · rw [hf, reverse_zero, natDegree_zero, natTrailingDegree_zero]
  apply le_antisymm
  · refine tsub_le_iff_right.mp ?_
    apply le_natDegree_of_ne_zero
    rw [reverse]; rw [coeff_reflect]; rw [← revAt_le f.natTrailingDegree_le_natDegree]; rw [revAt_invol]
    exact trail

中文:
定理 natDegree_eq_reverse_natDegree_add_natTrailingDegree
  条件: (f : R[X])
  证明: by
  by_cases hf : f = 0
  · rw [hf, reverse_zero, natDegree_zero, natTrailingDegree_zero]
  apply le_antisymm
  · refine tsub_le_iff_right.mp ?_
    apply le_natDegree_of_ne_zero
    rw [reverse]; rw [coeff_reflect]; rw [← revAt_le f.natTrailingDegree_le_natDegree]; rw [revAt_invol]
    exact trail

Depends on / 依赖: coeff_reflect, coeff_revers, f.natTrailingDegree_le_natDegree, f.reverse_natDegree_le, le_antisymm, le_natDegree_of_ne_zero, le_tsub_iff_left, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, natDegree_zero, natTrailingDegree_le_natDegree, natTrailingDegree_le_of_ne_zero, natTrailingDegree_zero, revAt_invol, revAt_le, reverse, reverse_eq_zero, reverse_eq_zero.mp, reverse_natDegree_le
-/
theorem natDegree_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) :
    f.natDegree = f.reverse.natDegree + f.natTrailingDegree := by
  by_cases hf : f = 0
  · rw [hf, reverse_zero, natDegree_zero, natTrailingDegree_zero]
  apply le_antisymm
  · refine tsub_le_iff_right.mp ?_
    apply le_natDegree_of_ne_zero
    rw [reverse]; rw [coeff_reflect]; rw [← revAt_le f.natTrailingDegree_le_natDegree]; rw [revAt_invol]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hf
  · rw [← le_tsub_iff_left f.reverse_natDegree_le]
    apply natTrailingDegree_le_of_ne_zero
    have key := mt leadingCoeff_eq_zero.mp (mt reverse_eq_zero.mp hf)
    rwa [leadingCoeff, coeff_reverse, revAt_le f.reverse_natDegree_le] at key

/--
theorem `reverse_natDegree` / 定理 `reverse_natDegree`

English:
theorem reverse_natDegree
  given: (f : R[X])
  statement: f.reverse.natDegree = f.natDegree - f.natTrailingDegree
  proof: by
  rw [f.natDegree_eq_reverse_natDegree_add_natTrailingDegree]; rw [add_tsub_cancel_right]

中文:
定理 reverse_natDegree
  条件: (f : R[X])
  结论: f.reverse.natDegree = f.natDegree - f.natTrailingDegree
  证明: by
  rw [f.natDegree_eq_reverse_natDegree_add_natTrailingDegree]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, f.natDegree_eq_reverse_natDegree_add_natTrailingDegree, natDegree_eq_reverse_natDegree_add_natTrailingDegree
-/
theorem reverse_natDegree (f : R[X]) : f.reverse.natDegree = f.natDegree - f.natTrailingDegree := by
  rw [f.natDegree_eq_reverse_natDegree_add_natTrailingDegree]; rw [add_tsub_cancel_right]

/--
theorem `reverse_leadingCoeff` / 定理 `reverse_leadingCoeff`

English:
theorem reverse_leadingCoeff
  given: (f : R[X])
  statement: f.reverse.leadingCoeff = f.trailingCoeff
  proof: by
  rw [leadingCoeff]; rw [reverse_natDegree]; rw [← revAt_le f.natTrailingDegree_le_natDegree]; rw [coeff_reverse]; rw [revAt_invol]; rw [trailingCoeff]

中文:
定理 reverse_leadingCoeff
  条件: (f : R[X])
  结论: f.reverse.leadingCoeff = f.trailingCoeff
  证明: by
  rw [leadingCoeff]; rw [reverse_natDegree]; rw [← revAt_le f.natTrailingDegree_le_natDegree]; rw [coeff_reverse]; rw [revAt_invol]; rw [trailingCoeff]

Depends on / 依赖: coeff_reverse, f.natTrailingDegree_le_natDegree, leadingCoeff, natTrailingDegree_le_natDegree, revAt_invol, revAt_le, reverse_natDegree, trailingCoeff
-/
theorem reverse_leadingCoeff (f : R[X]) : f.reverse.leadingCoeff = f.trailingCoeff := by
  rw [leadingCoeff]; rw [reverse_natDegree]; rw [← revAt_le f.natTrailingDegree_le_natDegree]; rw [coeff_reverse]; rw [revAt_invol]; rw [trailingCoeff]

/--
theorem `natTrailingDegree_reverse` / 定理 `natTrailingDegree_reverse`

English:
theorem natTrailingDegree_reverse
  given: (f : R[X])
  statement: f.reverse.natTrailingDegree = 0
  proof: by
  rw [natTrailingDegree_eq_zero]; rw [reverse_eq_zero]; rw [coeff_zero_reverse]; rw [leadingCoeff_ne_zero]
  exact eq_or_ne _ _

中文:
定理 natTrailingDegree_reverse
  条件: (f : R[X])
  结论: f.reverse.natTrailingDegree = 0
  证明: by
  rw [natTrailingDegree_eq_zero]; rw [reverse_eq_zero]; rw [coeff_zero_reverse]; rw [leadingCoeff_ne_zero]
  exact eq_or_ne _ _

Depends on / 依赖: coeff_zero_reverse, eq_or_ne, leadingCoeff_ne_zero, natTrailingDegree_eq_zero, reverse_eq_zero
-/
theorem natTrailingDegree_reverse (f : R[X]) : f.reverse.natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]; rw [reverse_eq_zero]; rw [coeff_zero_reverse]; rw [leadingCoeff_ne_zero]
  exact eq_or_ne _ _

/--
theorem `reverse_trailingCoeff` / 定理 `reverse_trailingCoeff`

English:
theorem reverse_trailingCoeff
  given: (f : R[X])
  statement: f.reverse.trailingCoeff = f.leadingCoeff
  proof: by
  rw [trailingCoeff]; rw [natTrailingDegree_reverse]; rw [coeff_zero_reverse]

中文:
定理 reverse_trailingCoeff
  条件: (f : R[X])
  结论: f.reverse.trailingCoeff = f.leadingCoeff
  证明: by
  rw [trailingCoeff]; rw [natTrailingDegree_reverse]; rw [coeff_zero_reverse]

Depends on / 依赖: coeff_zero_reverse, natTrailingDegree_reverse, trailingCoeff
-/
theorem reverse_trailingCoeff (f : R[X]) : f.reverse.trailingCoeff = f.leadingCoeff := by
  rw [trailingCoeff]; rw [natTrailingDegree_reverse]; rw [coeff_zero_reverse]

/--
theorem `reverse_mul` / 定理 `reverse_mul`

English:
theorem reverse_mul
  given: {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff != 0)
  proof: by
  unfold reverse
  rw [natDegree_mul' fg]; rw [reflect_mul f g rfl.le rfl.le]

@[simp]

中文:
定理 reverse_mul
  条件: {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff != 0)
  证明: by
  unfold reverse
  rw [natDegree_mul' fg]; rw [reflect_mul f g rfl.le rfl.le]

@[simp]

Depends on / 依赖: natDegree_mul, reflect_mul, reverse, rfl.le
-/
theorem reverse_mul {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff != 0) :
    reverse (f * g) = reverse f * reverse g := by
  unfold reverse
  rw [natDegree_mul' fg]; rw [reflect_mul f g rfl.le rfl.le]

@[simp]
/--
theorem `reverse_mul_of_domain` / 定理 `reverse_mul_of_domain`

English:
theorem reverse_mul_of_domain
  given: {R : Type*} [Semiring R] [NoZeroDivisors R] (f g : R[X])
  proof: by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, reverse_zero, mul_zero]
  simp [reverse_mul, *]

中文:
定理 reverse_mul_of_domain
  条件: {R : 类型} [Semiring R] [NoZeroDivisors R] (f g : R[X])
  证明: by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, reverse_zero, mul_zero]
  simp [reverse_mul, *]

Depends on / 依赖: mul_zero, reverse_mul, reverse_zero, zero_mul
-/
theorem reverse_mul_of_domain {R : Type*} [Semiring R] [NoZeroDivisors R] (f g : R[X]) :
    reverse (f * g) = reverse f * reverse g := by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, reverse_zero, mul_zero]
  simp [reverse_mul, *]

/--
theorem `trailingCoeff_mul` / 定理 `trailingCoeff_mul`

English:
theorem trailingCoeff_mul
  given: {R : Type*} [Semiring R] [NoZeroDivisors R] (p q : R[X])
  proof: by
  rw [← reverse_leadingCoeff]; rw [reverse_mul_of_domain]; rw [leadingCoeff_mul]; rw [reverse_leadingCoeff]; rw [reverse_leadingCoeff]

@[simp]

中文:
定理 trailingCoeff_mul
  条件: {R : 类型} [Semiring R] [NoZeroDivisors R] (p q : R[X])
  证明: by
  rw [← reverse_leadingCoeff]; rw [reverse_mul_of_domain]; rw [leadingCoeff_mul]; rw [reverse_leadingCoeff]; rw [reverse_leadingCoeff]

@[simp]

Depends on / 依赖: leadingCoeff_mul, reverse_leadingCoeff, reverse_mul_of_domain
-/
theorem trailingCoeff_mul {R : Type*} [Semiring R] [NoZeroDivisors R] (p q : R[X]) :
    (p * q).trailingCoeff = p.trailingCoeff * q.trailingCoeff := by
  rw [← reverse_leadingCoeff]; rw [reverse_mul_of_domain]; rw [leadingCoeff_mul]; rw [reverse_leadingCoeff]; rw [reverse_leadingCoeff]

@[simp]
/--
theorem `coeff_one_reverse` / 定理 `coeff_one_reverse`

English:
theorem coeff_one_reverse
  given: (f : R[X])
  statement: coeff (reverse f) 1 = nextCoeff f
  proof: by
  rw [coeff_reverse]; rw [nextCoeff]
  split_ifs with hf
  · have : coeff f 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp only [hf, zero_lt_one])
    simp [*, revAt]
  · rw [revAt_le]
    exact Nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf)

中文:
定理 coeff_one_reverse
  条件: (f : R[X])
  结论: coeff (reverse f) 1 = nextCoeff f
  证明: by
  rw [coeff_reverse]; rw [nextCoeff]
  split_ifs with hf
  · have : coeff f 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp only [hf, zero_lt_one])
    simp [*, revAt]
  · rw [revAt_le]
    exact Nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf)

Depends on / 依赖: Nat.succ_le_iff, coeff_eq_zero_of_natDegree_lt, coeff_reverse, nextCoeff, pos_iff_ne_zero, revAt_le, split_ifs, succ_le_iff, zero_lt_one
-/
theorem coeff_one_reverse (f : R[X]) : coeff (reverse f) 1 = nextCoeff f := by
  rw [coeff_reverse]; rw [nextCoeff]
  split_ifs with hf
  · have : coeff f 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp only [hf, zero_lt_one])
    simp [*, revAt]
  · rw [revAt_le]
    exact Nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf)

/--
lemma `reverse_C` / 引理 `reverse_C`

English:
lemma reverse_C
  given: (t : R)
  proof: by
  simp [reverse]

中文:
引理 reverse_C
  条件: (t : R)
  证明: by
  simp [reverse]
-/
@[simp] lemma reverse_C (t : R) :
    reverse (C t) = C t := by
  simp [reverse]

/--
lemma `reverse_mul_X` / 引理 `reverse_mul_X`

English:
lemma reverse_mul_X
  given: (p : R[X])
  statement: reverse (p * X) = reverse p
  proof: by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [reverse, hp]

中文:
引理 reverse_mul_X
  条件: (p : R[X])
  结论: reverse (p * X) = reverse p
  证明: by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [reverse, hp]
-/
@[simp] lemma reverse_mul_X (p : R[X]) : reverse (p * X) = reverse p := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [reverse, hp]

/--
lemma `reverse_X_mul` / 引理 `reverse_X_mul`

English:
lemma reverse_X_mul
  given: (p : R[X])
  statement: reverse (X * p) = reverse p
  proof: by
  rw [commute_X p]; rw [reverse_mul_X]

中文:
引理 reverse_X_mul
  条件: (p : R[X])
  结论: reverse (X * p) = reverse p
  证明: by
  rw [commute_X p]; rw [reverse_mul_X]
-/
@[simp] lemma reverse_X_mul (p : R[X]) : reverse (X * p) = reverse p := by
  rw [commute_X p]; rw [reverse_mul_X]

/--
lemma `reverse_mul_X_pow` / 引理 `reverse_mul_X_pow`

English:
lemma reverse_mul_X_pow
  given: (p : R[X]) (n : Nat)
  statement: reverse (p * X ^ n) = reverse p
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, reverse_mul_X, ih]

中文:
引理 reverse_mul_X_pow
  条件: (p : R[X]) (n : 自然数)
  结论: reverse (p * X ^ n) = reverse p
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, reverse_mul_X, ih]
-/
@[simp] lemma reverse_mul_X_pow (p : R[X]) (n : Nat) : reverse (p * X ^ n) = reverse p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, reverse_mul_X, ih]

/--
lemma `reverse_X_pow_mul` / 引理 `reverse_X_pow_mul`

English:
lemma reverse_X_pow_mul
  given: (p : R[X]) (n : Nat)
  statement: reverse (X ^ n * p) = reverse p
  proof: by
  rw [commute_X_pow p]; rw [reverse_mul_X_pow]

中文:
引理 reverse_X_pow_mul
  条件: (p : R[X]) (n : 自然数)
  结论: reverse (X ^ n * p) = reverse p
  证明: by
  rw [commute_X_pow p]; rw [reverse_mul_X_pow]
-/
@[simp] lemma reverse_X_pow_mul (p : R[X]) (n : Nat) : reverse (X ^ n * p) = reverse p := by
  rw [commute_X_pow p]; rw [reverse_mul_X_pow]

/--
lemma `reverse_add_C` / 引理 `reverse_add_C`

English:
lemma reverse_add_C
  given: (p : R[X]) (t : R)
  proof: by
  simp [reverse]

中文:
引理 reverse_add_C
  条件: (p : R[X]) (t : R)
  证明: by
  simp [reverse]
-/
@[simp] lemma reverse_add_C (p : R[X]) (t : R) :
    reverse (p + C t) = reverse p + C t * X ^ p.natDegree := by
  simp [reverse]

/--
lemma `reverse_C_add` / 引理 `reverse_C_add`

English:
lemma reverse_C_add
  given: (p : R[X]) (t : R)
  proof: by
  rw [add_comm]; rw [reverse_add_C]; rw [add_comm]

中文:
引理 reverse_C_add
  条件: (p : R[X]) (t : R)
  证明: by
  rw [add_comm]; rw [reverse_add_C]; rw [add_comm]
-/
@[simp] lemma reverse_C_add (p : R[X]) (t : R) :
    reverse (C t + p) = C t * X ^ p.natDegree + reverse p := by
  rw [add_comm]; rw [reverse_add_C]; rw [add_comm]

section Eval₂

variable {S : Type*} [CommSemiring S]

/--
theorem `eval₂_reverse_mul_pow` / 定理 `eval₂_reverse_mul_pow`

English:
theorem eval₂_reverse_mul_pow
  given: (i : R ->+* S) (x : S) [Invertible x] (f : R[X])
  proof: eval₂_reflect_mul_pow i _ _ f le_rfl

@[simp]

中文:
定理 eval₂_reverse_mul_pow
  条件: (i : R ->+* S) (x : S) [Invertible x] (f : R[X])
  证明: eval₂_reflect_mul_pow i _ _ f le_rfl

@[simp]

Depends on / 依赖: le_rfl
-/
theorem eval₂_reverse_mul_pow (i : R ->+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟x) (reverse f) * x ^ f.natDegree = eval₂ i x f :=
  eval₂_reflect_mul_pow i _ _ f le_rfl

@[simp]
/--
theorem `eval₂_reverse_eq_zero_iff` / 定理 `eval₂_reverse_eq_zero_iff`

English:
theorem eval₂_reverse_eq_zero_iff
  given: (i : R ->+* S) (x : S) [Invertible x] (f : R[X])
  proof: eval₂_reflect_eq_zero_iff i x _ _ le_rfl

中文:
定理 eval₂_reverse_eq_zero_iff
  条件: (i : R ->+* S) (x : S) [Invertible x] (f : R[X])
  证明: eval₂_reflect_eq_zero_iff i x _ _ le_rfl

Depends on / 依赖: le_rfl
-/
theorem eval₂_reverse_eq_zero_iff (i : R ->+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟x) (reverse f) = 0 ↔ eval₂ i x f = 0 :=
  eval₂_reflect_eq_zero_iff i x _ _ le_rfl

end Eval₂

end Semiring

section Ring

variable {R : Type*} [Ring R]

@[simp]
/--
theorem `reflect_neg` / 定理 `reflect_neg`

English:
theorem reflect_neg
  given: (f : R[X]) (N : Nat)
  statement: reflect N (-f) = -reflect N f
  proof: by
  rw [neg_eq_neg_one_mul]; rw [← C_1]; rw [← C_neg]; rw [reflect_C_mul]; rw [C_neg]; rw [C_1]; rw [← neg_eq_neg_one_mul]

@[simp]

中文:
定理 reflect_neg
  条件: (f : R[X]) (N : 自然数)
  结论: reflect N (-f) = -reflect N f
  证明: by
  rw [neg_eq_neg_one_mul]; rw [← C_1]; rw [← C_neg]; rw [reflect_C_mul]; rw [C_neg]; rw [C_1]; rw [← neg_eq_neg_one_mul]

@[simp]

Depends on / 依赖: C_neg, neg_eq_neg_one_mul, reflect_C_mul
-/
theorem reflect_neg (f : R[X]) (N : Nat) : reflect N (-f) = -reflect N f := by
  rw [neg_eq_neg_one_mul]; rw [← C_1]; rw [← C_neg]; rw [reflect_C_mul]; rw [C_neg]; rw [C_1]; rw [← neg_eq_neg_one_mul]

@[simp]
/--
theorem `reflect_sub` / 定理 `reflect_sub`

English:
theorem reflect_sub
  given: (f g : R[X]) (N : Nat)
  statement: reflect N (f - g) = reflect N f - reflect N g
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [reflect_add]; rw [reflect_neg]

@[simp]

中文:
定理 reflect_sub
  条件: (f g : R[X]) (N : 自然数)
  结论: reflect N (f - g) = reflect N f - reflect N g
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [reflect_add]; rw [reflect_neg]

@[simp]

Depends on / 依赖: reflect_add, reflect_neg, sub_eq_add_neg
-/
theorem reflect_sub (f g : R[X]) (N : Nat) : reflect N (f - g) = reflect N f - reflect N g := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [reflect_add]; rw [reflect_neg]

@[simp]
/--
theorem `reverse_neg` / 定理 `reverse_neg`

English:
theorem reverse_neg
  given: (f : R[X])
  statement: reverse (-f) = -reverse f
  proof: by
  rw [reverse]; rw [reverse]; rw [reflect_neg]; rw [natDegree_neg]

中文:
定理 reverse_neg
  条件: (f : R[X])
  结论: reverse (-f) = -reverse f
  证明: by
  rw [reverse]; rw [reverse]; rw [reflect_neg]; rw [natDegree_neg]

Depends on / 依赖: natDegree_neg, reflect_neg, reverse
-/
theorem reverse_neg (f : R[X]) : reverse (-f) = -reverse f := by
  rw [reverse]; rw [reverse]; rw [reflect_neg]; rw [natDegree_neg]

end Ring

end Polynomial
