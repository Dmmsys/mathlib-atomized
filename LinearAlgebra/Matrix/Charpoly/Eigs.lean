/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

* `Matrix.mem_spectrum_iff_isRoot_charpoly`: the roots of the characteristic polynomial are exactly
  the spectrum of the matrix.
* `Matrix.det_eq_prod_roots_charpoly_of_splits`: the determinant (in the field of the matrix)
  is the product of the roots of the characteristic polynomial if the polynomial splits in the field
  of the matrix.
* `Matrix.trace_eq_sum_roots_charpoly_of_splits`: the trace is the sum of the roots of the
  characteristic polynomial if the polynomial splits in the field of the matrix.

In an algebraically closed field we show that:

* `Matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
  characteristic polynomial.
* `Matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the
  characteristic polynomial.

Note that over other fields such as `ℝ`, these results can be used by using
`A.map (algebraMap ℝ ℂ)` as the matrix, and then applying `RingHom.map_det`.

The two lemmas `Matrix.det_eq_prod_roots_charpoly` and `Matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `LinearAlgebra.Eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.

## TODO

The proofs of `det_eq_prod_roots_charpoly_of_splits` and
`trace_eq_sum_roots_charpoly_of_splits` closely resemble
`norm_gen_eq_prod_roots` and `trace_gen_eq_sum_roots` respectively, but the
dependencies are not general enough to unify them. We should refactor
`Polynomial.coeff_zero_eq_prod_roots_of_monic_of_split` and
`Polynomial.nextCoeff_eq_neg_sum_roots_of_monic_of_splits` to assume splitting over an
arbitrary map.
-/

public section


variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R K : Type*} [CommRing R] [Field K]
variable {A : Matrix n n K} {B : Matrix n n R}

open Matrix Polynomial

open scoped Matrix

namespace Matrix

/-
**Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：mem_spectrum_iff_not_isUnit_eval_charpoly {r : R} : r in spectrum R B ↔ ¬I
sUnit (B.charpoly.eval r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.eval_charpoly`：eval_charpoly (M : Matrix m m R) (t : R) : M.charp
oly.eval t = (Matrix.scalar _ t - M).det
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_spectrum_iff_not_isUnit_eval_charpoly {r : R} :
    r ∈ spectrum R B ↔ ¬IsUnit (B.charpoly.eval r) := by
  simp [eval_charpoly, spectrum.mem_iff, isUnit_iff_isUnit_det, algebraMap_eq_diagonal,
    Pi.algebraMap_def]

/-- The roots of the characteristic polynomial are in the spectrum of the matrix. -/
/-
**Matrix.mem_spectrum_of_isRoot_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_spectrum_of_isRoot_charpoly [Nontrivial R] {r : R} (hr : IsRoot B.char
poly r) : r in spectrum R B
参数：hr : IsRoot B.charpoly r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_zero`：∀ {R : Type u} [inst : Semiring R] {p : Polyn
omial R} {x : R}, p.IsRoot x → Polynomial.eval x p = 0
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The roots of the characteristic polynomial are in the spectrum of the matrix.
-/
theorem mem_spectrum_of_isRoot_charpoly [Nontrivial R] {r : R} (hr : IsRoot B.charpoly r) :
    r ∈ spectrum R B := by
  simp [mem_spectrum_iff_not_isUnit_eval_charpoly, hr.eq_zero]

/--
In fields, the roots of the characteristic polynomial are exactly the spectrum of the matrix.
The weaker direction is true in nontrivial rings (see `Matrix.mem_spectrum_of_isRoot_charpoly`).
-/
/-
**Matrix.mem_spectrum_iff_isRoot_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_spectrum_iff_isRoot_charpoly {r : K} : r in spectrum K A ↔ IsRoot A.ch
arpoly r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
In fields, the roots of the characteristic polynomial are exactly the spectrum o
f the matrix.
The weaker direction is true in nontrivial rings (see `Matrix.mem_spectrum_of_is
Root_charpoly`).
-/
theorem mem_spectrum_iff_isRoot_charpoly {r : K} : r ∈ spectrum K A ↔ IsRoot A.charpoly r := by
  simp [mem_spectrum_iff_not_isUnit_eval_charpoly]
/-
**Matrix.det_eq_prod_roots_charpoly_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：det_eq_prod_roots_charpoly_of_splits [IsDomain R] (hAps : B.charpoly.Split
s) : B.det = (Matrix.charpoly B).roots.prod
参数：hAps : B.charpoly.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_eq_sign_charpoly_coeff`：det_eq_sign_charpoly_coeff (M : Matri
x n n R) : M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic`：∀ {R : Type u_1} [i
nst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic
 → f.coeff 0 = (-1) ^ f.natDegree * f.roo…
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `pow_right_comm`：pow_right_comm (a : M) (m n : Nat) : (a ^ m) ^ n = (a ^ 
n) ^ m
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem det_eq_prod_roots_charpoly_of_splits [IsDomain R] (hAps : B.charpoly.Splits) :
    B.det = (Matrix.charpoly B).roots.prod := by
  rw [det_eq_sign_charpoly_coeff, ← charpoly_natDegree_eq_dim B,
    hAps.coeff_zero_eq_prod_roots_of_monic B.charpoly_monic, ← mul_assoc,
    ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]
/-
**Matrix.trace_eq_sum_roots_charpoly_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：trace_eq_sum_roots_charpoly_of_splits [IsDomain R] (hAps : B.charpoly.Spli
ts) : B.trace = (Matrix.charpoly B).roots.sum
参数：hAps : B.charpoly.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.trace_eq_zero_of_isEmpty`：trace_eq_zero_of_isEmpty [IsEmpty n] (A
 : Matrix n n R) : trace A = 0
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Matrix.charpoly_isEmpty`：charpoly_isEmpty [IsEmpty n] {A : Matrix n n R}
 : charpoly A = 1
· 使用定理 `Polynomial.roots_one`：roots_one : (1 : R[X]).roots = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.trace_eq_neg_charpoly_nextCoeff`：trace_eq_neg_charpoly_nextCoeff 
(M : Matrix n n R) : M.trace = -M.charpoly.nextCoeff
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic`：∀ {R : Type u_1} 
[inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Mon
ic → f.nextCoeff = -f.roots.sum
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
-/
theorem trace_eq_sum_roots_charpoly_of_splits [IsDomain R] (hAps : B.charpoly.Splits) :
    B.trace = (Matrix.charpoly B).roots.sum := by
  rcases isEmpty_or_nonempty n with h | _
  · simp
  · rw [trace_eq_neg_charpoly_nextCoeff, neg_eq_iff_eq_neg,
      ← hAps.nextCoeff_eq_neg_sum_roots_of_monic B.charpoly_monic]

variable (A)
/-
**Matrix.det_eq_prod_roots_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).r
oots.prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_eq_prod_roots_charpoly_of_splits`：det_eq_prod_roots_charpoly_
of_splits [IsDomain R] (hAps : B.charpoly.Splits) : B.det = (Matrix.charpoly B).
roots.prod
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
-/
theorem det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).roots.prod :=
  det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)
/-
**Matrix.trace_eq_sum_roots_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_eq_sum_roots_charpoly [IsAlgClosed K] : A.trace = (Matrix.charpoly A
).roots.sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_eq_sum_roots_charpoly_of_splits`：trace_eq_sum_roots_charpol
y_of_splits [IsDomain R] (hAps : B.charpoly.Splits) : B.trace = (Matrix.charpoly
 B).roots.sum
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
-/
theorem trace_eq_sum_roots_charpoly [IsAlgClosed K] : A.trace = (Matrix.charpoly A).roots.sum :=
  trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

end Matrix

