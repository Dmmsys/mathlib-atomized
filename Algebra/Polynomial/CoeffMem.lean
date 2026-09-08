/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Span

/-!
# Bounding the coefficients of the quotient and remainder of polynomials

This file proves that, for polynomials `p q : R[X]`, the coefficients of `p /ₘ q` and `p %ₘ q` can
be written as sums of products of coefficients of `p` and `q`.

Precisely, we show that each summand needs at most one coefficient of `p` and `deg p` coefficients
of `q`.
-/

public section

namespace Polynomial
variable {ι R S : Type*} [CommRing R] [Ring S] [Algebra R S]

local notation3 "deg("p")" => natDegree p
local notation3 "coeffs("p")" => Set.range (coeff p)
local notation3 "spanCoeffs("p")" => 1 ⊔ Submodule.span R coeffs(p)

open Submodule Set in
/-
**Polynomial.coeff_divModByMonicAux_mem_span_pow_mul_span** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial`。
形式化陈述：coeff_divModByMonicAux_mem_span_pow_mul_span : forall (p q : S[X]) (hq : q
.Monic) (i), (p.divModByMonicAux hq).1.coeff i in spanCoeffs(q) ^ deg(p) * spanC
oeffs(p) ∧ (p.divModByMonicAux hq).2.coeff i in spanCoeffs(q) ^ deg(p) * spanCoe
ffs(p) | p, q, hq, i => by rw [divModByMonicAux] have H₀ (i) : p.coeff i in span
Coeffs(q) ^ deg(p) * spanCoeffs(p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_divModByMonicAux_mem_span_pow_mul_span._unary`：∀ {R : T
ype u_2} {S : Type u_3} [inst : CommRing R] [inst_1 : Ring S] [inst_2 : Algebra 
R S]   (_x : (_ : Polynomial S) ×' (q : Polynomial S…
-/
lemma coeff_divModByMonicAux_mem_span_pow_mul_span : ∀ (p q : S[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) ∧
    (p.divModByMonicAux hq).2.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by
      refine SetLike.le_def.mp ?_ <| subset_span <| mem_range_self i
      calc
        span R coeffs(p)
        _ = 1 ^ deg(p) * span R coeffs(p) := by simp
        _ ≤ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, le_sup_right]
    split_ifs with hpq; swap
    · simpa using H₀ _
    simp only [coeff_add, coeff_C_mul, coeff_X_pow]
    generalize hr : (p - q * (C p.leadingCoeff * X ^ (deg(p) - deg(q)))) = r
    by_cases hr' : r = 0
    · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero, le_bot_iff,
        degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte, coeff_zero, add_zero,
        Submodule.zero_mem, and_true]
      split_ifs
      exacts [H₀ _, zero_mem _]
    have H : span R coeffs(r) ≤ span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p) := by
      rw [span_le, ← hr]
      rintro _ ⟨i, rfl⟩
      rw [coeff_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
      apply sub_mem
      · exact SetLike.le_def.mp le_sup_left (subset_span (mem_range_self _))
      · split_ifs
        · refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_) <;> exact subset_span ⟨_, rfl⟩
        · exact zero_mem _
    have deg_r_lt_deg_p : deg(r) < deg(p) := natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
    have H'' := calc
      spanCoeffs(q) ^ deg(r) * spanCoeffs(r)
      _ ≤ spanCoeffs(q) ^ deg(r) *
          (1 ⊔ (span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p))) := by gcongr
      _ ≤ spanCoeffs(q) ^ deg(r) * (spanCoeffs(q) * spanCoeffs(p)) := by
        gcongr
        simp only [sup_le_iff]
        refine ⟨one_le_mul le_sup_left le_sup_left, ?_, mul_le_mul' le_sup_right le_sup_right⟩
        rw [Submodule.sup_mul, one_mul]
        exact le_sup_of_le_left le_sup_right
      _ = spanCoeffs(q) ^ (deg(r) + 1) * spanCoeffs(p) := by rw [pow_succ, mul_assoc]
      _ ≤ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, deg_r_lt_deg_p]
    refine ⟨add_mem ?_ ?_, ?_⟩
    · split_ifs <;> simp only [mul_one, mul_zero]
      exacts [H₀ _, zero_mem _]
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span r _ hq i).1
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span _ _ hq i).2
  termination_by p => deg(p)

/-- For polynomials `p q : R[X]`, the coefficients of `p %ₘ q` can be written as sums of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coefficients of `q`. -/
/-
**Polynomial.coeff_modByMonic_mem_pow_natDegree_mul** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
形式化陈述：coeff_modByMonic_mem_pow_natDegree_mul (p q : S[X]) (Mp : Submodule R S) (
hp : forall i, p.coeff i in Mp) (hp' : 1 in Mp) (Mq : Submodule R S) (hq : foral
l i, q.coeff i in Mq) (hq' : 1 in Mq) (i : Nat) : (p %ₘ q).coeff i in Mq ^ p.nat
Degree * Mp
参数：p q : S[X]；Mp : Submodule R S；hp : forall i, p.coeff i in Mp；hp' : 1 in Mp；Mq
 : Submodule R S；hq : forall i, q.coeff i in Mq；hq' : 1 in Mq；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.instIsOrderedRing`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A],   IsOrderedRing (Submodul
e R A)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Polynomial.coeff_divModByMonicAux_mem_span_pow_mul_span`：coeff_divModByM
onicAux_mem_span_pow_mul_span : forall (p q : S[X]) (hq : q.Monic) (i), (p.divMo
dByMonicAux hq).1.coeff i in spanCoeffs(q) ^ …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Submodule.pow_mem_pow`：pow_mem_pow {x : A} (hx : x in M) (n : Nat) : x ^
 n in M ^ n

--- 原说明 ---
For polynomials `p q : R[X]`, the coefficients of `p %ₘ q` can be written as sum
s of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coeffic
ients of `q`.
-/
lemma coeff_modByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : ∀ i, p.coeff i ∈ Mp) (hp' : 1 ∈ Mp)
    (Mq : Submodule R S) (hq : ∀ i, q.coeff i ∈ Mq) (hq' : 1 ∈ Mq) (i : ℕ) :
    (p %ₘ q).coeff i ∈ Mq ^ p.natDegree * Mp := by
  delta modByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).2
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · rw [← one_mul (p.coeff i), ← one_pow p.natDegree]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow Mq hq' _) (hp i)

/-- For polynomials `p q : R[X]`, the coefficients of `p /ₘ q` can be written as sums of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coefficients of `q`. -/
/-
**Polynomial.coeff_divByMonic_mem_pow_natDegree_mul** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
形式化陈述：coeff_divByMonic_mem_pow_natDegree_mul (p q : S[X]) (Mp : Submodule R S) (
hp : forall i, p.coeff i in Mp) (hp' : 1 in Mp) (Mq : Submodule R S) (hq : foral
l i, q.coeff i in Mq) (hq' : 1 in Mq) (i : Nat) : (p /ₘ q).coeff i in Mq ^ p.nat
Degree * Mp
参数：p q : S[X]；Mp : Submodule R S；hp : forall i, p.coeff i in Mp；hp' : 1 in Mp；Mq
 : Submodule R S；hq : forall i, q.coeff i in Mq；hq' : 1 in Mq；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.instIsOrderedRing`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A],   IsOrderedRing (Submodul
e R A)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Polynomial.coeff_divModByMonicAux_mem_span_pow_mul_span`：coeff_divModByM
onicAux_mem_span_pow_mul_span : forall (p q : S[X]) (hq : q.Monic) (i), (p.divMo
dByMonicAux hq).1.coeff i in spanCoeffs(q) ^ …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
For polynomials `p q : R[X]`, the coefficients of `p /ₘ q` can be written as sum
s of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coeffic
ients of `q`.
-/
lemma coeff_divByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : ∀ i, p.coeff i ∈ Mp) (hp' : 1 ∈ Mp)
    (Mq : Submodule R S) (hq : ∀ i, q.coeff i ∈ Mq) (hq' : 1 ∈ Mq) (i : ℕ) :
    (p /ₘ q).coeff i ∈ Mq ^ p.natDegree * Mp := by
  delta divByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).1
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · simp

variable [DecidableEq ι] {i j : ι}

open Function Ideal in
/-
**Polynomial.idealSpan_range_update_divByMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
形式化陈述：idealSpan_range_update_divByMonic (hij : i != j) (v : ι -> R[X]) : span (S
et.range (Function.update v j (v j %ₘ v i))) = span (Set.range v)
参数：hij : i != j；v : ι -> R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用引理 `Submodule.span_range_update_sub_smul`：span_range_update_sub_smul (hij : 
i != j) (v : ι -> M) (r : R) : span R (Set.range (Function.update v j (v j - r •
 v i))) = span R (Set.rang…
-/
lemma idealSpan_range_update_divByMonic (hij : i ≠ j) (v : ι → R[X]) :
    span (Set.range (Function.update v j (v j %ₘ v i))) = span (Set.range v) := by
  rw [modByMonic_eq_sub_mul_div, mul_comm, ← smul_eq_mul, Ideal.span, Ideal.span,
    Submodule.span_range_update_sub_smul hij]

end Polynomial

