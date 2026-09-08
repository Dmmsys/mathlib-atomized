/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Evaluation of polynomials in subrings

## Main results

* `mem_map_rangeS`, `mem_map_range`: the range of `mapRingHom f` consists of
  polynomials with coefficients in the range of `f`

-/

public section

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]} [Semiring S]
variable (f : R →+* S)

/-
**Polynomial.mem_map_rangeS** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_map_rangeS {p : S[X]} : p in (mapRingHom f).rangeS ↔ forall n, p.coeff
 n in f.rangeS
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Polynomial.as_sum_range_C_mul_X_pow`：as_sum_range_C_mul_X_pow (p : R[X])
 : p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i
· 使用定理 `Subsemiring.sum_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R) {ι : Type u_1} {t : Finset ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∑ 
i ∈ t, f …
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
-/
theorem mem_map_rangeS {p : S[X]} : p ∈ (mapRingHom f).rangeS ↔ ∀ n, p.coeff n ∈ f.rangeS := by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_mapRingHom, coeff_map]
    exact Set.mem_range_self _
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine (mapRingHom f).rangeS.sum_mem ?_
    intro i _hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_mapRingHom, Polynomial.map_mul, map_C, hc, Polynomial.map_pow, map_X]
/-
**Polynomial.notMem_map_rangeS** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：notMem_map_rangeS {p : S[X]} : p ∉ (mapRingHom f).rangeS ↔ exists n, p.coe
ff n ∉ f.rangeS
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.mem_map_rangeS`：mem_map_rangeS {p : S[X]} : p in (mapRingHom 
f).rangeS ↔ forall n, p.coeff n in f.rangeS
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
-/
theorem notMem_map_rangeS {p : S[X]} : p ∉ (mapRingHom f).rangeS ↔ ∃ n, p.coeff n ∉ f.rangeS :=
  (mem_map_rangeS f (p := p)).not.trans not_forall
/-
**Polynomial.mem_map_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_map_range {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]} : 
p in (mapRingHom f).range ↔ forall n, p.coeff n in f.range
参数：f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mem_map_rangeS`：mem_map_rangeS {p : S[X]} : p in (mapRingHom 
f).rangeS ↔ forall n, p.coeff n in f.rangeS
-/
theorem mem_map_range {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {p : S[X]} :
    p ∈ (mapRingHom f).range ↔ ∀ n, p.coeff n ∈ f.range :=
  mem_map_rangeS f
/-
**Polynomial.notMem_map_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：notMem_map_range {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]}
 : p ∉ (mapRingHom f).range ↔ exists n, p.coeff n ∉ f.range
参数：f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.notMem_map_rangeS`：notMem_map_rangeS {p : S[X]} : p ∉ (mapRin
gHom f).rangeS ↔ exists n, p.coeff n ∉ f.rangeS
-/
theorem notMem_map_range {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {p : S[X]} :
    p ∉ (mapRingHom f).range ↔ ∃ n, p.coeff n ∉ f.range :=
  notMem_map_rangeS f

end Polynomial

