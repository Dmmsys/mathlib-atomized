/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Euler's homogeneous identity

## Main results

* `IsHomogeneous.sum_X_mul_pderiv`: Euler's identity for homogeneous polynomials:
  for a multivariate homogeneous polynomial,
  the product of each variable with the derivative with respect to that variable
  sums up to the degree times the polynomial.
* `IsWeightedHomogeneous.sum_weight_X_mul_pderiv`: the weighted version of Euler's identity.
-/

public section

namespace MvPolynomial

open Finsupp

variable {R σ M : Type*} [CommSemiring R] {φ : MvPolynomial σ R}

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.IsWeightedHomogeneous.pderiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial.IsWeightedHomogeneous`。
形式化陈述：∀ {R : Type u_1} {σ : Type u_2} {M : Type u_3} [inst : CommSemiring R] {φ 
: MvPolynomial σ R}   [inst_1 : AddCancelCommMonoid M] {w : σ → M} {n n' : M} {i
 : σ},   MvPolynomial.IsWeightedHomogeneous w φ n →     n' + w i = n → MvPolynom
ial.IsWeightedHomogeneous w ((MvPolynomial.pderiv i) φ) n'
参数：(MvPolynomial.pderiv i) φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.pderiv_monomial`：pderiv_monomial {i : σ} : pderiv i (monomi
al s a) = monomial (s - single i 1) (a * s i)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `MvPolynomial.isWeightedHomogeneous_zero`：isWeightedHomogeneous_zero (w :
 σ -> M) (m : M) : IsWeightedHomogeneous w (0 : MvPolynomial σ R) m
· 使用定理 `MvPolynomial.isWeightedHomogeneous_monomial`：isWeightedHomogeneous_monom
ial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M} (hm : weight w d = m) : IsWeigh
tedHomogeneous w (monomial d r) m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Finsupp.weight_sub_single_add`：weight_sub_single_add {f : σ ->₀ Nat} {i 
: σ} (hi : f i != 0) : (f - single i 1).weight w + w i = f.weight w
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.add`：add {w : σ -> M} (hφ : IsWeighte
dHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) : IsWeightedHomogeneous w
 (φ + ψ) n
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AddMonoidAlgebra.supported_eq_span_single`：∀ (R : Type u_1) {M : Type u_
3} [inst : Semiring R] (s : Set M),   AddMonoidAlgebra.supported R R s = Submodu
le.span R ((fun m => AddMonoidA…
· 使用定理 `MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported`：weighted
HomogeneousSubmodule_eq_finsupp_supported (w : σ -> M) (m : M) : weightedHomogen
eousSubmodule R w m = AddMonoidAlgebra.supported R R…
· 使用定理 `MvPolynomial.mem_weightedHomogeneousSubmodule`：mem_weightedHomogeneousSu
bmodule (w : σ -> M) (m : M) (p : MvPolynomial σ R) : p in weightedHomogeneousSu
bmodule R w m ↔ p.IsWeightedHomogen…
-/
protected lemma IsWeightedHomogeneous.pderiv [AddCancelCommMonoid M] {w : σ → M} {n n' : M} {i : σ}
    (h : φ.IsWeightedHomogeneous w n) (h' : n' + w i = n) :
    (pderiv i φ).IsWeightedHomogeneous w n' := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert! isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i), h', ← hm, weight_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h
/-
**MvPolynomial.IsHomogeneous.pderiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHo
mogeneous`。
形式化陈述：∀ {R : Type u_1} {σ : Type u_2} [inst : CommSemiring R] {φ : MvPolynomial 
σ R} {n : ℕ} {i : σ},   φ.IsHomogeneous n → ((MvPolynomial.pderiv i) φ).IsHomoge
neous (n - 1)
参数：(MvPolynomial.pderiv i) φ；n - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.totalDegree_zero_iff_isHomogeneous`：totalDegree_zero_iff_is
Homogeneous {p : MvPolynomial σ R} : p.totalDegree = 0 ↔ IsHomogeneous p 0
· 使用定理 `MvPolynomial.pderiv_C`：pderiv_C {i : σ} : pderiv i (C a) = 0
· 使用定理 `MvPolynomial.isHomogeneous_zero`：isHomogeneous_zero (n : Nat) : IsHomoge
neous (0 : MvPolynomial σ R) n
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.pderiv`：∀ {R : Type u_1} {σ : Type u_
2} {M : Type u_3} [inst : CommSemiring R] {φ : MvPolynomial σ R}   [inst_1 : Add
CancelCommMonoid M] {w : σ → M}…
-/
protected lemma IsHomogeneous.pderiv {n : ℕ} {i : σ} (h : φ.IsHomogeneous n) :
    (pderiv i φ).IsHomogeneous (n - 1) := by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    rw [h, pderiv_C]; apply isHomogeneous_zero
  · exact IsWeightedHomogeneous.pderiv h rfl

variable [Fintype σ] {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
open Finset in
/-- Euler's identity for weighted homogeneous polynomials. -/
/-
**MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv** 是 Mathlib 中的一个定理，
位于命名空间 `MvPolynomial.IsWeightedHomogeneous`。
形式化陈述：∀ {R : Type u_1} {σ : Type u_2} [inst : CommSemiring R] {φ : MvPolynomial 
σ R} [inst_1 : Fintype σ] {n : ℕ} {w : σ → ℕ},   MvPolynomial.IsWeightedHomogene
ous w φ n → ∑ i, w i • (MvPolynomial.X i * (MvPolynomial.pderiv i) φ) = n • φ
参数：MvPolynomial.X i * (MvPolynomial.pderiv i) φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `MvPolynomial.X_mul_pderiv_monomial`：X_mul_pderiv_monomial {i : σ} {m : σ
 ->₀ Nat} {r : R} : X i * pderiv i (monomial m r) = m i • monomial m r
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finsupp.weight_apply`：weight_apply (f : σ ->₀ R) : weight w f = Finsupp.
sum f (fun i c => c • w i)
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Euler's identity for weighted homogeneous polynomials.
-/
theorem IsWeightedHomogeneous.sum_weight_X_mul_pderiv {w : σ → ℕ}
    (h : φ.IsWeightedHomogeneous w n) : ∑ i : σ, w i • (X i * pderiv i φ) = n • φ := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← sum_smul, mul_comm (w _)]
    congr
    rwa [Set.mem_ofPred, weight_apply, sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum, ← nsmul_eq_mul, h]

/-- Euler's identity for homogeneous polynomials. -/
/-
**MvPolynomial.IsHomogeneous.sum_X_mul_pderiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial.IsHomogeneous`。
形式化陈述：∀ {R : Type u_1} {σ : Type u_2} [inst : CommSemiring R] {φ : MvPolynomial 
σ R} [inst_1 : Fintype σ] {n : ℕ},   φ.IsHomogeneous n → ∑ i, MvPolynomial.X i *
 (MvPolynomial.pderiv i) φ = n • φ
参数：MvPolynomial.pderiv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv`：∀ {R : Type 
u_1} {σ : Type u_2} [inst : CommSemiring R] {φ : MvPolynomial σ R} [inst_1 : Fin
type σ] {n : ℕ} {w : σ → ℕ},   MvPolynomial.IsWe…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Euler's identity for homogeneous polynomials.
-/
theorem IsHomogeneous.sum_X_mul_pderiv (h : φ.IsHomogeneous n) :
    ∑ i : σ, X i * pderiv i φ = n • φ := by
  simp_rw [← h.sum_weight_X_mul_pderiv, Pi.one_apply, one_smul]

end MvPolynomial

