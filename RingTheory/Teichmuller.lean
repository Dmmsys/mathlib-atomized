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

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {I : Ideal R} [CharP (R ⧸ I) p]

namespace Perfection

/-- An auxiliary sequence to define the Teichmüller map. The `(n + 1)`-st term is the `p^n`-th
power of an arbitrary lift in `R` of the `n`-th component from the perfection of `R ⧸ I`. -/
/-
**Perfection.teichmullerAux** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：{p : ℕ} →   [Fact (Nat.Prime p)] →     {R : Type u_1} → [inst : CommRing R
] → {I : Ideal R} → [CharP (R ⧸ I) p] → Perfection (R ⧸ I) p → ℕ → R
参数：Nat.Prime p；R ⧸ I；R ⧸ I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary sequence to define the Teichmüller map. The `(n + 1)`-st term is th
e `p^n`-th
power of an arbitrary lift in `R` of the `n`-th component from the perfection of
 `R ⧸ I`.
-/
noncomputable def teichmullerAux (x : Perfection (R ⧸ I) p) : ℕ → R
  | 0 => 1
  | n + 1 => (coeff _ p n x).out ^ p ^ n
/-
**Perfection.teichmullerAux_sModEq** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmullerAux_sModEq (x : Perfection (R ⧸ I) p) (m : Nat) : teichmullerAu
x x m ≡ teichmullerAux x (m + 1) [SMOD I ^ m]
参数：x : Perfection (R ⧸ I) p；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Perfection.teichmullerAux.congr_simp`：∀ {p : ℕ} [inst : Fact (Nat.Prime 
p)] {R : Type u_1} [inst_1 : CommRing R] {I : Ideal R} [inst_2 : CharP (R ⧸ I) p
]   (x x_1 : Perfection (R…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `Perfection.teichmullerAux.eq_2`：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R
 : Type u_1} [inst_1 : CommRing R] {I : Ideal R} [inst_2 : CharP (R ⧸ I) p]   (x
 : Perfection (R ⧸ I…
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `SModEq.pow_pow_add_one`：pow_pow_add_one {x y : R} (h : x ≡ y [SMOD I]) (
m : Nat) : x ^ p ^ m ≡ y ^ p ^ m [SMOD I ^ (m + 1)]
· 使用引理 `Ideal.natCast_mem_of_charP_quotient`：Ideal.natCast_mem_of_charP_quotient
 (p : Nat) (I : Ideal R) [CharP (R ⧸ I) p] : (p : R) in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.Quotient.mk_out`：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotien
t.out x) = x
· 使用定理 `Perfection.coeff_pow_p'`：coeff_pow_p' (f : Perfection R p) (n : Nat) : c
oeff R p (n + 1) f ^ p = coeff R p n f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem teichmullerAux_sModEq (x : Perfection (R ⧸ I) p) (m : ℕ) :
    teichmullerAux x m ≡ teichmullerAux x (m + 1) [SMOD I ^ m] := by
  obtain _ | m := m
  · simp
  symm
  rw [teichmullerAux, pow_succ' p, pow_mul]
  exact .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := m) <| by
    simp [SModEq.idealQuotientMk, coeff_pow_p']

/-- `teichmullerAux` as an adic Cauchy sequence. -/
/-
**Perfection.teichmullerCauchy** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmullerCauchy (x : Perfection (R ⧸ I) p) : AdicCompletion.AdicCauchySe
quence I R
参数：x : Perfection (R ⧸ I) p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`teichmullerAux` as an adic Cauchy sequence.
-/
noncomputable def teichmullerCauchy (x : Perfection (R ⧸ I) p) :
    AdicCompletion.AdicCauchySequence I R :=
  .mk _ _ (teichmullerAux x) <| by simpa using teichmullerAux_sModEq x

section IsPrecomplete
variable [IsPrecomplete I R]

/-
**Perfection.exists_teichmullerFun** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：exists_teichmullerFun (x : Perfection (R ⧸ I) p) : exists y : R, forall n,
 teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : Ideal R)]
参数：x : Perfection (R ⧸ I) p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrecomplete.prec'`：∀ {R : Type u_1} {inst : CommRing R} {I : Ideal R} 
{M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : 
IsPrecomp…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem exists_teichmullerFun (x : Perfection (R ⧸ I) p) :
    ∃ y : R, ∀ n, teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : Ideal R)] :=
  IsPrecomplete.prec' _ (teichmullerCauchy x).2

/-- Given an `I`-adically **pre**complete ring `R`, where `p ∈ I`, this is the underlying function
of the Teichmüller map. It is defined as the limit of `p^n`-th powers of arbitrary lifts in `R` of
the `n`-th component from the perfection of `R ⧸ I`.

The simp NF is `teichmuller₀` when `R` is `I`-adically complete. -/
/-
**Perfection.teichmullerFun** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmullerFun (x : Perfection (R ⧸ I) p) : R
参数：x : Perfection (R ⧸ I) p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.exists_teichmullerFun`：exists_teichmullerFun (x : Perfection 
(R ⧸ I) p) : exists y : R, forall n, teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : I
deal R)]

--- 原说明 ---
Given an `I`-adically **pre**complete ring `R`, where `p ∈ I`, this is the under
lying function
of the Teichmüller map. It is defined as the limit of `p^n`-th powers of arbitra
ry lifts in `R` of
the `n`-th component from the perfection of `R ⧸ I`.

The simp NF is `teichmuller₀` when `R` is `I`-adically complete.
-/
noncomputable def teichmullerFun (x : Perfection (R ⧸ I) p) : R :=
  (exists_teichmullerFun x).choose
/-
**Perfection.teichmullerFun_sModEq** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmullerFun_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : Nat} (h : Id
eal.Quotient.mk I y = coeff _ p n x) : teichmullerFun x ≡ y ^ p ^ n [SMOD I ^ (n
 + 1)]
参数：R ⧸ I；h : Ideal.Quotient.mk I y = coeff _ p n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Perfection.exists_teichmullerFun`：exists_teichmullerFun (x : Perfection 
(R ⧸ I) p) : exists y : R, forall n, teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : I
deal R)]
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SModEq.trans`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : 
AddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y z : M}, 
x …
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `SModEq.pow_pow_add_one`：pow_pow_add_one {x y : R} (h : x ≡ y [SMOD I]) (
m : Nat) : x ^ p ^ m ≡ y ^ p ^ m [SMOD I ^ (m + 1)]
· 使用引理 `Ideal.natCast_mem_of_charP_quotient`：Ideal.natCast_mem_of_charP_quotient
 (p : Nat) (I : Ideal R) [CharP (R ⧸ I) p] : (p : R) in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.Quotient.mk_out`：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotien
t.out x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem teichmullerFun_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmullerFun x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] := by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul, Ideal.mul_top] at this
  exact this.symm.trans <| .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := n) <| by
    simp [SModEq.idealQuotientMk, h]

end IsPrecomplete

variable [IsAdicComplete I R]

/-
**Perfection.teichmullerFun_spec'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmullerFun_spec' {x : Perfection (R ⧸ I) p} {y : R} (h : exists N, for
all n >= N, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMO
D I ^ (n + 1)]) : teichmullerFun x = y
参数：R ⧸ I；h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z = coeff _ 
p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsHausdorff.eq_iff_smodEq`：IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {
x y : M} : x = y ↔ forall n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `SModEq.mono`：mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD 
U₂]
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SModEq.trans`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : 
AddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y z : M}, 
x …
· 使用定理 `Perfection.teichmullerFun_sModEq`：teichmullerFun_sModEq {x : Perfection 
(R ⧸ I) p} {y : R} {n : Nat} (h : Ideal.Quotient.mk I y = coeff _ p n x) : teich
mullerFun x ≡ y ^ p ^ …
-/
theorem teichmullerFun_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y := by
  obtain ⟨N, h⟩ := h
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n ↦ ?_
  rw [smul_eq_mul, Ideal.mul_top]
  obtain hn | hn := le_total n N
  · obtain ⟨z, hz₁, hz₂⟩ := h N le_rfl
    exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono <| Ideal.pow_le_pow_right (by omega)
  · obtain ⟨z, hz₁, hz₂⟩ := h n hn
    exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono <| Ideal.pow_le_pow_right (by omega)
/-
**Perfection.teichmullerFun_spec** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmullerFun_spec {x : Perfection (R ⧸ I) p} {y : R} (h : forall n, exis
ts z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) 
: teichmullerFun x = y
参数：R ⧸ I；h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^
 n ≡ y [SMOD I ^ (n + 1)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Perfection.teichmullerFun_spec'`：teichmullerFun_spec' {x : Perfection (R
 ⧸ I) p} {y : R} (h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z =
 coeff _ p n x ∧ z ^ …
-/
theorem teichmullerFun_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y :=
  teichmullerFun_spec' ⟨0, fun n _ ↦ h n⟩

variable (p I) in
/-- Given an `I`-adically complete ring `R`, and a prime number `p` with `p ∈ I`, this is the
multiplicative map from `Perfection (R ⧸ I) p` to `R` itself. Specifically, it is defined as the
limit of `p^n`-th powers of arbitrary lifts in `R` of the `n`-th component from the perfection of
`R ⧸ I`.

The simp NF is `teichmuller₀`. -/
/-
**Perfection.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmuller : Perfection (R ⧸ I) p ->* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `I`-adically complete ring `R`, and a prime number `p` with `p ∈ I`, th
is is the
multiplicative map from `Perfection (R ⧸ I) p` to `R` itself. Specifically, it i
s defined as the
limit of `p^n`-th powers of arbitrary lifts in `R` of the `n`-th component from 
the perfection of
`R ⧸ I`.

The simp NF is `teichmuller₀`.
-/
noncomputable def teichmuller : Perfection (R ⧸ I) p →* R where
  toFun := teichmullerFun
  map_one' := teichmullerFun_spec fun _ ↦ ⟨1, by simp⟩
  map_mul' x y := by
    refine teichmullerFun_spec fun n ↦ ?_
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <;> simp
/-
**Perfection.teichmuller_sModEq** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmuller_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : Nat} (h : Ideal
.Quotient.mk I y = coeff _ p n x) : teichmuller p I x ≡ y ^ p ^ n [SMOD I ^ (n +
 1)]
参数：R ⧸ I；h : Ideal.Quotient.mk I y = coeff _ p n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Perfection.teichmullerFun_sModEq`：teichmullerFun_sModEq {x : Perfection 
(R ⧸ I) p} {y : R} {n : Nat} (h : Ideal.Quotient.mk I y = coeff _ p n x) : teich
mullerFun x ≡ y ^ p ^ …
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
-/
theorem teichmuller_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h
/-
**Perfection.teichmuller_spec'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmuller_spec' {x : Perfection (R ⧸ I) p} {y : R} (h : exists N, forall
 n >= N, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I
 ^ (n + 1)]) : teichmuller p I x = y
参数：R ⧸ I；h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z = coeff _ 
p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Perfection.teichmullerFun_spec'`：teichmullerFun_spec' {x : Perfection (R
 ⧸ I) p} {y : R} (h : exists N, forall n >= N, exists z, Ideal.Quotient.mk I z =
 coeff _ p n x ∧ z ^ …
-/
theorem teichmuller_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec' h
/-
**Perfection.teichmuller_spec** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmuller_spec {x : Perfection (R ⧸ I) p} {y : R} (h : forall n, exists 
z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) : t
eichmuller p I x = y
参数：R ⧸ I；h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^
 n ≡ y [SMOD I ^ (n + 1)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Perfection.teichmullerFun_spec`：teichmullerFun_spec {x : Perfection (R ⧸
 I) p} {y : R} (h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ 
z ^ p ^ n ≡ y [SMOD …
-/
theorem teichmuller_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec h
/-
**Perfection.teichmuller_zero** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：teichmuller_zero : teichmuller p I 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Perfection.teichmuller_spec`：teichmuller_spec {x : Perfection (R ⧸ I) p}
 {y : R} (h : forall n, exists z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p 
^ n ≡ y [SMOD I ^…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem teichmuller_zero : teichmuller p I 0 = 0 :=
  have : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec fun n ↦ ⟨0, by simp [zero_pow (pow_ne_zero n this)]⟩

variable (p I) in
/-- `teichmuller` as a `MonoidWithZeroHom`. This is the simp NF. -/
/-
**Perfection.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmuller : Perfection (R ⧸ I) p ->* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`teichmuller` as a `MonoidWithZeroHom`. This is the simp NF.
-/
noncomputable def teichmuller₀ : Perfection (R ⧸ I) p →*₀ R where
  __ := teichmuller p I
  map_zero' := teichmuller_zero
/-
**Perfection.teichmuller_eq_teichmuller** 是 Mathlib 中的一个引理，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma teichmuller_eq_teichmuller₀_toMonoidHom :
    teichmuller p I = (teichmuller₀ p I).toMonoidHom := rfl
/-
**Perfection.coe_teichmuller_eq_teichmuller** 是 Mathlib 中的一个引理，位于命名空间 `Perfectio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_teichmuller_eq_teichmuller₀ :
    ⇑(teichmuller p I) = teichmuller₀ p I := rfl
/-
**Perfection.teichmullerFun_eq_teichmuller** 是 Mathlib 中的一个引理，位于命名空间 `Perfection
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma teichmullerFun_eq_teichmuller₀ :
    teichmullerFun = teichmuller₀ p I := rfl
/-
**Perfection.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmuller : Perfection (R ⧸ I) p ->* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem teichmuller₀_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller₀ p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h
/-
**Perfection.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmuller : Perfection (R ⧸ I) p ->* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem teichmuller₀_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller₀ p I x = y :=
  teichmullerFun_spec' h
/-
**Perfection.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmuller : Perfection (R ⧸ I) p ->* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem teichmuller₀_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller₀ p I x = y :=
  teichmullerFun_spec h
/-
**Perfection.teichmuller** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：teichmuller : Perfection (R ⧸ I) p ->* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem teichmuller₀_mapMonoidHom_idealQuotientMk {x : Perfection R p} :
    teichmuller₀ p I (mapMonoidHom p (Ideal.Quotient.mk I) x) = coeffMonoidHom R p 0 x :=
  teichmuller₀_spec fun n ↦ ⟨coeffMonoidHom R p n x, by simp⟩
/-
**Perfection.mk_teichmuller** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：mk_teichmuller (x : Perfection (R ⧸ I) p) : Ideal.Quotient.mk I (teichmull
er p I x) = coeff _ p 0 x
参数：x : Perfection (R ⧸ I) p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Perfection.teichmuller_sModEq`：teichmuller_sModEq {x : Perfection (R ⧸ I
) p} {y : R} {n : Nat} (h : Ideal.Quotient.mk I y = coeff _ p n x) : teichmuller
 p I x ≡ y ^ p ^ n …
· 使用定理 `Ideal.Quotient.mk_out`：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotien
t.out x) = x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mk_teichmuller (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x := by
  have := teichmuller_sModEq <| Ideal.Quotient.mk_out <| coeff _ p 0 x
  simp_rw [zero_add, pow_one] at this
  simpa [SModEq.idealQuotientMk] using this
/-
**Perfection.mk_teichmuller** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：mk_teichmuller (x : Perfection (R ⧸ I) p) : Ideal.Quotient.mk I (teichmull
er p I x) = coeff _ p 0 x
参数：x : Perfection (R ⧸ I) p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Perfection.teichmuller_sModEq`：teichmuller_sModEq {x : Perfection (R ⧸ I
) p} {y : R} {n : Nat} (h : Ideal.Quotient.mk I y = coeff _ p n x) : teichmuller
 p I x ≡ y ^ p ^ n …
· 使用定理 `Ideal.Quotient.mk_out`：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotien
t.out x) = x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
@[simp] theorem mk_teichmuller₀ (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller₀ p I x) = coeff _ p 0 x := mk_teichmuller _

variable (p I) in
/-
**Perfection.mk_comp_teichmuller** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：mk_comp_teichmuller : (Ideal.Quotient.mk I : _ ->* _).comp (teichmuller p 
I) = (coeff (R ⧸ I) p 0 : Perfection (R ⧸ I) p ->* R ⧸ I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Perfection.mk_teichmuller`：mk_teichmuller (x : Perfection (R ⧸ I) p) : I
deal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x
-/
theorem mk_comp_teichmuller :
    (Ideal.Quotient.mk I : _ →* _).comp (teichmuller p I) =
      (coeff (R ⧸ I) p 0 : Perfection (R ⧸ I) p →* R ⧸ I) :=
  MonoidHom.ext mk_teichmuller

variable (p I) in
/-
**Perfection.mk_comp_teichmuller** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：mk_comp_teichmuller : (Ideal.Quotient.mk I : _ ->* _).comp (teichmuller p 
I) = (coeff (R ⧸ I) p 0 : Perfection (R ⧸ I) p ->* R ⧸ I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Perfection.mk_teichmuller`：mk_teichmuller (x : Perfection (R ⧸ I) p) : I
deal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x
-/
theorem mk_comp_teichmuller₀ :
    (MonoidWithZeroHom.ofClass (Ideal.Quotient.mk I)).comp (teichmuller₀ p I) =
      .ofClass (coeff (R ⧸ I) p 0) :=
  MonoidWithZeroHom.ext mk_teichmuller

variable (p I) in
/-
**Perfection.mk_comp_teichmuller'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：mk_comp_teichmuller' : Ideal.Quotient.mk I ∘ (teichmuller p I) = coeff (R 
⧸ I) p 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Perfection.mk_teichmuller`：mk_teichmuller (x : Perfection (R ⧸ I) p) : I
deal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x
-/
theorem mk_comp_teichmuller' :
    Ideal.Quotient.mk I ∘ (teichmuller p I) = coeff (R ⧸ I) p 0 :=
  funext mk_teichmuller

/-- If `R` is `I`-adically complete and `R ⧸ I` has characteristic `p`, then
`Perfection R p` and `Perfection (R ⧸ I) p` are isomorphic as monoids.

Note that `Perfection R p` is generally not a ring, and the forward map is induced by
the quotient map, and the backwards map is constructed using the Teichmüller map. -/
/-
**Perfection.quotientMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：quotientMulEquiv (p : Nat) [Fact p.Prime] {R : Type*} [CommRing R] (I : Id
eal R) [CharP (R ⧸ I) p] [IsAdicComplete I R] : Perfection R p ≃* Perfection (R 
⧸ I) p
参数：p : Nat；I : Ideal R；R ⧸ I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
If `R` is `I`-adically complete and `R ⧸ I` has characteristic `p`, then
`Perfection R p` and `Perfection (R ⧸ I) p` are isomorphic as monoids.

Note that `Perfection R p` is generally not a ring, and the forward map is induc
ed by
the quotient map, and the backwards map is constructed using the Teichmüller map
.
-/
noncomputable def quotientMulEquiv (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] (I : Ideal R) [CharP (R ⧸ I) p] [IsAdicComplete I R] :
    Perfection R p ≃* Perfection (R ⧸ I) p := MonoidHom.toMulEquiv
  (mapMonoidHom _ <| Ideal.Quotient.mk I)
  (liftMonoidHom p _ _ <| teichmuller p I)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)
/-
**Perfection.coeff_quotientMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommRing R]
 {I : Ideal R} [inst_2 : CharP (R ⧸ I) p]   [inst_3 : IsAdicComplete I R] (x : P
erfection R p) (n : ℕ),   (Perfection.coeff (R ⧸ I) p n) ((Perfection.quotientMu
lEquiv p I) x) =     (Ideal.Quotient.mk I) ((Perfection.coeffMonoidHom R p n) x)
参数：Nat.Prime p；R ⧸ I；x : Perfection R p；n : ℕ；Perfection.coeff (R ⧸ I) p n；(Perf
ection.quotientMulEquiv p I) x；Ideal.Quotient.mk I；(Perfection.coeffMonoidHom R 
p n) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coeff_quotientMulEquiv (x : Perfection R p) (n : ℕ) :
    coeff (R ⧸ I) p n (quotientMulEquiv p I x) = Ideal.Quotient.mk I (coeffMonoidHom R p n x) := rfl
/-
**Perfection.coeff_zero_symm_quotientMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Perfect
ion`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommRing R]
 {I : Ideal R} [inst_2 : CharP (R ⧸ I) p]   [inst_3 : IsAdicComplete I R] (x : P
erfection (R ⧸ I) p),   (Perfection.coeffMonoidHom R p 0) ((Perfection.quotientM
ulEquiv p I).symm x) = (Perfection.teichmuller₀ p I) x
参数：Nat.Prime p；R ⧸ I；x : Perfection (R ⧸ I) p；Perfection.coeffMonoidHom R p 0；(P
erfection.quotientMulEquiv p I).symm x；Perfection.teichmuller₀ p I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MonoidHom.toMulEquiv_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst :
 MulOneClass M] [inst_1 : MulOneClass N] (f : M →* N) (g : N →* M)   (h₁ : g.com
p f = MonoidHom.id M)…
· 使用定理 `Perfection.coeffMonoidHom_zero_liftMonoidHom`：∀ (p : ℕ) {M : Type u_2} {
N : Type u_3} [inst : CommMonoid M] [inst_1 : PerfectRing M p] [inst_2 : CommMon
oid N]   (e : M →* N) (x : M), (Pe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem coeff_zero_symm_quotientMulEquiv (x : Perfection (R ⧸ I) p) :
    coeffMonoidHom R p 0 (quotientMulEquiv p I |>.symm x) = teichmuller₀ p I x := by
  simp [quotientMulEquiv]

end Perfection

