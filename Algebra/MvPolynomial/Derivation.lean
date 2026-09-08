/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `MvPolynomial σ R` is determined by its values on all
monomials `MvPolynomial.X i`. We also provide a constructor `MvPolynomial.mkDerivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`MvPolynomial.mkDerivationEquiv` between `σ → A` and `Derivation (MvPolynomial σ R) A`.
-/

@[expose] public section


namespace MvPolynomial

noncomputable section

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

section

variable (R)

/-- The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`, as a linear map.
Use `MvPolynomial.mkDerivation` instead. -/
/-
**MvPolynomial.mkDerivation** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation (f : σ -> A) : Derivation R (MvPolynomial σ R) A where toLine
arMap
参数：f : σ -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`, as a linea
r map.
Use `MvPolynomial.mkDerivation` instead.
-/
def mkDerivationₗ (f : σ → A) : MvPolynomial σ R →ₗ[R] A :=
  Finsupp.lsum R (fun xs : σ →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf R R A).symm <|
      xs.sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

end

/-
**MvPolynomial.mkDerivation** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation (f : σ -> A) : Derivation R (MvPolynomial σ R) A where toLine
arMap
参数：f : σ -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkDerivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivationₗ R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  sum_monomial_eq <| map_zero _
/-
**MvPolynomial.mkDerivation** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation (f : σ -> A) : Derivation R (MvPolynomial σ R) A where toLine
arMap
参数：f : σ -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkDerivationₗ_C (f : σ → A) (r : R) : mkDerivationₗ R f (C r) = 0 :=
  (mkDerivationₗ_monomial f _ _).trans (smul_zero _)
/-
**MvPolynomial.mkDerivation** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation (f : σ -> A) : Derivation R (MvPolynomial σ R) A where toLine
arMap
参数：f : σ -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkDerivationₗ_X (f : σ → A) (i : σ) : mkDerivationₗ R f (X i) = f i :=
  (mkDerivationₗ_monomial f _ _).trans <| by simp [tsub_self]

@[simp]
/-
**MvPolynomial.derivation_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0
参数：D : Derivation R (MvPolynomial σ R) A；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
-/
theorem derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

@[simp]
/-
**MvPolynomial.derivation_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：derivation_C_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPo
lynomial σ R) : C (σ
参数：D : Derivation R (MvPolynomial σ R) A；a : R；f : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `MvPolynomial.derivation_C`：derivation_C (D : Derivation R (MvPolynomial 
σ R) A) (a : R) : D (C a) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
-/
theorem derivation_C_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R) :
    C (σ := σ) a • D f = a • D f := by
  have : C (σ := σ) a • D f = D (C a * f) := by simp
  rw [this, C_mul', D.map_smul]

/-- If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials from
`MvPolynomial.supported R s`. -/
/-
**MvPolynomial.derivation_eqOn_supported** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：derivation_eqOn_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s :
 Set σ} (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f in sup
ported R s) : D₁ f = D₂ f
参数：MvPolynomial σ R；h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s；hf : f in supported R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.eqOn_adjoin`：eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) :
 Set.EqOn D1 D2 (adjoin R s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)

--- 原说明 ---
If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials f
rom
`MvPolynomial.supported R s`.
-/
theorem derivation_eqOn_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
    (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f ∈ supported R s) :
    D₁ f = D₂ f :=
  Derivation.eqOn_adjoin (Set.forall_mem_image.2 h) hf
/-
**MvPolynomial.derivation_eq_of_forall_mem_vars** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) 
A} {f : MvPolynomial σ R} (h : forall i in f.vars, D₁ (X i) = D₂ (X i)) : D₁ f =
 D₂ f
参数：MvPolynomial σ R；h : forall i in f.vars, D₁ (X i) = D₂ (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.derivation_eqOn_supported`：derivation_eqOn_supported {D₁ D₂
 : Derivation R (MvPolynomial σ R) A} {s : Set σ} (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X
) s) {f : MvPolynomial σ R} …
· 使用定理 `MvPolynomial.mem_supported_vars`：mem_supported_vars (p : MvPolynomial σ 
R) : p in supported R (↑p.vars : Set σ)
-/
theorem derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D₁ (X i) = D₂ (X i)) : D₁ f = D₂ f :=
  derivation_eqOn_supported h f.mem_supported_vars
/-
**MvPolynomial.derivation_eq_zero_of_forall_mem_vars** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
形式化陈述：derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R)
 A} {f : MvPolynomial σ R} (h : forall i in f.vars, D (X i) = 0) : D f = 0
参数：MvPolynomial σ R；h : forall i in f.vars, D (X i) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.derivation_eq_of_forall_mem_vars`：derivation_eq_of_forall_m
em_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {f : MvPolynomial σ R} (h : 
forall i in f.vars, D₁ (X i) = D₂ (…
-/
theorem derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D (X i) = 0) : D f = 0 :=
  show D f = (0 : Derivation R (MvPolynomial σ R) A) f from derivation_eq_of_forall_mem_vars h

@[ext]
/-
**MvPolynomial.derivation_ext** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : forall i, 
D₁ (X i) = D₂ (X i)) : D₁ = D₂
参数：MvPolynomial σ R；h : forall i, D₁ (X i) = D₂ (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `MvPolynomial.derivation_eq_of_forall_mem_vars`：derivation_eq_of_forall_m
em_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {f : MvPolynomial σ R} (h : 
forall i in f.vars, D₁ (X i) = D₂ (…
-/
theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : ∀ i, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ :=
  Derivation.ext fun _ => derivation_eq_of_forall_mem_vars fun i _ => h i

variable [IsScalarTower R (MvPolynomial σ R) A]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.leibniz_iff_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：leibniz_iff_X (D : MvPolynomial σ R ->ₗ[R] A) (h₁ : D 1 = 0) : (forall p q
, D (p * q) = p • D q + q • D p) ↔ forall s i, D (monomial s 1 * X i) = (monomia
l s 1 : MvPolynomial σ R) • D (X i) + (X i : MvPolynomial σ R) • D (monomial s 1
)
参数：D : MvPolynomial σ R ->ₗ[R] A；h₁ : D 1 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.C_eq_smul_one`：C_eq_smul_one : (C a : MvPolynomial σ R) = a
 • (1 : MvPolynomial σ R)
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `_private.Mathlib.Algebra.MvPolynomial.Derivation.0.MvPolynomial.leibniz_
iff_X._abel_1_1`：∀ {σ : Type u_2} {R : Type u_3} {A : Type u_1} [inst : CommSemi
ring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [inst_3 : _…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
（共 31 条，此处仅展示前 30 条）
-/
theorem leibniz_iff_X (D : MvPolynomial σ R →ₗ[R] A) (h₁ : D 1 = 0) :
    (∀ p q, D (p * q) = p • D q + q • D p) ↔ ∀ s i, D (monomial s 1 * X i) =
    (monomial s 1 : MvPolynomial σ R) • D (X i) + (X i : MvPolynomial σ R) • D (monomial s 1) := by
  refine ⟨fun H p i => H _ _, fun H => ?_⟩
  have hC : ∀ r, D (C r) = 0 := by intro r; rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : ∀ p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction p using MvPolynomial.induction_on' with
    | monomial s r =>
      rw [← mul_one r, ← C_mul_monomial, mul_assoc, C_mul', D.map_smul, H, C_mul', smul_assoc,
        smul_add, D.map_smul, smul_comm r (X i)]
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_smul, smul_add, add_add_add_comm]
  intro p q
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [mul_comm, C_mul', hC, smul_zero, zero_add, D.map_smul, C_eq_smul_one, smul_one_smul]
  | add q₁ q₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]; abel
  | mul_X q i hq =>
    simp only [this, ← mul_assoc, hq, mul_smul, smul_add, add_assoc]
    rw [smul_comm (X i), smul_comm (X i)]

variable (R)

/-- The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`. -/
/-
**MvPolynomial.mkDerivation** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation (f : σ -> A) : Derivation R (MvPolynomial σ R) A where toLine
arMap
参数：f : σ -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`.
-/
def mkDerivation (f : σ → A) : Derivation R (MvPolynomial σ R) A where
  toLinearMap := mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mkDerivationₗ_C _ 1)).2 fun s i => by
      simp only [mkDerivationₗ_monomial, X, monomial_mul, one_smul, one_mul]
      rw [Finsupp.sum_add_index'] <;>
        [skip; simp; (intros; simp only [Nat.cast_add, (monomial _).map_add, add_smul])]
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> [skip; simp; simp]
      rw [tsub_self, add_tsub_cancel_right, Nat.cast_one, ← C_apply, C_1, one_smul, add_comm,
        Finsupp.smul_sum]
      refine congr_arg₂ (· + ·) rfl (Finset.sum_congr rfl fun j hj => ?_); dsimp only
      rw [smul_smul, monomial_mul, one_mul, add_comm s, add_tsub_assoc_of_le]
      rwa [Finsupp.single_le_iff, Nat.succ_le_iff, pos_iff_ne_zero, ← Finsupp.mem_support_iff]

@[simp]
/-
**MvPolynomial.mkDerivation_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation_X (f : σ -> A) (i : σ) : mkDerivation R f (X i) = f i
参数：f : σ -> A；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.mkDerivationₗ_X`：mkDerivationₗ_X (f : σ -> A) (i : σ) : mkD
erivationₗ R f (X i) = f i
-/
theorem mkDerivation_X (f : σ → A) (i : σ) : mkDerivation R f (X i) = f i :=
  mkDerivationₗ_X f i
/-
**MvPolynomial.mkDerivation_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivation_monomial (f : σ -> A) (s : σ ->₀ Nat) (r : R) : mkDerivation 
R f (monomial s r) = r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k :
 R) • f i
参数：f : σ -> A；s : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.mkDerivationₗ_monomial`：mkDerivationₗ_monomial (f : σ -> A)
 (s : σ ->₀ Nat) (r : R) : mkDerivationₗ R f (monomial s r) = r • s.sum fun i k 
=> monomial (s - Finsupp.…
-/
theorem mkDerivation_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivation R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  mkDerivationₗ_monomial f s r

/-- `MvPolynomial.mkDerivation` as a linear equivalence. -/
/-
**MvPolynomial.mkDerivationEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mkDerivationEquiv : (σ -> A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.mkDerivation` as a linear equivalence.
-/
def mkDerivationEquiv : (σ → A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D i => D (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_X _ _
      right_inv := fun _ => funext <| mkDerivation_X _ _ }

end

end MvPolynomial

