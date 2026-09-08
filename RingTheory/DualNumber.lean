/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Algebraic properties of dual numbers

## Main results

* `DualNumber.instLocalRing`: The dual numbers over a field `K` form a local ring.
* `DualNumber.instPrincipalIdealRing`: The dual numbers over a field `K` form a principal ideal
  ring.

-/

public section

namespace TrivSqZeroExt

variable {R M : Type*}

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

/-
**TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst** 是 Mathlib 中的一个引理，位于命名空间 `TrivS
qZeroExt`。
形式化陈述：isNilpotent_iff_isNilpotent_fst {x : TrivSqZeroExt R M} : IsNilpotent x ↔ 
IsNilpotent x.fst
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.fst_pow`：fst_pow [Monoid R] [AddMonoid M] [DistribMulActio
n R M] [DistribMulAction Rᵐᵒᵖ M] (x : tsze R M) (n : Nat) : fst (x ^ n) = x.fst 
^ n
· 使用定理 `TrivSqZeroExt.fst_zero`：fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst 
= 0
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `TrivSqZeroExt.snd_mul`：snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] 
(x₁ x₂ : tsze R M) : (x₁ * x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst
· 使用定理 `MulOpposite.op_zero`：∀ {α : Type u_1} [inst : Zero α], MulOpposite.op 0 
= 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `TrivSqZeroExt.snd_zero`：snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd 
= 0
-/
lemma isNilpotent_iff_isNilpotent_fst {x : TrivSqZeroExt R M} :
    IsNilpotent x ↔ IsNilpotent x.fst := by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n, ?_⟩
    rw [← fst_pow, hn, fst_zero]
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_add,
        snd_zero]

@[simp]
/-
**TrivSqZeroExt.isNilpotent_inl_iff** 是 Mathlib 中的一个引理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isNilpotent_inl_iff (r : R) : IsNilpotent (.inl r : TrivSqZeroExt R M) ↔ I
sNilpotent r
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst`：isNilpotent_iff_isNilpote
nt_fst {x : TrivSqZeroExt R M} : IsNilpotent x ↔ IsNilpotent x.fst
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isNilpotent_inl_iff (r : R) : IsNilpotent (.inl r : TrivSqZeroExt R M) ↔ IsNilpotent r := by
  rw [isNilpotent_iff_isNilpotent_fst, fst_inl]

@[simp]
/-
**TrivSqZeroExt.isNilpotent_inr** 是 Mathlib 中的一个引理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isNilpotent_inr (x : M) : IsNilpotent (.inr x : TrivSqZeroExt R M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `TrivSqZeroExt.inr_mul_inr`：inr_mul_inr [Semiring R] [AddCommMonoid M] [M
odule R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) : (inr m₁ * inr m₂ : tsze R M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNilpotent_inr (x : M) : IsNilpotent (.inr x : TrivSqZeroExt R M) := by
  refine ⟨2, by simp [pow_two]⟩

end Semiring

/-
**TrivSqZeroExt.isUnit_or_isNilpotent_of_isMaximal_isNilpotent** 是 Mathlib 中的一个引
理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isUnit_or_isNilpotent_of_isMaximal_isNilpotent [CommSemiring R] [AddCommGr
oup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (h : forall I : Ideal 
R, I.IsMaximal -> IsNilpotent I) (a : TrivSqZeroExt R M) : IsUnit a ∨ IsNilpoten
t a
参数：h : forall I : Ideal R, I.IsMaximal -> IsNilpotent I；a : TrivSqZeroExt R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.isUnit_iff_isUnit_fst`：isUnit_iff_isUnit_fst {x : tsze R M
} : IsUnit x ↔ IsUnit x.fst
· 使用引理 `TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst`：isNilpotent_iff_isNilpote
nt_fst {x : TrivSqZeroExt R M} : IsNilpotent x ↔ IsNilpotent x.fst
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `exists_max_ideal_of_mem_nonunits`：exists_max_ideal_of_mem_nonunits [Comm
Semiring α] (h : a in nonunits α) : exists I : Ideal α, I.IsMaximal ∧ a in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma isUnit_or_isNilpotent_of_isMaximal_isNilpotent [CommSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (h : ∀ I : Ideal R, I.IsMaximal → IsNilpotent I)
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  rw [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst]
  refine (em _).imp_right fun ha ↦ ?_
  obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  refine (h _ hI).imp fun n hn ↦ ?_
  exact hn.le (Ideal.pow_mem_pow haI _)
/-
**TrivSqZeroExt.isUnit_or_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isUnit_or_isNilpotent [DivisionSemiring R] [AddCommGroup M] [Module R M] [
Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (a : TrivSqZeroExt R M) : IsUnit a ∨ IsN
ilpotent a
参数：a : TrivSqZeroExt R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
-/
lemma isUnit_or_isNilpotent [DivisionSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  simp [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst, em']

end TrivSqZeroExt

namespace DualNumber
variable {R : Type*}

/-
**DualNumber.fst_eq_zero_iff_eps_dvd** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`。
形式化陈述：fst_eq_zero_iff_eps_dvd [Semiring R] {x : R[ε]} : x.fst = 0 ↔ ε ∣ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma fst_eq_zero_iff_eps_dvd [Semiring R] {x : R[ε]} :
    x.fst = 0 ↔ ε ∣ x := by
  simp_rw [dvd_def, TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
    fst_eps, snd_eps, zero_mul, zero_smul, zero_add, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, one_mul, exists_and_left, iff_self_and]
  intro
  exact ⟨.inl x.snd, rfl⟩
/-
**DualNumber.isNilpotent_eps** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`。
形式化陈述：isNilpotent_eps [Semiring R] : IsNilpotent (ε : R[ε])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TrivSqZeroExt.isNilpotent_inr`：isNilpotent_inr (x : M) : IsNilpotent (.i
nr x : TrivSqZeroExt R M)
-/
lemma isNilpotent_eps [Semiring R] :
    IsNilpotent (ε : R[ε]) :=
  TrivSqZeroExt.isNilpotent_inr 1

open TrivSqZeroExt
/-
**DualNumber.isNilpotent_iff_eps_dvd** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`。
形式化陈述：isNilpotent_iff_eps_dvd [DivisionSemiring R] {x : R[ε]} : IsNilpotent x ↔ 
ε ∣ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isNilpotent_iff_eps_dvd [DivisionSemiring R] {x : R[ε]} :
    IsNilpotent x ↔ ε ∣ x := by
  simp only [isNilpotent_iff_isNilpotent_fst, isNilpotent_iff_eq_zero, fst_eq_zero_iff_eps_dvd]

section Field

variable {K : Type*}

/-
**DualNumber.** 是 Mathlib 中的一个实例，位于命名空间 `DualNumber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionRing K] : IsLocalRing K[ε] where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [add_comm, ← eq_sub_iff_add_eq] at h
    rcases eq_or_ne (fst a) 0 with ha | ha <;>
    simp [isUnit_iff_isUnit_fst, h, ha]
/-
**DualNumber.ideal_trichotomy** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`。
形式化陈述：ideal_trichotomy [DivisionRing K] (I : Ideal K[ε]) : I = ⊥ ∨ I = .span {ε}
 ∨ I = ⊤
参数：I : Ideal K[ε]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用引理 `TrivSqZeroExt.isUnit_or_isNilpotent`：isUnit_or_isNilpotent [DivisionSemi
ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (
a : TrivSqZeroExt R M) : …
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DualNumber.isNilpotent_iff_eps_dvd`：isNilpotent_iff_eps_dvd [DivisionSem
iring R] {x : R[ε]} : IsNilpotent x ↔ ε ∣ x
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `DualNumber.commute_eps_right`：commute_eps_right [Semiring R] (x : DualNu
mber R) : Commute x ε
（共 36 条，此处仅展示前 30 条）
-/
lemma ideal_trichotomy [DivisionRing K] (I : Ideal K[ε]) :
    I = ⊥ ∨ I = .span {ε} ∨ I = ⊤ := by
  refine (eq_or_ne I ⊥).imp_right fun hb ↦ ?_
  refine (eq_or_ne I ⊤).symm.imp_left fun ht ↦ ?_
  have hd : ∀ x ∈ I, ε ∣ x := by
    intro x hxI
    rcases isUnit_or_isNilpotent x with hx | hx
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hxI hx) ht
    · rwa [← isNilpotent_iff_eps_dvd]
  have hd' : ∀ x ∈ I, x ≠ 0 → ∃ r, ε = r * x := by
    intro x hxI hx0
    obtain ⟨r, rfl⟩ := hd _ hxI
    have : ε * r = (fst r) • ε := by ext <;> simp
    rw [this] at hxI hx0 ⊢
    have hr : fst r ≠ 0 := by
      contrapose hx0
      simp [hx0]
    refine ⟨r⁻¹, ?_⟩
    simp [TrivSqZeroExt.ext_iff, inv_mul_cancel₀ hr]
  refine le_antisymm ?_ ?_ <;> intro x <;>
    simp_rw [Ideal.mem_span_singleton', (commute_eps_right _).eq, eq_comm, ← dvd_def]
  · intro hx
    simp_rw [hd _ hx]
  · intro hx
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨r, hr⟩ := hd' _ hyI hy0
    rw [(commute_eps_left _).eq, hr, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ hyI
/-
**DualNumber.isMaximal_span_singleton_eps** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`
。
形式化陈述：isMaximal_span_singleton_eps [DivisionRing K] : (Ideal.span {ε} : Ideal K[
ε]).IsMaximal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `DualNumber.ideal_trichotomy`：ideal_trichotomy [DivisionRing K] (I : Idea
l K[ε]) : I = ⊥ ∨ I = .span {ε} ∨ I = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isMaximal_span_singleton_eps [DivisionRing K] :
    (Ideal.span {ε} : Ideal K[ε]).IsMaximal := by
  refine ⟨?_, fun I hI ↦ ?_⟩
  · simp [ne_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton', TrivSqZeroExt.ext_iff]
  · rcases ideal_trichotomy I with rfl | rfl | rfl <;>
    first | simp at hI | simp
/-
**DualNumber.maximalIdeal_eq_span_singleton_eps** 是 Mathlib 中的一个引理，位于命名空间 `DualN
umber`。
形式化陈述：maximalIdeal_eq_span_singleton_eps [Field K] : IsLocalRing.maximalIdeal K[
ε] = Ideal.span {ε}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DualNumber.instIsLocalRing`：∀ {K : Type u_2} [inst : DivisionRing K], Is
LocalRing (DualNumber K)
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用引理 `DualNumber.isMaximal_span_singleton_eps`：isMaximal_span_singleton_eps [D
ivisionRing K] : (Ideal.span {ε} : Ideal K[ε]).IsMaximal
-/
lemma maximalIdeal_eq_span_singleton_eps [Field K] :
    IsLocalRing.maximalIdeal K[ε] = Ideal.span {ε} :=
  (IsLocalRing.eq_maximalIdeal isMaximal_span_singleton_eps).symm
/-
**DualNumber.** 是 Mathlib 中的一个实例，位于命名空间 `DualNumber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionRing K] : IsPrincipalIdealRing K[ε] where
  principal I := by
    rcases ideal_trichotomy I with rfl | rfl | rfl
    · exact bot_isPrincipal
    · exact ⟨_, rfl⟩
    · exact top_isPrincipal
/-
**DualNumber.exists_mul_left_or_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`
。
形式化陈述：exists_mul_left_or_mul_right [DivisionRing K] (a b : K[ε]) : exists c, a *
 c = b ∨ b * c = a
参数：a b : K[ε]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TrivSqZeroExt.isUnit_or_isNilpotent`：isUnit_or_isNilpotent [DivisionSemi
ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (
a : TrivSqZeroExt R M) : …
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `DualNumber.isNilpotent_iff_eps_dvd`：isNilpotent_iff_eps_dvd [DivisionSem
iring R] {x : R[ε]} : IsNilpotent x ↔ ε ∣ x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `TrivSqZeroExt.inl_mul`：inl_mul [Monoid R] [AddMonoid M] [DistribMulActio
n R M] [DistribMulAction Rᵐᵒᵖ M] (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl 
r₁ * inl r₂
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_mul_left_or_mul_right [DivisionRing K] (a b : K[ε]) :
    ∃ c, a * c = b ∨ b * c = a := by
  rcases isUnit_or_isNilpotent a with ha | ha
  · lift a to K[ε]ˣ using ha
    exact ⟨a⁻¹ * b, by simp⟩
  rcases isUnit_or_isNilpotent b with hb | hb
  · lift b to K[ε]ˣ using hb
    exact ⟨b⁻¹ * a, by simp⟩
  rw [isNilpotent_iff_eps_dvd] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  suffices ∃ c, fst x * fst c = fst y ∨ fst y * fst c = fst x by
    simpa [TrivSqZeroExt.ext_iff] using this
  rcases eq_or_ne (fst x) 0 with hx | hx
  · refine ⟨ε, Or.inr ?_⟩
    simp [hx]
  refine ⟨inl ((fst x)⁻¹ * fst y), ?_⟩
  simp [← mul_assoc, mul_inv_cancel₀ hx]

end Field

end DualNumber

