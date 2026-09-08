/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Eigenvalues are the roots of the minimal polynomial.

## Tags

eigenvalue, minimal polynomial
-/

public section


universe u v w

namespace Module

namespace End

open Polynomial Module

open scoped Polynomial

section CommSemiring

variable {R : Type v} {M : Type w} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-
**Module.End.ker_aeval_ring_hom'_unit_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.End`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommSemiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) (c : (Polynomial R)ˣ), 
LinearMap.ker ((Polynomial.aeval f) ↑c) = ⊥
参数：f : Module.End R M；c : (Polynomial R)ˣ；(Polynomial.aeval f) ↑c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem ker_aeval_ring_hom'_unit_polynomial (f : End R M) (c : R[X]ˣ) :
    LinearMap.ker (aeval f (c : R[X])) = ⊥ :=
  LinearMap.ker_eq_bot'.mpr fun m hm ↦ by
    simpa [← mul_apply, ← aeval_mul] using congr(c⁻¹.1.aeval f $hm)

end CommSemiring

section CommRing

variable {R : Type v} {M : Type w} [CommRing R] [AddCommGroup M] [Module R M] {f : End R M} {μ : R}
  {x : M} {p : R[X]}

/-
**Module.End.aeval_apply_of_hasEigenvector** 是 Mathlib 中的一个定理，位于命名空间 `Module.End
`。
形式化陈述：aeval_apply_of_hasEigenvector (h : f.HasEigenvector μ x) : aeval f p x = p
.eval μ • x
参数：h : f.HasEigenvector μ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 31 条，此处仅展示前 30 条）
-/
theorem aeval_apply_of_hasEigenvector (h : f.HasEigenvector μ x) :
    aeval f p x = p.eval μ • x := by
  refine p.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm, pow_succ', mul_assoc, map_mul, Module.End.mul_apply, mul_comm, hna]
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      map_smulₛₗ, RingHom.id_apply, mul_comm]

/-- A variant of `Module.End.aeval_apply_of_hasEigenvector` which does not require `x ≠ 0`. -/
/-
**Module.End.aeval_apply_of_mem_apply_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `Module.
End`。
形式化陈述：aeval_apply_of_mem_apply_eq_smul (hx : f x = μ • x) : aeval f p x = p.eval
 μ • x
参数：hx : f x = μ • x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.aeval_apply_of_hasEigenvector`：aeval_apply_of_hasEigenvector 
(h : f.HasEigenvector μ x) : aeval f p x = p.eval μ • x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x

--- 原说明 ---
A variant of `Module.End.aeval_apply_of_hasEigenvector` which does not require `
x ≠ 0`.
-/
lemma aeval_apply_of_mem_apply_eq_smul (hx : f x = μ • x) :
    aeval f p x = p.eval μ • x := by
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · exact aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩
/-
**Module.End.isRoot_of_hasEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：isRoot_of_hasEigenvalue [IsDomain R] [IsTorsionFree R M] {f : End R M} {μ 
: R} (h : f.HasEigenvalue μ) : (minpoly R f).IsRoot μ
参数：h : f.HasEigenvalue μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.aeval_apply_of_hasEigenvector`：aeval_apply_of_hasEigenvector 
(h : f.HasEigenvector μ x) : aeval f p x = p.eval μ • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isRoot_of_hasEigenvalue [IsDomain R] [IsTorsionFree R M] {f : End R M} {μ : R}
    (h : f.HasEigenvalue μ) : (minpoly R f).IsRoot μ := by
  rcases (Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine Or.resolve_right (smul_eq_zero.1 ?_) ne0
  rw [← aeval_apply_of_hasEigenvector ⟨H, ne0⟩]
  simp

section IsDomain

variable [IsDomain R] [Module.Finite R M]

/-
**Module.End.hasEigenvalue_of_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvalue_of_isRoot (h : (minpoly R f).IsRoot μ) : f.HasEigenvalue μ
参数：h : (minpoly R f).IsRoot μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.End.hasEigenvalue_of_hasEigenvector`：hasEigenvalue_of_hasEigenvec
tor {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) : HasEigenvalue f μ
· 使用引理 `Module.End.hasEigenvector_iff`：hasEigenvector_iff {f : End R M} {μ : R} 
{x : M} : f.HasEigenvector μ x ↔ x in f.eigenspace μ ∧ x != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 33 条，此处仅展示前 30 条）
-/
theorem hasEigenvalue_of_isRoot (h : (minpoly R f).IsRoot μ) : f.HasEigenvalue μ := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h
  obtain ⟨v, hv⟩ : ∃ v : M, q.aeval f v ≠ 0 := by
    by_contra! h_contra
    have := minpoly.min R f
      ((monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral f)))
      (LinearMap.ext h_contra)
    rw [hq, degree_mul, degree_X_sub_C, degree_eq_natDegree] at this
    · norm_cast at this; grind
    · rintro rfl
      exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral f) (mul_zero (X - C μ) ▸ hq)
  refine Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_iff.mpr ⟨?_, hv⟩)
  simpa [sub_eq_zero, hq] using congr($(minpoly.aeval R f) v)

variable [IsTorsionFree R M]
/-
**Module.End.hasEigenvalue_iff_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvalue_iff_isRoot : f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.isRoot_of_hasEigenvalue`：isRoot_of_hasEigenvalue [IsDomain R]
 [IsTorsionFree R M] {f : End R M} {μ : R} (h : f.HasEigenvalue μ) : (minpoly R 
f).IsRoot μ
· 使用定理 `Module.End.hasEigenvalue_of_isRoot`：hasEigenvalue_of_isRoot (h : (minpol
y R f).IsRoot μ) : f.HasEigenvalue μ
-/
theorem hasEigenvalue_iff_isRoot : f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ :=
  ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩

variable (f)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Module.End.finite_hasEigenvalue** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：finite_hasEigenvalue : Set.Finite {μ | f.HasEigenvalue μ}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Polynomial.rootSet_finite`：rootSet_finite (p : T[X]) (S : Type*) [CommRi
ng S] [IsDomain S] [Algebra T S] : (p.rootSet S).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma finite_hasEigenvalue : Set.Finite {μ | f.HasEigenvalue μ} := by
  have h : minpoly R f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := R) f)
  refine ((minpoly R f).rootSet_finite R).subset ?_
  simp [Set.subset_def, hasEigenvalue_iff_isRoot, mem_rootSet, h]

/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
/-
**Module.End.** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An endomorphism of a finite-dimensional vector space has finitely many eigenvalu
es.
-/
noncomputable instance : Fintype f.Eigenvalues :=
  Set.Finite.fintype f.finite_hasEigenvalue

end IsDomain

end CommRing

section Field

variable {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]

/-
**Module.End.eigenspace_aeval_polynomial_degree_1** 是 Mathlib 中的一个定理，位于命名空间 `Mod
ule.End`。
形式化陈述：eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : K[X]) (hq : degree
 q = 1) : eigenspace f (-q.coeff 0 / q.leadingCoeff) = LinearMap.ker (aeval f q)
参数：f : End K V；q : K[X]；hq : degree q = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.eigenspace_div`：eigenspace_div (f : End K V) (a b : K) (hb : 
b != 0) : eigenspace f (a / b) = LinearMap.ker (b • f - algebraMap K (End K V) a
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot`：leadingCoeff_eq_zero_iff
_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥
· 使用定理 `WithBot.one_ne_bot`：∀ {α : Type u} [inst : One α], 1 ≠ ⊥
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Polynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_smul`：eval₂_smul (g : R ->+* S) (p : R[X]) (x : S) {s :
 R} : eval₂ g x (s • p) = g s * eval₂ g x p
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_X_add_C_of_degree_eq_one`：eq_X_add_C_of_degree_eq_one (h :
 degree p = 1) : p = C p.leadingCoeff * X + C (p.coeff 0)
-/
theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : K[X]) (hq : degree q = 1) :
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = LinearMap.ker (aeval f q) :=
  calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff)
    _ = LinearMap.ker (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)) := by
          apply eigenspace_div
          rw [Ne, leadingCoeff_eq_zero_iff_deg_eq_bot, hq]
          exact WithBot.one_ne_bot
    _ = LinearMap.ker (aeval f (C q.leadingCoeff * X + C (q.coeff 0))) := by
          rw [C_mul', aeval_def]; simp [algebraMap, Algebra.algebraMap]
    _ = LinearMap.ker (aeval f q) := by rwa [← eq_X_add_C_of_degree_eq_one]

end Field

end End

end Module

section FiniteSpectrum

set_option backward.isDefEq.respectTransparency.types false in
/-- An endomorphism of a finite-dimensional vector space has a finite spectrum. -/
/-
**Module.End.finite_spectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.finite_spectrum {K : Type v} {V : Type w} [Field K] [AddCommGro
up V] [Module K V] [FiniteDimensional K V] (f : Module.End K V) : Set.Finite (sp
ectrum K f)
参数：f : Module.End K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Module.End.hasEigenvalue_iff_mem_spectrum`：hasEigenvalue_iff_mem_spectru
m [FiniteDimensional K V] {f : End K V} {μ : K} : f.HasEigenvalue μ ↔ μ in spect
rum K f
· 使用引理 `Module.End.finite_hasEigenvalue`：finite_hasEigenvalue : Set.Finite {μ | 
f.HasEigenvalue μ}
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M

--- 原说明 ---
An endomorphism of a finite-dimensional vector space has a finite spectrum.
-/
theorem Module.End.finite_spectrum {K : Type v} {V : Type w} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) :
    Set.Finite (spectrum K f) := by
  convert! f.finite_hasEigenvalue using 1
  ext x
  exact Module.End.hasEigenvalue_iff_mem_spectrum.symm

variable {n R : Type*} [Field R] [Fintype n] [DecidableEq n]

/-- An n x n matrix over a field has a finite spectrum. -/
/-
**Matrix.finite_spectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.finite_spectrum (A : Matrix n n R) : Set.Finite (spectrum R A)
参数：A : Matrix n n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.spectrum_eq`：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiri
ng R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivC
lass F R A…
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Module.End.finite_spectrum`：Module.End.finite_spectrum {K : Type v} {V :
 Type w} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Mo
dule.End K V) : …

--- 原说明 ---
An n x n matrix over a field has a finite spectrum.
-/
theorem Matrix.finite_spectrum (A : Matrix n n R) : Set.Finite (spectrum R A) := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n) A]
  exact Module.End.finite_spectrum _
/-
**Matrix.instFiniteSpectrum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Matrix.instFiniteSpectrum (A : Matrix n n R) : Finite (spectrum R A)
参数：A : Matrix n n R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Matrix.finite_spectrum`：Matrix.finite_spectrum (A : Matrix n n R) : Set.
Finite (spectrum R A)
-/
instance Matrix.instFiniteSpectrum (A : Matrix n n R) : Finite (spectrum R A) :=
  Set.finite_coe_iff.mpr (Matrix.finite_spectrum A)

end FiniteSpectrum

