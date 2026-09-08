/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Invariant and root-positive bilinear forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
Given a root pairing we define a structure which contains a bilinear form together with axioms for
reflection-invariance, symmetry, and strict positivity on all roots.  We show that root-positive
forms display the same sign behavior as the canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras.  In the finite case, the canonical polarization yields a root-positive form that is
positive semi-definite on weight space and positive-definite on the span of roots.

## Main definitions / results:

* `RootPairing.InvariantForm`: an invariant bilinear form on a root pairing.
* `RootPairing.RootPositiveForm`: Given a root pairing this is a structure which contains a
  bilinear form together with axioms for reflection-invariance, symmetry, and strict positivity on
  all roots.
* `RootPairing.zero_lt_pairingIn_iff`: sign relations between `RootPairing.pairingIn` and a
  root-positive form.
* `RootPairing.pairing_eq_zero_iff`: symmetric vanishing condition for `RootPairing.pairing`
* `RootPairing.coxeterWeight_nonneg`: All pairs of roots have non-negative Coxeter weight.
* `RootPairing.coxeterWeight_zero_iff_isOrthogonal` : A Coxeter weight vanishes iff the roots are
  orthogonal.

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R S M N : Type*} [CommRing S] [LinearOrder S]
  [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- Given a root pairing, this is an invariant symmetric bilinear form. -/
/-
**RootPairing.InvariantForm** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_4} →       {N : Type u
_5} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Type (max u_2 u_4)
参数：max u_2 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a root pairing, this is an invariant symmetric bilinear form.
-/
structure InvariantForm (P : RootPairing ι R M N) where
  /-- The bilinear form bundled inside an `InvariantForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  ne_zero (i : ι) : form (P.root i) (P.root i) ≠ 0
  isOrthogonal_reflection (i : ι) : form.IsOrthogonal (P.reflection i)

namespace InvariantForm

variable {P : RootPairing ι R M N} (B : P.InvariantForm) (i j : ι)

/-
**RootPairing.InvariantForm.apply_root_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring.InvariantForm`。
形式化陈述：apply_root_ne_zero : B.form (P.root i) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_root_ne_zero : B.form (P.root i) ≠ 0 :=
  fun contra ↦ B.ne_zero i <| by simp [contra]
/-
**RootPairing.InvariantForm.two_mul_apply_root_root** 是 Mathlib 中的一个引理，位于命名空间 `R
ootPairing.InvariantForm`。
形式化陈述：two_mul_apply_root_root : 2 * B.form (P.root i) (P.root j) = P.pairing i j
 * B.form (P.root j) (P.root j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `RootPairing.InvariantForm.isOrthogonal_reflection`：∀ {ι : Type u_1} {R :
 Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGr
oup M]   [inst_2 : _root_.Module R M] […
· 使用引理 `RootPairing.reflection_apply`：reflection_apply (x : M) : P.reflection i 
x = x - (P.coroot' i x) • P.root i
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `RootPairing.root_coroot'_eq_pairing`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `LinearMap.map_sub₂`：map_sub₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z) :
 f (x - y) z = f x z - f y z
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
-/
lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j]
  rw [reflection_apply, reflection_apply_self, root_coroot'_eq_pairing, LinearMap.map_sub₂,
    LinearMap.map_smul₂, smul_eq_mul, map_neg, map_neg, mul_neg, neg_sub_neg]
/-
**RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.InvariantForm`。
形式化陈述：pairing_mul_eq_pairing_mul_swap : P.pairing j i * B.form (P.root i) (P.roo
t i) = P.pairing i j * B.form (P.root j) (P.root j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `RootPairing.InvariantForm.symm`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
-/
lemma pairing_mul_eq_pairing_mul_swap :
    P.pairing j i * B.form (P.root i) (P.root i) =
    P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [← B.two_mul_apply_root_root i j, ← B.two_mul_apply_root_root j i, ← B.symm.eq,
    RingHom.id_apply]

@[simp]
/-
**RootPairing.InvariantForm.apply_reflection_reflection** 是 Mathlib 中的一个引理，位于命名空
间 `RootPairing.InvariantForm`。
形式化陈述：apply_reflection_reflection (x y : M) : B.form (P.reflection i x) (P.refle
ction i y) = B.form x y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.InvariantForm.isOrthogonal_reflection`：∀ {ι : Type u_1} {R :
 Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGr
oup M]   [inst_2 : _root_.Module R M] […
-/
lemma apply_reflection_reflection (x y : M) :
    B.form (P.reflection i x) (P.reflection i y) = B.form x y :=
  B.isOrthogonal_reflection i x y

@[simp]
/-
**RootPairing.InvariantForm.apply_root_root_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.InvariantForm`。
形式化陈述：apply_root_root_zero_iff [IsDomain R] [NeZero (2 : R)] : B.form (P.root i)
 (P.root j) = 0 ↔ P.pairing i j = 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma apply_root_root_zero_iff [IsDomain R] [NeZero (2 : R)] :
    B.form (P.root i) (P.root j) = 0 ↔ P.pairing i j = 0 := by
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp [two_ne_zero]
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [B.two_mul_apply_root_root i j]
    _ ↔ P.pairing i j = 0 := by simp [B.ne_zero j]

end InvariantForm

variable (S) in
/-- Given a root pairing, this is an invariant symmetric bilinear form satisfying a positivity
condition. -/
/-
**RootPairing.RootPositiveForm** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     (S : Type u_3) →       {M : Type u
_4} →         {N : Type u_5} →           [inst : CommRing S] →             [Line
arOrder S] →               [inst_2 : CommRing R] →                 [inst_3 : Alg
ebra S R] →                   [inst_4 : AddCommGroup M] →                     [i
nst_5 : _root_.Module R M] →                       [inst_6 : AddCommGroup N] →  
                       [inst_7 : _root_.Module R N] → (P : RootPairing ι R M N) 
→ [P.IsValuedIn S] → Type (max u_2 u_4)
参数：S : Type u_3；P : RootPairing ι R M N；max u_2 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a root pairing, this is an invariant symmetric bilinear form satisfying a 
positivity
condition.
-/
structure RootPositiveForm (P : RootPairing ι R M N) [P.IsValuedIn S] where
  /-- The bilinear form bundled inside a `RootPositiveForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  isOrthogonal_reflection (i : ι) : form.IsOrthogonal (P.reflection i)
  exists_eq (i j : ι) : ∃ s, algebraMap S R s = form (P.root i) (P.root j)
  exists_pos_eq (i : ι) : ∃ s > 0, algebraMap S R s = form (P.root i) (P.root i)

variable {P : RootPairing ι R M N} [P.IsValuedIn S] (B : P.RootPositiveForm S) (i j : ι)
  [FaithfulSMul S R] [Module S M] [IsScalarTower S R M]

namespace RootPositiveForm

omit [Module S M] [IsScalarTower S R M] in
/-
**RootPairing.RootPositiveForm.form_apply_root_ne_zero** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing.RootPositiveForm`。
形式化陈述：form_apply_root_ne_zero (i : ι) : B.form (P.root i) (P.root i) != 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.RootPositiveForm.exists_pos_eq`：∀ {ι : Type u_1} {R : Type u
_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [inst_1 :
 LinearOrder S] [inst_2 : CommRi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma form_apply_root_ne_zero (i : ι) :
    B.form (P.root i) (P.root i) ≠ 0 := by
  obtain ⟨s, hs, hs'⟩ := B.exists_pos_eq i
  simpa [← hs'] using hs.ne'

/-- Forgetting the positivity condition, we may regard a `RootPositiveForm` as an `InvariantForm`.
-/
/-
**RootPairing.RootPositiveForm.toInvariantForm** 是 Mathlib 中的一个定义，位于命名空间 `RootPa
iring.RootPositiveForm`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {S : Type u_3} →       {M : Type u
_4} →         {N : Type u_5} →           [inst : CommRing S] →             [inst
_1 : LinearOrder S] →               [inst_2 : CommRing R] →                 [ins
t_3 : Algebra S R] →                   [inst_4 : AddCommGroup M] →              
       [inst_5 : _root_.Module R M] →                       [inst_6 : AddCommGro
up N] →                         [inst_7 : _root_.Module R N] →                  
         {P : RootPairing ι R M N} →                             [inst_8 : P.IsV
aluedIn S] →                               RootPairing.RootPositiveForm S P → [F
aithfulSMul S R] → P.InvariantForm
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.RootPositiveForm.symm`：∀ {ι : Type u_1} {R : Type u_2} {S : 
Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [inst_1 : LinearOr
der S] [inst_2 : CommRi…
· 使用引理 `RootPairing.RootPositiveForm.form_apply_root_ne_zero`：form_apply_root_ne
_zero (i : ι) : B.form (P.root i) (P.root i) != 0
· 使用定理 `RootPairing.RootPositiveForm.isOrthogonal_reflection`：∀ {ι : Type u_1} {
R : Type u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]  
 [inst_1 : LinearOrder S] [inst_2 : CommRi…

--- 原说明 ---
Forgetting the positivity condition, we may regard a `RootPositiveForm` as an `I
nvariantForm`.
-/
@[simps] def toInvariantForm : InvariantForm P where
  form := B.form
  symm := B.symm
  ne_zero := B.form_apply_root_ne_zero
  isOrthogonal_reflection := B.isOrthogonal_reflection

omit [Module S M] [IsScalarTower S R M] in
/-
**RootPairing.RootPositiveForm.two_mul_apply_root_root** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing.RootPositiveForm`。
形式化陈述：two_mul_apply_root_root : 2 * B.form (P.root i) (P.root j) = P.pairing i j
 * B.form (P.root j) (P.root j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
-/
lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) :=
  B.toInvariantForm.two_mul_apply_root_root i j

/-- Given a root-positive form associated to a root pairing with coefficients in `R` but taking
values in `S`, this is the associated `S`-bilinear form on the `S`-span of the roots. -/
/-
**RootPairing.RootPositiveForm.posForm** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Ro
otPositiveForm`。
形式化陈述：posForm : LinearMap.BilinForm S (span S (range P.root))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a root-positive form associated to a root pairing with coefficients in `R`
 but taking
values in `S`, this is the associated `S`-bilinear form on the `S`-span of the r
oots.
-/
def posForm :
    LinearMap.BilinForm S (span S (range P.root)) :=
  LinearMap.restrictScalarsRange₂ (span S (range P.root)).subtype (span S (range P.root)).subtype
  (Algebra.linearMap S R) (FaithfulSMul.algebraMap_injective S R) B.form
  (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (s := range P.root) (t := range P.root)
      (B := (LinearMap.restrictScalarsₗ S R _ _ _).comp (B.form.restrictScalars S))
    · rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
      simpa using B.exists_eq i j
    · simpa
    · simpa)

set_option backward.isDefEq.respectTransparency.types false in
/-
**RootPairing.RootPositiveForm.algebraMap_posForm** 是 Mathlib 中的一个定理，位于命名空间 `Roo
tPairing.RootPositiveForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} {M : Type u_4} {N : Type u_
5} [inst : CommRing S]   [inst_1 : LinearOrder S] [inst_2 : CommRing R] [inst_3 
: Algebra S R] [inst_4 : AddCommGroup M]   [inst_5 : _root_.Module R M] [inst_6 
: AddCommGroup N] [inst_7 : _root_.Module R N] {P : RootPairing ι R M N}   [inst
_8 : P.IsValuedIn S] (B : RootPairing.RootPositiveForm S P) [inst_9 : FaithfulSM
ul S R]   [inst_10 : _root_.Module S M] [inst_11 : IsScalarTower S R M] {x y : ↥
(Submodule.span S (Set.range ⇑P.root))},   (algebraMap S R) ((B.posForm x) y) = 
(B.form ↑x) ↑y
参数：B : RootPairing.RootPositiveForm S P；Submodule.span S (Set.range ⇑P.root)；alg
ebraMap S R；(B.posForm x) y；B.form ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.restrictScalarsRange₂_apply`：∀ {R : Type u_1} {S : Type u_2} {
M : Type u_3} {N : Type u_4} {P : Type u_5} {M' : Type u_6} {N' : Type u_7}   {P
' : Type u_8} [inst : CommS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma algebraMap_posForm {x y : span S (range P.root)} :
    algebraMap S R (B.posForm x y) = B.form x y := by
  change Algebra.linearMap S R _ = _
  simp [posForm]

set_option backward.isDefEq.respectTransparency.types false in
/-
**RootPairing.RootPositiveForm.algebraMap_apply_eq_form_iff** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：algebraMap_apply_eq_form_iff {x y : span S (range P.root)} {s : S} : algeb
raMap S R s = B.form x y ↔ s = B.posForm x y
参数：range P.root。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma algebraMap_apply_eq_form_iff {x y : span S (range P.root)} {s : S} :
    algebraMap S R s = B.form x y ↔ s = B.posForm x y := by
  simp [RootPositiveForm.posForm]
/-
**RootPairing.RootPositiveForm.zero_lt_posForm_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.RootPositiveForm`。
形式化陈述：zero_lt_posForm_iff {x y : span S (range P.root)} : 0 < B.posForm x y ↔ ex
ists s > 0, algebraMap S R s = B.form x y
参数：range P.root。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma zero_lt_posForm_iff {x y : span S (range P.root)} :
    0 < B.posForm x y ↔ ∃ s > 0, algebraMap S R s = B.form x y := by
  refine ⟨fun h ↦ ⟨B.posForm x y, h, by simp⟩, fun ⟨s, h, h'⟩ ↦ ?_⟩
  rw [← B.algebraMap_posForm] at h'
  rwa [← FaithfulSMul.algebraMap_injective S R h']
/-
**RootPairing.RootPositiveForm.zero_lt_posForm_apply_root** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing.RootPositiveForm`。
形式化陈述：zero_lt_posForm_apply_root (i : ι) (hi : P.root i in span S (range P.root)
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.RootPositiveForm.exists_pos_eq`：∀ {ι : Type u_1} {R : Type u
_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [inst_1 :
 LinearOrder S] [inst_2 : CommRi…
-/
lemma zero_lt_posForm_apply_root (i : ι)
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i)) :
    0 < B.posForm ⟨P.root i, hi⟩ ⟨P.root i, hi⟩ := by
  simpa only [zero_lt_posForm_iff] using B.exists_pos_eq i
/-
**RootPairing.RootPositiveForm.isSymm_posForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.RootPositiveForm`。
形式化陈述：isSymm_posForm : B.posForm.IsSymm where eq x y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `RootPairing.RootPositiveForm.symm`：∀ {ι : Type u_1} {R : Type u_2} {S : 
Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [inst_1 : LinearOr
der S] [inst_2 : CommRi…
-/
lemma isSymm_posForm :
    B.posForm.IsSymm where
  eq x y := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa using B.symm.eq x y

/-- The length of the `i`-th root w.r.t. a root-positive form taking values in `S`. -/
/-
**RootPairing.RootPositiveForm.rootLength** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing
.RootPositiveForm`。
形式化陈述：rootLength (i : ι) : S
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of the `i`-th root w.r.t. a root-positive form taking values in `S`.
-/
def rootLength (i : ι) : S :=
  B.posForm (P.rootSpanMem S i) (P.rootSpanMem S i)
/-
**RootPairing.RootPositiveForm.rootLength_pos** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.RootPositiveForm`。
形式化陈述：rootLength_pos (i : ι) : 0 < B.rootLength i
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.RootPositiveForm.zero_lt_posForm_apply_root`：zero_lt_posForm
_apply_root (i : ι) (hi : P.root i in span S (range P.root)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma rootLength_pos (i : ι) : 0 < B.rootLength i := by
  simpa using! B.zero_lt_posForm_apply_root i

@[simp]
/-
**RootPairing.RootPositiveForm.rootLength_reflectionPerm_self** 是 Mathlib 中的一个引理
，位于命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：rootLength_reflectionPerm_self (i : ι) : B.rootLength (P.reflectionPerm i 
i) = B.rootLength i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.rootSpanMem_reflectionPerm_self`：rootSpanMem_reflectionPerm_
self [Module S M] (i : ι) : P.rootSpanMem S (P.reflectionPerm i i) = - P.rootSpa
nMem S i
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rootLength_reflectionPerm_self (i : ι) :
    B.rootLength (P.reflectionPerm i i) = B.rootLength i := by
  simp [rootLength, rootSpanMem_reflectionPerm_self]
/-
**RootPairing.RootPositiveForm.algebraMap_rootLength** 是 Mathlib 中的一个定理，位于命名空间 `
RootPairing.RootPositiveForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} {M : Type u_4} {N : Type u_
5} [inst : CommRing S]   [inst_1 : LinearOrder S] [inst_2 : CommRing R] [inst_3 
: Algebra S R] [inst_4 : AddCommGroup M]   [inst_5 : _root_.Module R M] [inst_6 
: AddCommGroup N] [inst_7 : _root_.Module R N] {P : RootPairing ι R M N}   [inst
_8 : P.IsValuedIn S] (B : RootPairing.RootPositiveForm S P) [inst_9 : FaithfulSM
ul S R]   [inst_10 : _root_.Module S M] [inst_11 : IsScalarTower S R M] (i : ι),
   (algebraMap S R) (B.rootLength i) = (B.form (P.root i)) (P.root i)
参数：B : RootPairing.RootPositiveForm S P；i : ι；algebraMap S R；B.rootLength i；B.fo
rm (P.root i)；P.root i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma algebraMap_rootLength (i : ι) :
    algebraMap S R (B.rootLength i) = B.form (P.root i) (P.root i) := by
  simp [rootLength]
/-
**RootPairing.RootPositiveForm.pairingIn_mul_eq_pairingIn_mul_swap** 是 Mathlib 中
的一个引理，位于命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：pairingIn_mul_eq_pairingIn_mul_swap : P.pairingIn S j i * B.rootLength i =
 P.pairingIn S i j * B.rootLength j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_rootLength`：∀ {ι : Type u_1} {R 
: Type u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [
inst_1 : LinearOrder S] [inst_2 : CommRi…
· 使用引理 `RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap`：pairing_mul_e
q_pairing_mul_swap : P.pairing j i * B.form (P.root i) (P.root i) = P.pairing i 
j * B.form (P.root j) (P.root j)
-/
lemma pairingIn_mul_eq_pairingIn_mul_swap :
    P.pairingIn S j i * B.rootLength i = P.pairingIn S i j * B.rootLength j := by
  simpa only [← (algebraMap_injective S R).eq_iff, algebraMap_pairingIn, map_mul,
    B.algebraMap_rootLength] using! B.toInvariantForm.pairing_mul_eq_pairing_mul_swap i j

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[simp]
/-
**RootPairing.RootPositiveForm.zero_lt_apply_root_root_iff** 是 Mathlib 中的一个引理，位于
命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：zero_lt_apply_root_root_iff [IsStrictOrderedRing S] (hi : P.root i in span
 S (range P.root)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RootPairing.RootPositiveForm.toInvariantForm_form`：∀ {ι : Type u_1} {R :
 Type u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [i
nst_1 : LinearOrder S] [inst_2 : CommRi…
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用定理 `mul_pos_iff_of_pos_left`：mul_pos_iff_of_pos_left [PosMulStrictMono α] [P
osMulReflectLT α] (h : 0 < a) : 0 < a * b ↔ 0 < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `mul_pos_iff_of_pos_right`：mul_pos_iff_of_pos_right [MulPosStrictMono α] 
[MulPosReflectLT α] (h : 0 < b) : 0 < a * b ↔ 0 < a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 33 条，此处仅展示前 30 条）
-/
lemma zero_lt_apply_root_root_iff [IsStrictOrderedRing S]
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i))
    (hj : P.root j ∈ span S (range P.root) := subset_span (mem_range_self j)) :
    0 < B.posForm ⟨P.root i, hi⟩ ⟨P.root j, hj⟩ ↔ 0 < P.pairingIn S i j := by
  let ri : span S (range P.root) := ⟨P.root i, hi⟩
  let rj : span S (range P.root) := ⟨P.root j, hj⟩
  have : 2 * B.posForm ri rj = P.pairingIn S i j * B.posForm rj rj := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa [map_ofNat] using B.toInvariantForm.two_mul_apply_root_root i j
  calc  0 < B.posForm ri rj
      ↔ 0 < 2 * B.posForm ri rj := by rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.posForm rj rj := by rw [this]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_posForm_apply_root j)]

@[simp]
/-
**RootPairing.RootPositiveForm.posForm_apply_root_root_le_zero_iff** 是 Mathlib 中
的一个引理，位于命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：posForm_apply_root_root_le_zero_iff [IsStrictOrderedRing S] (hi : P.root i
 in span S (range P.root)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `RootPairing.RootPositiveForm.zero_lt_apply_root_root_iff`：zero_lt_apply_
root_root_iff [IsStrictOrderedRing S] (hi : P.root i in span S (range P.root)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma posForm_apply_root_root_le_zero_iff [IsStrictOrderedRing S]
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i))
    (hj : P.root j ∈ span S (range P.root) := subset_span (mem_range_self j)) :
    B.posForm ⟨P.root i, hi⟩ ⟨P.root j, hj⟩ ≤ 0 ↔ P.pairingIn S i j ≤ 0 := by
  rw [← not_iff_not, not_le, not_le, zero_lt_apply_root_root_iff]

end RootPositiveForm

include B

/-
**RootPairing.zero_lt_pairingIn_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：zero_lt_pairingIn_iff [IsStrictOrderedRing S] : 0 < P.pairingIn S i j ↔ 0 
< P.pairingIn S j i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.RootPositiveForm.zero_lt_apply_root_root_iff`：zero_lt_apply_
root_root_iff [IsStrictOrderedRing S] (hi : P.root i in span S (range P.root)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用引理 `RootPairing.RootPositiveForm.isSymm_posForm`：isSymm_posForm : B.posForm.
IsSymm where eq x y
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma zero_lt_pairingIn_iff [IsStrictOrderedRing S] :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i := by
  rw [← B.zero_lt_apply_root_root_iff, ← B.isSymm_posForm.eq, RingHom.id_apply,
    B.zero_lt_apply_root_root_iff]
/-
**RootPairing.coxeterWeight_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeight_nonneg [IsStrictOrderedRing S] : 0 <= P.coxeterWeightIn S i 
j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.zero_lt_pairingIn_iff`：zero_lt_pairingIn_iff [IsStrictOrdere
dRing S] : 0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `mul_nonneg_of_nonpos_of_nonpos`：mul_nonneg_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (ha : a <= 0) (hb
 : b <= 0) : 0 <= a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
lemma coxeterWeight_nonneg [IsStrictOrderedRing S] : 0 ≤ P.coxeterWeightIn S i j := by
  dsimp [coxeterWeightIn]
  rcases lt_or_ge 0 (P.pairingIn S i j) with h | h
  · exact le_of_lt <| mul_pos h ((zero_lt_pairingIn_iff B i j).mp h)
  · have hn : P.pairingIn S j i ≤ 0 := by rwa [← not_lt, ← zero_lt_pairingIn_iff B i j, not_lt]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

end RootPairing

