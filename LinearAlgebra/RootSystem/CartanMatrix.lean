/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ZMatrix
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
* `RootPairing.Base.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with
  respect to a base `b`.
* `RootPairing.Base.cartanMatrix_nondegenerate`: the Cartan matrix is non-degenerate.
* `RootPairing.Base.induction_on_cartanMatrix`: an induction principle expressing the connectedness
  of the Dynkin diagram of an irreducible root pairing.
* `RootPairing.Base.equivOfCartanMatrixEq`: a root system is determined by its Cartan matrix.

-/

@[expose] public section

noncomputable section

open FaithfulSMul (algebraMap_injective)
open Function Set
open Matrix
open Module.End (invtSubmodule mem_invtSubmodule)
open Submodule (span subset_span)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing.Base

variable (S : Type*) [CommRing S] [Algebra S R]
  {P : RootPairing ι R M N} [P.IsValuedIn S] (b : P.Base)

/-- The Cartan matrix of a root pairing, taking values in `S`, with respect to a base `b`.

See also `RootPairing.Base.cartanMatrix`. -/
/-
**RootPairing.Base.cartanMatrixIn** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：cartanMatrixIn : Matrix b.support b.support S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of a root pairing, taking values in `S`, with respect to a bas
e `b`.

See also `RootPairing.Base.cartanMatrix`.
-/
def cartanMatrixIn :
    Matrix b.support b.support S :=
  .of fun i j ↦ P.pairingIn S i j
/-
**RootPairing.Base.cartanMatrixIn_def** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Bas
e`。
形式化陈述：cartanMatrixIn_def (i j : b.support) : b.cartanMatrixIn S i j = P.pairingI
n S i j
参数：i j : b.support。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cartanMatrixIn_def (i j : b.support) :
    b.cartanMatrixIn S i j = P.pairingIn S i j :=
  rfl

@[simp]
/-
**RootPairing.Base.algebraMap_cartanMatrixIn_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.Base`。
形式化陈述：algebraMap_cartanMatrixIn_apply (i j : b.support) : algebraMap S R (b.cart
anMatrixIn S i j) = P.pairing i j
参数：i j : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMap_cartanMatrixIn_apply (i j : b.support) :
    algebraMap S R (b.cartanMatrixIn S i j) = P.pairing i j := by
  simp [cartanMatrixIn_def]

@[simp]
/-
**RootPairing.Base.cartanMatrixIn_apply_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.Base`。
形式化陈述：cartanMatrixIn_apply_same [FaithfulSMul S R] (i : b.support) : b.cartanMat
rixIn S i i = 2
参数：i : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_same`：pairingIn_same [FaithfulSMul S R] [P.IsValue
dIn S] (i : ι) : P.pairingIn S i i = 2
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cartanMatrixIn_apply_same [FaithfulSMul S R] (i : b.support) :
    b.cartanMatrixIn S i i = 2 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [cartanMatrixIn_def, map_ofNat]

/- See `RootPairing.Base.cartanMatrix_mul_diagonal_eq` below for a version of this lemma in the case
`S = ℤ`, which does not need to use `Matrix.map`.

If we generalised the notion of `RootPairing.Base` to work relative to an assumption
`[P.IsValuedIn S]` then such a base would provide basis of `P.rootSpan S` and we could avoid
using `Matrix.map` here too but this does not seem to be worth it. -/
/-
**RootPairing.Base.cartanMatrixIn_mul_diagonal_eq** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing.Base`。
形式化陈述：cartanMatrixIn_mul_diagonal_eq {P : RootPairing ι R M N} [P.IsRootSystem] 
[P.IsValuedIn S] (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] : (b.cartanM
atrixIn S).map (algebraMap S R) * (Matrix.diagonal fun i : b.support => B.form (
P.root i) (P.root i)) = (2 : R) • B.form.toMatrix b.toWeightBasis
参数：B : P.InvariantForm；b : P.Base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.Base.algebraMap_cartanMatrixIn_apply`：algebraMap_cartanMatri
xIn_apply (i j : b.support) : algebraMap S R (b.cartanMatrixIn S i j) = P.pairin
g i j
· 使用定理 `LinearMap.BilinForm.toMatrix_apply`：LinearMap.BilinForm.toMatrix_apply (
B : BilinForm R₁ M₁) (i j : n) : BilinForm.toMatrix b B i j = B (b i) (b j)
· 使用定理 `RootPairing.Base.toWeightBasis_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `RootPairing.Base.cartanMatrix_mul_diagonal_eq` below for a version of this 
lemma in the case
`S = ℤ`, which does not need to use `Matrix.map`.

If we generalised the notion of `RootPairing.Base` to work relative to an assump
tion
`[P.IsValuedIn S]` then such a base would provide basis of `P.rootSpan S` and we
 could avoid
using `Matrix.map` here too but this does not seem to be worth it.
-/
lemma cartanMatrixIn_mul_diagonal_eq {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S]
    (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] :
    (b.cartanMatrixIn S).map (algebraMap S R) *
      (Matrix.diagonal fun i : b.support ↦ B.form (P.root i) (P.root i)) =
      (2 : R) • B.form.toMatrix b.toWeightBasis := by
  ext
  simp [B.two_mul_apply_root_root]
/-
**RootPairing.Base.cartanMatrixIn_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.Base`。
形式化陈述：cartanMatrixIn_nondegenerate [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S
 R] [IsDomain S] {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S] [Fi
ntype ι] [P.IsAnisotropic] (b : P.Base) : (b.cartanMatrixIn S).Nondegenerate
参数：2 : R；b : P.Base。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RootPairing.rootForm_nondegenerate`：rootForm_nondegenerate [P.IsRootSyst
em] : P.RootForm.Nondegenerate
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.Nondegenerate.smul_iff`：∀ {n : Type u_1} {A : Type u_4} [inst : C
ommRing A] [IsDomain A] {M : Matrix n n A} [inst_2 : Finite n] {t : A},   t ≠ 0 
→ ((t • M).Nondegen…
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `LinearMap.BilinForm.nondegenerate_toMatrix_iff`：nondegenerate_toMatrix_i
ff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) : (BilinForm.toMatrix b B).Nondegen
erate ↔ B.Nondegenerate
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.Nondegenerate.mul_iff_right`：∀ {n : Type u_1} [inst : Fintype n] 
{A : Type u_4} [inst_1 : CommRing A] [IsDomain A] {M N : Matrix n n A},   N.Nond
egenerate → ((M * N).Non…
· 使用引理 `RootPairing.Base.cartanMatrixIn_mul_diagonal_eq`：cartanMatrixIn_mul_diag
onal_eq {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S] (B : P.Invar
iantForm) (b : P.Base) [DecidableEq ι…
-/
lemma cartanMatrixIn_nondegenerate [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S R] [IsDomain S]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S] [Fintype ι] [P.IsAnisotropic]
    (b : P.Base) :
    (b.cartanMatrixIn S).Nondegenerate := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : P.InvariantForm, B.form.Nondegenerate :=
    ⟨P.toInvariantForm, P.rootForm_nondegenerate⟩
  replace hB : ((2 : R) • B.form.toMatrix b.toWeightBasis).Nondegenerate := by
    rwa [Matrix.Nondegenerate.smul_iff two_ne_zero, LinearMap.BilinForm.nondegenerate_toMatrix_iff]
  have aux : (Matrix.diagonal fun i : b.support ↦ B.form (P.root i) (P.root i)).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    aesop
  rw [← cartanMatrixIn_mul_diagonal_eq (S := S), Matrix.Nondegenerate.mul_iff_right aux,
    Matrix.nondegenerate_iff_det_ne_zero, ← (algebraMap S R).mapMatrix_apply,
    ← RingHom.map_det, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff] at hB
  rwa [Matrix.nondegenerate_iff_det_ne_zero]

section IsCrystallographic

variable [P.IsCrystallographic]

/-- The Cartan matrix of a crystallographic root pairing, with respect to a base `b`. -/
/-
**RootPairing.Base.cartanMatrix** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.Base`。
形式化陈述：cartanMatrix : Matrix b.support b.support Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of a crystallographic root pairing, with respect to a base `b`
.
-/
abbrev cartanMatrix :
    Matrix b.support b.support ℤ :=
  b.cartanMatrixIn ℤ

variable [CharZero R]
/-
**RootPairing.Base.cartanMatrix_apply_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Base`。
形式化陈述：cartanMatrix_apply_same (i : b.support) : b.cartanMatrix i i = 2
参数：i : b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.cartanMatrixIn_apply_same`：cartanMatrixIn_apply_same [F
aithfulSMul S R] (i : b.support) : b.cartanMatrixIn S i i = 2
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
-/
lemma cartanMatrix_apply_same (i : b.support) :
    b.cartanMatrix i i = 2 :=
  b.cartanMatrixIn_apply_same ℤ i
/-
**RootPairing.Base.cartanMatrix_apply_eq_zero_iff_pairing** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing.Base`。
形式化陈述：cartanMatrix_apply_eq_zero_iff_pairing {i j : b.support} : b.cartanMatrix 
i j = 0 ↔ P.pairing i j = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.Base.cartanMatrix.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.Base.cartanMatrixIn_def`：cartanMatrixIn_def (i j : b.support
) : b.cartanMatrixIn S i j = P.pairingIn S i j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cartanMatrix_apply_eq_zero_iff_pairing {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ P.pairing i j = 0 := by
  rw [cartanMatrix, cartanMatrixIn_def, ← (algebraMap_injective ℤ R).eq_iff,
    algebraMap_pairingIn, map_zero]

variable [IsDomain R]
/-
**RootPairing.Base.cartanMatrix_apply_eq_zero_iff_symm** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing.Base`。
形式化陈述：cartanMatrix_apply_eq_zero_iff_symm {i j : b.support} : b.cartanMatrix i j
 = 0 ↔ b.cartanMatrix j i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cartanMatrix_apply_eq_zero_iff_symm {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ b.cartanMatrix j i = 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp only [cartanMatrix_apply_eq_zero_iff_pairing, P.pairing_eq_zero_iff]

variable [Finite ι]
/-
**RootPairing.Base.cartanMatrix_le_zero_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.Base`。
形式化陈述：cartanMatrix_le_zero_of_ne (i j : b.support) (h : i != j) : b.cartanMatrix
 i j <= 0
参数：i j : b.support；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.pairingIn_le_zero_of_ne`：pairingIn_le_zero_of_ne [IsDom
ain R] [P.IsCrystallographic] [Finite ι] {i j} (hij : i != j) (hi : i in b.suppo
rt) (hj : j in b.support) : P.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma cartanMatrix_le_zero_of_ne
    (i j : b.support) (h : i ≠ j) :
    b.cartanMatrix i j ≤ 0 :=
  b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

set_option backward.isDefEq.respectTransparency.types false in
/-
**RootPairing.Base.cartanMatrix_mem_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Base`。
形式化陈述：cartanMatrix_mem_of_ne {i j : b.support} (hij : i != j) : b.cartanMatrix i
 j in ({-3, -2, -1, 0} : Set Int)
参数：hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic`：pairingIn
_pairingIn_mem_set_of_isCrystallographic : (P.pairingIn Int i j, P.pairingIn Int
 j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1)…
· 使用引理 `RootPairing.Base.cartanMatrix_le_zero_of_ne`：cartanMatrix_le_zero_of_ne 
(i j : b.support) (h : i != j) : b.cartanMatrix i j <= 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_linearIndependent_iff`：not_linearIndependent_iff : ¬LinearIndependen
t R v ↔ exists s : Finset ι, exists g : ι -> R, ∑ i in s, g i • v i = 0 ∧ exists
 i in s, g i !=…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
（共 56 条，此处仅展示前 30 条）
-/
lemma cartanMatrix_mem_of_ne {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j ∈ ({-3, -2, -1, 0} : Set ℤ) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  simp only [cartanMatrix, cartanMatrixIn_def]
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have h₂ : P.pairingIn ℤ i j ≤ 0 := b.cartanMatrix_le_zero_of_ne i j hij
  suffices P.pairingIn ℤ i j ≠ -4 by aesop
  by_contra contra
  replace contra : P.pairingIn ℤ j i = -1 ∧ P.pairingIn ℤ i j = -4 := ⟨by simp_all, contra⟩
  rw [pairingIn_neg_one_neg_four_iff] at contra
  refine (not_linearIndependent_iff.mpr ?_) b.linearIndepOn_root
  refine ⟨⟨{i, j}, by simpa⟩, Finsupp.single i (1 : R) + Finsupp.single j (2 : R), ?_⟩
  simp [contra, hij, hij.symm]
/-
**RootPairing.Base.cartanMatrix_eq_neg_chainTopCoeff** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.Base`。
形式化陈述：cartanMatrix_eq_neg_chainTopCoeff {i j : b.support} (hij : i != j) : b.car
tanMatrix i j = - P.chainTopCoeff j i
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.Base.cartanMatrix.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.Base.cartanMatrixIn_def`：cartanMatrixIn_def (i j : b.support
) : b.cartanMatrixIn S i j = P.pairingIn S i j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用引理 `RootPairing.Base.chainTopCoeff_eq_of_ne`：chainTopCoeff_eq_of_ne (hij : i
 != j) : P.chainTopCoeff i j = -P.pairingIn Int j i
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma cartanMatrix_eq_neg_chainTopCoeff {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j = - P.chainTopCoeff j i := by
  rw [cartanMatrix, cartanMatrixIn_def, ← neg_eq_iff_eq_neg, ← b.chainTopCoeff_eq_of_ne hij.symm]
/-
**RootPairing.Base.cartanMatrix_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing.Base`。
形式化陈述：cartanMatrix_apply_eq_zero_iff {i j : b.support} (hij : i != j) : b.cartan
Matrix i j = 0 ↔ P.root i + P.root j ∉ range P.root
参数：hij : i != j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.cartanMatrix_eq_neg_chainTopCoeff`：cartanMatrix_eq_neg_
chainTopCoeff {i j : b.support} (hij : i != j) : b.cartanMatrix i j = - P.chainT
opCoeff j i
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Int.natCast_eq_zero`：∀ {n : ℕ}, ↑n = 0 ↔ n = 0
· 使用引理 `RootPairing.chainTopCoeff_eq_zero_iff`：chainTopCoeff_eq_zero_iff : P.cha
inTopCoeff i j = 0 ↔ ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j + P.
root i ∉ range P.root
· 使用引理 `RootPairing.Base.linearIndependent_pair_of_ne`：linearIndependent_pair_of
_ne {i j : b.support} (hij : i != j) : LinearIndependent R ![P.root i, P.root j]
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
lemma cartanMatrix_apply_eq_zero_iff {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j = 0 ↔ P.root i + P.root j ∉ range P.root := by
  rw [b.cartanMatrix_eq_neg_chainTopCoeff hij, neg_eq_zero, Int.natCast_eq_zero,
    P.chainTopCoeff_eq_zero_iff]
  replace hij := b.linearIndependent_pair_of_ne hij.symm
  tauto
/-
**RootPairing.Base.abs_cartanMatrix_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Base`。
形式化陈述：abs_cartanMatrix_apply [DecidableEq ι] {i j : b.support} : |b.cartanMatrix
 i j| = (if i = j then 4 else 0) - b.cartanMatrix i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.cartanMatrixIn_apply_same`：cartanMatrixIn_apply_same [F
aithfulSMul S R] (i : b.support) : b.cartanMatrixIn S i i = 2
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Nat.abs_ofNat`：abs_ofNat (n : Nat) [n.AtLeastTwo] : |(ofNat(n) : R)| = o
fNat(n)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `RootPairing.Base.cartanMatrix_le_zero_of_ne`：cartanMatrix_le_zero_of_ne 
(i j : b.support) (h : i != j) : b.cartanMatrix i j <= 0
-/
lemma abs_cartanMatrix_apply [DecidableEq ι] {i j : b.support} :
    |b.cartanMatrix i j| = (if i = j then 4 else 0) - b.cartanMatrix i j := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simpa [h] using b.cartanMatrix_le_zero_of_ne i j h

@[simp]
/-
**RootPairing.Base.cartanMatrix_map_abs** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.B
ase`。
形式化陈述：cartanMatrix_map_abs [DecidableEq ι] : b.cartanMatrix.map abs = 4 - b.cart
anMatrix
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.abs_cartanMatrix_apply`：abs_cartanMatrix_apply [Decidab
leEq ι] {i j : b.support} : |b.cartanMatrix i j| = (if i = j then 4 else 0) - b.
cartanMatrix i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.ofNat_apply`：ofNat_apply [AddMonoidWithOne α] {i j} {d : Nat} [d.
AtLeastTwo] : (ofNat(d) : Matrix n n α) i j = if i = j then d else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cartanMatrix_map_abs [DecidableEq ι] :
    b.cartanMatrix.map abs = 4 - b.cartanMatrix := by
  ext; simp [abs_cartanMatrix_apply, Matrix.ofNat_apply]
/-
**RootPairing.Base.cartanMatrix_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.Base`。
形式化陈述：cartanMatrix_nondegenerate {P : RootPairing ι R M N} [P.IsRootSystem] [P.I
sCrystallographic] (b : P.Base) : b.cartanMatrix.Nondegenerate
参数：b : P.Base。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.cartanMatrixIn_nondegenerate`：cartanMatrixIn_nondegener
ate [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S R] [IsDomain S] {P : RootPairi
ng ι R M N} [P.IsRootSystem] [P.IsV…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
-/
lemma cartanMatrix_nondegenerate
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    b.cartanMatrix.Nondegenerate :=
  let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate ℤ b

omit [Finite ι] [IsDomain R] in
/-
**RootPairing.Base.cartanMatrix_mul_diagonal_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.Base`。
形式化陈述：cartanMatrix_mul_diagonal_eq [Fintype ι] [DecidableEq ι] [P.IsRootSystem] 
: letI d : b.support -> Int
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `RootPairing.algebraMap_rootFormIn`：algebraMap_rootFormIn (x y : P.rootSp
an S) : (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.posRootForm_eq`：posRootForm_eq : (P.posRootForm S).posForm =
 P.RootFormIn S
· 使用定理 `LinearMap.BilinForm.toMatrix_apply`：LinearMap.BilinForm.toMatrix_apply (
B : BilinForm R₁ M₁) (i j : n) : BilinForm.toMatrix b B i j = B (b i) (b j)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `RootPairing.Base.coe_toWeightBasisInt_apply`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]
   [inst_2 : _root_.Module R M] […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RootPairing.toInvariantForm_form`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 :
 AddCommGroup N] [inst…
· 使用定理 `RootPairing.Base.toWeightBasis_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用引理 `RootPairing.Base.cartanMatrixIn_mul_diagonal_eq`：cartanMatrixIn_mul_diag
onal_eq {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S] (B : P.Invar
iantForm) (b : P.Base) [DecidableEq ι…
-/
lemma cartanMatrix_mul_diagonal_eq [Fintype ι] [DecidableEq ι] [P.IsRootSystem] :
    letI d : b.support → ℤ := fun i ↦ P.RootFormIn ℤ (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ i)
    b.cartanMatrix * diagonal d =
      (2 : ℤ) • (P.posRootForm ℤ).posForm.toMatrix b.toWeightBasisInt := by
  ext i j
  apply algebraMap_injective ℤ R
  simp only [mul_diagonal, map_mul, algebraMap_rootFormIn, posRootForm_eq, Matrix.smul_apply,
    LinearMap.BilinForm.toMatrix_apply, Int.zsmul_eq_mul]
  simpa [← algebraMap_pairingIn P ℤ i j] using
    congr_fun₂ (cartanMatrixIn_mul_diagonal_eq ℤ P.toInvariantForm b) i j
/-
**RootPairing.Base.exists_cartanMatrix_mul_diagaonal_posDef** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.Base`。
形式化陈述：exists_cartanMatrix_mul_diagaonal_posDef [DecidableEq ι] [P.IsRootSystem] 
: exists d : b.support -> Int, (forall i, 0 < d i) ∧ (b.cartanMatrix * diagonal 
d).PosDef
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.posRootForm_eq`：posRootForm_eq : (P.posRootForm S).posForm =
 P.RootFormIn S
· 使用引理 `RootPairing.RootPositiveForm.zero_lt_posForm_apply_root`：zero_lt_posForm
_apply_root (i : ι) (hi : P.root i in span S (range P.root)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `RootPairing.Base.cartanMatrix_mul_diagonal_eq`：cartanMatrix_mul_diagonal
_eq [Fintype ι] [DecidableEq ι] [P.IsRootSystem] : letI d : b.support -> Int
· 使用定理 `Matrix.PosDef.smul`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [ins
t_1 : PartialOrder R] [inst_2 : StarRing R] {α : Type u_5}   [inst_3 : CommSemir
ing α] […
· 使用定理 `instPosSMulStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], PosSMulStrictMo
no ℤ G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.rootFormIn_isSymm`：rootFormIn_isSymm : (P.RootFormIn S).IsSy
mm
· 使用定理 `LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix`：∀ {n : Type u_2} [
inst : Fintype n] {R : Type u_5} {M : Type u_6} [inst_1 : CommRing R] [inst_2 : 
PartialOrder R]   [inst_3 : StarRing R] [T…
· 使用引理 `RootPairing.posRootForm_rootFormIn_posDef`：posRootForm_rootFormIn_posDef
 : (P.RootFormIn S).toQuadraticMap.PosDef
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma exists_cartanMatrix_mul_diagaonal_posDef [DecidableEq ι] [P.IsRootSystem] :
    ∃ d : b.support → ℤ, (∀ i, 0 < d i) ∧ (b.cartanMatrix * diagonal d).PosDef := by
  have _i : Fintype ι := Fintype.ofFinite ι
  set d : b.support → ℤ := fun i ↦ P.RootFormIn ℤ (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ i) with hd
  refine ⟨d, fun i ↦ ?_, ?_⟩
  · rw [hd, ← posRootForm_eq]
    exact RootPositiveForm.zero_lt_posForm_apply_root _ _
  · rw [cartanMatrix_mul_diagonal_eq]
    refine Matrix.PosDef.smul ?_ two_pos
    have aux : (P.posRootForm ℤ).posForm.IsSymm := by
      simpa only [posRootForm_eq, LinearMap.BilinForm.isSymm_iff] using P.rootFormIn_isSymm ℤ
    rw [← LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix _ _ aux]
    simpa using P.posRootForm_rootFormIn_posDef ℤ
/-
**RootPairing.Base.exists_cartanMatrix_diagaonal_mul_posDef** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.Base`。
形式化陈述：exists_cartanMatrix_diagaonal_mul_posDef [DecidableEq ι] [P.IsRootSystem] 
: exists d : b.support -> Int, (forall i, 0 < d i) ∧ (diagonal d * b.cartanMatri
x).PosDef
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用引理 `RootPairing.Base.exists_cartanMatrix_mul_diagaonal_posDef`：exists_cartan
Matrix_mul_diagaonal_posDef [DecidableEq ι] [P.IsRootSystem] : exists d : b.supp
ort -> Int, (forall i, 0 < d i) ∧ (b.cartanMatr…
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.PosDef.transpose_iff`：transpose_iff {M : Matrix n n R'} : Mᵀ.PosD
ef ↔ M.PosDef
-/
lemma exists_cartanMatrix_diagaonal_mul_posDef [DecidableEq ι] [P.IsRootSystem] :
    ∃ d : b.support → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * b.cartanMatrix).PosDef := by
  obtain ⟨d, hd, hd'⟩ := b.flip.exists_cartanMatrix_mul_diagaonal_posDef
  refine ⟨d, hd, ?_⟩
  rw [← PosDef.transpose_iff] at hd'
  aesop

open LinearMap Module.End in
/-
**RootPairing.Base.det_four_sub_cartanMatrix_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.Base`。
形式化陈述：det_four_sub_cartanMatrix_ne_zero [DecidableEq ι] [P.IsRootSystem] : (4 - 
b.cartanMatrix).det != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.Base.exists_cartanMatrix_diagaonal_mul_posDef`：exists_cartan
Matrix_diagaonal_mul_posDef [DecidableEq ι] [P.IsRootSystem] : exists d : b.supp
ort -> Int, (forall i, 0 < d i) ∧ (diagonal d *…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.cartanMatrixIn_apply_same`：cartanMatrixIn_apply_same [F
aithfulSMul S R] (i : b.support) : b.cartanMatrixIn S i i = 2
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.Base.cartanMatrix_le_zero_of_ne`：cartanMatrix_le_zero_of_ne 
(i j : b.support) (h : i != j) : b.cartanMatrix i j <= 0
· 使用定理 `Matrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen`：∀ {ι : T
ype u_1} {R : Type u_2} [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Co
mmRing R]   [inst_3 : LinearOrder R] [IsStrictOrdere…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 52 条，此处仅展示前 30 条）
-/
lemma det_four_sub_cartanMatrix_ne_zero [DecidableEq ι] [P.IsRootSystem] :
    (4 - b.cartanMatrix).det ≠ 0 := by
  suffices ¬ HasEigenvalue b.cartanMatrix.toLin' 4 by
    have aux : (4 - b.cartanMatrix).toLin' = - (b.cartanMatrix.toLin' - (4 : ℤ) • 1) := by ext; simp
    rwa [ne_eq, ← det_toLin', det_eq_zero_iff_ker_ne_bot, aux, ker_neg, ← eigenspace_def,
      ← hasEigenvalue_iff]
  obtain ⟨d, hd, hdS⟩ := b.exists_cartanMatrix_diagaonal_mul_posDef
  have aux (i j : b.support) : b.cartanMatrix i j ≤ if i = j then 2 else 0 := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simpa [hij] using cartanMatrix_le_zero_of_ne b i j hij
  have := b.cartanMatrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen d hdS hd 2 4 aux
  aesop

/-- A characterisation of the connectedness of the Dynkin diagram for irreducible root pairings. -/
/-
**RootPairing.Base.induction_on_cartanMatrix** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.Base`。
形式化陈述：induction_on_cartanMatrix [P.IsReduced] [P.IsIrreducible] (p : b.support -
> Prop) {i j : b.support} (hi : p i) (hp : forall i j, p i -> b.cartanMatrix j i
 != 0 -> p j) : p j
参数：p : b.support -> Prop；hi : p i；hp : forall i j, p i -> b.cartanMatrix j i != 
0 -> p j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LinearIndependent.notMem_span_image`：LinearIndependent.notMem_span_image
 [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι} {x : ι} (h : x ∉ s) : v
 x ∉ Submodule.span R (v …
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `LinearIndepOn.linearIndependent`：LinearIndepOn.linearIndependent {s : Se
t ι} (h : LinearIndepOn R v s) : LinearIndependent R (fun x : s => v x)
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `RootPairing.Base.cartanMatrix_apply_eq_zero_iff_symm`：cartanMatrix_apply
_eq_zero_iff_symm {i j : b.support} : b.cartanMatrix i j = 0 ↔ b.cartanMatrix j 
i = 0
· 使用引理 `RootPairing.Base.cartanMatrix_apply_eq_zero_iff_pairing`：cartanMatrix_ap
ply_eq_zero_iff_pairing {i j : b.support} : b.cartanMatrix i j = 0 ↔ P.pairing i
 j = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
A characterisation of the connectedness of the Dynkin diagram for irreducible ro
ot pairings.
-/
lemma induction_on_cartanMatrix [P.IsReduced] [P.IsIrreducible]
    (p : b.support → Prop) {i j : b.support} (hi : p i)
    (hp : ∀ i j, p i → b.cartanMatrix j i ≠ 0 → p j) :
    p j := by
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
  have hq₀ : q ≠ ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span <| by simpa, P.ne_zero i⟩
  have hq_mem (k : b.support) : P.root k ∈ q ↔ p k := by
    refine ⟨fun hk ↦ ?_, fun hk ↦ subset_span <| by simpa⟩
    contrapose hk
    exact b.linearIndepOn_root.linearIndependent.notMem_span_image hk
  have hq_notMem (k : b.support) (hk : P.root k ∉ q) : q ≤ LinearMap.ker (P.coroot' k) := by
    refine fun x hx ↦ LinearMap.mem_ker.mpr ?_
    contrapose! hk
    rw [hq_mem]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ : ∃ l : b.support, p l ∧ P.root l = x := by simp_all
      replace hk : b.cartanMatrix k l ≠ 0 := by
        rwa [ne_eq, cartanMatrix_apply_eq_zero_iff_symm, cartanMatrix_apply_eq_zero_iff_pairing]
      tauto
    | zero => simp_all
    | add x y hx hy hx' hy' =>
      replace hk : P.coroot' k x ≠ 0 ∨ P.coroot' k y ≠ 0 := by by_contra! contra; simp_all
      tauto
    | smul a x hx hx' => simp_all
  have hq : ∀ k, q ∈ invtSubmodule (P.reflection k) := by
    rw [← b.forall_mem_support_invtSubmodule_iff]
    refine fun k hkb ↦ (mem_invtSubmodule _).mpr fun x hx ↦ ?_
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply]
    apply q.sub_mem hx
    by_cases hk : P.root k ∈ q
    · exact q.smul_mem _ hk
    · replace hk : P.coroot' k x = 0 := hq_notMem ⟨k, hkb⟩ hk hx
      simp [hk]
  simp [← hq_mem, IsIrreducible.eq_top_of_invtSubmodule_reflection q hq hq₀]

-- TODO Derive from `LinearIndependent.injective`
set_option backward.isDefEq.respectTransparency.types false in
open scoped Matrix in
/-
**RootPairing.Base.injective_pairingIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Ba
se`。
形式化陈述：injective_pairingIn {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrysta
llographic] (b : P.Base) : Injective (fun i (k : b.support) => P.pairingIn Int i
 k)
参数：b : P.Base。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_subtype`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι),   (∀ (x : ι), x ∈ 
s ↔ p x)…
· 使用定理 `RootPairing.Base.cartanMatrixIn.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecMul_eq_sum`：vecMul_eq_sum [Fintype m] (v : m -> α) (M : Matrix
 m n α) : v ᵥ* M = ∑ i, v i • M i
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Matrix.vecMul_injective_iff`：Matrix.vecMul_injective_iff {M : Matrix m n
 R} : Function.Injective M.vecMul ↔ LinearIndependent R M.row
（共 38 条，此处仅展示前 30 条）
-/
lemma injective_pairingIn {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    (b : P.Base) :
    Injective (fun i (k : b.support) ↦ P.pairingIn ℤ i k) := by
  classical
  intro i j hij
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  let f' : b.support → ℤ := f ∘ (↑)
  let g' : b.support → ℤ := g ∘ (↑)
  suffices f' = g' by
    rw [← P.root.apply_eq_iff_eq, hf, hg]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    replace this : f k = g k := congr_fun this ⟨k, hk⟩
    rw [this]
  replace hf : (fun k : b.support ↦ P.pairingIn ℤ i k) = f' ᵥ* b.cartanMatrix := by
    suffices ∀ k, P.pairingIn ℤ i k = ∑ l ∈ b.support, f l * P.pairingIn ℤ l k by
      ext; simp [f', this, cartanMatrixIn, Matrix.vecMul_eq_sum, b.support.sum_subtype (by tauto)]
    refine fun k ↦ algebraMap_injective ℤ R ?_
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← P.root_coroot'_eq_pairing]
    simp [hf]
  replace hg : (fun k : b.support ↦ P.pairingIn ℤ j k) = g' ᵥ* b.cartanMatrix := by
    suffices ∀ k, P.pairingIn ℤ j k = ∑ l ∈ b.support, g l * P.pairingIn ℤ l k by
      ext; simp [g', this, cartanMatrixIn, Matrix.vecMul_eq_sum, b.support.sum_subtype (by tauto)]
    refine fun k ↦ algebraMap_injective ℤ R ?_
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← P.root_coroot'_eq_pairing]
    simp [hg]
  suffices Injective fun v ↦ v ᵥ* b.cartanMatrix from this <| by simpa [← hf, ← hg]
  rw [Matrix.vecMul_injective_iff]
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate
/-
**RootPairing.Base.exists_mem_span_pairingIn_ne_zero_and_pairwise_ne** 是 Mathlib
 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：exists_mem_span_pairingIn_ne_zero_and_pairwise_ne {K : Type*} [Field K] [C
harZero K] [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem] 
[P.IsCrystallographic] (b : P.Base) : exists d in span K (range fun (i : b.suppo
rt) j => (P.pairingIn Int j i : K)), (forall i, d i != 0) ∧ Pairwise ((· != ·) o
n d)
参数：b : P.Base。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Dual.exists_forall_mem_ne_zero_of_forall_exists`：Module.Dual.exis
ts_forall_mem_ne_zero_of_forall_exists (p : Submodule K M) (f : ι -> Dual K M) (
h : forall i, exists x in p, f i x != 0) : e…
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `CharZero.infinite`：∀ (M : Type u_1) [inst : AddMonoidWithOne M] [CharZer
o M], Infinite M
· 使用引理 `RootPairing.Base.exists_mem_support_pos_pairingIn_ne_zero`：exists_mem_su
pport_pos_pairingIn_ne_zero [P.IsCrystallographic] (i : ι) : exists j in b.suppo
rt, P.pairingIn Int j i != 0
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `RootPairing.pairingIn_eq_zero_iff`：pairingIn_eq_zero_iff {S : Type*} [Co
mmRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] [IsDomain R] [Module
.IsTorsionFree R M] [Ne…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `RootPairing.Base.injective_pairingIn`：injective_pairingIn {P : RootPairi
ng ι R M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) : Injective (fu
n i (k : b.support) => P.p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_mem_span_pairingIn_ne_zero_and_pairwise_ne
    {K : Type*} [Field K] [CharZero K] [Module K M] [Module K N]
    {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    ∃ d ∈ span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K)),
      (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) := by
  set p := span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K))
  let f : ι ⊕ {(i, j) : ι × ι | i ≠ j} → Module.Dual K (ι → K) := Sum.elim
    LinearMap.proj (fun x ↦ LinearMap.proj (R := K) (φ := fun _ ↦ K) x.1.1 - LinearMap.proj x.1.2)
  suffices ∃ d ∈ p, ∀ i, f i d ≠ 0 by
    obtain ⟨d, hp, hf⟩ := this
    refine ⟨d, hp, fun i ↦ hf (Sum.inl i), fun i j h ↦ ?_⟩
    simpa [f, sub_eq_zero] using hf (Sum.inr ⟨⟨i, j⟩, h⟩)
  apply Module.Dual.exists_forall_mem_ne_zero_of_forall_exists p f
  rintro (i | ⟨⟨i, j⟩, h : i ≠ j⟩)
  · obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
    refine ⟨fun i ↦ P.pairingIn ℤ i j, subset_span ⟨⟨j, hj⟩, rfl⟩, ?_⟩
    rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
    simpa [f, ne_eq, Int.cast_eq_zero]
  · obtain ⟨k, hk, hk'⟩ : ∃ k ∈ b.support, P.pairingIn ℤ i k ≠ P.pairingIn ℤ j k := by
      contrapose! h
      apply b.injective_pairingIn
      aesop
    simpa [f, sub_eq_zero] using ⟨fun i ↦ P.pairingIn ℤ i k, subset_span ⟨⟨k, hk⟩, rfl⟩, by simpa⟩

section Uniqueness

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
  {P₂ : RootPairing ι₂ R M₂ N₂} [P₂.IsCrystallographic] (b₂ : P₂.Base)
  (e : b.support ≃ b₂.support)

/-
**RootPairing.Base.apply_mem_range_root_of_cartanMatrixEq** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing.Base`。
形式化陈述：apply_mem_range_root_of_cartanMatrixEq (f : M ≃ₗ[R] M₂) (hf : forall i : b
.support, f (P.root i) = P₂.root (e i)) (m : M) (hm : m in range P.root) (he : f
orall i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) : f m in range P₂.r
oot
参数：f : M ≃ₗ[R] M₂；hf : forall i : b.support, f (P.root i) = P₂.root (e i)；m : M；
hm : m in range P.root；he : forall i j, b₂.cartanMatrix (e i) (e j) = b.cartanMa
trix i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `RootPairing.Base.toWeightBasis_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用引理 `RootPairing.Base.induction_reflect`：induction_reflect (i : ι) {p : ι -> 
Prop} (h₀ : forall i, p i -> p (P.reflectionPerm i i)) (h₁ : forall i in b.suppo
rt, p i) (h₂ : forall i …
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `LinearEquiv.congr_fun`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma apply_mem_range_root_of_cartanMatrixEq
    (f : M ≃ₗ[R] M₂) (hf : ∀ i : b.support, f (P.root i) = P₂.root (e i))
    (m : M) (hm : m ∈ range P.root)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    f m ∈ range P₂.root := by
  have (k : b.support) : (P.reflection k).trans f = f.trans (P₂.reflection (e k)) := by
    suffices ∀ j : b.support,
        (P.reflection k).trans f (P.root j) = f.trans (P₂.reflection (e k)) (P.root j) by
      rw [← LinearEquiv.toLinearMap_inj]
      exact b.toWeightBasis.ext fun j ↦ by simpa using this j
    intro j
    suffices P₂.pairing (e j) (e k) = P.pairing j k by simp [reflection_apply, hf, this]
    simpa only [cartanMatrixIn_def, algebraMap_pairingIn] using congr_arg (algebraMap ℤ R) (he j k)
  obtain ⟨i, rfl⟩ := hm
  apply b.induction_reflect i
  · exact fun j ⟨k, hk⟩ ↦ ⟨P₂.reflectionPerm k k, by simpa⟩
  · exact fun j hj ↦ ⟨e ⟨j, hj⟩, (hf _).symm⟩
  · intro j k ⟨l, hl⟩ hk
    replace this : f (P.reflection k (P.root j)) = (P₂.reflection (e ⟨k, hk⟩)) (f (P.root j)) := by
      simpa using LinearEquiv.congr_fun (this ⟨k, hk⟩) (P.root j)
    rw [root_reflectionPerm, this, ← hl, ← root_reflectionPerm]
    exact mem_range_self _

set_option backward.isDefEq.respectTransparency.types false in
/-- A root system is determined by its Cartan matrix. -/
/-
**RootPairing.Base.equivOfCartanMatrixEq** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.
Base`。
形式化陈述：equivOfCartanMatrixEq [Finite ι₂] [P₂.IsRootSystem] [P₂.IsReduced] (he : f
orall i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) : P.Equiv P₂
参数：he : forall i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A root system is determined by its Cartan matrix.
-/
def equivOfCartanMatrixEq [Finite ι₂] [P₂.IsRootSystem] [P₂.IsReduced]
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    P.Equiv P₂ :=
  let f : M ≃ₗ[R] M₂ := b.toWeightBasis.equiv b₂.toWeightBasis e
  have hf : ∀ m, f m ∈ range P₂.root ↔ m ∈ range P.root := by
    refine fun m ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simpa using apply_mem_range_root_of_cartanMatrixEq _ b e.symm f.symm
        (by simp [f, Module.Basis.equiv]) (f m) h (by simp [(he _ _).symm])
    · exact apply_mem_range_root_of_cartanMatrixEq b b₂ e f (by simp [f, Module.Basis.equiv]) m h he
  let : Fintype ι := Fintype.ofFinite _
  let : Fintype ι₂ := Fintype.ofFinite _
  have : DecidableEq M := Classical.typeDecidableEq M
  have : DecidableEq M₂ := Classical.typeDecidableEq M₂
  let e' : ι ≃ ι₂ := P.root.toEquivRange.trans <| (f.bijOn hf).equiv.trans P₂.root.toEquivRange.symm
  have he' (i : ι) : f (P.root i) = P₂.root (e' i) := by
    simp [f, e', BijOn.equiv, Embedding.toEquivRange]
  have : Module.IsReflexive R M₂ := .of_isPerfPair P₂.toLinearMap
  Equiv.mk' P P₂ (b.toWeightBasis.equiv b₂.toWeightBasis e) e' he'

end Uniqueness

end IsCrystallographic

end RootPairing.Base

