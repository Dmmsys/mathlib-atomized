/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Finiteness.Prod

/-!

# Characteristic polynomial

## Main result

* `LinearMap.charpoly_toMatrix f` : `charpoly f` is the characteristic polynomial of the matrix
  of `f` in any basis.

-/

public section

noncomputable section

open Module Free Polynomial Matrix

universe u v w

variable {R M M₁ M₂ : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁] [Module.Free R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂] [Module.Free R M₂]
variable (f : M →ₗ[R] M)

namespace LinearMap

section Basic

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp]
/-
**LinearMap.charpoly_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_toMatrix {ι : Type w} [DecidableEq ι] [Fintype ι] (b : Basis ι R 
M) : (toMatrix b b f).charpoly = f.charpoly
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`：basis_toMatrix
_mul_linearMap_toMatrix_mul_basis_toMatrix [Fintype κ'] [DecidableEq ι] [Decidab
leEq ι'] : c.toMatrix c' * LinearMap.toMatrix …
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Matrix.charpoly_reindex`：charpoly_reindex (e : n ≃ m) (M : Matrix n n R)
 : (reindex e e M).charpoly = M.charpoly
· 使用定理 `Matrix.reindexLinearEquiv_mul`：reindexLinearEquiv_mul [Fintype n] [Finty
pe n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o') (M : Matrix m n A) (N : Matrix 
n o A) : reindexLin…
· 使用定理 `Matrix.charpoly_mul_comm`：charpoly_mul_comm (A B : Matrix n n R) : (A * 
B).charpoly = (B * A).charpoly
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `Module.Basis.toMatrix_mul_toMatrix`：toMatrix_mul_toMatrix {ι'' : Type*} 
[Fintype ι'] (b'' : ι'' -> M) : b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b''
· 使用定理 `Module.Basis.toMatrix_self`：toMatrix_self [DecidableEq ι] : e.toMatrix e
 = 1
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`charpoly f` is the characteristic polynomial of the matrix of `f` in any basis.
-/
theorem charpoly_toMatrix {ι : Type w} [DecidableEq ι] [Fintype ι] (b : Basis ι R M) :
    (toMatrix b b f).charpoly = f.charpoly := by
  nontriviality R
  unfold LinearMap.charpoly
  set b' := chooseBasis R M
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b']
  set P := b.toMatrix b'
  set A := toMatrix b' b' f
  set Q := b'.toMatrix b
  let e := Basis.indexEquiv b b'
  let ι' := ChooseBasisIndex R M
  let φ := reindexLinearEquiv R R e e
  let φ₁ := reindexLinearEquiv R R e (Equiv.refl ι')
  let φ₂ := reindexLinearEquiv R R (Equiv.refl ι') (Equiv.refl ι')
  let φ₃ := reindexLinearEquiv R R (Equiv.refl ι') e
  calc
    (P * A * Q).charpoly = (φ (P * A * Q)).charpoly := (charpoly_reindex ..).symm
    _ = (φ₁ P * φ₂ A * φ₃ Q).charpoly := by rw [reindexLinearEquiv_mul, reindexLinearEquiv_mul]
    _ = A.charpoly := by rw [charpoly_mul_comm, ← mul_assoc]; simp [P, Q, φ₁, φ₂, φ₃]
/-
**LinearMap.charpoly_prodMap** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_prodMap (f₁ : M₁ ->ₗ[R] M₁) (f₂ : M₂ ->ₗ[R] M₂) : (f₁.prodMap f₂)
.charpoly = f₁.charpoly * f₂.charpoly
参数：f₁ : M₁ ->ₗ[R] M₁；f₂ : M₂ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.prod`：∀ (R : Type u_7) (M : Type u_8) (N : Type u_9) [inst :
 Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 :
 AddCo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用引理 `LinearMap.toMatrix_prodMap`：LinearMap.toMatrix_prodMap [DecidableEq m] [
DecidableEq (n oplus m)] (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) : toMatri
x (v₁.prod v₂) (…
· 使用引理 `Matrix.charpoly_fromBlocks_zero₁₂`：charpoly_fromBlocks_zero₁₂ : (fromBlo
cks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly)
-/
lemma charpoly_prodMap (f₁ : M₁ →ₗ[R] M₁) (f₂ : M₂ →ₗ[R] M₂) :
    (f₁.prodMap f₂).charpoly = f₁.charpoly * f₂.charpoly := by
  let b₁ := chooseBasis R M₁
  let b₂ := chooseBasis R M₂
  let b := b₁.prod b₂
  rw [← charpoly_toMatrix f₁ b₁, ← charpoly_toMatrix f₂ b₂, ← charpoly_toMatrix (f₁.prodMap f₂) b,
    toMatrix_prodMap b₁ b₂ f₁ f₂, Matrix.charpoly_fromBlocks_zero₁₂]

end Basic

end LinearMap

@[simp]
/-
**LinearEquiv.charpoly_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.charpoly_conj (e : M₁ ≃ₗ[R] M₂) (φ : Module.End R M₁) : (e.con
j φ).charpoly = φ.charpoly
参数：e : M₁ ≃ₗ[R] M₂；φ : Module.End R M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用引理 `Fintype.sum_single_smul`：sum_single_smul {R : Type*} [Semiring R] [Modul
e R α] (f : ι -> α) (r : R) (i₀ : ι) : ∑ i, (Pi.single (M
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LinearEquiv.charpoly_conj (e : M₁ ≃ₗ[R] M₂) (φ : Module.End R M₁) :
    (e.conj φ).charpoly = φ.charpoly := by
  let b := chooseBasis R M₁
  rw [← LinearMap.charpoly_toMatrix φ b, ← LinearMap.charpoly_toMatrix (e.conj φ) (b.map e)]
  congr 1
  ext i j : 1
  simp [LinearMap.toMatrix]

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp]
/-
**Matrix.charpoly_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_toLin (A : Matrix n n R) (b : Basis n R M) : (A.toLin b b).charpo
ly = A.charpoly
参数：A : Matrix n n R；b : Basis n R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_toLin (A : Matrix n n R) (b : Basis n R M) :
    (A.toLin b b).charpoly = A.charpoly := by
  simp [← LinearMap.charpoly_toMatrix (A.toLin b b) b]

@[simp]
/-
**Matrix.charpoly_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_toLin' (A : Matrix n n R) : A.toLin'.charpoly = A.charpoly
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin_eq_toLin'`：Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisF
un R n) (Pi.basisFun R m) = Matrix.toLin'
· 使用定理 `Matrix.charpoly_toLin`：charpoly_toLin (A : Matrix n n R) (b : Basis n R 
M) : (A.toLin b b).charpoly = A.charpoly
-/
theorem charpoly_toLin' (A : Matrix n n R) : A.toLin'.charpoly = A.charpoly := by
  rw [← Matrix.toLin_eq_toLin', charpoly_toLin]

@[simp]
/-
**Matrix.charpoly_mulVecLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_mulVecLin (A : Matrix n n R) : A.mulVecLin.charpoly = A.charpoly
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charpoly_toLin'`：charpoly_toLin' (A : Matrix n n R) : A.toLin'.ch
arpoly = A.charpoly
-/
theorem charpoly_mulVecLin (A : Matrix n n R) : A.mulVecLin.charpoly = A.charpoly :=
  charpoly_toLin' A

end Matrix

