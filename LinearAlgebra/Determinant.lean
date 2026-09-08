/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.FieldSimp

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Determinant of families of vectors

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`LinearAlgebra.Matrix.Determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `Basis.det`: the determinant of a family of vectors with respect to a basis,
  as a multilinear map
* `LinearMap.det`: the determinant of an endomorphism `f : End R M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)
* `LinearEquiv.det`: the determinant of an isomorphism `f : M ≃ₗ[R] M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)

## Tags

basis, det, determinant
-/

@[expose] public section


noncomputable section

open Matrix Module LinearMap Submodule Set Function

universe u v w

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (e : Basis ι R M)

section Conjugate

variable {A : Type*} [CommRing A]
variable {m n : Type*}

/-- If `R^m` and `R^n` are linearly equivalent, then `m` and `n` are also equivalent. -/
/-
**equivOfPiLEquivPi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：equivOfPiLEquivPi {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivi
al R] (e : (m -> R) ≃ₗ[R] n -> R) : m ≃ n
参数：e : (m -> R) ≃ₗ[R] n -> R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R

--- 原说明 ---
If `R^m` and `R^n` are linearly equivalent, then `m` and `n` are also equivalent
.
-/
def equivOfPiLEquivPi {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivial R]
    (e : (m → R) ≃ₗ[R] n → R) : m ≃ n :=
  Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

namespace Matrix

variable [Fintype m] [Fintype n]

/-- If `M` and `M'` are each other's inverse matrices, they are square matrices up to
equivalence of types. -/
/-
**Matrix.indexEquivOfInv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix
 m n A} {M' : Matrix n m A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : m ≃ n
参数：hMM' : M * M' = 1；hM'M : M' * M = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `M` and `M'` are each other's inverse matrices, they are square matrices up t
o
equivalence of types.
-/
def indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : m ≃ n :=
  equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)
/-
**Matrix.det_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_comm [DecidableEq n] (M N : Matrix n n A) : det (M * N) = det (N * M)
参数：M N : Matrix n n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem det_comm [DecidableEq n] (M N : Matrix n n A) : det (M * N) = det (N * M) := by
  rw [det_mul, det_mul, mul_comm]

/-- If there exists a two-sided inverse `M'` for `M` (indexed differently),
then `det (N * M) = det (M * N)`. -/
/-
**Matrix.det_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m
 n A} {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : det (M * N) 
= det (N * M)
参数：hMM' : M * M' = 1；hM'M : M' * M = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `Matrix.det_comm`：det_comm [DecidableEq n] (M N : Matrix n n A) : det (M 
* N) = det (N * M)
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A

--- 原说明 ---
If there exists a two-sided inverse `M'` for `M` (indexed differently),
then `det (N * M) = det (M * N)`.
-/
theorem det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m n A}
    {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : det (M * N) = det (N * M) := by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := indexEquivOfInv hMM' hM'M
  rw [← det_submatrix_equiv_self e, ← submatrix_mul_equiv _ _ _ (Equiv.refl n) _, det_comm,
    submatrix_mul_equiv, Equiv.coe_refl, submatrix_id_id]

/-- If `M'` is a two-sided inverse for `M` (indexed differently), `det (M * N * M') = det N`.

See `Matrix.det_conj` and `Matrix.det_conj'` for the case when `M' = M⁻¹` or vice versa. -/
/-
**Matrix.det_conj_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_conj_of_mul_eq_one [DecidableEq m] [DecidableEq n] {M : Matrix m n A} 
{M' : Matrix n m A} {N : Matrix n n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) :
 det (M * N * M') = det N
参数：hMM' : M * M' = 1；hM'M : M' * M = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_comm'`：det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix 
n m A} {N : Matrix m n A} {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M
 = 1) …
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…

--- 原说明 ---
If `M'` is a two-sided inverse for `M` (indexed differently), `det (M * N * M') 
= det N`.

See `Matrix.det_conj` and `Matrix.det_conj'` for the case when `M' = M⁻¹` or vic
e versa.
-/
theorem det_conj_of_mul_eq_one [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} {N : Matrix n n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) :
    det (M * N * M') = det N := by
  rw [← det_comm' hM'M hMM', ← Matrix.mul_assoc, hM'M, Matrix.one_mul]

end Matrix

end Conjugate

namespace LinearMap

/-! ### Determinant of a linear map -/


variable {A : Type*} [CommRing A] [Module A M]
variable {κ : Type*} [Fintype κ]

/-- The determinant of `LinearMap.toMatrix` does not depend on the choice of basis. -/
/-
**LinearMap.det_toMatrix_eq_det_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_toMatrix_eq_det_toMatrix [DecidableEq κ] (b : Basis ι A M) (c : Basis 
κ A M) (f : M ->ₗ[A] M) : det (LinearMap.toMatrix b b f) = det (LinearMap.toMatr
ix c c f)
参数：b : Basis ι A M；c : Basis κ A M；f : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearMap_toMatrix_mul_basis_toMatrix`：linearMap_toMatrix_mul_basis_toMa
trix [Finite κ'] [DecidableEq ι] [DecidableEq ι'] : LinearMap.toMatrix b' c' f *
 b'.toMatrix b = LinearMap.…
· 使用定理 `basis_toMatrix_mul_linearMap_toMatrix`：basis_toMatrix_mul_linearMap_toMa
trix [Finite κ] [Fintype κ'] [DecidableEq ι'] : c.toMatrix c' * LinearMap.toMatr
ix b' c' f = LinearMap.toMa…
· 使用定理 `Matrix.det_conj_of_mul_eq_one`：det_conj_of_mul_eq_one [DecidableEq m] [D
ecidableEq n] {M : Matrix m n A} {M' : Matrix n m A} {N : Matrix n n A} (hMM' : 
M * M' = 1) (hM'M :…
· 使用定理 `Module.Basis.toMatrix_mul_toMatrix`：toMatrix_mul_toMatrix {ι'' : Type*} 
[Fintype ι'] (b'' : ι'' -> M) : b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b''
· 使用定理 `Module.Basis.toMatrix_self`：toMatrix_self [DecidableEq ι] : e.toMatrix e
 = 1

--- 原说明 ---
The determinant of `LinearMap.toMatrix` does not depend on the choice of basis.
-/
theorem det_toMatrix_eq_det_toMatrix [DecidableEq κ] (b : Basis ι A M) (c : Basis κ A M)
    (f : M →ₗ[A] M) : det (LinearMap.toMatrix b b f) = det (LinearMap.toMatrix c c f) := by
  rw [← linearMap_toMatrix_mul_basis_toMatrix c b c, ← basis_toMatrix_mul_linearMap_toMatrix b c b,
      Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]


/-- The determinant of an endomorphism given a basis.

See `LinearMap.det` for a version that populates the basis non-computably.

Although the `Trunc (Basis ι A M)` parameter makes it slightly more convenient to switch bases,
there is no good way to generalize over universe parameters, so we can't fully state in `detAux`'s
type that it does not depend on the choice of basis. Instead you can use the `detAux_def''` lemma,
or avoid mentioning a basis at all using `LinearMap.det`.
-/
irreducible_def detAux : Trunc (Basis ι A M) → (M →ₗ[A] M) →* A :=
  Trunc.lift
    (fun b : Basis ι A M => detMonoidHom.comp (toMatrixAlgEquiv b : (M →ₗ[A] M) →* Matrix ι ι A))
    fun b c => MonoidHom.ext <| det_toMatrix_eq_det_toMatrix b c

/-- Unfold lemma for `detAux`.

See also `detAux_def''` which allows you to vary the basis.
-/
/-
**LinearMap.detAux_def'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：detAux_def' (b : Basis ι A M) (f : M ->ₗ[A] M) : LinearMap.detAux (Trunc.m
k b) f = Matrix.det (LinearMap.toMatrix b b f)
参数：b : Basis ι A M；f : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.detAux_def`：∀ {M : Type u_7} [inst : AddCommGroup M] {ι : Type
 u_8} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] {A : Type u_9}   [inst_3 : C
ommRing A]…

--- 原说明 ---
Unfold lemma for `detAux`.

See also `detAux_def''` which allows you to vary the basis.
-/
theorem detAux_def' (b : Basis ι A M) (f : M →ₗ[A] M) :
    LinearMap.detAux (Trunc.mk b) f = Matrix.det (LinearMap.toMatrix b b f) := by
  #adaptation_note /-- Proof repaired after leanprover/lean4#13492.
  The first line below was previously just `rw [detAux]`.
  The replacement proof is a short-term fix, and we request that the authors/maintainers of
  this file review the proof, and either approve it by removing this note, revise
  the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
  needs addressing. -/
  simp only [detAux_def, Trunc.lift_mk]
  rfl
/-
**LinearMap.detAux_def''** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：detAux_def'' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Bas
is ι A M) (b' : Basis ι' A M) (f : M ->ₗ[A] M) : LinearMap.detAux tb f = Matrix.
det (LinearMap.toMatrix b' b' f)
参数：tb : Trunc <| Basis ι A M；b' : Basis ι' A M；f : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.induction_on`：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α),
 (∀ (a : α), β (Trunc.mk a)) → β q
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.detAux_def'`：detAux_def' (b : Basis ι A M) (f : M ->ₗ[A] M) : 
LinearMap.detAux (Trunc.mk b) f = Matrix.det (LinearMap.toMatrix b b f)
· 使用定理 `LinearMap.det_toMatrix_eq_det_toMatrix`：det_toMatrix_eq_det_toMatrix [De
cidableEq κ] (b : Basis ι A M) (c : Basis κ A M) (f : M ->ₗ[A] M) : det (LinearM
ap.toMatrix b b f) = det (Li…
-/
theorem detAux_def'' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M)
    (b' : Basis ι' A M) (f : M →ₗ[A] M) :
    LinearMap.detAux tb f = Matrix.det (LinearMap.toMatrix b' b' f) := by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']

@[simp]
/-
**LinearMap.detAux_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：detAux_id (b : Trunc <| Basis ι A M) : LinearMap.detAux b LinearMap.id = 1
参数：b : Trunc <| Basis ι A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem detAux_id (b : Trunc <| Basis ι A M) : LinearMap.detAux b LinearMap.id = 1 :=
  (LinearMap.detAux b).map_one

@[simp]
/-
**LinearMap.detAux_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：detAux_comp (b : Trunc <| Basis ι A M) (f g : M ->ₗ[A] M) : LinearMap.detA
ux b (f.comp g) = LinearMap.detAux b f * LinearMap.detAux b g
参数：b : Trunc <| Basis ι A M；f g : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem detAux_comp (b : Trunc <| Basis ι A M) (f g : M →ₗ[A] M) :
    LinearMap.detAux b (f.comp g) = LinearMap.detAux b f * LinearMap.detAux b g :=
  (LinearMap.detAux b).map_mul f g

section

open scoped Classical in
-- Discourage the elaborator from unfolding `det` and producing a huge term by marking it
-- as irreducible.
/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
protected irreducible_def det : (M →ₗ[A] M) →* A :=
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.choose_spec.some)
  else 1

open scoped Classical in
/-
**LinearMap.coe_det** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_det [DecidableEq M] : ⇑(LinearMap.det : (M ->ₗ[A] M) ->* A) = if H : e
xists s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.cho
ose_spec.some) else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_def`：∀ {M : Type u_7} [inst : AddCommGroup M] {A : Type u_
8} [inst_1 : CommRing A] [inst_2 : _root_.Module A M],   LinearMap.det = if H : 
∃ s, No…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem coe_det [DecidableEq M] :
    ⇑(LinearMap.det : (M →ₗ[A] M) →* A) =
      if H : ∃ s : Finset M, Nonempty (Basis s A M) then
        LinearMap.detAux (Trunc.mk H.choose_spec.some)
      else 1 := by
  ext
  rw [LinearMap.det_def]
  split_ifs
  · congr -- use the correct `DecidableEq` instance
  rfl
/-
**LinearMap._root_.Module.Free.of_det_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Free.of_det_ne_one {f : M →ₗ[R] M} (hf : f.det ≠ 1) :
    Module.Free R M := by
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

end

-- Auxiliary lemma, the `simp` normal form goes in the other direction
-- (using `LinearMap.det_toMatrix`)
/-
**LinearMap.det_eq_det_toMatrix_of_finset** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_eq_det_toMatrix_of_finset [DecidableEq M] {s : Finset M} (b : Basis s 
A M) (f : M ->ₗ[A] M) : LinearMap.det f = Matrix.det (LinearMap.toMatrix b b f)
参数：b : Basis s A M；f : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_det`：coe_det [DecidableEq M] : ⇑(LinearMap.det : (M ->ₗ[A]
 M) ->* A) = if H : exists s : Finset M, Nonempty (Basis s A M) then LinearMap.d
etAux (…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LinearMap.detAux_def''`：detAux_def'' {ι' : Type*} [Fintype ι'] [Decidabl
eEq ι'] (tb : Trunc <| Basis ι A M) (b' : Basis ι' A M) (f : M ->ₗ[A] M) : Linea
rMap.detAux …
-/
theorem det_eq_det_toMatrix_of_finset [DecidableEq M] {s : Finset M} (b : Basis s A M)
    (f : M →ₗ[A] M) : LinearMap.det f = Matrix.det (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s A M) := ⟨s, ⟨b⟩⟩
  rw [LinearMap.coe_det, dif_pos this, detAux_def'' _ b]

@[simp]
/-
**LinearMap.det_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) : Matrix.det (toMatrix b b
 f) = LinearMap.det f
参数：b : Basis ι A M；f : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_eq_det_toMatrix_of_finset`：det_eq_det_toMatrix_of_finset [
DecidableEq M] {s : Finset M} (b : Basis s A M) (f : M ->ₗ[A] M) : LinearMap.det
 f = Matrix.det (LinearMap.to…
· 使用定理 `LinearMap.det_toMatrix_eq_det_toMatrix`：det_toMatrix_eq_det_toMatrix [De
cidableEq κ] (b : Basis ι A M) (c : Basis κ A M) (f : M ->ₗ[A] M) : det (LinearM
ap.toMatrix b b f) = det (Li…
-/
theorem det_toMatrix (b : Basis ι A M) (f : M →ₗ[A] M) :
    Matrix.det (toMatrix b b f) = LinearMap.det f := by
  have := Classical.decEq M
  rw [det_eq_det_toMatrix_of_finset b.reindexFinsetRange,
    det_toMatrix_eq_det_toMatrix b b.reindexFinsetRange]

@[simp]
/-
**LinearMap.det_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_toMatrix' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι -> A) ->ₗ[A]
 ι -> A) : Matrix.det (LinearMap.toMatrix' f) = LinearMap.det f
参数：f : (ι -> A) ->ₗ[A] ι -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_toMatrix' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → A) →ₗ[A] ι → A) :
    Matrix.det (LinearMap.toMatrix' f) = LinearMap.det f := by simp [← toMatrix_eq_toMatrix']

@[simp]
/-
**LinearMap.det_toLin** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_toLin (b : Basis ι R M) (f : Matrix ι ι R) : LinearMap.det (Matrix.toL
in b b f) = f.det
参数：b : Basis ι R M；f : Matrix ι ι R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
-/
theorem det_toLin (b : Basis ι R M) (f : Matrix ι ι R) :
    LinearMap.det (Matrix.toLin b b f) = f.det := by
  rw [← LinearMap.det_toMatrix b, LinearMap.toMatrix_toLin]

@[simp]
/-
**LinearMap.det_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_toLin' (f : Matrix ι ι R) : LinearMap.det (Matrix.toLin' f) = Matrix.d
et f
参数：f : Matrix ι ι R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_toLin`：det_toLin (b : Basis ι R M) (f : Matrix ι ι R) : Li
nearMap.det (Matrix.toLin b b f) = f.det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_toLin' (f : Matrix ι ι R) : LinearMap.det (Matrix.toLin' f) = Matrix.det f := by
  simp only [← toLin_eq_toLin', det_toLin]

/-- To show `P (LinearMap.det f)` it suffices to consider `P (Matrix.det (toMatrix _ _ f))` and
`P 1`. -/
@[elab_as_elim]
/-
**LinearMap.det_cases** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_cases [DecidableEq M] {P : A -> Prop} (f : M ->ₗ[A] M) (hb : forall (s
 : Finset M) (b : Basis s A M), P (Matrix.det (toMatrix b b f))) (h1 : P 1) : P 
(LinearMap.det f)
参数：f : M ->ₗ[A] M；hb : forall (s : Finset M) (b : Basis s A M), P (Matrix.det (t
oMatrix b b f))；h1 : P 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `LinearMap.det_def`：∀ {M : Type u_7} [inst : AddCommGroup M] {A : Type u_
8} [inst_1 : CommRing A] [inst_2 : _root_.Module A M],   LinearMap.det = if H : 
∃ s, No…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
To show `P (LinearMap.det f)` it suffices to consider `P (Matrix.det (toMatrix _
 _ f))` and
`P 1`.
-/
theorem det_cases [DecidableEq M] {P : A → Prop} (f : M →ₗ[A] M)
    (hb : ∀ (s : Finset M) (b : Basis s A M), P (Matrix.det (toMatrix b b f))) (h1 : P 1) :
    P (LinearMap.det f) := by
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then
    obtain ⟨s, ⟨b⟩⟩ := H
    rw [← det_toMatrix b]
    exact hb s b
  else
    rwa [LinearMap.det_def, dif_neg H]

@[simp]
/-
**LinearMap.det_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_comp (f g : M ->ₗ[A] M) : LinearMap.det (f.comp g) = LinearMap.det f *
 LinearMap.det g
参数：f g : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem det_comp (f g : M →ₗ[A] M) :
    LinearMap.det (f.comp g) = LinearMap.det f * LinearMap.det g :=
  LinearMap.det.map_mul f g

@[simp]
/-
**LinearMap.det_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem det_id : LinearMap.det (LinearMap.id : M →ₗ[A] M) = 1 :=
  LinearMap.det.map_one

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ dim M`. -/
@[simp]
/-
**LinearMap.det_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) : LinearMap.det (c • f
) = c ^ Module.finrank A M * LinearMap.det f
参数：c : A；f : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finrank_eq_zero_of_not_exists_basis`：finrank_eq_zero_of_not_exists_basis
 (h : ¬exists s : Finset M, Nonempty (Basis (s : Set M) R M)) : finrank R M = 0
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_det`：coe_det [DecidableEq M] : ⇑(LinearMap.det : (M ->ₗ[A]
 M) ->* A) = if H : exists s : Finset M, Nonempty (Basis s A M) then LinearMap.d
etAux (…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Multiplying a map by a scalar `c` multiplies its determinant by `c ^ dim M`.
-/
theorem det_smul [Module.Free A M] (c : A) (f : M →ₗ[A] M) :
    LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f := by
  nontriviality A
  by_cases H : ∃ s : Finset M, Nonempty (Basis s A M)
  · have : Module.Finite A M := by
      rcases H with ⟨s, ⟨hs⟩⟩
      exact Module.Finite.of_basis hs
    simp only [← det_toMatrix (Module.finBasis A M), map_smul, Fintype.card_fin, Matrix.det_smul]
  · classical
      have : Module.finrank A M = 0 := finrank_eq_zero_of_not_exists_basis H
      simp [coe_det, H, this]
/-
**LinearMap.det_zero'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_zero' {ι : Type*} [Finite ι] [Nonempty ι] (b : Basis ι A M) : LinearMa
p.det (0 : M ->ₗ[A] M) = 0
参数：b : Basis ι A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Matrix.det_zero`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] [Nonempty n],   Matrix.det 0 = 0
-/
theorem det_zero' {ι : Type*} [Finite ι] [Nonempty ι] (b : Basis ι A M) :
    LinearMap.det (0 : M →ₗ[A] M) = 0 := by
  have := Classical.decEq ι
  cases nonempty_fintype ι
  rw [← det_toMatrix b, map_zero, det_zero]

/-- In a finite-dimensional vector space, the zero map has determinant `1` in dimension `0`,
and `0` otherwise. We give a formula that also works in infinite dimension, where we define
the determinant to be `1`. -/
@[simp]
/-
**LinearMap.det_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_zero [Module.Free A M] : LinearMap.det (0 : M ->ₗ[A] M) = (0 : A) ^ Mo
dule.finrank A M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `LinearMap.det_smul`：det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) 
: LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a finite-dimensional vector space, the zero map has determinant `1` in dimens
ion `0`,
and `0` otherwise. We give a formula that also works in infinite dimension, wher
e we define
the determinant to be `1`.
-/
theorem det_zero [Module.Free A M] :
    LinearMap.det (0 : M →ₗ[A] M) = (0 : A) ^ Module.finrank A M := by
  simp only [← zero_smul A (1 : M →ₗ[A] M), det_smul, mul_one, map_one]
/-
**LinearMap.det_eq_one_of_not_module_finite** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：det_eq_one_of_not_module_finite (h : ¬Module.Finite R M) (f : M ->ₗ[R] M) 
: f.det = 1
参数：h : ¬Module.Finite R M；f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_def`：∀ {M : Type u_7} [inst : AddCommGroup M] {A : Type u_
8} [inst_1 : CommRing A] [inst_2 : _root_.Module A M],   LinearMap.det = if H : 
∃ s, No…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MonoidHom.one_apply`：MonoidHom.one_apply [MulOne M] [MulOneClass N] (x :
 M) : (1 : M ->* N) x = 1
-/
theorem det_eq_one_of_not_module_finite (h : ¬Module.Finite R M) (f : M →ₗ[R] M) : f.det = 1 := by
  rw [LinearMap.det, dif_neg, MonoidHom.one_apply]
  exact fun ⟨_, ⟨b⟩⟩ ↦ h (Module.Finite.of_basis b)

@[nontriviality]
/-
**LinearMap.det_eq_one_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_eq_one_of_subsingleton [Subsingleton M] (f : M ->ₗ[R] M) : LinearMap.d
et (f : M ->ₗ[R] M) = 1
参数：f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
-/
theorem det_eq_one_of_subsingleton [Subsingleton M] (f : M →ₗ[R] M) :
    LinearMap.det (f : M →ₗ[R] M) = 1 := by
  have b : Basis (Fin 0) R M := Basis.empty M
  rw [← f.det_toMatrix b]
  exact Matrix.det_isEmpty
/-
**LinearMap.det_eq_one_of_finrank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_eq_one_of_finrank_eq_zero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGr
oup M] [Module 𝕜 M] (h : Module.finrank 𝕜 M = 0) (f : M ->ₗ[𝕜] M) : LinearMap.de
t (f : M ->ₗ[𝕜] M) = 1
参数：h : Module.finrank 𝕜 M = 0；f : M ->ₗ[𝕜] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.det_cases`：det_cases [DecidableEq M] {P : A -> Prop} (f : M ->
ₗ[A] M) (hb : forall (s : Finset M) (b : Basis s A M), P (Matrix.det (toMatrix b
 b f))) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem det_eq_one_of_finrank_eq_zero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] (h : Module.finrank 𝕜 M = 0) (f : M →ₗ[𝕜] M) :
    LinearMap.det (f : M →ₗ[𝕜] M) = 1 := by
  classical
    refine @LinearMap.det_cases M _ 𝕜 _ _ _ (fun t => t = 1) f ?_ rfl
    intro s b
    have : IsEmpty s := by
      rw [← Fintype.card_eq_zero_iff]
      exact (Module.finrank_eq_card_basis b).symm.trans h
    exact Matrix.det_isEmpty

/-- Conjugating a linear map by a linear equiv does not change its determinant. -/
@[simp]
/-
**LinearMap.det_conj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_conj {N : Type*} [AddCommGroup N] [Module A N] (f : M ->ₗ[A] M) (e : M
 ≃ₗ[A] N) : LinearMap.det ((e : M ->ₗ[A] N) ∘ₗ f ∘ₗ (e.symm : N ->ₗ[A] M)) = Lin
earMap.det f
参数：f : M ->ₗ[A] M；e : M ≃ₗ[A] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.det_conj_of_mul_eq_one`：det_conj_of_mul_eq_one [DecidableEq m] [D
ecidableEq n] {M : Matrix m n A} {M' : Matrix n m A} {N : Matrix n n A} (hMM' : 
M * M' = 1) (hM'M :…
· 使用定理 `LinearEquiv.comp_coe`：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃
) : (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃
] M₃)
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearEquiv.refl_toLinearMap`：refl_toLinearMap [Module R M] : (LinearEqu
iv.refl R M : M ->ₗ[R] M) = LinearMap.id
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_det`：coe_det [DecidableEq M] : ⇑(LinearMap.det : (M ->ₗ[A]
 M) ->* A) = if H : exists s : Finset M, Nonempty (Basis s A M) then LinearMap.d
etAux (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Conjugating a linear map by a linear equiv does not change its determinant.
-/
theorem det_conj {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] M) (e : M ≃ₗ[A] N) :
    LinearMap.det ((e : M →ₗ[A] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[A] M)) = LinearMap.det f := by
  classical
    by_cases H : ∃ s : Finset M, Nonempty (Basis s A M)
    · rcases H with ⟨s, ⟨b⟩⟩
      rw [← det_toMatrix b f, ← det_toMatrix (b.map e), toMatrix_comp (b.map e) b (b.map e),
        toMatrix_comp (b.map e) b b, ← Matrix.mul_assoc, Matrix.det_conj_of_mul_eq_one]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
    · have H' : ¬∃ t : Finset N, Nonempty (Basis t A N) := by
        contrapose H
        rcases H with ⟨s, ⟨b⟩⟩
        exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
      simp only [coe_det, H, H', MonoidHom.one_apply, dif_neg, not_false_eq_true]

/-- If a linear map is invertible, so is its determinant. -/
/-
**LinearMap.isUnit_det** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isUnit_det {A : Type*} [CommRing A] [Module A M] (f : M ->ₗ[A] M) (hf : Is
Unit f) : IsUnit (LinearMap.det f)
参数：f : M ->ₗ[A] M；hf : IsUnit f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)

--- 原说明 ---
If a linear map is invertible, so is its determinant.
-/
theorem isUnit_det {A : Type*} [CommRing A] [Module A M] (f : M →ₗ[A] M) (hf : IsUnit f) :
    IsUnit (LinearMap.det f) := IsUnit.map LinearMap.det hf
/-
**LinearMap.isUnit_iff_isUnit_det** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isUnit_iff_isUnit_det [Module.Finite R M] [Module.Free R M] (f : M ->ₗ[R] 
M) : IsUnit f ↔ IsUnit f.det
参数：f : M ->ₗ[R] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.isUnit_toMatrix_iff`：LinearMap.isUnit_toMatrix_iff {f : M₁ ->ₗ
[R] M₁} : IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isUnit_iff_isUnit_det [Module.Finite R M] [Module.Free R M] (f : M →ₗ[R] M) :
    IsUnit f ↔ IsUnit f.det := by
  let b := Module.Free.chooseBasis R M
  rw [← isUnit_toMatrix_iff b, ← det_toMatrix b, Matrix.isUnit_iff_isUnit_det (toMatrix b b f)]

/-- If a linear map has determinant different from `1`, then the module is free. -/
/-
**LinearMap.free_of_det_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：free_of_det_ne_one {f : M ->ₗ[R] M} (hf : f.det != 1) : Module.Free R M
参数：hf : f.det != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_det`：coe_det [DecidableEq M] : ⇑(LinearMap.det : (M ->ₗ[A]
 M) ->* A) = if H : exists s : Finset M, Nonempty (Basis s A M) then LinearMap.d
etAux (…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If a linear map has determinant different from `1`, then the module is free.
-/
theorem free_of_det_ne_one {f : M →ₗ[R] M} (hf : f.det ≠ 1) : Module.Free R M := by
  by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

/-- If a linear map has determinant different from `1`, then the space is finite-dimensional. -/
/-
**LinearMap.finite_of_det_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：finite_of_det_ne_one {f : M ->ₗ[R] M} (hf : f.det != 1) : Module.Finite R 
M
参数：hf : f.det != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_det`：coe_det [DecidableEq M] : ⇑(LinearMap.det : (M ->ₗ[A]
 M) ->* A) = if H : exists s : Finset M, Nonempty (Basis s A M) then LinearMap.d
etAux (…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If a linear map has determinant different from `1`, then the space is finite-dim
ensional.
-/
theorem finite_of_det_ne_one {f : M →ₗ[R] M} (hf : f.det ≠ 1) : Module.Finite R M := by
  by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Finite.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

set_option backward.isDefEq.respectTransparency false in
/-- If the determinant of a map vanishes, then the map is not injective. -/
/-
**LinearMap.bot_lt_ker_of_det_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：bot_lt_ker_of_det_eq_zero [IsDomain R] [Free R M] {f : M ->ₗ[R] M} (hf : f
.det = 0) : ⊥ < ker f
参数：hf : f.det = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearMap.finite_of_det_ne_one`：finite_of_det_ne_one {f : M ->ₗ[R] M} (h
f : f.det != 1) : Module.Finite R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.exists_mulVec_eq_zero_iff`：exists_mulVec_eq_zero_iff [DecidableEq
 n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If the determinant of a map vanishes, then the map is not injective.
-/
theorem bot_lt_ker_of_det_eq_zero [IsDomain R] [Free R M] {f : M →ₗ[R] M} (hf : f.det = 0) :
    ⊥ < ker f := by
  have : Module.Finite R M := by simp [finite_of_det_ne_one (f := f), hf]
  let b := Module.finBasis R M
  suffices ∃ x, f x = 0 ∧ x ≠ 0 by simpa [bot_lt_iff_ne_bot, ker_eq_bot']
  obtain ⟨v, hv_ne_zero, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (det_toMatrix b f ▸ hf)
  refine ⟨b.equivFun.symm v, ?_, b.equivFun.symm.map_ne_zero_iff.mpr hv_ne_zero⟩
  rw [← b.equivFun.injective.eq_iff]
  simp_all [funext_iff, Matrix.mulVec, dotProduct, toMatrix_apply, mul_comm]

/-- The determinant of a map vanishes iff the map is not injective. -/
/-
**LinearMap.det_eq_zero_iff_ker_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_eq_zero_iff_ker_ne_bot [IsDomain R] [Free R M] [Module.Finite R M] {f 
: M ->ₗ[R] M} : f.det = 0 ↔ ker f != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `LinearMap.bot_lt_ker_of_det_eq_zero`：bot_lt_ker_of_det_eq_zero [IsDomain
 R] [Free R M] {f : M ->ₗ[R] M} (hf : f.det = 0) : ⊥ < ker f
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.exists_mulVec_eq_zero_iff`：exists_mulVec_eq_zero_iff [DecidableEq
 n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toMatrix_mulVec_repr`：LinearMap.toMatrix_mulVec_repr (f : M₁ -
>ₗ[R] M₂) (x : M₁) : LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x)

--- 原说明 ---
The determinant of a map vanishes iff the map is not injective.
-/
theorem det_eq_zero_iff_ker_ne_bot [IsDomain R] [Free R M] [Module.Finite R M] {f : M →ₗ[R] M} :
    f.det = 0 ↔ ker f ≠ ⊥ := by
  constructor <;> intro h
  · exact bot_lt_iff_ne_bot.mp (bot_lt_ker_of_det_eq_zero h)
  · let b := Module.finBasis R M
    obtain ⟨v, ⟨_, hv_ne_zero⟩⟩ := (ker f).ne_bot_iff.mp h
    rw [← det_toMatrix b, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun i => b.repr v i, by simpa, by simpa [toMatrix_mulVec_repr]⟩

/-- If the determinant of a map vanishes, then the map is not onto. -/
/-
**LinearMap.range_lt_top_of_det_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_lt_top_of_det_eq_zero [IsDomain R] [Free R M] {f : M ->ₗ[R] M} (hf :
 f.det = 0) : range f < ⊤
参数：hf : f.det = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `LinearMap.exists_rightInverse_of_surjective`：∀ {R : Type u_1} [inst : Se
miring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]
   {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.det_comp`：det_comp (f g : M ->ₗ[A] M) : LinearMap.det (f.comp 
g) = LinearMap.det f * LinearMap.det g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If the determinant of a map vanishes, then the map is not onto.
-/
theorem range_lt_top_of_det_eq_zero [IsDomain R] [Free R M] {f : M →ₗ[R] M}
    (hf : f.det = 0) : range f < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective h
  simpa [hf] using congr_arg LinearMap.det hg

/-- When the function is over the base ring, the determinant is the evaluation at `1`. -/
/-
**LinearMap.det_ring** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R), LinearMap.det f = f 
1
参数：f : R →ₗ[R] R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用引理 `LinearMap.toMatrix_singleton`：LinearMap.toMatrix_singleton {ι : Type*} [
Unique ι] (f : R ->ₗ[R] R) (i j : ι) : f.toMatrix (.singleton ι R) (.singleton ι
 R) i j = f 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When the function is over the base ring, the determinant is the evaluation at `1
`.
-/
@[simp] lemma det_ring (f : R →ₗ[R] R) : f.det = f 1 := by
  simp [← det_toMatrix (Basis.singleton Unit R)]
/-
**LinearMap.det_mulLeft** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：det_mulLeft (a : R) : (mulLeft R a).det = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_ring`：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R)
, LinearMap.det f = f 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma det_mulLeft (a : R) : (mulLeft R a).det = a := by simp
/-
**LinearMap.det_mulRight** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：det_mulRight (a : R) : (mulRight R a).det = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_ring`：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R)
, LinearMap.det f = f 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma det_mulRight (a : R) : (mulRight R a).det = a := by simp
/-
**LinearMap.det_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_prodMap [Module.Free R M] [Module.Free R M'] [Module.Finite R M] [Modu
le.Finite R M'] (f : Module.End R M) (f' : Module.End R M') : (prodMap f f').det
 = f.det * f'.det
参数：f : Module.End R M；f' : Module.End R M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用引理 `LinearMap.toMatrix_prodMap`：LinearMap.toMatrix_prodMap [DecidableEq m] [
DecidableEq (n oplus m)] (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) : toMatri
x (v₁.prod v₂) (…
· 使用定理 `Matrix.det_fromBlocks_zero₂₁`：det_fromBlocks_zero₂₁ (A : Matrix m m R) (
B : Matrix m n R) (D : Matrix n n R) : (Matrix.fromBlocks A B 0 D).det = A.det *
 D.det
-/
theorem det_prodMap [Module.Free R M] [Module.Free R M'] [Module.Finite R M] [Module.Finite R M']
    (f : Module.End R M) (f' : Module.End R M') :
    (prodMap f f').det = f.det * f'.det := by
  let b := Module.Free.chooseBasis R M
  let b' := Module.Free.chooseBasis R M'
  rw [← det_toMatrix (b.prod b'), ← det_toMatrix b, ← det_toMatrix b', toMatrix_prodMap,
    det_fromBlocks_zero₂₁, det_toMatrix]

omit [DecidableEq ι] in
/-
**LinearMap.det_pi** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_pi [Module.Free R M] [Module.Finite R M] (f : ι -> M ->ₗ[R] M) : (Line
arMap.pi (fun i => (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det
参数：f : ι -> M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `LinearMap.toMatrix_apply'`：LinearMap.toMatrix_apply' (f : M₁ ->ₗ[R] M₂) 
(i : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Module.Basis.repr_reindex_apply`：repr_reindex_apply (i' : ι') : (b.reind
ex e).repr x i' = b.repr x (e.symm i')
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `Pi.basis_apply`：basis_apply [DecidableEq η] (s : forall j, Basis (ιs j) 
R (Ms j)) (ji) : Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2)
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
theorem det_pi [Module.Free R M] [Module.Finite R M] (f : ι → M →ₗ[R] M) :
    (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det := by
  classical
  let b := Module.Free.chooseBasis R M
  let B := (Pi.basis (fun _ : ι ↦ b)).reindex <|
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix b]
  have : ((LinearMap.toMatrix B B) (LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i)) =
      Matrix.blockDiagonal (fun i ↦ LinearMap.toMatrix b b (f i)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    unfold B
    simp_rw [LinearMap.toMatrix_apply', Matrix.blockDiagonal_apply, Basis.coe_reindex,
      Function.comp_apply, Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Equiv.sigmaEquivProd_symm_apply, Prod.swap_prod_mk, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toMatrix_apply', LinearMap.coe_proj, Function.eval, Pi.single_apply]
    split_ifs with h
    · rw [h]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [this, Matrix.det_blockDiagonal]

end LinearMap

namespace Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Free R S]

/-
**Algebra.det_lsmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：det_lsmul (x : R) : LinearMap.det (lsmul R R S x) = x ^ finrank R S
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.lsmul_eq_smul_one`：lsmul_eq_smul_one (a : A) : lsmul R R M a = a
 • 1
· 使用定理 `LinearMap.det_smul`：det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) 
: LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma det_lsmul (x : R) : LinearMap.det (lsmul R R S x) = x ^ finrank R S := by
  rw [lsmul_eq_smul_one, LinearMap.det_smul, map_one, mul_one]

end Algebra

namespace LinearEquiv

/-- On a `LinearEquiv`, the domain of `LinearMap.det` can be promoted to `Rˣ`. -/
/-
**LinearEquiv.det** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] → {M : Type u_2} → [inst_1 : AddCom
mGroup M] → [inst_2 : _root_.Module R M] → (M ≃ₗ[R] M) →* Rˣ
参数：M ≃ₗ[R] M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a `LinearEquiv`, the domain of `LinearMap.det` can be promoted to `Rˣ`.
-/
protected def det : (M ≃ₗ[R] M) →* Rˣ :=
  (Units.map (LinearMap.det : (M →ₗ[R] M) →* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom

@[simp]
/-
**LinearEquiv.coe_det** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = LinearMap.det (f : M ->ₗ[
R] M)
参数：f : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = LinearMap.det (f : M →ₗ[R] M) :=
  rfl

@[simp]
/-
**LinearEquiv.coe_inv_det** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_inv_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f)⁻¹ = LinearMap.det (f.sy
mm : M ->ₗ[R] M)
参数：f : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f)⁻¹ = LinearMap.det (f.symm : M →ₗ[R] M) :=
  rfl

@[simp]
/-
**LinearEquiv.det_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：det_refl : LinearEquiv.det (LinearEquiv.refl R M) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
-/
theorem det_refl : LinearEquiv.det (LinearEquiv.refl R M) = 1 :=
  Units.ext <| LinearMap.det_id

@[simp]
/-
**LinearEquiv.det_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：det_trans (f g : M ≃ₗ[R] M) : LinearEquiv.det (f.trans g) = LinearEquiv.de
t g * LinearEquiv.det f
参数：f g : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem det_trans (f g : M ≃ₗ[R] M) :
    LinearEquiv.det (f.trans g) = LinearEquiv.det g * LinearEquiv.det f :=
  map_mul _ g f

@[simp]
/-
**LinearEquiv.det_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：det_symm (f : M ≃ₗ[R] M) : LinearEquiv.det f.symm = LinearEquiv.det f⁻¹
参数：f : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem det_symm (f : M ≃ₗ[R] M) : LinearEquiv.det f.symm = LinearEquiv.det f⁻¹ :=
  map_inv _ f

/-- Conjugating a linear equiv by a linear equiv does not change its determinant. -/
@[simp]
/-
**LinearEquiv.det_conj** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：det_conj (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M') : LinearEquiv.det ((e.symm.trans
 f).trans e) = LinearEquiv.det f
参数：f : M ≃ₗ[R] M；e : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `LinearEquiv.comp_coe`：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃
) : (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃
] M₃)
· 使用定理 `LinearMap.det_conj`：det_conj {N : Type*} [AddCommGroup N] [Module A N] (
f : M ->ₗ[A] M) (e : M ≃ₗ[A] N) : LinearMap.det ((e : M ->ₗ[A] N) ∘ₗ f ∘ₗ (e.sym
m : N ->…

--- 原说明 ---
Conjugating a linear equiv by a linear equiv does not change its determinant.
-/
theorem det_conj (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M') :
    LinearEquiv.det ((e.symm.trans f).trans e) = LinearEquiv.det f := by
  rw [← Units.val_inj, coe_det, coe_det, ← comp_coe, ← comp_coe, LinearMap.det_conj]

attribute [irreducible] LinearEquiv.det

end LinearEquiv

/-
**LinearMap.det_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {K : Type u_5} {V : Type u_6} {W : Type u_7} [inst : Field K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup W] [inst_4
 : _root_.Module K W] {F : Type u_8}   [inst_5 : EquivLike F (Module.End K V) (M
odule.End K W)] [AlgEquivClass F K (Module.End K V) (Module.End K W)] (f : F)   
(x : Module.End K V), LinearMap.det (f x) = LinearMap.det x
参数：Module.End K V；Module.End K W；Module.End K V；Module.End K W；f : F；x : Module.
End K V；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.eq_linearEquivConjAlgEquiv`：∀ {K : Type u_1} {V : Type u_2} {W 
: Type u_3} [inst : Semifield K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.M
odule K V] [Module.Projec…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.det_conj`：det_conj {N : Type*} [AddCommGroup N] [Module A N] (
f : M ->ₗ[A] M) (e : M ≃ₗ[A] N) : LinearMap.det ((e : M ->ₗ[A] N) ∘ₗ f ∘ₗ (e.sym
m : N ->…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] theorem LinearMap.det_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {F : Type*} [EquivLike F (End K V) (End K W)]
    [AlgEquivClass F K _ _] (f : F) (x : End K V) : (f x).det = x.det :=
  have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ det_conj _ _
/-
**Matrix.det_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {K : Type u_5} {m : Type u_6} {n : Type u_7} [inst : Field K] [inst_1 : 
Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq m] [inst_4 : DecidableEq
 n] {F : Type u_8} [inst_5 : EquivLike F (Matrix m m K) (Matrix n n K)]   [AlgEq
uivClass F K (Matrix m m K) (Matrix n n K)] (f : F) (x : Matrix m m K), (f x).de
t = x.det
参数：Matrix m m K；Matrix n n K；Matrix m m K；Matrix n n K；f : F；x : Matrix m m K；f 
x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `LinearMap.toMatrix'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {n : T
ype u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' 1 
= 1
· 使用定理 `LinearMap.toMatrix'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (f g : (m → R) →ₗ[R] m 
→ R), LinearM…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.ofLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
· 使用定理 `LinearMap.det_toLin'`：det_toLin' (f : Matrix ι ι R) : LinearMap.det (Mat
rix.toLin' f) = Matrix.det f
· 使用定理 `LinearMap.det_map`：∀ {K : Type u_5} {V : Type u_6} {W : Type u_7} [inst 
: Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : Ad
dCommGr…
-/
@[simp] theorem Matrix.det_map {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {F : Type*} [EquivLike F (Matrix m m K) (Matrix n n K)]
    [AlgEquivClass F K _ _] (f : F) (x : Matrix m m K) : (f x).det = x.det := by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.det_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'
/-
**Matrix.det_map'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {K : Type u_5} {m : Type u_6} {F : Type u_7} [inst : Field K] [inst_1 : 
Fintype m] [inst_2 : DecidableEq m]   [inst_3 : FunLike F (Matrix m m K) (Matrix
 m m K)] [AlgHomClass F K (Matrix m m K) (Matrix m m K)] (f : F)   (x : Matrix m
 m K), (f x).det = x.det
参数：Matrix m m K；Matrix m m K；Matrix m m K；Matrix m m K；f : F；x : Matrix m m K；f 
x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_map`：∀ {K : Type u_5} {m : Type u_6} {n : Type u_7} [inst : F
ield K] [inst_1 : Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq m] [in
st_4…
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgHom.bijective`：AlgHom.bijective {K S : Type*} [Field K] [Ring S] [IsS
impleRing S] [Algebra K S] [FiniteDimensional K S] (f : S ->ₐ[K] S) : Function.B
ijecti…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.coe_det_isEmpty`：coe_det_isEmpty [IsEmpty n] : (det : Matrix n n 
R -> R) = Function.const _ 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Matrix.det_map' {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
    [FunLike F (Matrix m m K) (Matrix m m K)] [AlgHomClass F K _ _] (f : F) (x : Matrix m m K) :
    (f x).det = x.det := by
  by_cases! Nonempty m
  · exact det_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp

/-- The determinants of a `LinearEquiv` and its inverse multiply to 1. -/
@[simp]
/-
**LinearEquiv.det_mul_det_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.det_mul_det_symm {A : Type*} [CommRing A] [Module A M] (f : M 
≃ₗ[A] M) : LinearMap.det (f : M ->ₗ[A] M) * LinearMap.det (f.symm : M ->ₗ[A] M) 
= 1
参数：f : M ≃ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The determinants of a `LinearEquiv` and its inverse multiply to 1.
-/
theorem LinearEquiv.det_mul_det_symm {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    LinearMap.det (f : M →ₗ[A] M) * LinearMap.det (f.symm : M →ₗ[A] M) = 1 := by
  simp [← LinearMap.det_comp]

/-- The determinants of a `LinearEquiv` and its inverse multiply to 1. -/
@[simp]
/-
**LinearEquiv.det_symm_mul_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.det_symm_mul_det {A : Type*} [CommRing A] [Module A M] (f : M 
≃ₗ[A] M) : LinearMap.det (f.symm : M ->ₗ[A] M) * LinearMap.det (f : M ->ₗ[A] M) 
= 1
参数：f : M ≃ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The determinants of a `LinearEquiv` and its inverse multiply to 1.
-/
theorem LinearEquiv.det_symm_mul_det {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    LinearMap.det (f.symm : M →ₗ[A] M) * LinearMap.det (f : M →ₗ[A] M) = 1 := by
  simp [← LinearMap.det_comp]

-- Cannot be stated using `LinearMap.det` because `f` is not an endomorphism.
/-
**LinearEquiv.isUnit_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isUnit_det (f : M ≃ₗ[R] M') (v : Basis ι R M) (v' : Basis ι R 
M') : IsUnit (LinearMap.toMatrix v v' f).det
参数：f : M ≃ₗ[R] M'；v : Basis ι R M；v' : Basis ι R M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isUnit_det_of_left_inverse`：isUnit_det_of_left_inverse (h : B * A
 = 1) : IsUnit A.det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `LinearMap.toMatrix_id_eq_basis_toMatrix`：LinearMap.toMatrix_id_eq_basis_
toMatrix [Fintype ι] [DecidableEq ι] [Finite ι'] : LinearMap.toMatrix b b' id = 
b'.toMatrix b
· 使用定理 `Module.Basis.toMatrix_self`：toMatrix_self [DecidableEq ι] : e.toMatrix e
 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
-/
theorem LinearEquiv.isUnit_det (f : M ≃ₗ[R] M') (v : Basis ι R M) (v' : Basis ι R M') :
    IsUnit (LinearMap.toMatrix v v' f).det := by
  apply isUnit_det_of_left_inverse
  simpa using (LinearMap.toMatrix_comp v v' v f.symm f).symm

/-- Specialization of `LinearEquiv.isUnit_det` -/
/-
**LinearEquiv.isUnit_det'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isUnit_det' {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A]
 M) : IsUnit (LinearMap.det (f : M ->ₗ[A] M))
参数：f : M ≃ₗ[A] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `LinearEquiv.det_mul_det_symm`：LinearEquiv.det_mul_det_symm {A : Type*} [
CommRing A] [Module A M] (f : M ≃ₗ[A] M) : LinearMap.det (f : M ->ₗ[A] M) * Line
arMap.det (f.symm …

--- 原说明 ---
Specialization of `LinearEquiv.isUnit_det`
-/
theorem LinearEquiv.isUnit_det' {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    IsUnit (LinearMap.det (f : M →ₗ[A] M)) :=
  .of_mul_eq_one _ f.det_mul_det_symm

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The determinant of `f.symm` is the inverse of that of `f` when `f` is a linear equiv. -/
/-
**LinearEquiv.det_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M
) : LinearMap.det (f.symm : M ->ₗ[𝕜] M) = (LinearMap.det (f : M ->ₗ[𝕜] M))⁻¹
参数：f : M ≃ₗ[𝕜] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `LinearEquiv.isUnit_det'`：LinearEquiv.isUnit_det' {A : Type*} [CommRing A
] [Module A M] (f : M ≃ₗ[A] M) : IsUnit (LinearMap.det (f : M ->ₗ[A] M))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The determinant of `f.symm` is the inverse of that of `f` when `f` is a linear e
quiv.
-/
theorem LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) :
    LinearMap.det (f.symm : M →ₗ[𝕜] M) = (LinearMap.det (f : M →ₗ[𝕜] M))⁻¹ := by
  simp [field, IsUnit.ne_zero f.isUnit_det']

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
/-
**LinearEquiv.ofIsUnitDet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.ofIsUnitDet {f : M ->ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι 
R M'} (h : IsUnit (LinearMap.toMatrix v v' f).det) : M ≃ₗ[R] M' where toFun
参数：h : IsUnit (LinearMap.toMatrix v v' f).det。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Builds a linear equivalence from a linear map whose determinant in some bases is
 a unit.
-/
def LinearEquiv.ofIsUnitDet {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) : M ≃ₗ[R] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv x :=
    calc toLin v' v (toMatrix v v' f)⁻¹ (f x)
      _ = toLin v v ((toMatrix v v' f)⁻¹ * toMatrix v v' f) x := by
        rw [toLin_mul v v' v, toLin_toMatrix, LinearMap.comp_apply]
      _ = x := by simp [h]
  right_inv x :=
    calc f (toLin v' v (toMatrix v v' f)⁻¹ x)
      _ = toLin v' v' (toMatrix v v' f * (toMatrix v v' f)⁻¹) x := by
        rw [toLin_mul v' v v', LinearMap.comp_apply, toLin_toMatrix v v']
      _ = x := by simp [h]

@[simp]
/-
**LinearEquiv.coe_ofIsUnitDet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.coe_ofIsUnitDet {f : M ->ₗ[R] M'} {v : Basis ι R M} {v' : Basi
s ι R M'} (h : IsUnit (LinearMap.toMatrix v v' f).det) : (LinearEquiv.ofIsUnitDe
t h : M ->ₗ[R] M') = f
参数：h : IsUnit (LinearMap.toMatrix v v' f).det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem LinearEquiv.coe_ofIsUnitDet {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) :
    (LinearEquiv.ofIsUnitDet h : M →ₗ[R] M') = f := by
  ext x
  rfl

/-- Builds a linear equivalence from an endomorphism whose determinant is a unit. -/
/-
**LinearMap.equivOfIsUnitDet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.equivOfIsUnitDet [Module.Free R M] [Module.Finite R M] {f : M ->
ₗ[R] M} (h : IsUnit f.det) : M ≃ₗ[R] M
参数：h : IsUnit f.det。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Builds a linear equivalence from an endomorphism whose determinant is a unit.
-/
noncomputable def LinearMap.equivOfIsUnitDet
    [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : IsUnit f.det) :
    M ≃ₗ[R] M := by
  by_cases hR : Nontrivial R
  · let ⟨ι, b⟩ := (Module.Free.exists_basis R M).some
    have : Finite ι := Module.Finite.finite_basis b
    have : Fintype ι := Fintype.ofFinite ι
    have : DecidableEq ι := Classical.typeDecidableEq ι
    exact LinearEquiv.ofIsUnitDet (v := b) (v' := b) (f := f) (by rwa [det_toMatrix b])
  · exact 1

@[simp]
/-
**LinearMap.equivOfIsUnitDet_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.equivOfIsUnitDet_apply [Module.Free R M] [Module.Finite R M] {f 
: M ->ₗ[R] M} (h : IsUnit f.det) (x : M) : (LinearMap.equivOfIsUnitDet h) x = f 
x
参数：h : IsUnit f.det；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LinearEquiv.ofIsUnitDet_apply`：∀ {R : Type u_1} [inst : CommRing R] {M :
 Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {M' : Type u
_3} [inst_3 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.equivOfIsUnitDet_apply
    [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : IsUnit f.det) (x : M) :
    (LinearMap.equivOfIsUnitDet h) x = f x := by
  nontriviality M
  simp [equivOfIsUnitDet, dif_pos (Module.nontrivial R M)]

@[simp]
/-
**LinearMap.coe_equivOfIsUnitDet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.coe_equivOfIsUnitDet [Module.Free R M] [Module.Finite R M] {f : 
M ->ₗ[R] M} (h : IsUnit f.det) : (LinearMap.equivOfIsUnitDet h : M ->ₗ[R] M) = f
参数：h : IsUnit f.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.equivOfIsUnitDet_apply`：LinearMap.equivOfIsUnitDet_apply [Modu
le.Free R M] [Module.Finite R M] {f : M ->ₗ[R] M} (h : IsUnit f.det) (x : M) : (
LinearMap.equivOfIsUni…
-/
theorem LinearMap.coe_equivOfIsUnitDet
    [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : IsUnit f.det) :
    (LinearMap.equivOfIsUnitDet h : M →ₗ[R] M) = f := by
  ext
  apply LinearMap.equivOfIsUnitDet_apply

/-- Builds a linear equivalence from a linear map on a finite-dimensional vector space whose
determinant is nonzero. -/
/-
**LinearMap.equivOfDetNeZero** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearMap.equivOfDetNeZero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup
 M] [Module 𝕜 M] [FiniteDimensional 𝕜 M] (f : M ->ₗ[𝕜] M) (hf : LinearMap.det f 
!= 0) : M ≃ₗ[𝕜] M
参数：f : M ->ₗ[𝕜] M；hf : LinearMap.det f != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Builds a linear equivalence from a linear map on a finite-dimensional vector spa
ce whose
determinant is nonzero.
-/
abbrev LinearMap.equivOfDetNeZero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (f : M →ₗ[𝕜] M) (hf : LinearMap.det f ≠ 0) : M ≃ₗ[𝕜] M :=
  have : IsUnit (LinearMap.toMatrix (Module.finBasis 𝕜 M)
      (Module.finBasis 𝕜 M) f).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 hf
  LinearEquiv.ofIsUnitDet this
/-
**LinearMap.associated_det_of_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.associated_det_of_eq_comp (e : M ≃ₗ[R] M) (f f' : M ->ₗ[R] M) (h
 : forall x, f x = f' (e x)) : Associated (LinearMap.det f) (LinearMap.det f')
参数：e : M ≃ₗ[R] M；f f' : M ->ₗ[R] M；h : forall x, f x = f' (e x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.det_comp`：det_comp (f g : M ->ₗ[A] M) : LinearMap.det (f.comp 
g) = LinearMap.det f * LinearMap.det g
· 使用定理 `Associated.mul_left`：Associated.mul_left [Monoid M] (a : M) {b c : M} (h
 : b ~ᵤ c) : a * b ~ᵤ a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
· 使用定理 `LinearEquiv.isUnit_det'`：LinearEquiv.isUnit_det' {A : Type*} [CommRing A
] [Module A M] (f : M ≃ₗ[A] M) : IsUnit (LinearMap.det (f : M ->ₗ[A] M))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem LinearMap.associated_det_of_eq_comp (e : M ≃ₗ[R] M) (f f' : M →ₗ[R] M)
    (h : ∀ x, f x = f' (e x)) : Associated (LinearMap.det f) (LinearMap.det f') := by
  suffices Associated (LinearMap.det (f' ∘ₗ ↑e)) (LinearMap.det f') by
    convert! this using 2
    ext x
    exact h x
  rw [← mul_one (LinearMap.det f'), LinearMap.det_comp]
  exact Associated.mul_left _ (associated_one_iff_isUnit.mpr e.isUnit_det')
/-
**LinearMap.associated_det_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.associated_det_comp_equiv {N : Type*} [AddCommGroup N] [Module R
 N] (f : N ->ₗ[R] M) (e e' : M ≃ₗ[R] N) : Associated (LinearMap.det (f ∘ₗ ↑e)) (
LinearMap.det (f ∘ₗ ↑e'))
参数：f : N ->ₗ[R] M；e e' : M ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.associated_det_of_eq_comp`：LinearMap.associated_det_of_eq_comp
 (e : M ≃ₗ[R] M) (f f' : M ->ₗ[R] M) (h : forall x, f x = f' (e x)) : Associated
 (LinearMap.det f) (Linea…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.associated_det_comp_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (e e' : M ≃ₗ[R] N) :
    Associated (LinearMap.det (f ∘ₗ ↑e)) (LinearMap.det (f ∘ₗ ↑e')) := by
  refine LinearMap.associated_det_of_eq_comp (e.trans e'.symm) _ _ ?_
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

namespace Module.Basis

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
nonrec def det : M [⋀^ι]→ₗ[R] R where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v ↦ det (e.toMatrix v))
      (fun v i x y ↦ by
        simp only [e.toMatrix_update, map_add, Finsupp.coe_add, det_updateCol_add])
      (fun u i c x ↦ by
        simp only [e.toMatrix_update, smul_eq_mul, map_smul]
        apply det_updateCol_smul)
  map_eq_zero_of_eq' := by
    intro v i j h hij
    dsimp
    rw [← Function.update_eq_self i v, h, ← det_transpose, e.toMatrix_update, ← updateRow_transpose,
      ← e.toMatrix_transpose_apply]
    apply det_zero_of_row_eq hij
    rw [updateRow_ne hij.symm, updateRow_self]

/-
**Module.Basis.det_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_apply (v : ι -> M) : e.det v = Matrix.det (e.toMatrix v)
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem det_apply (v : ι → M) : e.det v = Matrix.det (e.toMatrix v) :=
  rfl
/-
**Module.Basis.det_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_self : e.det e = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Module.Basis.toMatrix_self`：toMatrix_self [DecidableEq ι] : e.toMatrix e
 = 1
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_self : e.det e = 1 := by simp [e.det_apply]

@[simp]
/-
**Module.Basis.det_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_isEmpty [IsEmpty ι] : e.det = AlternatingMap.constOfIsEmpty R M ι 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
-/
theorem det_isEmpty [IsEmpty ι] : e.det = AlternatingMap.constOfIsEmpty R M ι 1 := by
  ext v
  exact Matrix.det_isEmpty

/-- `Basis.det` is not the zero map. -/
/-
**Module.Basis.det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_ne_zero [Nontrivial R] : e.det != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_self`：det_self : e.det e = 1

--- 原说明 ---
`Basis.det` is not the zero map.
-/
theorem det_ne_zero [Nontrivial R] : e.det ≠ 0 := fun h => by simpa [h] using e.det_self
/-
**Module.Basis.smul_det** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：smul_det {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M] (g : G
) (v : ι -> M) : (g • e).det v = e.det (g⁻¹ • v)
参数：g : G；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_det {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    (g : G) (v : ι → M) :
    (g • e).det v = e.det (g⁻¹ • v) := by
  simp_rw [det_apply, toMatrix_smul_left]
/-
**Module.Basis.is_basis_iff_det** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：is_basis_iff_det {v : ι -> M} : LinearIndependent R v ∧ span R (Set.range 
v) = ⊤ ↔ IsUnit (e.det v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_id_eq_basis_toMatrix`：LinearMap.toMatrix_id_eq_basis_
toMatrix [Fintype ι] [DecidableEq ι] [Finite ι'] : LinearMap.toMatrix b b' id = 
b'.toMatrix b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.isUnit_det`：LinearEquiv.isUnit_det (f : M ≃ₗ[R] M') (v : Bas
is ι R M) (v' : Basis ι R M') : IsUnit (LinearMap.toMatrix v v' f).det
· 使用定理 `Module.Basis.toMatrix_eq_toMatrix_constr`：toMatrix_eq_toMatrix_constr [F
intype ι] [DecidableEq ι] (v : ι -> M) : e.toMatrix v = LinearMap.toMatrix e e (
e.constr Nat v)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.map_apply`：map_apply (i) : b.map f i = f (b i)
· 使用定理 `LinearEquiv.ofIsUnitDet_apply`：∀ {R : Type u_1} [inst : CommRing R] {M :
 Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {M' : Type u
_3} [inst_3 : AddCo…
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
-/
theorem is_basis_iff_det {v : ι → M} :
    LinearIndependent R v ∧ span R (Set.range v) = ⊤ ↔ IsUnit (e.det v) := by
  constructor
  · rintro ⟨hli, hspan⟩
    set v' := Basis.mk hli hspan.ge
    rw [e.det_apply]
    convert! LinearEquiv.isUnit_det (LinearEquiv.refl R M) v' e using 2
    ext i j
    simp [v']
  · intro h
    rw [Basis.det_apply, Basis.toMatrix_eq_toMatrix_constr] at h
    set v' := Basis.map e (LinearEquiv.ofIsUnitDet h) with v'_def
    have : ⇑v' = v := by
      ext i
      rw [v'_def, Basis.map_apply, LinearEquiv.ofIsUnitDet_apply, e.constr_basis]
    rw [← this]
    exact ⟨v'.linearIndependent, v'.span_eq⟩
/-
**Module.Basis.isUnit_det** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：isUnit_det (e' : Basis ι R M) : IsUnit (e.det e')
参数：e' : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.is_basis_iff_det`：is_basis_iff_det {v : ι -> M} : LinearInd
ependent R v ∧ span R (Set.range v) = ⊤ ↔ IsUnit (e.det v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
-/
theorem isUnit_det (e' : Basis ι R M) : IsUnit (e.det e') :=
  (is_basis_iff_det e).mp ⟨e'.linearIndependent, e'.span_eq⟩

end Module.Basis

/-- Any alternating map to `R` where `ι` has the cardinality of a basis equals the determinant
map with respect to that basis, multiplied by the value of that alternating map on that basis. -/
/-
**AlternatingMap.eq_smul_basis_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlternatingMap.eq_smul_basis_det (f : M [⋀^ι]->ₗ[R] R) : f = f e • e.det
参数：f : M [⋀^ι]->ₗ[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_alternating`：Module.Basis.ext_alternating {f g : N₁ [⋀^
ι]->ₗ[R'] N₂} (e : Basis ι₁ R' N₁) (h : forall v : ι -> ι₁, Function.Injective v
 -> (f fun i => e …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.injective_iff_bijective`：injective_iff_bijective {f : α -> α} : I
njective f ↔ Bijective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.map_perm`：map_perm [DecidableEq ι] [Fintype ι] (v : ι -> 
M) (σ : Equiv.Perm ι) : g (v ∘ σ) = Equiv.Perm.sign σ • g v
· 使用定理 `Module.Basis.det_self`：det_self : e.det e = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any alternating map to `R` where `ι` has the cardinality of a basis equals the d
eterminant
map with respect to that basis, multiplied by the value of that alternating map 
on that basis.
-/
theorem AlternatingMap.eq_smul_basis_det (f : M [⋀^ι]→ₗ[R] R) : f = f e • e.det := by
  refine Basis.ext_alternating e fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self]

@[simp]
/-
**AlternatingMap.map_basis_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlternatingMap.map_basis_eq_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R
 M) (f : M [⋀^ι]->ₗ[R] R) : f e = 0 ↔ f = 0
参数：e : Basis ι R M；f : M [⋀^ι]->ₗ[R] R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `AlternatingMap.zero_apply`：zero_apply : (0 : M [⋀^ι]->ₗ[R] N) v = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem AlternatingMap.map_basis_eq_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] R) : f e = 0 ↔ f = 0 :=
  ⟨fun h => by
    cases nonempty_fintype ι
    let := Classical.decEq ι
    simpa [h] using f.eq_smul_basis_det e,
   fun h => h.symm ▸ AlternatingMap.zero_apply _⟩
/-
**AlternatingMap.map_basis_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlternatingMap.map_basis_ne_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R
 M) (f : M [⋀^ι]->ₗ[R] R) : f e != 0 ↔ f != 0
参数：e : Basis ι R M；f : M [⋀^ι]->ₗ[R] R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AlternatingMap.map_basis_eq_zero_iff`：AlternatingMap.map_basis_eq_zero_i
ff {ι : Type*} [Finite ι] (e : Basis ι R M) (f : M [⋀^ι]->ₗ[R] R) : f e = 0 ↔ f 
= 0
-/
theorem AlternatingMap.map_basis_ne_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] R) : f e ≠ 0 ↔ f ≠ 0 :=
  not_congr <| f.map_basis_eq_zero_iff e

variable {A : Type*} [CommRing A] [Module A M]

namespace Module.Basis

@[simp]
/-
**Module.Basis.det_comp** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_comp (e : Basis ι A M) (f : M ->ₗ[A] M) (v : ι -> M) : e.det (f ∘ v) =
 (LinearMap.det f) * e.det v
参数：e : Basis ι A M；f : M ->ₗ[A] M；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Module.Basis.toMatrix_eq_toMatrix_constr`：toMatrix_eq_toMatrix_constr [F
intype ι] [DecidableEq ι] (v : ι -> M) : e.toMatrix v = LinearMap.toMatrix e e (
e.constr Nat v)
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `Module.Basis.constr_comp`：constr_comp (f : M' ->ₗ[R] M') (v : ι -> M') :
 constr (M'
-/
theorem det_comp (e : Basis ι A M) (f : M →ₗ[A] M) (v : ι → M) :
    e.det (f ∘ v) = (LinearMap.det f) * e.det v := by
  rw [det_apply, det_apply, ← f.det_toMatrix e, ← Matrix.det_mul,
    e.toMatrix_eq_toMatrix_constr (f ∘ v), e.toMatrix_eq_toMatrix_constr v, ← toMatrix_comp,
    e.constr_comp]

@[simp]
/-
**Module.Basis.det_comp_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_comp_basis [Module A M'] (b : Basis ι A M) (b' : Basis ι A M') (f : M 
->ₗ[A] M') : b'.det (f ∘ b) = LinearMap.det (f ∘ₗ (b'.equiv b (Equiv.refl ι) : M
' ->ₗ[A] M))
参数：b : Basis ι A M；b' : Basis ι A M'；f : M ->ₗ[A] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `LinearMap.toMatrix_basis_equiv`：LinearMap.toMatrix_basis_equiv [Fintype 
l] [DecidableEq l] (b : Basis l R M₁) (b' : Basis l R M₂) : LinearMap.toMatrix b
' b (b'.equiv b (Equ…
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Module.Basis.toMatrix_apply`：toMatrix_apply : e.toMatrix v i j = e.repr 
(v j) i
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem det_comp_basis [Module A M'] (b : Basis ι A M) (b' : Basis ι A M') (f : M →ₗ[A] M') :
    b'.det (f ∘ b) = LinearMap.det (f ∘ₗ (b'.equiv b (Equiv.refl ι) : M' →ₗ[A] M)) := by
  rw [det_apply, ← LinearMap.det_toMatrix b', LinearMap.toMatrix_comp _ b, Matrix.det_mul,
    LinearMap.toMatrix_basis_equiv, Matrix.det_one, mul_one]
  congr 1; ext i j
  rw [toMatrix_apply, LinearMap.toMatrix_apply, Function.comp_apply]

@[simp]
/-
**Module.Basis.det_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_basis (b : Basis ι A M) (b' : Basis ι A M) : LinearMap.det (b'.equiv b
 (Equiv.refl ι)).toLinearMap = b'.det b
参数：b : Basis ι A M；b' : Basis ι A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Module.Basis.det_comp_basis`：det_comp_basis [Module A M'] (b : Basis ι A
 M) (b' : Basis ι A M') (f : M ->ₗ[A] M') : b'.det (f ∘ b) = LinearMap.det (f ∘ₗ
 (b'.equiv b (Equ…
-/
theorem det_basis (b : Basis ι A M) (b' : Basis ι A M) :
    LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b :=
  (b.det_comp_basis b' (LinearMap.id)).symm
/-
**Module.Basis.det_mul_det** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_mul_det (b b' b'' : Basis ι A M) : b.det b' * b'.det b'' = b.det b''
参数：b b' b'' : Basis ι A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.det_comp`：det_comp (e : Basis ι A M) (f : M ->ₗ[A] M) (v : 
ι -> M) : e.det (f ∘ v) = (LinearMap.det f) * e.det v
· 使用定理 `Module.Basis.det_basis`：det_basis (b : Basis ι A M) (b' : Basis ι A M) :
 LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem det_mul_det (b b' b'' : Basis ι A M) :
    b.det b' * b'.det b'' = b.det b'' := by
  have : b'' = (b'.equiv b'' (Equiv.refl ι)).toLinearMap ∘ b' := by
    ext; simp
  conv_rhs =>
    rw [this, Basis.det_comp, det_basis, mul_comm]
/-
**Module.Basis.det_inv** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_inv (b : Basis ι A M) (b' : Basis ι A M) : (b.isUnit_det b').unit⁻¹ = 
b'.det b
参数：b : Basis ι A M；b' : Basis ι A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.isUnit_det`：isUnit_det (e' : Basis ι R M) : IsUnit (e.det e
')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 
↔ ↑u⁻¹ = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Module.Basis.det_basis`：det_basis (b : Basis ι A M) (b' : Basis ι A M) :
 LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b
· 使用定理 `LinearEquiv.det_mul_det_symm`：LinearEquiv.det_mul_det_symm {A : Type*} [
CommRing A] [Module A M] (f : M ≃ₗ[A] M) : LinearMap.det (f : M ->ₗ[A] M) * Line
arMap.det (f.symm …
-/
theorem det_inv (b : Basis ι A M) (b' : Basis ι A M) :
    (b.isUnit_det b').unit⁻¹ = b'.det b := by
  rw [← Units.mul_eq_one_iff_inv_eq, IsUnit.unit_spec, ← det_basis, ← det_basis]
  exact LinearEquiv.det_mul_det_symm _
/-
**Module.Basis.det_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (
v : ι' -> M) (e : ι ≃ ι') : (b.reindex e).det v = b.det (v ∘ e)
参数：b : Basis ι R M；v : ι' -> M；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Module.Basis.toMatrix_reindex'`：toMatrix_reindex' [DecidableEq ι] [Decid
ableEq ι'] (b : Basis ι R M) (v : ι' -> M) (e : ι ≃ ι') : (b.reindex e).toMatrix
 v = Matrix.reindexA…
· 使用定理 `Matrix.det_reindexAlgEquiv`：det_reindexAlgEquiv (B : Type*) [CommSemirin
g R] [CommRing B] [Algebra R B] [Fintype m] [DecidableEq m] [Fintype n] [Decidab
leEq n] (e : m ≃…
-/
theorem det_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M)
    (e : ι ≃ ι') : (b.reindex e).det v = b.det (v ∘ e) := by
  rw [det_apply, toMatrix_reindex', det_reindexAlgEquiv, det_apply]
/-
**Module.Basis.det_reindex'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_reindex' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) 
(e : ι ≃ ι') : (b.reindex e).det = b.det.domDomCongr e
参数：b : Basis ι R M；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Module.Basis.det_reindex`：det_reindex {ι' : Type*} [Fintype ι'] [Decidab
leEq ι'] (b : Basis ι R M) (v : ι' -> M) (e : ι ≃ ι') : (b.reindex e).det v = b.
det (v ∘ e)
-/
theorem det_reindex' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (e : ι ≃ ι') : (b.reindex e).det = b.det.domDomCongr e :=
  AlternatingMap.ext fun _ => det_reindex _ _ _
/-
**Module.Basis.det_reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_reindex_symm {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R
 M) (v : ι -> M) (e : ι' ≃ ι) : (b.reindex e.symm).det (v ∘ e) = b.det v
参数：b : Basis ι R M；v : ι -> M；e : ι' ≃ ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_reindex`：det_reindex {ι' : Type*} [Fintype ι'] [Decidab
leEq ι'] (b : Basis ι R M) (v : ι' -> M) (e : ι ≃ ι') : (b.reindex e).det v = b.
det (v ∘ e)
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
-/
theorem det_reindex_symm {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (v : ι → M) (e : ι' ≃ ι) : (b.reindex e.symm).det (v ∘ e) = b.det v := by
  rw [det_reindex, Function.comp_assoc, e.self_comp_symm, Function.comp_id]

@[simp]
/-
**Module.Basis.det_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι -> M') : (b.map f).det v
 = b.det (f.symm ∘ v)
参数：b : Basis ι R M；f : M ≃ₗ[R] M'；v : ι -> M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Module.Basis.toMatrix_map`：toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N
) (v : ι -> N) : (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v)
-/
theorem det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι → M') :
    (b.map f).det v = b.det (f.symm ∘ v) := by
  rw [det_apply, toMatrix_map, det_apply]
/-
**Module.Basis.det_map'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_map' (b : Basis ι R M) (f : M ≃ₗ[R] M') : (b.map f).det = b.det.compLi
nearMap f.symm
参数：b : Basis ι R M；f : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Module.Basis.det_map`：det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι 
-> M') : (b.map f).det v = b.det (f.symm ∘ v)
-/
theorem det_map' (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).det = b.det.compLinearMap f.symm :=
  AlternatingMap.ext <| b.det_map f

end Module.Basis

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Pi.basisFun_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.basisFun_det : (Pi.basisFun R ι).det = Matrix.detRowAlternating
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `Module.Basis.coePiBasisFun.toMatrix_eq_transpose`：∀ {ι : Type u_1} {R : 
Type u_5} [inst : CommSemiring R] [inst_1 : Finite ι],   (Pi.basisFun R ι).toMat
rix = Matrix.transpose
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det.eq_1`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] (M : Matrix n n R),   M.det = Matrix.de
tRowA…
-/
theorem Pi.basisFun_det : (Pi.basisFun R ι).det = Matrix.detRowAlternating := by
  ext M
  rw [Basis.det_apply, Basis.coePiBasisFun.toMatrix_eq_transpose, det_transpose, det]
/-
**Pi.basisFun_det_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.basisFun_det_apply (v : ι -> ι -> R) : (Pi.basisFun R ι).det v = (Matri
x.of v).det
参数：v : ι -> ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.basisFun_det`：Pi.basisFun_det : (Pi.basisFun R ι).det = Matrix.detRow
Alternating
-/
theorem Pi.basisFun_det_apply (v : ι → ι → R) :
    (Pi.basisFun R ι).det v = (Matrix.of v).det := by
  rw [Pi.basisFun_det]
  rfl

namespace Module.Basis

/-- If we fix a background basis `e`, then for any other basis `v`, we can characterise the
coordinates provided by `v` in terms of determinants relative to `e`. -/
/-
**Module.Basis.det_smul_mk_coord_eq_det_update** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Basis`。
形式化陈述：det_smul_mk_coord_eq_det_update {v : ι -> M} (hli : LinearIndependent R v)
 (hsp : ⊤ <= span R (range v)) (i : ι) : e.det v • (Basis.mk hli hsp).coord i = 
e.det.toMultilinearMap.toLinearMap v i
参数：hli : LinearIndependent R v；hsp : ⊤ <= span R (range v)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MultilinearMap.toLinearMap_apply`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι 
→ Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoi
d (M₁ i)] [inst_2 : Ad…
· 使用定理 `Module.Basis.mk_coord_apply_eq`：mk_coord_apply_eq (i : ι) : (Basis.mk hl
i hsp).coord i (v i) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Module.Basis.mk_coord_apply_ne`：mk_coord_apply_ne {i j : ι} (h : j != i)
 : (Basis.mk hli hsp).coord i (v j) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If we fix a background basis `e`, then for any other basis `v`, we can character
ise the
coordinates provided by `v` in terms of determinants relative to `e`.
-/
theorem det_smul_mk_coord_eq_det_update {v : ι → M} (hli : LinearIndependent R v)
    (hsp : ⊤ ≤ span R (range v)) (i : ι) :
    e.det v • (Basis.mk hli hsp).coord i = e.det.toMultilinearMap.toLinearMap v i := by
  apply (Basis.mk hli hsp).ext
  intro k
  rcases eq_or_ne k i with (rfl | hik) <;>
    simp only [smul_eq_mul, coe_mk, LinearMap.smul_apply,
      MultilinearMap.toLinearMap_apply]
  · rw [mk_coord_apply_eq, mul_one, update_eq_self]
    congr
  · rw [mk_coord_apply_ne hik, mul_zero, eq_comm]
    exact e.det.map_eq_zero_of_eq _ (by simp [hik]) hik

/-- If a basis is multiplied columnwise by scalars `w : ι → Rˣ`, then the determinant with respect
to this basis is multiplied by the product of the inverse of these scalars. -/
/-
**Module.Basis.det_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_unitsSMul (e : Basis ι R M) (w : ι -> Rˣ) : (e.unitsSMul w).det = (↑(∏
 i, w i)⁻¹ : R) • e.det
参数：e : Basis ι R M；w : ι -> Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.repr_unitsSMul`：repr_unitsSMul (e : Basis ι R₂ M) (w : ι ->
 R₂ˣ) (v : M) (i : ι) : (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Units.coe_prod`：Units.coe_prod [CommMonoid M] (f : α -> Mˣ) (s : Finset 
α) : (↑(∏ i in s, f i) : M) = ∏ i in s, (f i : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.det_mul_column`：det_mul_column (v : n -> R) (A : Matrix n n R) : 
det (of fun i j => v i * A i j) = (∏ i, v i) * det A

--- 原说明 ---
If a basis is multiplied columnwise by scalars `w : ι → Rˣ`, then the determinan
t with respect
to this basis is multiplied by the product of the inverse of these scalars.
-/
theorem det_unitsSMul (e : Basis ι R M) (w : ι → Rˣ) :
    (e.unitsSMul w).det = (↑(∏ i, w i)⁻¹ : R) • e.det := by
  ext f
  change
    (Matrix.det fun i j => (e.unitsSMul w).repr (f j) i) =
      (↑(∏ i, w i)⁻¹ : R) • Matrix.det fun i j => e.repr (f j) i
  simp only [e.repr_unitsSMul]
  convert! Matrix.det_mul_column (fun i => (↑(w i)⁻¹ : R)) fun i j => e.repr (f j) i
  simp [← Finset.prod_inv_distrib]

/-- The determinant of a basis constructed by `unitsSMul` is the product of the given units. -/
@[simp]
/-
**Module.Basis.det_unitsSMul_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_unitsSMul_self (w : ι -> Rˣ) : e.det (e.unitsSMul w) = ∏ i, (w i : R)
参数：w : ι -> Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Module.Basis.toMatrix_unitsSMul`：toMatrix_unitsSMul [DecidableEq ι] (e :
 Basis ι R₂ M₂) (w : ι -> R₂ˣ) : e.toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w)
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The determinant of a basis constructed by `unitsSMul` is the product of the give
n units.
-/
theorem det_unitsSMul_self (w : ι → Rˣ) : e.det (e.unitsSMul w) = ∏ i, (w i : R) := by
  simp [det_apply]

/-- The determinant of a basis constructed by `isUnitSMul` is the product of the given units. -/
@[simp]
/-
**Module.Basis.det_isUnitSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_isUnitSMul {w : ι -> R} (hw : forall i, IsUnit (w i)) : e.det (e.isUni
tSMul hw) = ∏ i, w i
参数：hw : forall i, IsUnit (w i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.det_unitsSMul_self`：det_unitsSMul_self (w : ι -> Rˣ) : e.de
t (e.unitsSMul w) = ∏ i, (w i : R)

--- 原说明 ---
The determinant of a basis constructed by `isUnitSMul` is the product of the giv
en units.
-/
theorem det_isUnitSMul {w : ι → R} (hw : ∀ i, IsUnit (w i)) :
    e.det (e.isUnitSMul hw) = ∏ i, w i :=
  e.det_unitsSMul_self _

end Module.Basis

section Dual

/-- The determinant of the transpose of an endomorphism coincides with its determinant. -/
/-
**_root_.LinearMap.det_dualMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.LinearMap.det_dualMap [Module.Free R M] [Module.Finite R M] (f : M 
->ₗ[R] M) : f.dualMap.det = f.det
参数：f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of the transpose of an endomorphism coincides with its determina
nt.
-/
theorem _root_.LinearMap.det_dualMap
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    f.dualMap.det = f.det := by
  set b := Module.Free.chooseBasis R M
  have : Fintype (Module.Free.ChooseBasisIndex R M) :=
    Module.Free.ChooseBasisIndex.fintype R M
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b.dualBasis]
  simp [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]

end Dual

section

variable {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [Module.Finite R V]
    (W : Submodule R V) [Module.Free R W] [Module.Finite R W] [Module.Free R (V ⧸ W)]

open Module.Basis in
/-
**LinearMap.det_eq_det_mul_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.det_eq_det_mul_det (e : V ->ₗ[R] V) (he : W <= W.comap e) : e.de
t = (e.restrict he).det * (W.mapQ W e he).det
参数：e : V ->ₗ[R] V；he : W <= W.comap e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.sumQuot_inl`：sumQuot_inl (i : m) : sumQuot bW bQ (Sum.inl i
) = bW i
· 使用定理 `Module.Basis.sumQuot_repr_inl_of_mem`：sumQuot_repr_inl_of_mem (v : V) (h
v : v in W) (i : m) : (sumQuot bW bQ).repr v (Sum.inl i) = bW.repr ⟨v, hv⟩ i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Module.Basis.sumQuot_repr_inr`：sumQuot_repr_inr (v : V) (j : n) : (sumQu
ot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.sumQuot_inr`：sumQuot_inr (j : n) : Submodule.Quotient.mk (s
umQuot bW bQ (Sum.inr j)) = bQ j
· 使用定理 `Submodule.mapQ_apply`：mapQ_apply (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M) : mapQ
 p q f h (Quotient.mk x) = Quotient.mk (f x)
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_fromBlocks_zero₂₁`：det_fromBlocks_zero₂₁ (A : Matrix m m R) (
B : Matrix m n R) (D : Matrix n n R) : (Matrix.fromBlocks A B 0 D).det = A.det *
 D.det
-/
theorem LinearMap.det_eq_det_mul_det (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.det = (e.restrict he).det * (W.mapQ W e he).det := by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.det_toMatrix b, this, ← LinearMap.det_toMatrix bW,
      ← LinearMap.det_toMatrix bQ, Matrix.det_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

end

