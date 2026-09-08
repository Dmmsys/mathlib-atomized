/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with degree strictly less than `n`

This file contains the properties of the submodule of polynomials of degree less than `n` in a
(semi)ring `R`, denoted `R[X]_n`.

## Main definitions/lemmas

* `degreeLT.basis R n`: a basis for `R[X]_n` the submodule of polynomials with degree `< n`,
  given by the monomials `X^i` for `i < n`.

* `degreeLT.basisProd R m n`: a basis for `R[X]_m × R[X]_n`, which is the sum of two instances of
  the basis given above.

* `degreeLT.addLinearEquiv R m n`: an isomorphism between `R[X]_(m + n)` and `R[X]_m × R[X]_n`,
  given by the fact that the bases are both indexed by `Fin (m + n)`. This is used for the Sylvester
  matrix, which is the matrix representing the Sylvester map between these two spaces, in a future
  file.

* `taylorLinear r n`: The linear automorphism induced by `taylor r` on `R[X]_n` which sends `X` to
  `X + r` and preserves degrees.

-/

@[expose] public section

open Module

namespace Polynomial

@[inherit_doc] scoped notation:9000 R "[X]_" n:arg => Polynomial.degreeLT R n

namespace degreeLT

variable {R : Type*} [Semiring R] {m n : ℕ} (i : Fin n) (P : R[X]_n)

variable (R) in
/-- Basis for `R[X]_n` given by `X^i` with `i < n`. -/
/-
**Polynomial.degreeLT.basis** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.degreeLT`。
形式化陈述：basis (n : Nat) : Basis (Fin n) R R[X]_n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basis for `R[X]_n` given by `X^i` with `i < n`.
-/
noncomputable def basis (n : ℕ) : Basis (Fin n) R R[X]_n :=
  .ofEquivFun (degreeLTEquiv R n)
/-
**Polynomial.degreeLT.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.degreeLT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite R R[X]_n := .of_basis <| basis ..
/-
**Polynomial.degreeLT.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.degreeLT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R R[X]_n := .of_basis <| basis ..
/-
**Polynomial.degreeLT.basis_repr** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.degreeLT`
。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {n : ℕ} (i : Fin n) (P : ↥(Polynomial
.degreeLT R n)),   ((Polynomial.degreeLT.basis R n).repr P) i = (↑P).coeff ↑i
参数：i : Fin n；P : ↥(Polynomial.degreeLT R n)；(Polynomial.degreeLT.basis R n).repr
 P；↑P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma basis_repr : (basis R n).repr P i = (P : R[X]).coeff i :=
  rfl
/-
**Polynomial.degreeLT.basis_val** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.degreeLT`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {n : ℕ} (i : Fin n), ↑((Polynomial.de
greeLT.basis R n) i) = Polynomial.X ^ ↑i
参数：i : Fin n；(Polynomial.degreeLT.basis R n) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_X_pow_le`：degree_X_pow_le (n : Nat) : degree (X ^ n : 
R[X]) <= n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma basis_val : (basis R n i : R[X]) = X ^ (i : ℕ) := by
  change _ = ((⟨X ^ (i : ℕ), mem_degreeLT.2 <| (degree_X_pow_le i).trans_lt <|
      Nat.cast_lt.2 i.is_lt⟩ : R[X]_n) : R[X])
  refine congr_arg _ (Basis.apply_eq_iff.2 <| Finsupp.ext fun j ↦ ?_)
  simp only [basis_repr, coeff_X_pow, eq_comm, Finsupp.single_apply, Fin.ext_iff]

variable (R m n) in
/-- Basis for `R[X]_m × R[X]_n`. -/
/-
**Polynomial.degreeLT.basisProd** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.degreeLT`。
形式化陈述：basisProd : Basis (Fin (m + n)) R (R[X]_m × R[X]_n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basis for `R[X]_m × R[X]_n`.
-/
noncomputable def basisProd : Basis (Fin (m + n)) R (R[X]_m × R[X]_n) :=
  ((basis R m).prod (basis R n)).reindex finSumFinEquiv
/-
**Polynomial.degreeLT.basisProd_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.de
greeLT`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (m n : ℕ) (i : Fin m),   (Polynomial.
degreeLT.basisProd R m n) (Fin.castAdd n i) = ((Polynomial.degreeLT.basis R m) i
, 0)
参数：m n : ℕ；i : Fin m；Polynomial.degreeLT.basisProd R m n；Fin.castAdd n i；(Polyno
mial.degreeLT.basis R m) i, 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degreeLT.basisProd.eq_1`：∀ (R : Type u_1) [inst : Semiring R]
 (m n : ℕ),   Polynomial.degreeLT.basisProd R m n =     ((Polynomial.degreeLT.ba
sis R m).prod (Polynomia…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
· 使用定理 `finSumFinEquiv_symm_apply_castAdd`：finSumFinEquiv_symm_apply_castAdd (x 
: Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `Sum.elim_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α → γ)
 (g : β → γ) (x : α), Sum.elim f g (Sum.inl x) = f x
· 使用定理 `LinearMap.coe_inl`：coe_inl : (inl R M M₂ : M -> M × M₂) = fun x => (x, 0
)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
@[simp] lemma basisProd_castAdd (m n : ℕ) (i : Fin m) :
    basisProd R m n (i.castAdd n) = (basis R m i, 0) := by
  rw [basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Basis.prod_apply,
    Sum.elim_inl, LinearMap.coe_inl, Function.comp_apply]
/-
**Polynomial.degreeLT.basisProd_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.deg
reeLT`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (m n : ℕ) (i : Fin n),   (Polynomial.
degreeLT.basisProd R m n) (Fin.natAdd m i) = (0, (Polynomial.degreeLT.basis R n)
 i)
参数：m n : ℕ；i : Fin n；Polynomial.degreeLT.basisProd R m n；Fin.natAdd m i；0, (Poly
nomial.degreeLT.basis R n) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degreeLT.basisProd.eq_1`：∀ (R : Type u_1) [inst : Semiring R]
 (m n : ℕ),   Polynomial.degreeLT.basisProd R m n =     ((Polynomial.degreeLT.ba
sis R m).prod (Polynomia…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
· 使用定理 `finSumFinEquiv_symm_apply_natAdd`：finSumFinEquiv_symm_apply_natAdd (x : 
Fin n) : finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `Sum.elim_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α → γ)
 (g : β → γ) (x : β), Sum.elim f g (Sum.inr x) = g x
· 使用定理 `LinearMap.coe_inr`：coe_inr : (inr R M M₂ : M₂ -> M × M₂) = Prod.mk 0
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
@[simp] lemma basisProd_natAdd (m n : ℕ) (i : Fin n) :
    basisProd R m n (i.natAdd m) = (0, basis R n i) := by
  rw [basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd, Basis.prod_apply,
    Sum.elim_inr, LinearMap.coe_inr, Function.comp_apply]

variable (R m n) in
/-- An isomorphism between `R[X]_(m + n)` and `R[X]_m × R[X]_n` given by the fact that the bases are
both indexed by `Fin (m + n)`. -/
/-
**Polynomial.degreeLT.addLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.degre
eLT`。
形式化陈述：addLinearEquiv : R[X]_(m + n) ≃ₗ[R] R[X]_m × R[X]_n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
An isomorphism between `R[X]_(m + n)` and `R[X]_m × R[X]_n` given by the fact th
at the bases are
both indexed by `Fin (m + n)`.
-/
noncomputable def addLinearEquiv :
    R[X]_(m + n) ≃ₗ[R] R[X]_m × R[X]_n :=
  Basis.equiv (basis ..) (basisProd ..) (Equiv.refl _)
/-
**Polynomial.degreeLT.addLinearEquiv_castAdd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al.degreeLT`。
形式化陈述：addLinearEquiv_castAdd (i : Fin m) : addLinearEquiv R m n (basis R (m + n)
 (i.castAdd n)) = (basis R m i, 0)
参数：i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degreeLT.addLinearEquiv.eq_1`：∀ (R : Type u_1) [inst : Semiri
ng R] (m n : ℕ),   Polynomial.degreeLT.addLinearEquiv R m n =     (Polynomial.de
greeLT.basis R (m + n)).equiv…
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `Equiv.refl_apply`：∀ {α : Sort u} (x : α), (Equiv.refl α) x = x
· 使用定理 `Polynomial.degreeLT.basisProd_castAdd`：∀ {R : Type u_1} [inst : Semiring
 R] (m n : ℕ) (i : Fin m),   (Polynomial.degreeLT.basisProd R m n) (Fin.castAdd 
n i) = ((Polynomial.degreeL…
-/
lemma addLinearEquiv_castAdd (i : Fin m) :
    addLinearEquiv R m n (basis R (m + n) (i.castAdd n)) = (basis R m i, 0) := by
  rw [addLinearEquiv, Basis.equiv_apply, Equiv.refl_apply, basisProd_castAdd]
/-
**Polynomial.degreeLT.addLinearEquiv_natAdd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l.degreeLT`。
形式化陈述：addLinearEquiv_natAdd (i : Fin n) : addLinearEquiv R m n (basis R (m + n) 
(i.natAdd m)) = (0, basis R n i)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degreeLT.addLinearEquiv.eq_1`：∀ (R : Type u_1) [inst : Semiri
ng R] (m n : ℕ),   Polynomial.degreeLT.addLinearEquiv R m n =     (Polynomial.de
greeLT.basis R (m + n)).equiv…
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `Equiv.refl_apply`：∀ {α : Sort u} (x : α), (Equiv.refl α) x = x
· 使用定理 `Polynomial.degreeLT.basisProd_natAdd`：∀ {R : Type u_1} [inst : Semiring 
R] (m n : ℕ) (i : Fin n),   (Polynomial.degreeLT.basisProd R m n) (Fin.natAdd m 
i) = (0, (Polynomial.degre…
-/
lemma addLinearEquiv_natAdd (i : Fin n) :
    addLinearEquiv R m n (basis R (m + n) (i.natAdd m)) = (0, basis R n i) := by
  rw [addLinearEquiv, Basis.equiv_apply, Equiv.refl_apply, basisProd_natAdd]
/-
**Polynomial.degreeLT.addLinearEquiv_symm_apply_inl_basis** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial.degreeLT`。
形式化陈述：addLinearEquiv_symm_apply_inl_basis (i : Fin m) : (addLinearEquiv R m n).s
ymm (LinearMap.inl R _ _ (basis R m i)) = basis R (m + n) (i.castAdd n)
参数：i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_castAdd`：addLinearEquiv_castAdd (i : 
Fin m) : addLinearEquiv R m n (basis R (m + n) (i.castAdd n)) = (basis R m i, 0)
-/
lemma addLinearEquiv_symm_apply_inl_basis (i : Fin m) :
    (addLinearEquiv R m n).symm (LinearMap.inl R _ _ (basis R m i)) =
      basis R (m + n) (i.castAdd n) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_castAdd i).symm
/-
**Polynomial.degreeLT.addLinearEquiv_symm_apply_inr_basis** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial.degreeLT`。
形式化陈述：addLinearEquiv_symm_apply_inr_basis (j : Fin n) : (addLinearEquiv R m n).s
ymm (LinearMap.inr R _ _ (basis R n j)) = basis R (m + n) (j.natAdd m)
参数：j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_natAdd`：addLinearEquiv_natAdd (i : Fi
n n) : addLinearEquiv R m n (basis R (m + n) (i.natAdd m)) = (0, basis R n i)
-/
lemma addLinearEquiv_symm_apply_inr_basis (j : Fin n) :
    (addLinearEquiv R m n).symm (LinearMap.inr R _ _ (basis R n j)) =
      basis R (m + n) (j.natAdd m) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_natAdd j).symm
/-
**Polynomial.degreeLT.addLinearEquiv_symm_apply_inl** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial.degreeLT`。
形式化陈述：addLinearEquiv_symm_apply_inl (P : R[X]_m) : ((addLinearEquiv R m n).symm 
(LinearMap.inl R _ _ P) : R[X]) = (P : R[X])
参数：P : R[X]_m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_symm_apply_inl_basis`：addLinearEquiv_
symm_apply_inl_basis (i : Fin m) : (addLinearEquiv R m n).symm (LinearMap.inl R 
_ _ (basis R m i)) = basis R (m + n) (i.castA…
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `Polynomial.degreeLT.basis_val`：∀ {R : Type u_1} [inst : Semiring R] {n :
 ℕ} (i : Fin n), ↑((Polynomial.degreeLT.basis R n) i) = Polynomial.X ^ ↑i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma addLinearEquiv_symm_apply_inl (P : R[X]_m) :
    ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ P) : R[X]) = (P : R[X]) := by
  rw [← (basis ..).sum_repr P]
  simp [-LinearMap.coe_inl, addLinearEquiv_symm_apply_inl_basis]
/-
**Polynomial.degreeLT.addLinearEquiv_symm_apply_inr** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial.degreeLT`。
形式化陈述：addLinearEquiv_symm_apply_inr (Q : R[X]_n) : ((addLinearEquiv R m n).symm 
(LinearMap.inr R _ _ Q) : R[X]) = (Q : R[X]) * X ^ (m : Nat)
参数：Q : R[X]_n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_symm_apply_inr_basis`：addLinearEquiv_
symm_apply_inr_basis (j : Fin n) : (addLinearEquiv R m n).symm (LinearMap.inr R 
_ _ (basis R n j)) = basis R (m + n) (j.natAd…
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `Polynomial.degreeLT.basis_val`：∀ {R : Type u_1} [inst : Semiring R] {n :
 ℕ} (i : Fin n), ↑((Polynomial.degreeLT.basis R n) i) = Polynomial.X ^ ↑i
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma addLinearEquiv_symm_apply_inr (Q : R[X]_n) :
    ((addLinearEquiv R m n).symm (LinearMap.inr R _ _ Q) : R[X]) = (Q : R[X]) * X ^ (m : ℕ) := by
  rw [← (basis ..).sum_repr Q]
  simp [-LinearMap.coe_inr, Finset.sum_mul, addLinearEquiv_symm_apply_inr_basis,
    smul_eq_C_mul, mul_assoc, ← pow_add, add_comm]
/-
**Polynomial.degreeLT.addLinearEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omial.degreeLT`。
形式化陈述：addLinearEquiv_symm_apply (PQ) : ((addLinearEquiv R m n).symm PQ : R[X]) =
 (PQ.1 : R[X]) + (PQ.2 : R[X]) * X ^ (m : Nat)
参数：PQ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.inl_apply`：inl_apply (x : M) : inl R M M₂ x = (x, 0)
· 使用定理 `LinearMap.inr_apply`：inr_apply (x : M₂) : inr R M M₂ x = (0, x)
· 使用定理 `Prod.add_def`：∀ {M : Type u_8} {N : Type u_9} [inst : Add M] [inst_1 : A
dd N] (p q : M × N), p + q = (p.1 + q.1, p.2 + q.2)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Submodule.coe_add`：coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_symm_apply_inl`：addLinearEquiv_symm_a
pply_inl (P : R[X]_m) : ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ P) : R
[X]) = (P : R[X])
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_symm_apply_inr`：addLinearEquiv_symm_a
pply_inr (Q : R[X]_n) : ((addLinearEquiv R m n).symm (LinearMap.inr R _ _ Q) : R
[X]) = (Q : R[X]) * X ^ (m : Nat)
-/
lemma addLinearEquiv_symm_apply (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + (PQ.2 : R[X]) * X ^ (m : ℕ) := calc
  _ = ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ PQ.1 + LinearMap.inr R _ _ PQ.2) :
      R[X]) := by
    rw [LinearMap.inl_apply, LinearMap.inr_apply, Prod.add_def, add_zero, zero_add]
  _ = _ := by
    rw [map_add, Submodule.coe_add, addLinearEquiv_symm_apply_inl, addLinearEquiv_symm_apply_inr]
/-
**Polynomial.degreeLT.addLinearEquiv_symm_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial.degreeLT`。
形式化陈述：addLinearEquiv_symm_apply' (PQ) : ((addLinearEquiv R m n).symm PQ : R[X]) 
= (PQ.1 : R[X]) + X ^ (m : Nat) * (PQ.2 : R[X])
参数：PQ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_symm_apply`：addLinearEquiv_symm_apply
 (PQ) : ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + (PQ.2 : R[X]) 
* X ^ (m : Nat)
-/
lemma addLinearEquiv_symm_apply' (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + X ^ (m : ℕ) * (PQ.2 : R[X]) := by
  rw [X_pow_mul, addLinearEquiv_symm_apply]
/-
**Polynomial.degreeLT.addLinearEquiv_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l.degreeLT`。
形式化陈述：addLinearEquiv_apply' {R : Type*} [Ring R] (f) : ((addLinearEquiv R m n f)
.1 : R[X]) = f %ₘ (X ^ m) ∧ ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m)
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_symm_apply'`：addLinearEquiv_symm_appl
y' (PQ) : ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + X ^ (m : Nat
) * (PQ.2 : R[X])
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma addLinearEquiv_apply' {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) ∧
      ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m) := by
  rw [and_comm, eq_comm, eq_comm (b := _ %ₘ _)]
  nontriviality R; refine div_modByMonic_unique _ _ (monic_X_pow _) ⟨?_, ?_⟩
  · rw [← addLinearEquiv_symm_apply', LinearEquiv.symm_apply_apply]
  · rw [degree_X_pow, ← mem_degreeLT]; exact Subtype.prop _
/-
**Polynomial.degreeLT.addLinearEquiv_apply_fst** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial.degreeLT`。
形式化陈述：addLinearEquiv_apply_fst {R : Type*} [Ring R] (f) : ((addLinearEquiv R m n
 f).1 : R[X]) = f %ₘ (X ^ m)
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_apply'`：addLinearEquiv_apply' {R : Ty
pe*} [Ring R] (f) : ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) ∧ ((addLi
nearEquiv R m n f).2 : R[X]) = …
-/
lemma addLinearEquiv_apply_fst {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) :=
  (addLinearEquiv_apply' f).1
/-
**Polynomial.degreeLT.addLinearEquiv_apply_snd** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial.degreeLT`。
形式化陈述：addLinearEquiv_apply_snd {R : Type*} [Ring R] (f) : ((addLinearEquiv R m n
 f).2 : R[X]) = f /ₘ (X ^ m)
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_apply'`：addLinearEquiv_apply' {R : Ty
pe*} [Ring R] (f) : ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) ∧ ((addLi
nearEquiv R m n f).2 : R[X]) = …
-/
lemma addLinearEquiv_apply_snd {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m) :=
  (addLinearEquiv_apply' f).2
/-
**Polynomial.degreeLT.addLinearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
.degreeLT`。
形式化陈述：addLinearEquiv_apply {R : Type*} [Ring R] (f) : addLinearEquiv R m n f = (
⟨f %ₘ (X ^ m), addLinearEquiv_apply_fst f ▸ Subtype.prop _⟩, ⟨f /ₘ (X ^ m), addL
inearEquiv_apply_snd f ▸ Subtype.prop _⟩)
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_apply_fst`：addLinearEquiv_apply_fst {
R : Type*} [Ring R] (f) : ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m)
· 使用引理 `Polynomial.degreeLT.addLinearEquiv_apply_snd`：addLinearEquiv_apply_snd {
R : Type*} [Ring R] (f) : ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma addLinearEquiv_apply {R : Type*} [Ring R] (f) :
    addLinearEquiv R m n f =
      (⟨f %ₘ (X ^ m), addLinearEquiv_apply_fst f ▸ Subtype.prop _⟩,
      ⟨f /ₘ (X ^ m), addLinearEquiv_apply_snd f ▸ Subtype.prop _⟩) :=
  Prod.ext (Subtype.ext <| addLinearEquiv_apply_fst f) (Subtype.ext <| addLinearEquiv_apply_snd f)

end degreeLT

section taylor

variable {R : Type*} [CommRing R] {r : R} {m n : ℕ} {s : R} {f g : R[X]}

@[simp]
/-
**Polynomial.taylor_mem_degreeLT** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：taylor_mem_degreeLT : taylor r f in R[X]_n ↔ f in R[X]_n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_taylor`：degree_taylor (p : R[X]) (r : R) : degree (tay
lor r p) = degree p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma taylor_mem_degreeLT : taylor r f ∈ R[X]_n ↔ f ∈ R[X]_n := by simp [mem_degreeLT]
/-
**Polynomial.comap_taylorEquiv_degreeLT** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：comap_taylorEquiv_degreeLT : (R[X]_n).comap (taylorEquiv r : R[X] ->ₗ[R] R
[X]) = R[X]_n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.taylorAlgHom_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
(r : R) (a : Polynomial R),   (Polynomial.taylorAlgHom r) a = (Polynomial.taylor
 r) a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_taylorEquiv_degreeLT : (R[X]_n).comap (taylorEquiv r : R[X] →ₗ[R] R[X]) = R[X]_n := by
  ext; simp [taylorEquiv]
/-
**Polynomial.map_taylorEquiv_degreeLT** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：map_taylorEquiv_degreeLT : (R[X]_n).map (taylorEquiv r : R[X] ->ₗ[R] R[X])
 = R[X]_n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.comap_taylorEquiv_degreeLT`：comap_taylorEquiv_degreeLT : (R[X
]_n).comap (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n
· 使用定理 `Submodule.map_comap_eq_of_surjective`：map_comap_eq_of_surjective (p : Su
bmodule R₂ M₂) : (p.comap f).map f = p
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma map_taylorEquiv_degreeLT : (R[X]_n).map (taylorEquiv r : R[X] →ₗ[R] R[X]) = R[X]_n := by
  nth_rw 1 [← comap_taylorEquiv_degreeLT (r := r), Submodule.map_comap_eq_of_surjective]
  exact (taylorEquiv r).surjective

/-- The map `taylor r` induces an automorphism of the module `R[X]_n` of polynomials of
degree `< n`. -/
@[simps! apply_coe]
/-
**Polynomial.taylorLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：taylorLinearEquiv (r : R) (n : Nat) : R[X]_n ≃ₗ[R] R[X]_n
参数：r : R；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.map_taylorEquiv_degreeLT`：map_taylorEquiv_degreeLT : (R[X]_n)
.map (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n

--- 原说明 ---
The map `taylor r` induces an automorphism of the module `R[X]_n` of polynomials
 of
degree `< n`.
-/
noncomputable def taylorLinearEquiv (r : R) (n : ℕ) : R[X]_n ≃ₗ[R] R[X]_n :=
  (taylorEquiv r : R[X] ≃ₗ[R] R[X]).ofSubmodules _ _ map_taylorEquiv_degreeLT
/-
**Polynomial.taylorLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} (r : R),   (Polynomial.taylor
LinearEquiv r n).symm = Polynomial.taylorLinearEquiv (-r) n
参数：r : R；Polynomial.taylorLinearEquiv r n；-r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
@[simp] lemma taylorLinearEquiv_symm (r : R) :
    (taylorLinearEquiv r n).symm = taylorLinearEquiv (-r) n :=
  LinearEquiv.ext <| fun _ ↦ rfl
/-
**Polynomial.det_taylorLinearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {r : R} {n : ℕ}, LinearMap.det ↑(Poly
nomial.taylorLinearEquiv r n) = 1
参数：Polynomial.taylorLinearEquiv r n。
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
· 使用定理 `LinearMap.det_eq_one_of_subsingleton`：det_eq_one_of_subsingleton [Subsin
gleton M] (f : M ->ₗ[R] M) : LinearMap.det (f : M ->ₗ[R] M) = 1
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `Polynomial.degreeLT.basis_repr`：∀ {R : Type u_1} [inst : Semiring R] {n 
: ℕ} (i : Fin n) (P : ↥(Polynomial.degreeLT R n)),   ((Polynomial.degreeLT.basis
 R n).repr P) i = (↑…
· 使用定理 `Polynomial.degreeLT.basis_val`：∀ {R : Type u_1} [inst : Semiring R] {n :
 ℕ} (i : Fin n), ↑((Polynomial.degreeLT.basis R n) i) = Polynomial.X ^ ↑i
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `Polynomial.degree_taylor`：degree_taylor (p : R[X]) (r : R) : degree (tay
lor r p) = degree p
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fintype.prod_eq_one`：prod_eq_one (f : α -> M) (h : forall a, f a = 1) : 
∏ a, f a = 1
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `Polynomial.coeff_taylor_natDegree`：coeff_taylor_natDegree : (taylor r f)
.coeff f.natDegree = f.leadingCoeff
· 使用定理 `Polynomial.leadingCoeff_X_pow`：leadingCoeff_X_pow (n : Nat) : leadingCoe
ff ((X : R[X]) ^ n) = 1
-/
@[simp] theorem det_taylorLinearEquiv_toLinearMap :
    (taylorLinearEquiv r n).toLinearMap.det = 1 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n),
    Matrix.det_of_isUpperTriangular, Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply, degreeLT.basis_repr, ← natDegree_X_pow (R := R) (i : ℕ)]
    change (taylor r (degreeLT.basis R n i)).coeff _ = 1
    rw [degreeLT.basis_val, coeff_taylor_natDegree, leadingCoeff_X_pow]
  · intro i j hji
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, degreeLT.basis_repr]
    change (taylor r (degreeLT.basis R n j)).coeff i = 0
    rw [degreeLT.basis_val, coeff_eq_zero_of_degree_lt (by simpa [-taylor_X_pow, -taylor_pow])]
/-
**Polynomial.det_taylorLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {r : R} {n : ℕ}, LinearEquiv.det (Pol
ynomial.taylorLinearEquiv r n) = 1
参数：Polynomial.taylorLinearEquiv r n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `Polynomial.det_taylorLinearEquiv_toLinearMap`：∀ {R : Type u_1} [inst : C
ommRing R] {r : R} {n : ℕ}, LinearMap.det ↑(Polynomial.taylorLinearEquiv r n) = 
1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
-/
@[simp] theorem det_taylorLinearEquiv :
    (taylorLinearEquiv r n).det = 1 :=
  Units.ext <| by rw [LinearEquiv.coe_det, det_taylorLinearEquiv_toLinearMap, Units.val_one]

end taylor

end Polynomial

