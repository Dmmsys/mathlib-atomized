/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `Algebra.trace`, which is defined similarly as the trace of
`Algebra.leftMulMatrix`.

## References

* https://en.wikipedia.org/wiki/Field_norm

-/

@[expose] public section


universe u v w

variable {R S : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K : Type*} [Field K]
variable {ι : Type w}

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
@[stacks 0BIF "Norm"]
/-
**Algebra.norm** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：norm : S ->* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`.
-/
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom
/-
**Algebra.norm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x)
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) := rfl

@[simp]
/-
**Algebra.norm_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_self : Algebra.norm R = MonoidHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.det_ring`：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R)
, LinearMap.det f = f 1
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_self : Algebra.norm R = MonoidHom.id R := by
  ext
  simp [norm_apply]
/-
**Algebra.norm_eq_one_of_not_exists_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_one_of_not_exists_basis (h : ¬exists s : Finset S, Nonempty (Basis
 s R S)) (x : S) : norm R x = 1
参数：h : ¬exists s : Finset S, Nonempty (Basis s R S)；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `LinearMap.det_def`：∀ {M : Type u_7} [inst : AddCommGroup M] {A : Type u_
8} [inst_1 : CommRing A] [inst_2 : _root_.Module A M],   LinearMap.det = if H : 
∃ s, No…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) :
    norm R x = 1 := by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial

variable {R}
/-
**Algebra.norm_eq_one_of_not_module_finite** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_one_of_not_module_finite (h : ¬Module.Finite R S) (x : S) : norm R
 x = 1
参数：h : ¬Module.Finite R S；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.norm_eq_one_of_not_exists_basis`：norm_eq_one_of_not_exists_basis
 (h : ¬exists s : Finset S, Nonempty (Basis s R S)) (x : S) : norm R x = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem norm_eq_one_of_not_module_finite (h : ¬Module.Finite R S) (x : S) : norm R x = 1 := by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b

-- Can't be a `simp` lemma because it depends on a choice of basis
/-
**Algebra.norm_eq_matrix_det** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
 norm R s = Matrix.det (Algebra.leftMulMatrix b s)
参数：b : Basis ι R S；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.toMatrix_lmul_eq`：toMatrix_lmul_eq (x : S) : LinearMap.toMatrix 
b b (LinearMap.mulLeft R x) = leftMulMatrix b x
-/
theorem norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply, ← LinearMap.det_toMatrix b, ← toMatrix_lmul_eq]; rfl

/-- If `x` is in the base ring `K`, then the norm is `x ^ [L : K]`. -/
/-
**Algebra.norm_algebraMap_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_algebraMap_of_basis [Fintype ι] (b : Basis ι R S) (x : R) : norm R (a
lgebraMap R S x) = x ^ Fintype.card ι
参数：b : Basis ι R S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.lmul_algebraMap`：lmul_algebraMap (x : R) : Algebra.lmul R A (alg
ebraMap R A x) = Algebra.lsmul R R A x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Algebra.toMatrix_lsmul`：toMatrix_lsmul (x : R) : LinearMap.toMatrix b b 
(Algebra.lsmul R R S x) = Matrix.diagonal fun _ => x
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `x` is in the base ring `K`, then the norm is `x ^ [L : K]`.
-/
theorem norm_algebraMap_of_basis [Fintype ι] (b : Basis ι R S) (x : R) :
    norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  have := Classical.decEq ι
  rw [norm_apply, ← det_toMatrix b, lmul_algebraMap]
  simp

variable [Free R S]

/-- If `x` is in the base ring `R` and `S` is free over `R`, then the norm is `x ^ [S : R]`.

(If `S` is not finitely generated over `R`, then `norm = 1 = x ^ 0 = x ^ (finrank R S)`.)
-/
@[simp]
/-
**Algebra.norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : Ring S] [ins
t_2 : Algebra R S] [Module.Free R S] (x : R),   (Algebra.norm R) ((algebraMap R 
S) x) = x ^ Module.finrank R S
参数：x : R；Algebra.norm R；(algebraMap R S) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.lmul_algebraMap`：lmul_algebraMap (x : R) : Algebra.lmul R A (alg
ebraMap R A x) = Algebra.lsmul R R A x
· 使用引理 `Algebra.det_lsmul`：det_lsmul (x : R) : LinearMap.det (lsmul R R S x) = x
 ^ finrank R S

--- 原说明 ---
If `x` is in the base ring `R` and `S` is free over `R`, then the norm is `x ^ [
S : R]`.

(If `S` is not finitely generated over `R`, then `norm = 1 = x ^ 0 = x ^ (finran
k R S)`.)
-/
protected theorem norm_algebraMap (x : R) : norm R (algebraMap R S x) = x ^ finrank R S := by
  rw [norm_apply, lmul_algebraMap, det_lsmul]

variable (R) in
/-
**Algebra.norm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ (R : Type u_1) {S : Type u_2} [inst : CommRing R] [inst_1 : Ring S] [ins
t_2 : Algebra R S] [Module.Free R S] (n : ℕ),   (Algebra.norm R) ↑n = ↑n ^ Modul
e.finrank R S
参数：R : Type u_1；n : ℕ；Algebra.norm R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Algebra.norm_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (x : R),   (Alge
bra.norm R) (…
-/
protected lemma norm_natCast (n : ℕ) : norm R (n : S) = n ^ Module.finrank R S := by
  rw [← map_natCast (algebraMap R S), Algebra.norm_algebraMap]

end Algebra

