/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Composition
public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

We obtain the algebra isomorphism
```
def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
```
which is characterized by
```
coeff (matPolyEquiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

@[expose] public section

universe u v w

open Polynomial TensorProduct
open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type*)
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

open Matrix

variable {R}
variable {n : Type w} [DecidableEq n] [Fintype n]

/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`matPolyEquiv_coeff_apply` below.)
-/
/-
**matPolyEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism stating "matrices of polynomials are the same as polynom
ials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`matPolyEquiv_coeff_apply` below.)
-/
noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor n R R[X]).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm
/-
**matPolyEquiv_symm_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type w} [inst_1 : DecidableE
q n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEquiv.symm (Polynomial.C 
M) = M.map ⇑Polynomial.C
参数：M : Matrix n n R；Polynomial.C M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem matPolyEquiv_symm_C (M : Matrix n n R) : matPolyEquiv.symm (C M) = M.map C := by
  simp [matPolyEquiv]
/-
**matPolyEquiv_map_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type w} [inst_1 : DecidableE
q n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEquiv (M.map ⇑Polynomial.
C) = Polynomial.C M
参数：M : Matrix n n R；M.map ⇑Polynomial.C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `matPolyEquiv_symm_C`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEq
uiv.symm …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
@[simp] theorem matPolyEquiv_map_C (M : Matrix n n R) : matPolyEquiv (M.map C) = C M := by
  rw [← matPolyEquiv_symm_C, AlgEquiv.apply_symm_apply]
/-
**matPolyEquiv_symm_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type w} [inst_1 : DecidableE
q n] [inst_2 : Fintype n],   matPolyEquiv.symm Polynomial.X = Matrix.diagonal fu
n x => Polynomial.X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Matrix.smul_one_eq_diagonal`：smul_one_eq_diagonal [DecidableEq m] (a : α
) : a • (1 : Matrix m m α) = diagonal fun _ => a
-/
@[simp] theorem matPolyEquiv_symm_X :
    matPolyEquiv.symm X = diagonal fun _ : n => (X : R[X]) := by
  simp [matPolyEquiv, Matrix.smul_one_eq_diagonal]
/-
**matPolyEquiv_diagonal_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type w} [inst_1 : DecidableE
q n] [inst_2 : Fintype n],   matPolyEquiv (Matrix.diagonal fun x => Polynomial.X
) = Polynomial.X
参数：Matrix.diagonal fun x => Polynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `matPolyEquiv_symm_X`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   matPolyEquiv.symm Polynomial
.X = Matr…
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
@[simp] theorem matPolyEquiv_diagonal_X :
    matPolyEquiv (diagonal fun _ : n => (X : R[X])) = X := by
  rw [← matPolyEquiv_symm_X, AlgEquiv.apply_symm_apply]

open Finset

unseal Algebra.TensorProduct.mul in
/-
**matPolyEquiv_coeff_apply_aux_1** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : Nat) (x : R) : matPolyEquiv 
(single i j <| monomial k x) = monomial k (single i j x)
参数：i j : n；k : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `matrixEquivTensor_apply_single`：matrixEquivTensor_apply_single (i j : n)
 (x : A) : matrixEquivTensor n R A (single i j x) = x otimesₜ single i j 1
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Polynomial.eval₂_monomial`：eval₂_monomial {n : Nat} {r : R} : (monomial 
n r).eval₂ f x = f r * x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.TensorProduct.tmul_pow`：tmul_pow (a : A) (b : B) (k : Nat) : a o
timesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smul_X_eq_monomial`：smul_X_eq_monomial {n} : a • X ^ n = mono
mial n (a : R)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
    matPolyEquiv (single i j <| monomial k x) = monomial k (single i j x) := by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_single]
  apply (polyEquivTensor R (Matrix n n R)).injective
  simp only [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [one_pow,
    Algebra.TensorProduct.tmul_pow]
  rw [← smul_X_eq_monomial, ← TensorProduct.smul_tmul]
  congr with i' <;> simp [single]
/-
**matPolyEquiv_coeff_apply_aux_2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : Nat) : coeff (mat
PolyEquiv (single i j p)) k = single i j (coeff p k)
参数：i j : n；p : R[X]；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.single_add`：single_add [AddZeroClass α] (i : m) (j : n) (a b : α)
 : single i j (a + b) = single i j a + single i j b
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Matrix.single.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7}
 {inst : DecidableEq m} [inst_1 : DecidableEq m] {inst_2 : DecidableEq n}   [ins
t_3 : Decidabl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `matPolyEquiv_coeff_apply_aux_1`：matPolyEquiv_coeff_apply_aux_1 (i j : n)
 (k : Nat) (x : R) : matPolyEquiv (single i j <| monomial k x) = monomial k (sin
gle i j x)
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Matrix.single_zero`：single_zero (i : m) (j : n) : single i j (0 : α) = 0
-/
theorem matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : ℕ) :
    coeff (matPolyEquiv (single i j p)) k = single i j (coeff p k) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, Matrix.add_apply, single_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp

@[simp]
/-
**matPolyEquiv_coeff_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : Nat) (i j : n) : coeff
 (matPolyEquiv m) k i j = coeff (m i j) k
参数：m : Matrix n n R[X]；k : Nat；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.induction_on'`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7} [in
st : DecidableEq m] [inst_1 : DecidableEq n]   [inst_2 : AddCommMonoid α] [Finit
e m] [Fini…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `matPolyEquiv_coeff_apply_aux_2`：matPolyEquiv_coeff_apply_aux_2 (i j : n)
 (p : R[X]) (k : Nat) : coeff (matPolyEquiv (single i j p)) k = single i j (coef
f p k)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : ℕ) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k := by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    rw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [single]
    split_ifs <;> rename_i h
    · constructor
    · simp

@[simp]
/-
**matPolyEquiv_symm_apply_coeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : Nat) 
: coeff (matPolyEquiv.symm p i j) k = coeff p k i j
参数：p : (Matrix n n R)[X]；i j : n；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `matPolyEquiv_coeff_apply`：matPolyEquiv_coeff_apply (m : Matrix n n R[X])
 (k : Nat) (i j : n) : coeff (matPolyEquiv m) k i j = coeff (m i j) k
-/
theorem matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : ℕ) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j := by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]
/-
**matPolyEquiv_smul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_smul_one (p : R[X]) : matPolyEquiv (p • (1 : Matrix n n R[X])
) = p.map (algebraMap R (Matrix n n R))
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `matPolyEquiv_coeff_apply`：matPolyEquiv_coeff_apply (m : Matrix n n R[X])
 (k : Nat) (i j : n) : coeff (matPolyEquiv m) k i j = coeff (m i j) k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem matPolyEquiv_smul_one (p : R[X]) :
    matPolyEquiv (p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R)) := by
  ext m i j
  simp only [matPolyEquiv_coeff_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, coeff_map, algebraMap_matrix_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs <;> simp

@[simp]
/-
**matPolyEquiv_map_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：matPolyEquiv_map_smul (p : R[X]) (M : Matrix n n R[X]) : matPolyEquiv (p •
 M) = p.map (algebraMap _ _) * matPolyEquiv M
参数：p : R[X]；M : Matrix n n R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `matPolyEquiv_smul_one`：matPolyEquiv_smul_one (p : R[X]) : matPolyEquiv (
p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R))
-/
lemma matPolyEquiv_map_smul (p : R[X]) (M : Matrix n n R[X]) :
    matPolyEquiv (p • M) = p.map (algebraMap _ _) * matPolyEquiv M := by
  rw [← one_mul M, ← smul_mul_assoc, map_mul, matPolyEquiv_smul_one, one_mul]
/-
**matPolyEquiv_symm_map_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_symm_map_eval (M : (Matrix n n R)[X]) (r : R) : (matPolyEquiv
.symm M).map (eval r) = M.eval (scalar n r)
参数：M : (Matrix n n R)[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Matrix.scalar_commute`：scalar_commute (r : α) (hr : forall r', Commute r
 r') (M : Matrix n n α) : Commute (scalar n r) M
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Polynomial.algHom_ext'`：algHom_ext' {f g : A[X] ->ₐ[R] B} (hC : f.comp C
AlgHom = g.comp CAlgHom) (hX : f X = g X) : f = g
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgHom.mapMatrix_apply`：∀ {m : Type u_2} {R : Type u_7} {α : Type u_11} 
{β : Type u_12} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : CommSemi
ring R] [ins…
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `matPolyEquiv_symm_C`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEq
uiv.symm …
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Matrix.map_id'`：map_id' (M : Matrix m n α) : M.map (·) = M
· 使用定理 `Polynomial.eval₂AlgHom_apply`：∀ {R : Type u} {A : Type z} {B : Type u_2}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [ins…
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `matPolyEquiv_symm_X`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   matPolyEquiv.symm Polynomial
.X = Matr…
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem matPolyEquiv_symm_map_eval (M : (Matrix n n R)[X]) (r : R) :
    (matPolyEquiv.symm M).map (eval r) = M.eval (scalar n r) := by
  suffices ((aeval r).mapMatrix.comp matPolyEquiv.symm.toAlgHom : (Matrix n n R)[X] →ₐ[R] _) =
      (eval₂AlgHom (AlgHom.id R _) (scalar n r)
        fun x => (scalar_commute _ (Commute.all _) _).symm) from
    DFunLike.congr_fun this M
  ext : 1
  · ext M : 1
    simp [Function.comp_def]
  · simp
/-
**matPolyEquiv_eval_eq_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_eval_eq_map (M : Matrix n n R[X]) (r : R) : (matPolyEquiv M).
eval (scalar n r) = M.map (eval r)
参数：M : Matrix n n R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `matPolyEquiv_symm_map_eval`：matPolyEquiv_symm_map_eval (M : (Matrix n n 
R)[X]) (r : R) : (matPolyEquiv.symm M).map (eval r) = M.eval (scalar n r)
-/
theorem matPolyEquiv_eval_eq_map (M : Matrix n n R[X]) (r : R) :
    (matPolyEquiv M).eval (scalar n r) = M.map (eval r) := by
  simpa only [AlgEquiv.symm_apply_apply] using (matPolyEquiv_symm_map_eval (matPolyEquiv M) r).symm

-- I feel like this should use `Polynomial.algHom_eval₂_algebraMap`
/-
**matPolyEquiv_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_eval (M : Matrix n n R[X]) (r : R) (i j : n) : (matPolyEquiv 
M).eval (scalar n r) i j = (M i j).eval r
参数：M : Matrix n n R[X]；r : R；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `matPolyEquiv_eval_eq_map`：matPolyEquiv_eval_eq_map (M : Matrix n n R[X])
 (r : R) : (matPolyEquiv M).eval (scalar n r) = M.map (eval r)
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
-/
theorem matPolyEquiv_eval (M : Matrix n n R[X]) (r : R) (i j : n) :
    (matPolyEquiv M).eval (scalar n r) i j = (M i j).eval r := by
  rw [matPolyEquiv_eval_eq_map, map_apply]
/-
**support_subset_support_matPolyEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) : supp
ort (m i j) subseteq support (matPolyEquiv m)
参数：m : Matrix n n R[X]；i j : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `matPolyEquiv_coeff_apply`：matPolyEquiv_coeff_apply (m : Matrix n n R[X])
 (k : Nat) (i j : n) : coeff (matPolyEquiv m) k i j = coeff (m i j) k
· 使用定理 `Matrix.zero_apply`：zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n
 α) i j = 0
-/
theorem support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) ⊆ support (matPolyEquiv m) := by
  intro k
  contrapose
  simp only [notMem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply, hk, Matrix.zero_apply]
/-
**eval_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eval_det {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R) : Polynomi
al.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det
参数：M : Matrix n n R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval.eq_1`：∀ {R : Type u} [inst : Semiring R] (x : R) (p : Po
lynomial R), Polynomial.eval x p = Polynomial.eval₂ (RingHom.id R) x p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_eval₂RingHom`：coe_eval₂RingHom (f : R ->+* S) (x) : ⇑(eva
l₂RingHom f x) = eval₂ f x
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `matPolyEquiv_eval`：matPolyEquiv_eval (M : Matrix n n R[X]) (r : R) (i j 
: n) : (matPolyEquiv M).eval (scalar n r) i j = (M i j).eval r
-/
theorem eval_det {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R) :
    Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det := by
  rw [Polynomial.eval, ← coe_eval₂RingHom, RingHom.map_det]
  exact congr_arg det <| ext fun _ _ ↦ matPolyEquiv_eval _ _ _ _ |>.symm
/-
**eval_det_add_X_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eval_det_add_X_smul {R : Type*} [CommRing R] (A : Matrix n n R[X]) (M : Ma
trix n n R) : (det (A + (X : R[X]) • M.map C)).eval 0 = (det A).eval 0
参数：A : Matrix n n R[X]；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eval_det`：eval_det {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R
) : Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `matPolyEquiv_smul_one`：matPolyEquiv_smul_one (p : R[X]) : matPolyEquiv (
p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R))
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_det_add_X_smul {R : Type*} [CommRing R] (A : Matrix n n R[X]) (M : Matrix n n R) :
    (det (A + (X : R[X]) • M.map C)).eval 0 = (det A).eval 0 := by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, map_mul]
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X,
    mul_zero, add_zero]

variable {A}
/-- Extend a ring hom `A → Mₙ(R)` to a ring hom `A[X] → Mₙ(R[X])`. -/
/-
**RingHom.polyToMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.polyToMatrix (f : A ->+* Matrix n n R) : A[X] ->+* Matrix n n R[X]
参数：f : A ->+* Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a ring hom `A → Mₙ(R)` to a ring hom `A[X] → Mₙ(R[X])`.
-/
def RingHom.polyToMatrix (f : A →+* Matrix n n R) : A[X] →+* Matrix n n R[X] :=
  matPolyEquiv.symm.toRingHom.comp (mapRingHom f)

variable {S : Type*} [CommSemiring S] (f : S →+* Matrix n n R)
/-
**evalRingHom_mapMatrix_comp_polyToMatrix** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：evalRingHom_mapMatrix_comp_polyToMatrix : (evalRingHom 0).mapMatrix.comp f
.polyToMatrix = f.comp (evalRingHom 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ringHom_ext'`：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* 
S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `matPolyEquiv_symm_C`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEq
uiv.symm …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `matPolyEquiv_symm_X`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   matPolyEquiv.symm Polynomial
.X = Matr…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma evalRingHom_mapMatrix_comp_polyToMatrix :
    (evalRingHom 0).mapMatrix.comp f.polyToMatrix = f.comp (evalRingHom 0) := by
  ext <;> simp [RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, diagonal, apply_ite]
/-
**evalRingHom_mapMatrix_comp_compRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：evalRingHom_mapMatrix_comp_compRingEquiv {m} [Fintype m] [DecidableEq m] :
 (evalRingHom 0).mapMatrix.comp (compRingEquiv m n R[X]) = (compRingEquiv m n R)
.toRingHom.comp (evalRingHom 0).mapMatrix.mapMatrix
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.comp_apply`：∀ (I : Type u_1) (J : Type u_2) (K : Type u_3) (L : T
ype u_4) (R : Type u_5) (m : Matrix I J (Matrix K L R))   (ik : I × K) (jl : J ×
 L), (M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalRingHom_mapMatrix_comp_compRingEquiv {m} [Fintype m] [DecidableEq m] :
    (evalRingHom 0).mapMatrix.comp (compRingEquiv m n R[X]) =
      (compRingEquiv m n R).toRingHom.comp (evalRingHom 0).mapMatrix.mapMatrix := by
  ext; simp
