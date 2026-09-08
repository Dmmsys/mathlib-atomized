/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The universal characteristic polynomial

In this file we define the universal characteristic polynomial `Matrix.charpoly.univ`,
which is the characteristic polynomial of the matrix with entries `Xᵢⱼ`,
and hence has coefficients that are multivariate polynomials.

It is universal in the sense that one obtains the characteristic polynomial of a matrix `M`
by evaluating the coefficients of `univ` at the entries of `M`.

We use it to show that the coefficients of the characteristic polynomial
of a matrix are homogeneous polynomials in the matrix entries.

## Main results

* `Matrix.charpoly.univ`: the universal characteristic polynomial
* `Matrix.charpoly.univ_map_eval₂Hom`: evaluating `univ` on the entries of a matrix `M`
  gives the characteristic polynomial of `M`.
* `Matrix.charpoly.univ_coeff_isHomogeneous`:
  the `i`-th coefficient of `univ` is a homogeneous polynomial of degree `n - i`.
-/

public section

namespace Matrix.charpoly

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
variable (f : R →+* S)

variable (R) in
/-- The universal characteristic polynomial for `n × n`-matrices,
is the characteristic polynomial of `Matrix.mvPolynomialX n n ℤ` with entries `Xᵢⱼ`.

Its `i`-th coefficient is a homogeneous polynomial of degree `n - i`,
see `Matrix.charpoly.univ_coeff_isHomogeneous`.

By evaluating the coefficients at the entries of a matrix `M`,
one obtains the characteristic polynomial of `M`,
see `Matrix.charpoly.univ_map_eval₂Hom`. -/
noncomputable
/-
**Matrix.charpoly.univ** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix.charpoly`。
形式化陈述：univ : Polynomial (MvPolynomial (n × n) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev univ : Polynomial (MvPolynomial (n × n) R) :=
  charpoly <| mvPolynomialX n n R

open MvPolynomial RingHomClass in
@[simp]
/-
**Matrix.charpoly.univ_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.charpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma univ_map_eval₂Hom (M : n × n → S) :
    (univ R n).map (eval₂Hom f M) = charpoly (Matrix.of M.curry) := by
  rw [univ, ← charpoly_map, coe_eval₂Hom, ← mvPolynomialX_map_eval₂ f (Matrix.of M.curry)]
  simp only [of_apply, Function.curry_apply, Prod.mk.eta]
/-
**Matrix.charpoly.univ_map_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.charpoly`。
形式化陈述：univ_map_map : (univ R n).map (MvPolynomial.map f) = univ S n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.map_eq_eval₂Hom_C_comp`：map_eq_eval₂Hom_C_comp : map (σ
· 使用引理 `Matrix.charpoly.univ_map_eval₂Hom`：univ_map_eval₂Hom (M : n × n -> S) : 
(univ R n).map (eval₂Hom f M) = charpoly (Matrix.of M.curry)
-/
lemma univ_map_map :
    (univ R n).map (MvPolynomial.map f) = univ S n := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp, univ_map_eval₂Hom]; rfl

@[simp]
/-
**Matrix.charpoly.univ_coeff_eval** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.charpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma univ_coeff_eval₂Hom (M : n × n → S) (i : ℕ) :
    MvPolynomial.eval₂Hom f M ((univ R n).coeff i) =
      (charpoly (Matrix.of M.curry)).coeff i := by
  rw [← univ_map_eval₂Hom n f M, Polynomial.coeff_map]

variable (R)
/-
**Matrix.charpoly.univ_monic** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.charpoly`。
形式化陈述：univ_monic : (univ R n).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
-/
lemma univ_monic : (univ R n).Monic := charpoly_monic (mvPolynomialX n n R)
/-
**Matrix.charpoly.univ_natDegree** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.charpoly`。
形式化陈述：univ_natDegree [Nontrivial R] : (univ R n).natDegree = Fintype.card n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
-/
lemma univ_natDegree [Nontrivial R] : (univ R n).natDegree = Fintype.card n :=
  charpoly_natDegree_eq_dim (mvPolynomialX n n R)

@[simp]
/-
**Matrix.charpoly.univ_coeff_card** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.charpoly`。
形式化陈述：univ_coeff_card : (univ R n).coeff (Fintype.card n) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.charpoly.univ_natDegree`：univ_natDegree [Nontrivial R] : (univ R 
n).natDegree = Fintype.card n
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `Matrix.charpoly.univ_monic`：univ_monic : (univ R n).Monic
· 使用引理 `Matrix.charpoly.univ_map_map`：univ_map_map : (univ R n).map (MvPolynomia
l.map f) = univ S n
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
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
-/
lemma univ_coeff_card : (univ R n).coeff (Fintype.card n) = 1 := by
  suffices Polynomial.coeff (univ ℤ n) (Fintype.card n) = 1 by
    rw [← univ_map_map n (Int.castRingHom R), Polynomial.coeff_map, this, map_one]
  rw [← univ_natDegree ℤ n]
  exact (univ_monic ℤ n).leadingCoeff

open MvPolynomial in
/-
**Matrix.charpoly.optionEquivLeft_symm_univ_isHomogeneous** 是 Mathlib 中的一个引理，位于命
名空间 `Matrix.charpoly`。
形式化陈述：optionEquivLeft_symm_univ_isHomogeneous : ((optionEquivLeft R (n × n)).sym
m (univ R n)).IsHomogeneous (Fintype.card n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `MvPolynomial.optionEquivLeft_symm_apply`：∀ (R : Type u) (S₁ : Type v) [i
nst : CommSemiring R] (a : Polynomial (MvPolynomial S₁ R)),   (MvPolynomial.opti
onEquivLeft R S₁).symm a =   …
（共 47 条，此处仅展示前 30 条）
-/
lemma optionEquivLeft_symm_univ_isHomogeneous :
    ((optionEquivLeft R (n × n)).symm (univ R n)).IsHomogeneous (Fintype.card n) := by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, univ, charpoly, charmatrix, scalar_apply, RingHom.mapMatrix_apply, det_apply',
    sub_apply, map_apply, of_apply, map_sum, map_mul, map_intCast, map_prod, map_sub,
    optionEquivLeft_symm_apply, Polynomial.aevalTower_C, rename_X, diagonal, mvPolynomialX]
  apply IsHomogeneous.sum
  rintro i -
  apply IsHomogeneous.mul
  · apply isHomogeneous_C
  · apply IsHomogeneous.prod
    rintro j -
    by_cases h : i j = j
    · simp only [h, ↓reduceIte, Polynomial.aevalTower_X, IsHomogeneous.sub, isHomogeneous_X]
    · simp only [h, ↓reduceIte, map_zero, zero_sub, (isHomogeneous_X _ _).neg]
/-
**Matrix.charpoly.univ_coeff_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.cha
rpoly`。
形式化陈述：univ_coeff_isHomogeneous (i j : Nat) (h : i + j = Fintype.card n) : ((univ
 R n).coeff i).IsHomogeneous j
参数：i j : Nat；h : i + j = Fintype.card n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.IsHomogeneous.coeff_isHomogeneous_of_optionEquivLeft_symm`：
coeff_isHomogeneous_of_optionEquivLeft_symm [hσ : Finite σ] {p : Polynomial (MvP
olynomial σ R)} (hp : ((optionEquivLeft R σ).symm p).IsHomog…
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Matrix.charpoly.optionEquivLeft_symm_univ_isHomogeneous`：optionEquivLeft
_symm_univ_isHomogeneous : ((optionEquivLeft R (n × n)).symm (univ R n)).IsHomog
eneous (Fintype.card n)
-/
lemma univ_coeff_isHomogeneous (i j : ℕ) (h : i + j = Fintype.card n) :
    ((univ R n).coeff i).IsHomogeneous j :=
  (optionEquivLeft_symm_univ_isHomogeneous R n).coeff_isHomogeneous_of_optionEquivLeft_symm _ _ h

end Matrix.charpoly

