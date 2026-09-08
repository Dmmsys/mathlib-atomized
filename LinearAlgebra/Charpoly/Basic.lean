/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Determinant

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `LinearAlgebra/Charpoly/ToMatrix`.

## Main definition

* `LinearMap.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/

@[expose] public section


universe u v w

open Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

section Basic

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
/-
**LinearMap.charpoly** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：charpoly : R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic polynomial of `f : M →ₗ[R] M`.
-/
def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
/-
**LinearMap.charpoly_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) 
f).charpoly
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl
/-
**LinearMap.eval_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eval_charpoly (t : R) : f.charpoly.eval t = (algebraMap _ _ t - f).det
参数：t : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.charpoly.eq_1`：∀ {R : Type u} {M : Type v} [inst : CommRing R]
 [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_3 : Module.Free 
R M] [inst_4 …
· 使用定理 `Matrix.eval_charpoly`：eval_charpoly (M : Matrix m m R) (t : R) : M.charp
oly.eval t = (Matrix.scalar _ t - M).det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
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
· 使用定理 `Matrix.scalar_apply`：scalar_apply (a : α) : scalar n a = diagonal fun _ 
=> a
· 使用定理 `LinearMap.toMatrix_algebraMap`：LinearMap.toMatrix_algebraMap (x : R) : L
inearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x
-/
theorem eval_charpoly (t : R) :
    f.charpoly.eval t = (algebraMap _ _ t - f).det := by
  rw [charpoly, Matrix.eval_charpoly, ← LinearMap.det_toMatrix (chooseBasis R M), map_sub,
    scalar_apply, toMatrix_algebraMap, scalar_apply]

@[simp]
/-
**LinearMap.charpoly_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_zero [StrongRankCondition R] : (0 : M ->ₗ[R] M).charpoly = X ^ Mo
dule.finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
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
· 使用定理 `Matrix.charpoly_zero`：charpoly_zero : charpoly (0 : Matrix n n R) = X ^ 
Fintype.card n
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_zero [StrongRankCondition R] :
    (0 : M →ₗ[R] M).charpoly = X ^ Module.finrank R M := by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex]
/-
**LinearMap.charpoly_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_one [StrongRankCondition R] : (1 : M ->ₗ[R] M).charpoly = (X - 1)
 ^ Module.finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `Matrix.charpoly_one`：charpoly_one : charpoly (1 : Matrix n n R) = (X - 1
) ^ Fintype.card n
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_one [StrongRankCondition R] :
    (1 : M →ₗ[R] M).charpoly = (X - 1) ^ Module.finrank R M := by
  simp [charpoly, Module.finrank_eq_card_chooseBasisIndex, Matrix.charpoly_one]
/-
**LinearMap.charpoly_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_sub_smul (f : Module.End R M) (μ : R) : (f - μ • 1).charpoly = f.
charpoly.comp (X + C μ)
参数：f : Module.End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
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
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `Matrix.smul_eq_mul_diagonal`：smul_eq_mul_diagonal [Fintype n] [Decidable
Eq n] (M : Matrix m n α) (a : α) : a • M = M * diagonal fun _ => a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.charpoly_sub_scalar`：charpoly_sub_scalar (M : Matrix n n R) (μ : 
R) : (M - scalar n μ).charpoly = M.charpoly.comp (X + C μ)
-/
theorem charpoly_sub_smul (f : Module.End R M) (μ : R) :
    (f - μ • 1).charpoly = f.charpoly.comp (X + C μ) := by
  simpa [LinearMap.charpoly, smul_eq_mul_diagonal] using Matrix.charpoly_sub_scalar ..

end Basic

section Coeff

/-
**LinearMap.charpoly_monic** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_monic : f.charpoly.Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
-/
theorem charpoly_monic : f.charpoly.Monic :=
  Matrix.charpoly_monic _

open Module in
/-
**LinearMap.charpoly_natDegree** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：charpoly_natDegree [StrongRankCondition R] : natDegree (charpoly f) = finr
ank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.charpoly.eq_1`：∀ {R : Type u} {M : Type v} [inst : CommRing R]
 [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_3 : Module.Free 
R M] [inst_4 …
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
-/
lemma charpoly_natDegree [StrongRankCondition R] :
    natDegree (charpoly f) = finrank R M := by
  have := nontrivial_of_invariantBasisNumber
  rw [charpoly, Matrix.charpoly_natDegree_eq_dim, finrank_eq_card_chooseBasisIndex]

end Coeff

section CayleyHamilton

/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a linear map, applied
to the linear map itself, is zero.

See `Matrix.aeval_self_charpoly` for the equivalent statement about matrices. -/
/-
**LinearMap.aeval_self_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：aeval_self_charpoly : aeval f f.charpoly = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.charpoly_def`：charpoly_def : f.charpoly = (toMatrix (chooseBas
is R M) (chooseBasis R M) f).charpoly
· 使用定理 `Matrix.aeval_self_charpoly`：aeval_self_charpoly (M : Matrix n n R) : aev
al M M.charpoly = 0

--- 原说明 ---
The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a linear 
map, applied
to the linear map itself, is zero.

See `Matrix.aeval_self_charpoly` for the equivalent statement about matrices.
-/
theorem aeval_self_charpoly : aeval f f.charpoly = 0 := by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply, ← AlgEquiv.coe_toAlgHom, ← Polynomial.aeval_algHom_apply _ _ _,
    charpoly_def]
  exact Matrix.aeval_self_charpoly _
/-
**LinearMap.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isIntegral : IsIntegral R f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.charpoly_monic`：charpoly_monic : f.charpoly.Monic
· 使用定理 `LinearMap.aeval_self_charpoly`：aeval_self_charpoly : aeval f f.charpoly 
= 0
-/
theorem isIntegral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩
/-
**LinearMap.minpoly_dvd_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroup M] 
[Module K M] [FiniteDimensional K M] (f : M ->ₗ[K] M) : minpoly K f ∣ f.charpoly
参数：f : M ->ₗ[K] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.aeval_self_charpoly`：aeval_self_charpoly : aeval f f.charpoly 
= 0
-/
theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)

/-- Any endomorphism polynomial `p` is equivalent under evaluation to `p %ₘ f.charpoly`; that is,
`p` is equivalent to a polynomial with degree less than the dimension of the module. -/
/-
**LinearMap.aeval_eq_aeval_mod_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charp
oly)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_modByMonic_eq_self_of_root`：aeval_modByMonic_eq_self_of
_root [Algebra R S] {p q : R[X]} {x : S} (hx : aeval x q = 0) : aeval x (p %ₘ q)
 = aeval x p
· 使用定理 `LinearMap.aeval_self_charpoly`：aeval_self_charpoly : aeval f f.charpoly 
= 0

--- 原说明 ---
Any endomorphism polynomial `p` is equivalent under evaluation to `p %ₘ f.charpo
ly`; that is,
`p` is equivalent to a polynomial with degree less than the dimension of the mod
ule.
-/
theorem aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  (aeval_modByMonic_eq_self_of_root f.aeval_self_charpoly).symm

/-- Any endomorphism power can be computed as the sum of endomorphism powers less than the
dimension of the module. -/
/-
**LinearMap.pow_eq_aeval_mod_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pow_eq_aeval_mod_charpoly (k : Nat) : f ^ k = aeval f (X ^ k %ₘ f.charpoly
)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.aeval_eq_aeval_mod_charpoly`：aeval_eq_aeval_mod_charpoly (p : 
R[X]) : aeval f p = aeval f (p %ₘ f.charpoly)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x

--- 原说明 ---
Any endomorphism power can be computed as the sum of endomorphism powers less th
an the
dimension of the module.
-/
theorem pow_eq_aeval_mod_charpoly (k : ℕ) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

variable {f}
/-
**LinearMap.minpoly_coeff_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：minpoly_coeff_zero_of_injective [Nontrivial R] (hf : Function.Injective f)
 : (minpoly R f).coeff 0 != 0
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.X_dvd_iff`：X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.degree_lt_degree_mul_X`：degree_lt_degree_mul_X (hp : p != 0) 
: p.degree < (p * X).degree
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `LinearMap.isIntegral`：isIntegral : IsIntegral R f
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `Polynomial.leadingCoeff_mul_X`：leadingCoeff_mul_X {p : R[X]} : leadingCo
eff (p * X) = leadingCoeff p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
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
theorem minpoly_coeff_zero_of_injective [Nontrivial R] (hf : Function.Injective f) :
    (minpoly R f).coeff 0 ≠ 0 := by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree := by
    rw [hP, mul_comm]
    refine degree_lt_degree_mul_X fun h => ?_
    rw [h, mul_zero] at hP
    exact minpoly.ne_zero (isIntegral f) hP
  have hPmonic : P.Monic := by
    suffices (minpoly R f).Monic by
      rwa [Monic.def, hP, mul_comm, leadingCoeff_mul_X, ← Monic.def] at this
    exact minpoly.monic (isIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [hP, Module.End.mul_eq_comp, LinearMap.ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp,
    map_mul, zero_apply, Function.comp_apply] at hzero
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (LinearMap.ext hzero))

end CayleyHamilton

end LinearMap

section Algebra
variable {R M} [CommRing R] [Ring M] [Algebra R M]
  [Module.Finite R M] [Module.Free R M]

/-
**Algebra.aeval_self_charpoly_lmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.aeval_self_charpoly_lmul (α : M) : aeval α (Algebra.lmul R M α).ch
arpoly = 0
参数：α : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.lmul_injective`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   Function.Injective ⇑(Alg
ebra.lmul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `LinearMap.aeval_self_charpoly`：aeval_self_charpoly : aeval f f.charpoly 
= 0
-/
theorem Algebra.aeval_self_charpoly_lmul (α : M) :
    aeval α (Algebra.lmul R M α).charpoly = 0 :=
  Algebra.lmul_injective (R := R) <| by
    simpa [← aeval_algHom_apply] using LinearMap.aeval_self_charpoly <| Algebra.lmul _ _ α

end Algebra

