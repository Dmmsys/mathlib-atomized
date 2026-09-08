/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerBasis

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.

This also includes some miscellaneous results about `minpoly` on matrices.
-/

public section


noncomputable section

open Matrix Module Polynomial

universe u v w

variable {R : Type u} [CommRing R]
variable {n : Type v} [DecidableEq n] [Fintype n]
variable {N : Type w} [AddCommGroup N] [Module R N]

namespace Matrix

variable (M : Matrix n n R)

@[simp]
/-
**Matrix.minpoly_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：minpoly_toLin' : minpoly R (toLin' M) = minpoly R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem minpoly_toLin' : minpoly R (toLin' M) = minpoly R M :=
  minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M

@[simp]
/-
**Matrix.minpoly_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：minpoly_toLin (b : Basis n R N) (M : Matrix n n R) : minpoly R (toLin b b 
M) = minpoly R M
参数：b : Basis n R N；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
-/
theorem minpoly_toLin (b : Basis n R N) (M : Matrix n n R) :
    minpoly R (toLin b b M) = minpoly R M :=
  minpoly.algEquiv_eq (toLinAlgEquiv b : Matrix n n R ≃ₐ[R] _) M
/-
**Matrix.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isIntegral : IsIntegral R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
· 使用定理 `Matrix.aeval_self_charpoly`：aeval_self_charpoly (M : Matrix n n R) : aev
al M M.charpoly = 0
-/
theorem isIntegral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩
/-
**Matrix.minpoly_dvd_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) : minpoly K 
M ∣ M.charpoly
参数：M : Matrix n n K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Matrix.aeval_self_charpoly`：aeval_self_charpoly (M : Matrix n n R) : aev
al M M.charpoly = 0
-/
theorem minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)

end Matrix

namespace LinearMap

@[simp]
/-
**LinearMap.minpoly_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：minpoly_toMatrix' (f : (n -> R) ->ₗ[R] n -> R) : minpoly R (toMatrix' f) =
 minpoly R f
参数：f : (n -> R) ->ₗ[R] n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem minpoly_toMatrix' (f : (n → R) →ₗ[R] n → R) : minpoly R (toMatrix' f) = minpoly R f :=
  minpoly.algEquiv_eq (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f

@[simp]
/-
**LinearMap.minpoly_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：minpoly_toMatrix (b : Basis n R N) (f : N ->ₗ[R] N) : minpoly R (toMatrix 
b b f) = minpoly R f
参数：b : Basis n R N；f : N ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
-/
theorem minpoly_toMatrix (b : Basis n R N) (f : N →ₗ[R] N) :
    minpoly R (toMatrix b b f) = minpoly R f :=
  minpoly.algEquiv_eq (toMatrixAlgEquiv b : _ ≃ₐ[R] Matrix n n R) f

end LinearMap

section PowerBasis

open Algebra

/-- The characteristic polynomial of the map `fun x => a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
/-
**charpoly_leftMulMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charpoly_leftMulMatrix {S : Type*} [Ring S] [Algebra R S] (h : PowerBasis 
R S) : (leftMulMatrix h.basis h.gen).charpoly = minpoly R h.gen
参数：h : PowerBasis R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `minpoly.unique'`：unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeva
l x p = 0) (hl : forall q : A[X], degree q < degree p -> q = 0 ∨ Polynomial.aeva
l x q…
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Algebra.leftMulMatrix_injective`：leftMulMatrix_injective : Function.Inje
ctive (leftMulMatrix b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `Matrix.aeval_self_charpoly`：aeval_self_charpoly (M : Matrix n n R) : aev
al M M.charpoly = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PowerBasis.dim_le_degree_of_root`：dim_le_degree_of_root (h : PowerBasis 
A S) {p : A[X]} (ne_zero : p != 0) (root : aeval h.gen p = 0) : ↑h.dim <= p.degr
ee
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Matrix.charpoly_degree_eq_dim`：charpoly_degree_eq_dim [Nontrivial R] (M 
: Matrix n n R) : M.charpoly.degree = Fintype.card n

--- 原说明 ---
The characteristic polynomial of the map `fun x => a * x` is the minimal polynom
ial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff
`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
theorem charpoly_leftMulMatrix {S : Type*} [Ring S] [Algebra R S] (h : PowerBasis R S) :
    (leftMulMatrix h.basis h.gen).charpoly = minpoly R h.gen := by
  cases subsingleton_or_nontrivial R; · subsingleton
  apply minpoly.unique' R h.gen (charpoly_monic _)
  · apply (injective_iff_map_eq_zero (G := S) (leftMulMatrix _)).mp
      (leftMulMatrix_injective h.basis)
    rw [← Polynomial.aeval_algHom_apply, aeval_self_charpoly]
  refine fun q hq => or_iff_not_imp_left.2 fun h0 => ?_
  rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at hq
  contrapose! hq; exact h.dim_le_degree_of_root h0 hq

end PowerBasis

