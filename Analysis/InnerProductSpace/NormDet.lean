/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Geometry.Euclidean.Volume.Measure

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Norm determinant of a linear map

Given a rectangular matrix $T$, it is common to talk about $\sqrt{det(T^{H}T)}$, where $T^{H}$ is
the conjugate transpose of $T$, as a generalization to the determinant of a square matrix. It is the
$m$-dimensional volume factor for linear maps $\mathbb{R}^m \to \mathbb{R}^n$. It is given various
names in the literature:
* "Jacobian" (definition 3.4 of [lawrenceronald2025]), in the context of volume factor
  for a non-linear map. However, we choose to reserve this name for the matrix consisting of
  derivatives.
* "Gram determinant", which is already used by `Matrix.gram`, and it is often referring to
  $det(T^{H}T)$ without the square root.
* "Nonnegative determinant" (definition 1 of [haruoyoshiohidetoki2006]).

Without a standardized name, we give a descriptive name `LinearMap.normDet` to reflect its
definition and show that it is a generalization of `‖(f : LinearMap 𝕜 U U).det‖`
(See `LinearMap.normDet_eq_norm_det`). We also construct this on linear maps between inner product
spaces instead of matrices, and allow the codomain to have infinite dimension.

## Main definition
* `LinearMap.normDet` : the norm determinant of a linear map.

## Main result
* `ContinuousLinearMap.normDet_sq` and `LinearMap.normDet_sq`: The square of `f.normDet`
  equals to the determinant of `f.adjoint ∘ₗ f`.
* `LinearMap.normDet_sq_eq_det_gram`: The square of `LinearMap.normDet` equals to the determinant of
  the Gram matrix formed by vectors mapped from an orthonormal basis.
* `LinearMap.normDet_eq_prod_singularValues`: `LinearMap.normDet` equals to the product of singular
  values.
* `LinearMap.hausdorffMeasure_image`: `LinearMap.normDet` is the volume factor for Hausdorff
  measure.

-/

public section

open Module

namespace LinearMap

variable {𝕜 U V W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [FiniteDimensional 𝕜 U] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W]

open Classical in
/--
The norm determinant of a linear map `f : U →ₗ[𝕜] V` is defined as the norm of the determinant of
the square matrix representing the linear map `U →ₗ[𝕜] f.range` over a pair of orthonormal basis of
equal dimensions.
(See `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict` for using arbitrary orthonormal basis)

If such basis doesn't exist (e.g. the map is not injective), the norm determinant is zero.
(See `LinearMap.normDet_eq_zero_iff_ker_ne_bot`)
-/
/-
**LinearMap.normDet** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：normDet (f : U ->ₗ[𝕜] V) : Real
参数：f : U ->ₗ[𝕜] V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm determinant of a linear map `f : U →ₗ[𝕜] V` is defined as the norm of t
he determinant of
the square matrix representing the linear map `U →ₗ[𝕜] f.range` over a pair of o
rthonormal basis of
equal dimensions.
(See `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict` for using arbitrary 
orthonormal basis)

If such basis doesn't exist (e.g. the map is not injective), the norm determinan
t is zero.
(See `LinearMap.normDet_eq_zero_iff_ker_ne_bot`)
-/
noncomputable def normDet (f : U →ₗ[𝕜] V) : ℝ :=
  if h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) then
    ‖(f.rangeRestrict.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis h.some.toBasis).det‖
  else
    0
/-
**LinearMap.normDet_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_nonneg (f : U ->ₗ[𝕜] V) : 0 <= f.normDet
参数：f : U ->ₗ[𝕜] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem normDet_nonneg (f : U →ₗ[𝕜] V) : 0 ≤ f.normDet := by
  unfold normDet
  split <;> simp

/--
`LinearMap.normDet` is well-defined under any pair of orthonormal basis.
-/
/-
**LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
形式化陈述：normDet_eq_norm_det_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [Decida
bleEq ι] (f : U ->ₗ[𝕜] V) (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι
 𝕜 f.range) : f.normDet = ‖(f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det‖
参数：f : U ->ₗ[𝕜] V；bu : OrthonormalBasis ι 𝕜 U；bv : OrthonormalBasis ι 𝕜 f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_nat_card_basis`：finrank_eq_nat_card_basis (h : Basis ι
 R M) : finrank R M = Nat.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`：basis_toMatrix
_mul_linearMap_toMatrix_mul_basis_toMatrix [Fintype κ'] [DecidableEq ι] [Decidab
leEq ι'] : c.toMatrix c' * LinearMap.toMatrix …
· 使用定理 `Module.Basis.toMatrix_mul_toMatrix_flip`：toMatrix_mul_toMatrix_flip [Dec
idableEq ι] [Fintype ι'] : b.toMatrix b' * b'.toMatrix b = 1
· 使用定理 `Matrix.det_comm'`：det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix 
n m A} {N : Matrix m n A} {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M
 = 1) …
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `CStarRing.norm_of_mem_unitary`：norm_of_mem_unitary [Nontrivial E] {U : E
} (hU : U in unitary E) : ‖U‖ = 1
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Matrix.det_of_mem_unitary`：det_of_mem_unitary {A : Matrix n n α} (hA : A
 in Matrix.unitaryGroup n α) : A.det in unitary α
· 使用定理 `Matrix.mem_unitaryGroup_iff`：mem_unitaryGroup_iff : A in Matrix.unitaryG
roup n α ↔ A * star A = 1
· 使用定理 `Matrix.star_eq_conjTranspose`：star_eq_conjTranspose [Star α] (M : Matrix
 m m α) : star M = Mᴴ
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose`：Ortho
normalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose [Fintype ι'] (a : O
rthonormalBasis ι 𝕜 E) (b : OrthonormalBasis ι' 𝕜 E) : …
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
`LinearMap.normDet` is well-defined under any pair of orthonormal basis.
-/
theorem normDet_eq_norm_det_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : U →ₗ[𝕜] V) (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 f.range) :
    f.normDet = ‖(f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det‖ := by
  have hrank : finrank 𝕜 U = finrank 𝕜 f.range := by
    rw [finrank_eq_nat_card_basis bu.toBasis, finrank_eq_nat_card_basis bv.toBasis]
  have h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) := by
    rw [hrank]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  simp only [normDet, h, ↓reduceDIte]
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (stdOrthonormalBasis 𝕜 U).toBasis
    bu.toBasis h.some.toBasis bv.toBasis]
  have h1 : bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis = 1 :=
    Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis *
      bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis = 1 :=
    Basis.toMatrix_mul_toMatrix_flip _ _
  rw [← Matrix.det_comm' h1 h2, ← Matrix.mul_assoc, Matrix.det_mul, norm_mul]
  suffices ‖(bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      h.some.toBasis.toMatrix ⇑bv.toBasis).det‖ = 1 by
    rw [this, one_mul]
  refine CStarRing.norm_of_mem_unitary <| Matrix.det_of_mem_unitary ?_
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc, Matrix.mul_assoc (bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis)]
  simp

/--
`LinearMap.normDet` vanishes iff the map is not injective.
-/
/-
**LinearMap.normDet_eq_zero_iff_ker_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：normDet_eq_zero_iff_ker_ne_bot {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ f.ker !=
 ⊥ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.surjective_rangeRestrict`：surjective_rangeRestrict : Surjectiv
e f.rangeRestrict
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict`：normDet_eq_norm_de
t_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V
) (bu : OrthonormalBasis ι 𝕜 U) (bv : Orth…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `LinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (A : E ->ₗ[𝕜] F) 
: (A.adjoint ∘ₗ A).ker = A.ker
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用引理 `LinearMap.toMatrix_adjoint`：LinearMap.toMatrix_adjoint (f : E ->ₗ[𝕜] F) 
: toMatrix v₂.toBasis v₁.toBasis (adjoint f) = (toMatrix v₁.toBasis v₂.toBasis f
)ᴴ
· 使用定理 `Matrix.det_conjTranspose`：det_conjTranspose [StarRing R] (M : Matrix m m
 R) : det Mᴴ = star (det M)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
`LinearMap.normDet` vanishes iff the map is not injective.
-/
theorem normDet_eq_zero_iff_ker_ne_bot {f : U →ₗ[𝕜] V} :
    f.normDet = 0 ↔ f.ker ≠ ⊥ where
  mp h := by
    contrapose h
    let g : U ≃ₗ[𝕜] f.range := LinearEquiv.ofBijective f.rangeRestrict
      ⟨by simpa using ker_eq_bot.mp h, f.surjective_rangeRestrict⟩
    let bu := stdOrthonormalBasis 𝕜 U
    let bv := g.finrank_eq.symm ▸ stdOrthonormalBasis 𝕜 f.range
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv, norm_eq_zero.not]
    suffices (f.rangeRestrict.adjoint.toMatrix bv.toBasis bu.toBasis).det *
        (f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det ≠ 0 by
      simpa [toMatrix_adjoint, Matrix.det_conjTranspose] using this
    simpa [← Matrix.det_mul, ← LinearMap.toMatrix_comp, det_eq_zero_iff_ker_ne_bot,
      LinearMap.ker_adjoint_comp_self] using h
  mpr h := by
    suffices ¬ Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) by
      simp [normDet, this]
    contrapose h
    obtain ⟨b⟩ := h
    have hrank : finrank 𝕜 f.range = finrank 𝕜 U := by
      simpa using finrank_eq_card_basis b.toBasis
    simpa [hrank] using f.finrank_range_add_finrank_ker
/-
**LinearMap.normDet_eq_zero_iff_rank_range_ne** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：normDet_eq_zero_iff_rank_range_ne {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ finra
nk 𝕜 f.range != finrank 𝕜 U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem normDet_eq_zero_iff_rank_range_ne {f : U →ₗ[𝕜] V} :
    f.normDet = 0 ↔ finrank 𝕜 f.range ≠ finrank 𝕜 U := by
  simp [normDet_eq_zero_iff_ker_ne_bot, ← f.finrank_range_add_finrank_ker]
/-
**LinearMap.normDet_ne_zero_tfae** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_ne_zero_tfae (f : U ->ₗ[𝕜] V) : List.TFAE [f.normDet != 0, f.ker =
 ⊥, finrank 𝕜 f.range = finrank 𝕜 U, Nonempty (OrthonormalBasis (Fin (finrank 𝕜 
U)) 𝕜 f.range), Function.Injective f]
参数：f : U ->ₗ[𝕜] V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `LinearMap.normDet_eq_zero_iff_ker_ne_bot`：normDet_eq_zero_iff_ker_ne_bot
 {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ f.ker != ⊥ where mp h
· 使用定理 `LinearMap.normDet_eq_zero_iff_rank_range_ne`：normDet_eq_zero_iff_rank_ra
nge_ne {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ finrank 𝕜 f.range != finrank 𝕜 U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem normDet_ne_zero_tfae (f : U →ₗ[𝕜] V) :
    List.TFAE [f.normDet ≠ 0,
      f.ker = ⊥,
      finrank 𝕜 f.range = finrank 𝕜 U,
      Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range),
      Function.Injective f] := by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot.not_left
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne.not_left
  tfae_have 3 → 4 := by
    intro h
    rw [← h]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  tfae_have 4 → 3 := by
    rintro ⟨b⟩
    simpa using Module.finrank_eq_card_basis b.toBasis
  tfae_have 2 ↔ 5 := ker_eq_bot
  tfae_finish
/-
**LinearMap.orthonormalBasis_range** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def orthonormalBasis_range {ι : Type*} [Fintype ι] {f : U →ₗ[𝕜] V}
    (hf : f.ker = ⊥) (b : OrthonormalBasis ι 𝕜 U) : OrthonormalBasis ι 𝕜 f.range :=
  let h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) :=
    (f.normDet_ne_zero_tfae.out 1 3).mp hf
  h.some.reindex (Fintype.equivFinOfCardEq <| (Module.finrank_eq_card_basis b.toBasis).symm).symm
/-
**LinearMap.normDet_eq_zero_tfae** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_eq_zero_tfae (f : U ->ₗ[𝕜] V) : List.TFAE [f.normDet = 0, f.ker !=
 ⊥, finrank 𝕜 f.range != finrank 𝕜 U, finrank 𝕜 f.range < finrank 𝕜 U, IsEmpty (
OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range), ¬Function.Injective f]
参数：f : U ->ₗ[𝕜] V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.normDet_eq_zero_iff_ker_ne_bot`：normDet_eq_zero_iff_ker_ne_bot
 {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ f.ker != ⊥ where mp h
· 使用定理 `LinearMap.normDet_eq_zero_iff_rank_range_ne`：normDet_eq_zero_iff_rank_ra
nge_ne {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ finrank 𝕜 f.range != finrank 𝕜 U
· 使用定理 `LinearMap.finrank_range_le`：LinearMap.finrank_range_le [Module.Finite R 
M] (f : M ->ₗ[R] M') : finrank R (LinearMap.range f) <= finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `LinearMap.normDet_ne_zero_tfae`：normDet_ne_zero_tfae (f : U ->ₗ[𝕜] V) : 
List.TFAE [f.normDet != 0, f.ker = ⊥, finrank 𝕜 f.range = finrank 𝕜 U, Nonempty 
(OrthonormalBasis (F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem normDet_eq_zero_tfae (f : U →ₗ[𝕜] V) :
    List.TFAE [f.normDet = 0,
      f.ker ≠ ⊥,
      finrank 𝕜 f.range ≠ finrank 𝕜 U,
      finrank 𝕜 f.range < finrank 𝕜 U,
      IsEmpty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range),
      ¬Function.Injective f] := by
  tfae_have 1 ↔ 2 := f.normDet_eq_zero_iff_ker_ne_bot
  tfae_have 1 ↔ 3 := f.normDet_eq_zero_iff_rank_range_ne
  tfae_have 3 ↔ 4 := by simpa using finrank_range_le f
  tfae_have 3 ↔ 5 := by
    have h := (f.normDet_ne_zero_tfae.out 2 3).not
    simpa using h
  tfae_have 2 ↔ 6 := ker_eq_bot.not
  tfae_finish

/--
`LinearMap.normDet` can be calculated with any pair of orthonormal basis if the domain and the
codomain have equal dimension.
-/
/-
**LinearMap.normDet_eq_norm_det_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_eq_norm_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (f : 
U ->ₗ[𝕜] V) (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 V) : f.norm
Det = ‖(f.toMatrix bu.toBasis bv.toBasis).det‖
参数：f : U ->ₗ[𝕜] V；bu : OrthonormalBasis ι 𝕜 U；bv : OrthonormalBasis ι 𝕜 V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict`：normDet_eq_norm_de
t_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V
) (bu : OrthonormalBasis ι 𝕜 U) (bv : Orth…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.normDet_eq_zero_iff_rank_range_ne`：normDet_eq_zero_iff_rank_ra
nge_ne {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ finrank 𝕜 f.range != finrank 𝕜 U
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N

--- 原说明 ---
`LinearMap.normDet` can be calculated with any pair of orthonormal basis if the 
domain and the
codomain have equal dimension.
-/
theorem normDet_eq_norm_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U →ₗ[𝕜] V)
    (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 V) :
    f.normDet = ‖(f.toMatrix bu.toBasis bv.toBasis).det‖ := by
  have : FiniteDimensional 𝕜 V := bv.toBasis.finiteDimensional_of_finite
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · have h : f.range = ⊤ := by
      apply Submodule.eq_of_le_of_finrank_le le_top
      simp [finrank_eq_card_basis bv.toBasis, ← hrank, finrank_eq_card_basis bu.toBasis]
    let bv' : OrthonormalBasis ι 𝕜 f.range := bv.map (LinearIsometryEquiv.ofTop _ _ h).symm
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv']
    rfl
  · symm
    rw [normDet_eq_zero_iff_rank_range_ne.mpr hrank.symm]
    contrapose hrank with hdet
    have h : IsUnit ((f.toMatrix bu.toBasis bv.toBasis).det) := by
      simpa using hdet
    let f' := LinearEquiv.ofIsUnitDet h
    have hf : f.range = ⊤ := f'.range
    rw [hf]
    simpa using f'.finrank_eq

/--
`LinearMap.normDet` equals the norm of `LinearMap.det` for an endomorphism.
-/
/-
**LinearMap.normDet_eq_norm_det** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_eq_norm_det (f : U ->ₗ[𝕜] U) : f.normDet = ‖f.det‖
参数：f : U ->ₗ[𝕜] U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.normDet_eq_norm_det_toMatrix`：normDet_eq_norm_det_toMatrix {ι 
: Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V) (bu : OrthonormalBasis ι 𝕜
 U) (bv : OrthonormalBasis ι…
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`LinearMap.normDet` equals the norm of `LinearMap.det` for an endomorphism.
-/
theorem normDet_eq_norm_det (f : U →ₗ[𝕜] U) : f.normDet = ‖f.det‖ := by
  simp [f.normDet_eq_norm_det_toMatrix (stdOrthonormalBasis 𝕜 U) (stdOrthonormalBasis 𝕜 U)]

/--
`LinearMap.normDet` of a linear isometry is 1.
-/
@[simp]
/-
**LinearMap._root_.LinearIsometry.normDet_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.normDet` of a linear isometry is 1.
-/
theorem _root_.LinearIsometry.normDet_eq_one (f : U →ₗᵢ[𝕜] V) : f.toLinearMap.normDet = 1 := by
  obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 4 3).mp f.injective
  rw [normDet_eq_norm_det_toMatrix_rangeRestrict _ (stdOrthonormalBasis 𝕜 U) b]
  apply CStarRing.norm_of_mem_unitary
  exact Matrix.det_of_mem_unitary <| (f.equivRange).toMatrix_mem_unitaryGroup _ _

@[simp]
/-
**LinearMap.normDet_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_id : (id : U ->ₗ[𝕜] U).normDet = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.normDet_eq_one`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Type
 u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProduct
Space 𝕜 U] [inst_3 …
-/
theorem normDet_id : (id : U →ₗ[𝕜] U).normDet = 1 :=
  LinearIsometry.id.normDet_eq_one

@[simp]
/-
**LinearMap.normDet_subtype** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_subtype (p : Submodule 𝕜 U) : p.subtype.normDet = 1
参数：p : Submodule 𝕜 U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.normDet_eq_one`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Type
 u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProduct
Space 𝕜 U] [inst_3 …
-/
theorem normDet_subtype (p : Submodule 𝕜 U) : p.subtype.normDet = 1 :=
  p.subtypeₗᵢ.normDet_eq_one

@[simp]
/-
**LinearMap.normDet_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_of_subsingleton [Subsingleton U] (f : U ->ₗ[𝕜] V) : f.normDet = 1
参数：f : U ->ₗ[𝕜] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton p
] : p = ⊥
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_zero_iff`：Module.finrank_zero_iff [IsDomain R] [IsTorsion
Free R M] : finrank R M = 0 ↔ Subsingleton M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict`：normDet_eq_norm_de
t_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V
) (bu : OrthonormalBasis ι 𝕜 U) (bv : Orth…
· 使用定理 `Matrix.det_fin_zero`：det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A
 = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normDet_of_subsingleton [Subsingleton U] (f : U →ₗ[𝕜] V) : f.normDet = 1 := by
  have h : f.ker = ⊥ := Submodule.eq_bot_of_subsingleton
  have hrank : finrank 𝕜 U = 0 := finrank_zero_iff.mpr ‹_›
  let bu : OrthonormalBasis (Fin 0) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (by rw [hrank])
  let bv := orthonormalBasis_range h bu
  simp [normDet_eq_norm_det_toMatrix_rangeRestrict f bu bv]

@[simp]
/-
**LinearMap.normDet_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_zero : (0 : U ->ₗ[𝕜] V).normDet = 0 ^ finrank 𝕜 U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.normDet_of_subsingleton`：normDet_of_subsingleton [Subsingleton
 U] (f : U ->ₗ[𝕜] V) : f.normDet = 1
· 使用定理 `Module.finrank_eq_zero_of_subsingleton`：finrank_eq_zero_of_subsingleton 
[Module.Free R M] [Subsingleton M] : Module.finrank R M = 0
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem normDet_zero : (0 : U →ₗ[𝕜] V).normDet = 0 ^ finrank 𝕜 U := by
  nontriviality U
  simp [zero_pow finrank_pos.ne.symm, normDet_eq_zero_iff_ker_ne_bot]

@[simp]
/-
**LinearMap.normDet_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_smul (f : U ->ₗ[𝕜] V) (c : 𝕜) : (c • f).normDet = ‖c‖ ^ finrank 𝕜 
U * f.normDet
参数：f : U ->ₗ[𝕜] V；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.normDet_of_subsingleton`：normDet_of_subsingleton [Subsingleton
 U] (f : U ->ₗ[𝕜] V) : f.normDet = 1
· 使用定理 `Module.finrank_eq_zero_of_subsingleton`：finrank_eq_zero_of_subsingleton 
[Module.Free R M] [Subsingleton M] : Module.finrank R M = 0
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.normDet.congr_simp`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Type 
u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProductS
pace 𝕜 U] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `LinearMap.normDet_zero`：normDet_zero : (0 : U ->ₗ[𝕜] V).normDet = 0 ^ fi
nrank 𝕜 U
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `LinearMap.normDet_ne_zero_tfae`：normDet_ne_zero_tfae (f : U ->ₗ[𝕜] V) : 
List.TFAE [f.normDet != 0, f.ker = ⊥, finrank 𝕜 f.range = finrank 𝕜 U, Nonempty 
(OrthonormalBasis (F…
（共 48 条，此处仅展示前 30 条）
-/
theorem normDet_smul (f : U →ₗ[𝕜] V) (c : 𝕜) :
    (c • f).normDet = ‖c‖ ^ finrank 𝕜 U * f.normDet := by
  by_cases hc : c = 0
  · nontriviality U
    simp [hc, zero_pow finrank_pos.ne.symm]
  by_cases h : f.ker = ⊥
  · obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    let bv' : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (c • f).range := bv.map
      (LinearIsometryEquiv.ofEq _ _ (LinearMap.range_smul _ _ hc).symm)
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv,
      (c • f).normDet_eq_norm_det_toMatrix_rangeRestrict bu bv', ← norm_pow, ← norm_mul]
    have : finrank 𝕜 U = Fintype.card (Fin (finrank 𝕜 U)) := by simp
    conv in c ^ finrank 𝕜 U => rw [this]
    rw [← Matrix.det_smul, ← map_smul]
    rfl
  · have h' : (c • f).ker ≠ ⊥ := by simpa [f.ker_smul _ hc] using h
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr h, normDet_eq_zero_iff_ker_ne_bot.mpr h']

@[simp]
/-
**LinearMap.normDet_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_neg (f : U ->ₗ[𝕜] V) : (-f).normDet = f.normDet
参数：f : U ->ₗ[𝕜] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.normDet.congr_simp`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Type 
u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProductS
pace 𝕜 U] [inst_3 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LinearMap.normDet_smul`：normDet_smul (f : U ->ₗ[𝕜] V) (c : 𝕜) : (c • f).
normDet = ‖c‖ ^ finrank 𝕜 U * f.normDet
-/
theorem normDet_neg (f : U →ₗ[𝕜] V) : (-f).normDet = f.normDet := by
  simpa using f.normDet_smul (-1)

/--
The square of `f.normDet` equals the determinant of `f.adjoint ∘L f`.
-/
/-
**LinearMap._root_.ContinuousLinearMap.normDet_sq** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The square of `f.normDet` equals the determinant of `f.adjoint ∘L f`.
-/
theorem _root_.ContinuousLinearMap.normDet_sq [CompleteSpace V] (f : U →L[𝕜] V) :
    haveI : CompleteSpace U := FiniteDimensional.complete 𝕜 U
    ↑(f.normDet ^ 2) = (f.adjoint ∘L f).det := by
  have : CompleteSpace U := FiniteDimensional.complete 𝕜 U
  have : CompleteSpace f.range := FiniteDimensional.complete 𝕜 f.range
  let bu := stdOrthonormalBasis 𝕜 U
  by_cases h : f.ker = ⊥
  · obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    have hf : f = f.range.subtypeₗᵢ.toContinuousLinearMap ∘L f.rangeRestrict := rfl
    conv_rhs => rw [hf]
    rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _),
      f.range.subtypeₗᵢ.adjoint_comp_self, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, ← det_toMatrix bu.toBasis,
      toMatrix_comp bu.toBasis b.toBasis bu.toBasis, ← ContinuousLinearMap.adjoint_toLinearMap,
      toMatrix_adjoint, f.toLinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict bu b]
    simp [RCLike.conj_mul]
  · trans 0
    · simp [show f.normDet = 0 from (f.normDet_eq_zero_tfae.out 1 0).mp h]
    symm
    rw [det_eq_zero_iff_ker_ne_bot, ContinuousLinearMap.ker_adjoint_comp_self]
    exact h

/--
The square of `f.normDet` equals the determinant of `f.adjoint ∘ₗ f` when the codomain is finite
dimensional.
-/
/-
**LinearMap.normDet_sq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_sq [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) : ↑(f.normDet ^ 2) = (
f.adjoint ∘ₗ f).det
参数：f : U ->ₗ[𝕜] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.normDet_sq`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Typ
e u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProduc
tSpace 𝕜 U] [inst_3 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
The square of `f.normDet` equals the determinant of `f.adjoint ∘ₗ f` when the co
domain is finite
dimensional.
-/
theorem normDet_sq [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) :
    ↑(f.normDet ^ 2) = (f.adjoint ∘ₗ f).det := by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  exact f.toContinuousLinearMap.normDet_sq

/--
The square of `f.normDet` equals the determinant of the Gram matrix formed by vectors mapped from
an orthonormal basis.
-/
/-
**LinearMap.normDet_sq_eq_det_gram** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_sq_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[
𝕜] V) (b : OrthonormalBasis ι 𝕜 U) : ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f <| b ·
)).det
参数：f : U ->ₗ[𝕜] V；b : OrthonormalBasis ι 𝕜 U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.gram_eq_conjTranspose_mul`：gram_eq_conjTranspose_mul {ι : Type*} 
[Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n -> E) : letI m
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_conjTranspose`：det_conjTranspose [StarRing R] (M : Matrix m m
 R) : det Mᴴ = star (det M)
· 使用定理 `RCLike.star_def`：star_def : (Star.star : K -> K) = conj
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict`：normDet_eq_norm_de
t_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V
) (bu : OrthonormalBasis ι 𝕜 U) (bv : Orth…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `LinearMap.normDet_eq_zero_tfae`：normDet_eq_zero_tfae (f : U ->ₗ[𝕜] V) : 
List.TFAE [f.normDet = 0, f.ker != ⊥, finrank 𝕜 f.range != finrank 𝕜 U, finrank 
𝕜 f.range < finrank …
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The square of `f.normDet` equals the determinant of the Gram matrix formed by ve
ctors mapped from
an orthonormal basis.
-/
theorem normDet_sq_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U →ₗ[𝕜] V)
    (b : OrthonormalBasis ι 𝕜 U) :
    ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f <| b ·)).det := by
  suffices ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f.rangeRestrict <| b ·)).det by
    simpa
  by_cases h : f.ker = ⊥
  · let bv := orthonormalBasis_range h b
    rw [Matrix.gram_eq_conjTranspose_mul bv, Matrix.det_mul, Matrix.det_conjTranspose]
    rw [RCLike.star_def, RCLike.conj_mul, f.normDet_eq_norm_det_toMatrix_rangeRestrict b bv]
    simp only [map_pow]
    congr
    ext i j
    simp [LinearMap.toMatrix_apply]
  · trans 0
    · simp [show f.normDet = 0 from (f.normDet_eq_zero_tfae.out 1 0).mp h]
    have hrank := (f.normDet_eq_zero_tfae.out 1 3).mp h
    symm
    contrapose! hrank with h0
    rw [finrank_eq_card_basis b.toBasis]
    exact (Matrix.linearIndependent_of_det_gram_ne_zero h0).fintype_card_le_finrank
/-
**LinearMap.normDet_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_comp (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W) : (g ∘ₗ f).normDet = (g.dom
Restrict f.range).normDet * f.normDet
参数：f : U ->ₗ[𝕜] V；g : V ->ₗ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `LinearMap.normDet_ne_zero_tfae`：normDet_ne_zero_tfae (f : U ->ₗ[𝕜] V) : 
List.TFAE [f.normDet != 0, f.ker = ⊥, finrank 𝕜 f.range = finrank 𝕜 U, Nonempty 
(OrthonormalBasis (F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `LinearMap.range_domRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict`：normDet_eq_norm_de
t_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ->ₗ[𝕜] V
) (bu : OrthonormalBasis ι 𝕜 U) (bv : Orth…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `LinearMap.ker_rangeRestrict`：ker_rangeRestrict : ker f.rangeRestrict = k
er f
· 使用定理 `LinearMap.ker_comp_of_ker_eq_bot`：ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂
] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) : ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) =
 ker f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.normDet_eq_zero_iff_ker_ne_bot`：normDet_eq_zero_iff_ker_ne_bot
 {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ f.ker != ⊥ where mp h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LinearMap.ker_le_ker_comp`：ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ 
->ₛₗ[τ₂₃] M₃) : ker f <= ker (g.comp f : M ->ₛₗ[τ₁₃] M₃)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem normDet_comp (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W) :
    (g ∘ₗ f).normDet = (g.domRestrict f.range).normDet * f.normDet := by
  by_cases hf : f.ker = ⊥
  · let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp hf
    by_cases hgf : (g ∘ₗ f).ker = ⊥
    · obtain ⟨bw⟩ := ((g ∘ₗ f).normDet_ne_zero_tfae.out 1 3).mp hgf
      let bw' : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (g.domRestrict f.range).range :=
        bw.map (LinearIsometryEquiv.ofEq _ _ (by simp [LinearMap.range_comp]))
      rw [(g ∘ₗ f).normDet_eq_norm_det_toMatrix_rangeRestrict bu bw,
        f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv,
        (g.domRestrict f.range).normDet_eq_norm_det_toMatrix_rangeRestrict bv bw']
      rw [← norm_mul, ← Matrix.det_mul, ← LinearMap.toMatrix_comp]
      rfl
    · have hg : (g.domRestrict f.range).ker ≠ ⊥ := by
        contrapose hf with hgf'
        rw [← LinearMap.ker_rangeRestrict, ← LinearMap.ker_comp_of_ker_eq_bot _ hgf']
        exact hgf
      simp [normDet_eq_zero_iff_ker_ne_bot.mpr hgf, normDet_eq_zero_iff_ker_ne_bot.mpr hg]
  · have hgf : (g ∘ₗ f).ker ≠ ⊥ := by
      contrapose hf with hbot
      simpa [hbot] using ker_le_ker_comp f g
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr hf, normDet_eq_zero_iff_ker_ne_bot.mpr hgf]
/-
**LinearMap.normDet_comp_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_comp_of_finrank_eq [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) (g : V
 ->ₗ[𝕜] W) (h : finrank 𝕜 U = finrank 𝕜 V) : (g ∘ₗ f).normDet = g.normDet * f.no
rmDet
参数：f : U ->ₗ[𝕜] V；g : V ->ₗ[𝕜] W；h : finrank 𝕜 U = finrank 𝕜 V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.normDet_comp`：normDet_comp (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W) :
 (g ∘ₗ f).normDet = (g.domRestrict f.range).normDet * f.normDet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.normDet_id`：normDet_id : (id : U ->ₗ[𝕜] U).normDet = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank`：ker_eq_bot_
iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensiona
l K V₂] (H : finrank K V = finrank K V₂) {f : V -…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LinearMap.ker_le_ker_comp`：ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ 
->ₛₗ[τ₂₃] M₃) : ker f <= ker (g.comp f : M ->ₛₗ[τ₁₃] M₃)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.normDet_eq_zero_iff_ker_ne_bot`：normDet_eq_zero_iff_ker_ne_bot
 {f : U ->ₗ[𝕜] V} : f.normDet = 0 ↔ f.ker != ⊥ where mp h
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem normDet_comp_of_finrank_eq [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W)
    (h : finrank 𝕜 U = finrank 𝕜 V) :
    (g ∘ₗ f).normDet = g.normDet * f.normDet := by
  by_cases htop : f.range = ⊤
  · rw [normDet_comp]
    congrm ?_ * _
    suffices (g.domRestrict f.range).normDet * (id : V →ₗ[𝕜] V).normDet = g.normDet by simpa
    have : f.range = id.range := by simp [htop]
    convert! (normDet_comp LinearMap.id g).symm
  · have hker : f.ker ≠ ⊥ := by
      simpa [ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank h] using htop
    have hker' : (g ∘ₗ f).ker ≠ ⊥ := by
      contrapose hker with hbot
      simpa [hbot] using ker_le_ker_comp f g
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr hker, normDet_eq_zero_iff_ker_ne_bot.mpr hker']

@[simp]
/-
**LinearMap.normDet_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_codRestrict {p : Submodule 𝕜 V} {f : U ->ₗ[𝕜] V} (h : forall c, f 
c in p) : (f.codRestrict p h).normDet = f.normDet
参数：h : forall c, f c in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.normDet_comp`：normDet_comp (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W) :
 (g ∘ₗ f).normDet = (g.domRestrict f.range).normDet * f.normDet
· 使用定理 `LinearIsometry.normDet_eq_one`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Type
 u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProduct
Space 𝕜 U] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normDet_codRestrict {p : Submodule 𝕜 V} {f : U →ₗ[𝕜] V} (h : ∀ c, f c ∈ p) :
    (f.codRestrict p h).normDet = f.normDet := by
  have : f = p.subtype ∘ₗ f.codRestrict p h := rfl
  conv_rhs => rw [this]
  rw [normDet_comp]
  have : (p.subtype.domRestrict (codRestrict p f h).range).normDet = 1 :=
    (p.subtypeₗᵢ.comp (codRestrict p f h).range.subtypeₗᵢ).normDet_eq_one
  simp [this]
/-
**LinearMap.normDet_eq_prod_singularValues** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：normDet_eq_prod_singularValues [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V) : 
f.normDet = ∏ i in Finset.range (finrank 𝕜 U), f.singularValues i
参数：f : U ->ₗ[𝕜] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LinearMap.normDet_nonneg`：normDet_nonneg (f : U ->ₗ[𝕜] V) : 0 <= f.normD
et
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LinearMap.singularValues_nonneg`：singularValues_nonneg (i : Nat) : 0 <= 
T.singularValues i
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `Fin.prod_univ_eq_prod_range`：Fin.prod_univ_eq_prod_range [CommMonoid α] 
(f : Nat -> α) (n : Nat) : ∏ i : Fin n, f i = ∏ i in range n, f i
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.normDet_sq`：normDet_sq [FiniteDimensional 𝕜 V] (f : U ->ₗ[𝕜] V
) : ↑(f.normDet ^ 2) = (f.adjoint ∘ₗ f).det
· 使用定理 `LinearMap.isSymmetric_adjoint_comp_self`：isSymmetric_adjoint_comp_self (
T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `LinearMap.sq_singularValues_fin`：sq_singularValues_fin {n : Nat} (hn : f
inrank 𝕜 E = n) (i : Fin n) : T.singularValues i ^ 2 = T.isSymmetric_adjoint_com
p_self.eigenvalues hn…
· 使用定理 `algebraMap.coe_prod`：coe_prod (a : ι -> R) : (↑(∏ i in s, a i : R) : A) 
= ∏ i in s, (↑(a i) : A)
· 使用定理 `LinearMap.IsSymmetric.det_eq_prod_eigenvalues`：det_eq_prod_eigenvalues (
hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : T.det = ∏ i, (hT.eigenvalues
 hn i : 𝕜)
-/
theorem normDet_eq_prod_singularValues [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) :
    f.normDet = ∏ i ∈ Finset.range (finrank 𝕜 U), f.singularValues i := by
  rw [← sq_eq_sq₀ f.normDet_nonneg (Finset.prod_nonneg fun i _ ↦ f.singularValues_nonneg i),
    ← RCLike.ofReal_inj (K := 𝕜), ← Finset.prod_pow, ← Fin.prod_univ_eq_prod_range, normDet_sq]
  simp_rw [sq_singularValues_fin]
  push_cast
  rw [← LinearMap.IsSymmetric.det_eq_prod_eigenvalues]

section Real

open MeasureTheory Measure

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-
**LinearMap.normDet_eq_abs_det** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：normDet_eq_abs_det (f : U ->ₗ[Real] U) : f.normDet = |f.det|
参数：f : U ->ₗ[Real] U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.normDet_eq_norm_det`：normDet_eq_norm_det (f : U ->ₗ[𝕜] U) : f.
normDet = ‖f.det‖
-/
theorem normDet_eq_abs_det (f : U →ₗ[ℝ] U) : f.normDet = |f.det| := by
  simpa using f.normDet_eq_norm_det

/--
Using Hausdorff measure with the domain dimension, the volume of the image is scaled by
`LinearMap.normDet`.
-/
/-
**LinearMap.hausdorffMeasure_image** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：hausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace
 V] [BorelSpace V] (f : U ->ₗ[Real] V) (s : Set U) : μH[finrank Real U] (f '' s)
 = ENNReal.ofReal f.normDet * μH[finrank Real U] s
参数：f : U ->ₗ[Real] V；s : Set U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `LinearMap.normDet_ne_zero_tfae`：normDet_ne_zero_tfae (f : U ->ₗ[𝕜] V) : 
List.TFAE [f.normDet != 0, f.ker = ⊥, finrank 𝕜 f.range = finrank 𝕜 U, Nonempty 
(OrthonormalBasis (F…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Isometry.hausdorffMeasure_image`：hausdorffMeasure_image (hf : Isometry f
) (hd : 0 <= d ∨ Surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.Measure.addHaar_image_linearMap`：addHaar_image_linearMap (
f : E ->ₗ[Real] E) (s : Set E) : μ (f '' s) = ENNReal.ofReal |LinearMap.det f| *
 μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.normDet_eq_abs_det`：normDet_eq_abs_det (f : U ->ₗ[Real] U) : f
.normDet = |f.det|
· 使用定理 `LinearMap.normDet_comp_of_finrank_eq`：normDet_comp_of_finrank_eq [Finite
Dimensional 𝕜 V] (f : U ->ₗ[𝕜] V) (g : V ->ₗ[𝕜] W) (h : finrank 𝕜 U = finrank 𝕜 
V) : (g ∘ₗ f).normDet = g.…
· 使用定理 `LinearIsometry.normDet_eq_one`：∀ {𝕜 : Type u_1} {U : Type u_2} {V : Type
 u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup U]   [inst_2 : InnerProduct
Space 𝕜 U] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.normDet_codRestrict`：normDet_codRestrict {p : Submodule 𝕜 V} {
f : U ->ₗ[𝕜] V} (h : forall c, f c in p) : (f.codRestrict p h).normDet = f.normD
et
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LinearMap.normDet_eq_zero_tfae`：normDet_eq_zero_tfae (f : U ->ₗ[𝕜] V) : 
List.TFAE [f.normDet = 0, f.ker != ⊥, finrank 𝕜 f.range != finrank 𝕜 U, finrank 
𝕜 f.range < finrank …
· 使用引理 `Real.hausdorffMeasure_of_finrank_lt`：hausdorffMeasure_of_finrank_lt [Mea
surableSpace E] [BorelSpace E] {d : Real} (hd : finrank Real E < d) : (μH[d] : M
easure E) = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Using Hausdorff measure with the domain dimension, the volume of the image is sc
aled by
`LinearMap.normDet`.
-/
theorem hausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    (f : U →ₗ[ℝ] V) (s : Set U) :
    μH[finrank ℝ U] (f '' s) = ENNReal.ofReal f.normDet * μH[finrank ℝ U] s := by
  by_cases h : f.ker = ⊥
  · have hrank : finrank ℝ ↥f.range = finrank ℝ U := (f.normDet_ne_zero_tfae.out 1 2).mp h
    obtain ⟨bv⟩ := (f.normDet_ne_zero_tfae.out 1 3).mp h
    let g : U ≃ₗᵢ[ℝ] f.range := (stdOrthonormalBasis ℝ U).equiv bv (Equiv.refl _)
    suffices μH[finrank ℝ U] ((f.range.subtypeₗᵢ.comp g.toLinearIsometry) ''
        ((g.symm.toLinearIsometry.toLinearMap ∘ₗ f.rangeRestrict) '' s)) =
        ENNReal.ofReal f.normDet * μH[finrank ℝ U] s by
      simpa [Set.image_image]
    rw [(LinearIsometry.isometry _).hausdorffMeasure_image (by simp),
      addHaar_image_linearMap μH[finrank ℝ U], ← normDet_eq_abs_det,
      normDet_comp_of_finrank_eq _ _ hrank.symm, g.symm.toLinearIsometry.normDet_eq_one]
    simp
  · suffices μH[finrank ℝ U] (f.range.subtypeₗᵢ '' (f.rangeRestrict '' s)) = 0 by
      simpa [(f.normDet_eq_zero_tfae.out 1 0).mp h, Set.image_image]
    rw [(LinearIsometry.isometry _).hausdorffMeasure_image (by simp)]
    have h : (finrank ℝ f.range : ℝ) < finrank ℝ U := by
      exact_mod_cast (f.normDet_eq_zero_tfae.out 1 3).mp h
    simp [Real.hausdorffMeasure_of_finrank_lt h]

/--
Using Euclidean Hausdorff measure with the domain dimension, the volume of the image is scaled by
`LinearMap.normDet`.
-/
/-
**LinearMap.euclideanHausdorffMeasure_image** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：euclideanHausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [Measur
ableSpace V] [BorelSpace V] (f : U ->ₗ[Real] V) (s : Set U) : μHE[finrank Real U
] (f '' s) = ENNReal.ofReal f.normDet * μHE[finrank Real U] s
参数：f : U ->ₗ[Real] V；s : Set U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `LinearMap.hausdorffMeasure_image`：hausdorffMeasure_image [MeasurableSpac
e U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] (f : U ->ₗ[Real] V) (s : 
Set U) : μH[finrank Re…
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)

--- 原说明 ---
Using Euclidean Hausdorff measure with the domain dimension, the volume of the i
mage is scaled by
`LinearMap.normDet`.
-/
theorem euclideanHausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V] (f : U →ₗ[ℝ] V) (s : Set U) :
    μHE[finrank ℝ U] (f '' s) = ENNReal.ofReal f.normDet * μHE[finrank ℝ U] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply,
    hausdorffMeasure_image]
  exact mul_left_comm _ _ _

/--
The volume of the image measured by Euclidean Hausdorff measure is equal to the Lebesgue measure
scaled by `LinearMap.normDet`.
-/
/-
**LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume** 是 Mathlib 中的
一个定理，位于命名空间 `LinearMap`。
形式化陈述：euclideanHausdorffMeasure_image_eq_normDet_mul_volume [MeasurableSpace U] 
[BorelSpace U] [MeasurableSpace V] [BorelSpace V] (f : U ->ₗ[Real] V) (s : Set U
) : μHE[finrank Real U] (f '' s) = ENNReal.ofReal f.normDet * volume s
参数：f : U ->ₗ[Real] V；s : Set U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.euclideanHausdorffMeasure_image`：euclideanHausdorffMeasure_ima
ge [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] (f : U 
->ₗ[Real] V) (s : Set U) : μHE[…
· 使用定理 `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`：InnerProductSpace
.euclideanHausdorffMeasure_eq_volume : (μHE[finrank Real V] : Measure V) = volum
e

--- 原说明 ---
The volume of the image measured by Euclidean Hausdorff measure is equal to the 
Lebesgue measure
scaled by `LinearMap.normDet`.
-/
theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace V] [BorelSpace V] (f : U →ₗ[ℝ] V) (s : Set U) :
    μHE[finrank ℝ U] (f '' s) = ENNReal.ofReal f.normDet * volume s := by
  rw [f.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Real

end LinearMap

