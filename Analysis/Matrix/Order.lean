/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The partial order on matrices

This file constructs the partial order and star ordered instances on matrices on `𝕜`.
This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices given by `x ≤ y := (y - x).PosSemidef`.
* `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: for a positive semi-definite matrix `A`,
  we have `x⋆ A x = 0` iff `A x = 0`.
* `Matrix.toMatrixInnerProductSpace`: the inner product on matrices induced by a
  positive semi-definite matrix `M`: `⟪x, y⟫ = (y * M * xᴴ).trace`.

## Implementation notes

Note that the partial order instance is scoped to `MatrixOrder`.
Please `open scoped MatrixOrder` to use this.
-/

@[expose] public section

variable {𝕜 n : Type*} [RCLike 𝕜]

open scoped ComplexOrder
open Matrix

namespace Matrix

section PartialOrder

/-- The preorder on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
/-
**Matrix.instPreOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：instPreOrder : Preorder (Matrix n n 𝕜) where le A B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preorder on matrices given by `A ≤ B := (B - A).PosSemidef`.
-/
abbrev instPreOrder : Preorder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

open MatrixOrder
/-
**Matrix.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：le_iff {A B : Matrix n n 𝕜} : A <= B ↔ (B - A).PosSemidef
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff {A B : Matrix n n 𝕜} : A ≤ B ↔ (B - A).PosSemidef := Iff.rfl
/-
**Matrix.nonneg_iff_posSemidef** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 <= A ↔ A.PosSemidef
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.le_iff`：le_iff {A B : Matrix n n 𝕜} : A <= B ↔ (B - A).PosSemidef
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosSemidef.nonneg
/-
**Matrix.le_antisymm_aux** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le_antisymm_aux {A : Matrix n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef) :
    A = 0 := by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_add_rev, hdiag, ← h₁.1.apply j i, -RCLike.star_def] at *
  simpa using le_antisymm h2 h1

/-- The partial order on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
/-
**Matrix.instPartialOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：instPartialOrder : PartialOrder (Matrix n n 𝕜) where le_antisymm A B h₁ h₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order on matrices given by `A ≤ B := (B - A).PosSemidef`.
-/
abbrev instPartialOrder : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder
/-
**Matrix.instIsOrderedAddMonoid** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where add_le_ad
d_left _ _ _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.le_iff`：le_iff {A B : Matrix n n 𝕜} : A <= B ↔ (B - A).PosSemidef
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
-/
lemma instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

variable [Fintype n]
/-
**Matrix.instNonnegSpectrumClass** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：instNonnegSpectrumClass : NonnegSpectrumClass Real (Matrix n n 𝕜) where qu
asispectrum_nonneg_of_nonneg A hA
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matrix.LE.le.posSemidef`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 
𝕜] {A : Matrix n n 𝕜}, 0 ≤ A → A.PosSemidef
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`：spectrum_real_eq_
range_eigenvalues : spectrum Real A = Set.range hA.eigenvalues
· 使用引理 `Matrix.PosSemidef.eigenvalues_nonneg`：eigenvalues_nonneg [DecidableEq n]
 (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i
-/
lemma instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero ℝ A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
      hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x |>.mp hx
    exact hA.posSemidef.eigenvalues_nonneg _

scoped[MatrixOrder] attribute [instance] instNonnegSpectrumClass
/-
**Matrix.instStarOrderedRing** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StarOrderedRing.of_nonneg_iff'`：of_nonneg_iff' [NonUnitalRing R] [Partia
lOrder R] [StarRing R] (h_add : forall {x y : R}, x <= y -> forall z, z + x <= z
 + y) (h_nonneg_iff …
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Matrix.instIsOrderedAddMonoid`：instIsOrderedAddMonoid : IsOrderedAddMono
id (Matrix n n 𝕜) where add_le_add_left _ _ _ _
· 使用引理 `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts`：CFC.exists_s
qrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A] [St
arRing A] [TopologicalSpace A] [Module Real A] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用引理 `QuasispectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [Module Real A
] [IsScalarTower Real A A] [SMulCommClass Real A A] [PartialOrder A] [NonnegSpec
trumClass Real A] {a : A} (ha…
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Matrix.posSemidef_conjTranspose_mul_self`：posSemidef_conjTranspose_mul_s
elf [StarOrderedRing R] (A : Matrix m n R) : PosSemidef (Aᴴ * A)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
-/
lemma instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_right fun A ↦
    ⟨fun hA ↦ by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ rfl⟩,
    fun ⟨A, hA⟩ => hA ▸ (posSemidef_conjTranspose_mul_self A).nonneg⟩

scoped[MatrixOrder] attribute [instance] instStarOrderedRing

end PartialOrder

open scoped MatrixOrder

variable [Fintype n]

namespace PosSemidef

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

include hA

/-
**Matrix.PosSemidef.inv_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Matrix.instStarOrderedRing`：instStarOrderedRing : StarOrderedRing (Matri
x n n 𝕜)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `CFC.sqrt_eq_iff`：sqrt_eq_iff (a b : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `Matrix.PosSemidef.inv`：∀ {n : Type u_2} {R' : Type u_4} [inst : CommRing
 R'] [inst_1 : PartialOrder R'] [inst_2 : StarRing R']   [inst_3 : Fintype n] [i
nst_4 : Dec…
· 使用定理 `Matrix.LE.le.posSemidef`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 
𝕜] {A : Matrix n n 𝕜}, 0 ≤ A → A.PosSemidef
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Matrix.inv_pow'`：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
· 使用引理 `CFC.sq_sqrt`：sq_sqrt (a : A) (ha : 0 <= a
-/
lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  rw [eq_comm, CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg, ← sq,
    inv_pow', CFC.sq_sqrt A]

end sqrtDeprecated

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
/-
**Matrix.PosSemidef.dotProduct_mulVec_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
.PosSemidef`。
形式化陈述：dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n -
> 𝕜) : star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0
参数：hA : PosSemidef A；x : n -> 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CStarAlgebra.nonneg_iff_eq_star_mul_self`：∀ {A : Type u_1} [inst : Parti
alOrder A] [inst_1 : NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : St
arRing A]   [inst_4 : _root_.M…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Matrix.instStarOrderedRing`：instStarOrderedRing : StarOrderedRing (Matri
x n n 𝕜)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Matrix.vecMul_conjTranspose`：vecMul_conjTranspose [Fintype n] [StarRing 
α] (A : Matrix m n α) (x : n -> α) : x ᵥ* Aᴴ = star (A *ᵥ star x)
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Matrix.mulVec_zero`：mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0

--- 原说明 ---
For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`.
-/
theorem dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero] at h ⊢
  rw [h, mulVec_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
/-
**Matrix.PosSemidef.toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps v
ersion).
-/
theorem toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x
/-
**Matrix.PosSemidef.det_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) : (CFC.sqr
t A).det = RCLike.sqrt A.det
参数：hA : A.PosSemidef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Matrix.instStarOrderedRing`：instStarOrderedRing : StarOrderedRing (Matri
x n n 𝕜)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_cfc`：sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Matrix.IsHermitian.cfc_eq`：cfc_eq (f : Real -> Real) : cfc f A = hA.cfc 
f
· 使用定理 `RCLike.sqrt_of_nonneg`：RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 <= a) : sqr
t a = √(re a)
· 使用引理 `Matrix.PosSemidef.det_nonneg`：det_nonneg [DecidableEq n] (hA : A.PosSemi
def) : 0 <= A.det
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
（共 40 条，此处仅展示前 30 条）
-/
theorem det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (CFC.sqrt A).det = RCLike.sqrt A.det := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A, hA.1.cfc_eq, RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.sqrt_prod _ fun _ _ ↦ hA.eigenvalues_nonneg _]
  grind

end PosSemidef

/-
**Matrix.IsHermitian.det_abs** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] {A : Matrix n n 𝕜},   A.IsHermitian → (CFC.abs A).det = ↑‖
A.det‖
参数：CFC.abs A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.instStarOrderedRing`：instStarOrderedRing : StarOrderedRing (Matri
x n n 𝕜)
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.abs_eq_cfc_norm`：abs_eq_cfc_norm (a : A) (ha : IsSelfAdjoint a
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Matrix.IsHermitian.cfc_eq`：cfc_eq (f : Real -> Real) : cfc f A = hA.cfc 
f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det_map`：∀ {K : Type u_5} {m : Type u_6} {n : Type u_7} [inst : F
ield K] [inst_1 : Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq m] [in
st_4…
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Matrix.IsHermitian.det_eq_prod_eigenvalues`：det_eq_prod_eigenvalues : de
t A = ∏ i, (hA.eigenvalues i : 𝕜)
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
（共 33 条，此处仅展示前 30 条）
-/
theorem IsHermitian.det_abs [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    det (CFC.abs A) = ‖det A‖ := by
  rw [CFC.abs_eq_cfc_norm A, hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]
/-
**Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg** 是 Mathlib 中的一个定理，位于命名空
间 `Matrix`。
形式化陈述：posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix
 n n 𝕜} : A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A subseteq {a : 𝕜 | 0 <= a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectrum_eq_image_range`：spectrum_eq_image_range : sp
ectrum 𝕜 A = RCLike.ofReal '' Set.range hA.eigenvalues
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `algebraMap.coe_zero`：coe_zero : (↑(0 : R) : A) = 0
· 使用引理 `Matrix.PosSemidef.eigenvalues_nonneg`：eigenvalues_nonneg [DecidableEq n]
 (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i
· 使用定理 `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`：∀ {n : Type u_2} {
𝕜 : Type u_3} [inst : Fintype n] [inst_1 : RCLike 𝕜] {A : Matrix n n 𝕜} [inst_2 
: DecidableEq n]   (hA : A.IsHermitian), A…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A ⊆ {a : 𝕜 | 0 ≤ a} := by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_ofPred_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    simpa [h1.spectrum_eq_image_range] using @h2 (h1.eigenvalues i)

/-- A positive semi-definite matrix is positive definite if and only if it is invertible. -/
@[grind =]
/-
**Matrix.PosSemidef.posDef_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemid
ef`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] {x : Matrix n n 𝕜},   x.PosSemidef → (x.PosDef ↔ IsUnit x)
参数：x.PosDef ↔ IsUnit x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.isUnit`：isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.
PosDef) : IsUnit M
· 使用引理 `Matrix.PosDef.of_dotProduct_mulVec_pos`：of_dotProduct_mulVec_pos {M : Ma
trix n n R} (hM1 : M.IsHermitian) (hM2 : forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M 
*ᵥ x)) : M.PosDef
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CStarAlgebra.nonneg_iff_eq_star_mul_self`：∀ {A : Type u_1} [inst : Parti
alOrder A] [inst_1 : NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : St
arRing A]   [inst_4 : _root_.M…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Matrix.instStarOrderedRing`：instStarOrderedRing : StarOrderedRing (Matri
x n n 𝕜)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
A positive semi-definite matrix is positive definite if and only if it is invert
ible.
-/
theorem PosSemidef.posDef_iff_isUnit [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) : x.PosDef ↔ IsUnit x := by
  refine ⟨fun h => h.isUnit, fun h => .of_dotProduct_mulVec_pos hx.1 fun v hv => ?_⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_iff]
  contrapose hv
  rw [← map_eq_zero_iff (f := (yᴴ * y).mulVecLin) (mulVec_injective_iff_isUnit.mpr h),
    mulVecLin_apply, ← mulVec_mulVec, hv, mulVec_zero]
/-
**Matrix.isStrictlyPositive_iff_posDef** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isStrictlyPositive_iff_posDef [DecidableEq n] {x : Matrix n n 𝕜} : IsStric
tlyPositive x ↔ x.PosDef
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.PosSemidef.posDef_iff_isUnit`：∀ {𝕜 : Type u_1} {n : Type u_2} [in
st : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {x : Matrix n n 𝕜},
   x.PosSemidef → (x.PosD…
· 使用定理 `Matrix.LE.le.posSemidef`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 
𝕜] {A : Matrix n n 𝕜}, 0 ≤ A → A.PosSemidef
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `IsUnit.isStrictlyPositive`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsUnit a → 0 ≤ a → IsStrictlyPositive a
· 使用定理 `Matrix.PosDef.isUnit`：isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.
PosDef) : IsUnit M
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `Matrix.PosDef.posSemidef`：posSemidef {M : Matrix n n R} (hM : M.PosDef) 
: M.PosSemidef
-/
theorem isStrictlyPositive_iff_posDef [DecidableEq n] {x : Matrix n n 𝕜} :
    IsStrictlyPositive x ↔ x.PosDef :=
  ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosDef.isStrictlyPositive
/-
**Matrix.PosSemidef.posDef_iff_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pos
Semidef`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] {A : Matrix n n 𝕜},   A.PosSemidef → (A.PosDef ↔ A.det ≠ 0
)
参数：A.PosDef ↔ A.det ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.PosSemidef.posDef_iff_isUnit`：∀ {𝕜 : Type u_1} {n : Type u_2} [in
st : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {x : Matrix n n 𝕜},
   x.PosSemidef → (x.PosD…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma PosSemidef.posDef_iff_det_ne_zero [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.PosDef ↔ A.det ≠ 0 := by
  simp [hA.posDef_iff_isUnit, isUnit_iff_isUnit_det]

section kronecker

omit [Fintype n]

variable [Finite n] {m : Type*} [Finite m]

open scoped Kronecker

/-- The kronecker product of two positive semi-definite matrices is positive semi-definite. -/
/-
**Matrix.PosSemidef.kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 𝕜] [Finite n] {m : Type u_3
} [Finite m] {x : Matrix n n 𝕜}   {y : Matrix m m 𝕜}, x.PosSemidef → y.PosSemide
f → (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) x y).PosSemidef
参数：Matrix.kroneckerMap (fun x1 x2 => x1 * x2) x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CStarAlgebra.nonneg_iff_eq_star_mul_self`：∀ {A : Type u_1} [inst : Parti
alOrder A] [inst_1 : NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : St
arRing A]   [inst_4 : _root_.M…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Matrix.instStarOrderedRing`：instStarOrderedRing : StarOrderedRing (Matri
x n n 𝕜)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.instNonnegSpectrumClass`：instNonnegSpectrumClass : NonnegSpectrum
Class Real (Matrix n n 𝕜) where quasispectrum_nonneg_of_nonneg A hA
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Matrix.PosSemidef.nonneg`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike
 𝕜] {A : Matrix n n 𝕜}, A.PosSemidef → 0 ≤ A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_kronecker_mul`：mul_kronecker_mul [Fintype m] [Fintype m'] [Co
mmSemiring α] (A : Matrix l m α) (B : Matrix m n α) (A' : Matrix l' m' α) (B' : 
Matrix m' n' α…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.posSemidef_conjTranspose_mul_self`：posSemidef_conjTranspose_mul_s
elf [StarOrderedRing R] (A : Matrix m n R) : PosSemidef (Aᴴ * A)
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The kronecker product of two positive semi-definite matrices is positive semi-de
finite.
-/
theorem PosSemidef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef := by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy.nonneg
  simpa [mul_kronecker_mul, ← conjTranspose_kronecker, star_eq_conjTranspose] using
    posSemidef_conjTranspose_mul_self _

open Matrix in
/-- The kronecker of two positive definite matrices is positive definite. -/
/-
**Matrix.PosDef.kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 𝕜] [Finite n] {m : Type u_3
} [Finite m] {x : Matrix n n 𝕜}   {y : Matrix m m 𝕜}, x.PosDef → y.PosDef → (Mat
rix.kroneckerMap (fun x1 x2 => x1 * x2) x y).PosDef
参数：Matrix.kroneckerMap (fun x1 x2 => x1 * x2) x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.PosSemidef.posDef_iff_isUnit`：∀ {𝕜 : Type u_1} {n : Type u_2} [in
st : RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {x : Matrix n n 𝕜},
   x.PosSemidef → (x.PosD…
· 使用定理 `Matrix.PosSemidef.kronecker`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCL
ike 𝕜] [Finite n] {m : Type u_3} [Finite m] {x : Matrix n n 𝕜}   {y : Matrix m m
 𝕜}, x.PosSemidef…
· 使用定理 `Matrix.PosDef.posSemidef`：posSemidef {M : Matrix n n R} (hM : M.PosDef) 
: M.PosSemidef
· 使用定理 `Matrix.IsUnit.kronecker`：∀ {n : Type u} [inst : DecidableEq n] [inst_1 :
 Fintype n] {R : Type u_3} {m : Type u_4} [inst_2 : CommSemiring R]   [inst_3 : 
Fintype m] [i…
· 使用定理 `Matrix.PosDef.isUnit`：isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.
PosDef) : IsUnit M

--- 原说明 ---
The kronecker of two positive definite matrices is positive definite.
-/
theorem PosDef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosDef) (hy : y.PosDef) : (x ⊗ₖ y).PosDef := by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  exact hx.posSemidef.kronecker hy.posSemidef |>.posDef_iff_isUnit.mpr <|
    hx.isUnit.kronecker hy.isUnit

end kronecker

section hadamard

variable {ι : Type*}

/-- [**Schur product theorem**][schur1911] (positive semidefinite version): the Hadamard (entrywise)
product of positive semidefinite matrices is positive semidefinite. -/
/-
**Matrix.PosSemidef.hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {ι : Type u_3} {A B : Matrix ι ι 𝕜},   
A.PosSemidef → B.PosSemidef → (A.hadamard B).PosSemidef
参数：A.hadamard B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.hadamard`：∀ {α : Type u_1} {n : Type u_4} [inst : Com
mMonoid α] [inst_1 : StarMul α] {A B : Matrix n n α},   A.IsHermitian → B.IsHerm
itian → (A.hadama…
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `Matrix.PosSemidef.submatrix`：submatrix {M : Matrix n n R} (hM : M.PosSem
idef) (e : m -> n) : (M.submatrix e e).PosSemidef
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_hadamard`：submatrix_hadamard {l o : Type*} [Mul α] (A B
 : Matrix m n α) (e : l -> m) (f : o -> n) : (A ⊙ B).submatrix e f = A.submatrix
 e f ⊙ B.submat…
· 使用定理 `Matrix.posSemidef_iff_dotProduct_mulVec`：posSemidef_iff_dotProduct_mulVe
c {M : Matrix n n R} : M.PosSemidef ↔ M.IsHermitian ∧ forall x, 0 <= star x ⬝ᵥ (
M *ᵥ x)
· 使用定理 `Matrix.star_dotProduct_hadamard_mulVec_eq_kronecker`：star_dotProduct_had
amard_mulVec_eq_kronecker [StarAddMonoid R] (x : m -> R) (A B : Matrix m n R) (x
' : n -> R) : star x ⬝ᵥ (A ⊙ B) *ᵥ x' = s…
· 使用定理 `Matrix.PosSemidef.dotProduct_mulVec_nonneg`：dotProduct_mulVec_nonneg {M 
: Matrix n n R} (hM : M.PosSemidef) : forall x : n -> R, 0 <= star x ⬝ᵥ (M *ᵥ x)
· 使用定理 `Matrix.PosSemidef.kronecker`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCL
ike 𝕜] [Finite n] {m : Type u_3} [Finite m] {x : Matrix n n 𝕜}   {y : Matrix m m
 𝕜}, x.PosSemidef…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
[**Schur product theorem**][schur1911] (positive semidefinite version): the Hada
mard (entrywise)
product of positive semidefinite matrices is positive semidefinite.
-/
theorem PosSemidef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x ↦ ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosSemidef := by
    have hAs := hA.submatrix ((↑) : x.support → ι)
    have hBs := hB.submatrix ((↑) : x.support → ι)
    rw [submatrix_hadamard, posSemidef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y ↦ ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hAs.kronecker hBs).dotProduct_mulVec_nonneg _
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using hAB.2 _

/-- **Schur product theorem**: the Hadamard (entrywise) product of positive definite
matrices is positive definite. -/
/-
**Matrix.PosDef.hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {ι : Type u_3} {A B : Matrix ι ι 𝕜}, A.
PosDef → B.PosDef → (A.hadamard B).PosDef
参数：A.hadamard B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.hadamard`：∀ {α : Type u_1} {n : Type u_4} [inst : Com
mMonoid α] [inst_1 : StarMul α] {A B : Matrix n n α},   A.IsHermitian → B.IsHerm
itian → (A.hadama…
· 使用定理 `Matrix.PosDef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.PosDef
) : M.IsHermitian
· 使用定理 `Matrix.PosDef.submatrix`：submatrix {M : Matrix n n R} (hM : M.PosDef) {e
 : m -> n} (he : Function.Injective e) : (M.submatrix e e).PosDef
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_hadamard`：submatrix_hadamard {l o : Type*} [Mul α] (A B
 : Matrix m n α) (e : l -> m) (f : o -> n) : (A ⊙ B).submatrix e f = A.submatrix
 e f ⊙ B.submat…
· 使用定理 `Matrix.posDef_iff_dotProduct_mulVec`：posDef_iff_dotProduct_mulVec {M : M
atrix n n R} : M.PosDef ↔ M.IsHermitian ∧ forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M
 *ᵥ x)
· 使用定理 `Matrix.star_dotProduct_hadamard_mulVec_eq_kronecker`：star_dotProduct_had
amard_mulVec_eq_kronecker [StarAddMonoid R] (x : m -> R) (A B : Matrix m n R) (x
' : n -> R) : star x ⬝ᵥ (A ⊙ B) *ᵥ x' = s…
· 使用引理 `Matrix.PosDef.dotProduct_mulVec_pos`：dotProduct_mulVec_pos {M : Matrix n
 n R} (hM : M.PosDef) {x} (hx : x != 0) : 0 < star x ⬝ᵥ (M *ᵥ x)
· 使用定理 `Matrix.PosDef.kronecker`：∀ {𝕜 : Type u_1} {n : Type u_2} [inst : RCLike 
𝕜] [Finite n] {m : Type u_3} [Finite m] {x : Matrix n n 𝕜}   {y : Matrix m m 𝕜},
 x.PosDef → y…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finsupp.support_subtypeDomain`：support_subtypeDomain [D : DecidablePred 
p] {f : α ->₀ M} : (subtypeDomain p f).support = f.support.subtype p
· 使用定理 `Finset.subtype_mem_eq_attach`：subtype_mem_eq_attach (s : Finset α) [Deci
dablePred (· in s)] : s.subtype (· in s) = s.attach
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.support_nonempty_iff`：support_nonempty_iff {f : α ->₀ M} : f.sup
port.Nonempty ↔ f != 0

--- 原说明 ---
**Schur product theorem**: the Hadamard (entrywise) product of positive definite
matrices is positive definite.
-/
theorem PosDef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊙ B).PosDef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx ↦ ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosDef := by
    have hAs : (A.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hA.submatrix Subtype.coe_injective
    have hBs : (B.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hB.submatrix Subtype.coe_injective
    rw [submatrix_hadamard, posDef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y hy ↦ ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hAs.kronecker hBs).dotProduct_mulVec_pos <| by simpa
  simp_rw [RCLike.star_def, hadamard_apply, Finsupp.sum,
    ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]
  refine hAB.2 ?_
  simpa [← Finsupp.support_nonempty_iff] using Finsupp.support_nonempty_iff.mpr hx

end hadamard

section tracePositiveLinearMap
variable (n α 𝕜 : Type*) [Fintype n] [Semiring α] [RCLike 𝕜] [Module α 𝕜]

/-- `Matrix.trace` as a positive linear map. -/
/-
**Matrix.tracePositiveLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：tracePositiveLinearMap : Matrix n n 𝕜 ->ₚ[α] 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.instIsOrderedAddMonoid`：instIsOrderedAddMonoid : IsOrderedAddMono
id (Matrix n n 𝕜) where add_le_add_left _ _ _ _
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _

--- 原说明 ---
`Matrix.trace` as a positive linear map.
-/
def tracePositiveLinearMap : Matrix n n 𝕜 →ₚ[α] 𝕜 :=
  .mk₀ (traceLinearMap n α 𝕜) fun _ h ↦ h.posSemidef.trace_nonneg
/-
**Matrix.toLinearMap_tracePositiveLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ (n : Type u_3) (α : Type u_4) (𝕜 : Type u_5) [inst : Fintype n] [inst_1 
: Semiring α] [inst_2 : RCLike 𝕜]   [inst_3 : _root_.Module α 𝕜], (Matrix.traceP
ositiveLinearMap n α 𝕜).toLinearMap = Matrix.traceLinearMap n α 𝕜
参数：n : Type u_3；α : Type u_4；𝕜 : Type u_5；Matrix.tracePositiveLinearMap n α 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_tracePositiveLinearMap :
    (tracePositiveLinearMap n α 𝕜).toLinearMap = traceLinearMap n α 𝕜 := rfl
/-
**Matrix.tracePositiveLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ (n : Type u_3) (α : Type u_4) (𝕜 : Type u_5) [inst : Fintype n] [inst_1 
: Semiring α] [inst_2 : RCLike 𝕜]   [inst_3 : _root_.Module α 𝕜] (x : Matrix n n
 𝕜), (Matrix.tracePositiveLinearMap n α 𝕜) x = x.trace
参数：n : Type u_3；α : Type u_4；𝕜 : Type u_5；x : Matrix n n 𝕜；Matrix.tracePositiveL
inearMap n α 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tracePositiveLinearMap_apply (x) : tracePositiveLinearMap n α 𝕜 x = trace x := rfl

end tracePositiveLinearMap

set_option backward.privateInPublic true in
/-- The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toMatrixSeminormedAddCommGroup`, `Matrix.toMatrixNormedAddCommGroup`,
and `Matrix.toMatrixInnerProductSpace`. -/
/-
**Matrix.PosSemidef.matrixPreInnerProductSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matr
ix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toMatrixSeminormedAddCommGroup`, `Matrix.toMatrixNormedAddCommGroup`,
and `Matrix.toMatrixInnerProductSpace`.
-/
private abbrev PosSemidef.matrixPreInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (Matrix n n 𝕜) where
  inner x y := (y * M * xᴴ).trace
  conj_inner_symm _ _ := by
    simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hM.isHermitian.eq]
  re_inner_nonneg x := RCLike.nonneg_iff.mp (hM.mul_mul_conjTranspose_same x).trace_nonneg |>.1
  add_left := by simp [mul_add]
  smul_left := by simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[instance_reducible]
/-
**Matrix.toMatrixSeminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toMatrixSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) : Se
minormedAddCommGroup (Matrix n n 𝕜)
参数：M : Matrix n n 𝕜；hM : M.PosSemidef。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`
`‖x‖ = sqrt (x * M * xᴴ).trace`.
-/
noncomputable def toMatrixSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (Matrix n n 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.matrixPreInnerProductSpace

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[instance_reducible]
/-
**Matrix.toMatrixNormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toMatrixNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) : NormedAddC
ommGroup (Matrix n n 𝕜)
参数：M : Matrix n n 𝕜；hM : M.PosDef。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`.
-/
noncomputable def toMatrixNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (Matrix n n 𝕜) :=
  letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { __ := hM.posSemidef.matrixPreInnerProductSpace
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      simp +instances only at hx
      rw [← mul_assoc, ← conjTranspose_conjTranspose x, star_eq_conjTranspose, ← conjTranspose_mul,
        conjTranspose_conjTranspose, mul_assoc, trace_conjTranspose_mul_self_eq_zero_iff] at hx
      lift y to (Matrix n n 𝕜)ˣ using hy
      simpa [← mul_assoc] using congr(y⁻¹ * $hx) }
  this.toNormedAddCommGroup

/-- A positive semi-definite matrix `M` induces an inner product on `Matrix n n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`. -/
@[instance_reducible]
/-
**Matrix.toMatrixInnerProductSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toMatrixInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) : letI : 
SeminormedAddCommGroup (Matrix n n 𝕜)
参数：M : Matrix n n 𝕜；hM : M.PosSemidef。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive semi-definite matrix `M` induces an inner product on `Matrix n n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`.
-/
def toMatrixInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    letI : SeminormedAddCommGroup (Matrix n n 𝕜) := M.toMatrixSeminormedAddCommGroup hM
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

open scoped Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
/-- The isometric continuous functional calculus on `Matrix n n 𝕜` arising from the operator norm
given by the identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
/-
**Matrix.instIsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名空间 `Ma
trix`。
形式化陈述：instIsometricContinuousFunctionalCalculus [DecidableEq n] : IsometricConti
nuousFunctionalCalculus Real (Matrix n n 𝕜) IsSelfAdjoint where isometric A hA
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isHermitian_iff_isSelfAdjoint`：isHermitian_iff_isSelfAdjoint {A :
 Matrix n n α} : A.IsHermitian ↔ IsSelfAdjoint A
· 使用定理 `Matrix.IsHermitian.isSelfAdjoint`：∀ {α : Type u_1} {n : Type u_4} [inst 
: Star α] {A : Matrix n n α}, A.IsHermitian → IsSelfAdjoint A
· 使用引理 `Matrix.IsHermitian.cfcHom_eq_cfcAux`：cfcHom_eq_cfcAux : cfcHom hA.isSelf
Adjoint = hA.cfcAux
· 使用定理 `TopologicalSpace.NoetherianSpace.compactSpace`：∀ (α : Type u_1) [inst : 
TopologicalSpace α] [h : TopologicalSpace.NoetherianSpace α], CompactSpace α
· 使用定理 `TopologicalSpace.Finite.to_noetherianSpace`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [Finite α], TopologicalSpace.NoetherianSpace α
· 使用定理 `Matrix.instFiniteElemRealSpectrum`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n
 : Type u_2} [inst_1 : Fintype n] {A : Matrix n n 𝕜} [inst_2 : DecidableEq n],  
 Finite ↑(spectrum ℝ A)
· 使用定理 `AddMonoidHomClass.isometry_iff_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [ins
t_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Matrix.IsHermitian.eigenvalues_mem_spectrum_real`：eigenvalues_mem_spectr
um_real (i : n) : hA.eigenvalues i in spectrum Real A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.IsHermitian.cfcAux_apply`：∀ {n : Type u_1} {𝕜 : Type u_2} [inst :
 RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n n 𝕜}   (h
A : A.IsHermitian) (g…
· 使用定理 `CStarRing.norm_mul_coe_unitary`：norm_mul_coe_unitary (A : E) (U : unitar
y E) : ‖A * U‖ = ‖A‖
· 使用定理 `Matrix.instCStarRing`：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] 
[inst_1 : Fintype n] [inst_2 : DecidableEq n],   CStarRing (Matrix n n 𝕜)
· 使用定理 `CStarRing.norm_coe_unitary_mul`：norm_coe_unitary_mul (U : unitary E) (A 
: E) : ‖(U : E) * A‖ = ‖A‖
· 使用定理 `Matrix.l2_opNorm_diagonal`：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLik
e 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] (v : n → 𝕜),   ‖Matrix.diagon
al v‖ = ‖v‖
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用引理 `Isometry.postcomp_pi`：postcomp_pi [Fintype α] {g : β -> γ} (hg : Isometr
y g) : Isometry (fun f : α -> β => g ∘ f)
· 使用定理 `algebraMap_isometry`：algebraMap_isometry [NormOneClass 𝕜'] : Isometry (a
lgebraMap 𝕜 𝕜')
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The isometric continuous functional calculus on `Matrix n n 𝕜` arising from the 
operator norm
given by the identification with (continuous) linear endomorphisms of `Euclidean
Space 𝕜 n`.
-/
instance instIsometricContinuousFunctionalCalculus [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  isometric A hA := by
    rw [← isHermitian_iff_isSelfAdjoint] at hA
    rw [IsHermitian.cfcHom_eq_cfcAux hA, AddMonoidHomClass.isometry_iff_norm]
    intro f
    simp only [IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
    rw [((algebraMap_isometry ℝ 𝕜).postcomp_pi).norm_map_of_map_zero (by ext; simp)]
    let : Fintype (spectrum ℝ A) := .ofFinite _
    rw [ContinuousMap.norm_eq_norm_coeFn]
    refine Function.Surjective.pi_norm_comp ?_ _
    rw [← Function.Surjective.of_comp_iff'
      (Equiv.setCongr hA.spectrum_real_eq_range_eigenvalues).bijective]
    exact Set.codRestrict_range_surjective hA.eigenvalues

scoped[Matrix.Norms.L2Operator] attribute [instance]
  Matrix.instIsometricContinuousFunctionalCalculus

end Matrix

