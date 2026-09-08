/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `L²` inner product space structure on products of inner product spaces

The `L²` norm on product of two inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.
$$
This is recorded in this file as an inner product space instance on `WithLp 2 (E × F)`.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

variable {𝕜 ι₁ ι₂ E F : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F]

namespace WithLp

/-
**WithLp.instProdInnerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdInnerProductSpace : InnerProductSpace 𝕜 (WithLp 2 (E × F)) where i
nner x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
noncomputable instance instProdInnerProductSpace :
    InnerProductSpace 𝕜 (WithLp 2 (E × F)) where
  inner x y := ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜
  norm_sq_eq_re_inner x := by
    simp [prod_norm_sq_eq_of_L2]
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

@[simp]
/-
**WithLp.prod_inner_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_inner_apply (x y : WithLp 2 (E × F)) : ⟪x, y⟫_𝕜 = ⟪(ofLp x).fst, (ofL
p y).fst⟫_𝕜 + ⟪(ofLp x).snd, (ofLp y).snd⟫_𝕜
参数：x y : WithLp 2 (E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem prod_inner_apply (x y : WithLp 2 (E × F)) :
    ⟪x, y⟫_𝕜 = ⟪(ofLp x).fst, (ofLp y).fst⟫_𝕜 + ⟪(ofLp x).snd, (ofLp y).snd⟫_𝕜 := rfl

end WithLp

noncomputable section
namespace OrthonormalBasis

variable [Fintype ι₁] [Fintype ι₂]

/-- The product of two orthonormal bases is a basis for the L2-product. -/
/-
**OrthonormalBasis.prod** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：prod (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) : Orthono
rmalBasis (ι₁ oplus ι₂) 𝕜 (WithLp 2 (E × F))
参数：v : OrthonormalBasis ι₁ 𝕜 E；w : OrthonormalBasis ι₂ 𝕜 F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The product of two orthonormal bases is a basis for the L2-product.
-/
def prod (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ ⊕ ι₂) 𝕜 (WithLp 2 (E × F)) :=
  ((v.toBasis.prod w.toBasis).map (WithLp.linearEquiv 2 𝕜 (E × F)).symm).toOrthonormalBasis
  (by
    constructor
    · simp
    · unfold Pairwise
      simp only [ne_eq, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl,
        OrthonormalBasis.coe_toBasis, LinearMap.coe_inr, WithLp.coe_symm_linearEquiv,
        WithLp.prod_inner_apply, Sum.forall, Sum.elim_inl, Function.comp_apply, inner_zero_right,
        add_zero, Sum.elim_inr, zero_add, Sum.inl.injEq, reduceCtorEq, not_false_eq_true,
        inner_zero_left, imp_self, implies_true, and_true, Sum.inr.injEq, true_and]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)
/-
**OrthonormalBasis.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {𝕜 : Type u_1} {ι₁ : Type u_2} {ι₂ : Type u_3} {E : Type u_4} {F : Type 
u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [in
st_5 : Fintype ι₁] [inst_6 : Fintype ι₂] (v : OrthonormalBasis ι₁ 𝕜 E)   (w : Or
thonormalBasis ι₂ 𝕜 F) (i : ι₁ ⊕ ι₂),   (v.prod w) i = Sum.elim (WithLp.toLp 2 ∘
 ⇑(LinearMap.inl 𝕜 E F) ∘ ⇑v) (WithLp.toLp 2 ∘ ⇑(LinearMap.inr 𝕜 E F) ∘ ⇑w) i
参数：v : OrthonormalBasis ι₁ 𝕜 E；w : OrthonormalBasis ι₂ 𝕜 F；i : ι₁ ⊕ ι₂；v.prod w；
WithLp.toLp 2 ∘ ⇑(LinearMap.inl 𝕜 E F) ∘ ⇑v；WithLp.toLp 2 ∘ ⇑(LinearMap.inr 𝕜 E 
F) ∘ ⇑w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sum.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α ⊕ β → Prop},   (∀ (x 
: α ⊕ β), p x) ↔ (∀ (a : α), p (Sum.inl a)) ∧ ∀ (b : β), p (Sum.inr b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [in
st : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] theorem prod_apply (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    ∀ i : ι₁ ⊕ ι₂, v.prod w i =
      Sum.elim ((WithLp.toLp 2) ∘ (LinearMap.inl 𝕜 E F) ∘ v)
        ((WithLp.toLp 2) ∘ (LinearMap.inr 𝕜 E F) ∘ w) i := by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  aesop

end OrthonormalBasis

namespace Submodule

variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E)

/-- If a subspace `K` of an inner product space `E` admits an orthogonal projection, then `E` is
isometrically isomorphic to the `L²` product of `K` and `Kᗮ`. -/
@[simps! symm_apply]
/-
**Submodule.orthogonalDecomposition** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：orthogonalDecomposition : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
If a subspace `K` of an inner product space `E` admits an orthogonal projection,
 then `E` is
isometrically isomorphic to the `L²` product of `K` and `Kᗮ`.
-/
def orthogonalDecomposition : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) where
  __ := (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm
    ≪≫ₗ (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), WithLp.prod_norm_sq_eq_of_L2,
      K.norm_sq_eq_add_norm_sq_projection]
    simp [starProjection_apply_eq_isComplProjection]

@[simp]
/-
**Submodule.orthogonalDecomposition_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonalDecomposition_apply : K.orthogonalDecomposition x = .toLp 2 (K.o
rthogonalProjectionOnto x, Kᗮ.orthogonalProjectionOnto x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply`：prodEquivOfIsCompl_symm_apply (
hpq : IsCompl p q) (x : E) : (p.prodEquivOfIsCompl q hpq).symm x = (p.projection
Onto q hpq x, q.projectionOnt…
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.projectionOnto.congr_simp`：∀ {R : Type u_1} [inst : Ring R] {E
 : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (p q q_1 :
 Submodule R E) (e_q : q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orthogonalDecomposition_apply :
    K.orthogonalDecomposition x =
      .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogonalProjectionOnto x) := by
  simp [orthogonalDecomposition, orthogonalProjectionOnto_apply_eq_projectionOnto]
/-
**Submodule.toLinearEquiv_orthogonalDecomposition** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：toLinearEquiv_orthogonalDecomposition : K.orthogonalDecomposition.toLinear
Equiv = (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm ≪≫ₗ (WithLp.linearEq
uiv 2 𝕜 (K × Kᗮ)).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem toLinearEquiv_orthogonalDecomposition :
    K.orthogonalDecomposition.toLinearEquiv =
      (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm ≪≫ₗ
        (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm :=
  rfl
/-
**Submodule.toLinearEquiv_orthogonalDecomposition_symm** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
形式化陈述：toLinearEquiv_orthogonalDecomposition_symm : K.orthogonalDecomposition.sym
m.toLinearEquiv = WithLp.linearEquiv 2 𝕜 (K × Kᗮ) ≪≫ₗ K.prodEquivOfIsCompl Kᗮ K.
isCompl_orthogonal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem toLinearEquiv_orthogonalDecomposition_symm :
    K.orthogonalDecomposition.symm.toLinearEquiv =
      WithLp.linearEquiv 2 𝕜 (K × Kᗮ) ≪≫ₗ
        K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal :=
  rfl
/-
**Submodule.coe_orthogonalDecomposition** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_orthogonalDecomposition : (K.orthogonalDecomposition : E ->L[𝕜] WithLp
 2 (K × Kᗮ)) = (WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ).symm ∘L K.orthogonalP
rojectionOnto.prod Kᗮ.orthogonalProjectionOnto
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalDecomposition_apply`：orthogonalDecomposition_apply :
 K.orthogonalDecomposition x = .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogo
nalProjectionOnto x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_orthogonalDecomposition :
    (K.orthogonalDecomposition : E →L[𝕜] WithLp 2 (K × Kᗮ)) =
      (WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ).symm ∘L
        K.orthogonalProjectionOnto.prod Kᗮ.orthogonalProjectionOnto := by
  ext; simp
/-
**Submodule.coe_orthogonalDecomposition_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：coe_orthogonalDecomposition_symm : (K.orthogonalDecomposition.symm : WithL
p 2 (K × Kᗮ) ->L[𝕜] E) = K.subtypeL.coprod Kᗮ.subtypeL ∘L WithLp.prodContinuousL
inearEquiv 2 𝕜 K Kᗮ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem coe_orthogonalDecomposition_symm :
    (K.orthogonalDecomposition.symm : WithLp 2 (K × Kᗮ) →L[𝕜] E) =
      K.subtypeL.coprod Kᗮ.subtypeL ∘L WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ :=
  rfl
/-
**Submodule.fst_orthogonalDecomposition_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：fst_orthogonalDecomposition_apply : (K.orthogonalDecomposition x).fst = K.
orthogonalProjectionOnto x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.orthogonalDecomposition_apply`：orthogonalDecomposition_apply :
 K.orthogonalDecomposition x = .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogo
nalProjectionOnto x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_orthogonalDecomposition_apply :
    (K.orthogonalDecomposition x).fst = K.orthogonalProjectionOnto x := by
  simp
/-
**Submodule.snd_orthogonalDecomposition_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：snd_orthogonalDecomposition_apply : (K.orthogonalDecomposition x).snd = Kᗮ
.orthogonalProjectionOnto x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalDecomposition_apply`：orthogonalDecomposition_apply :
 K.orthogonalDecomposition x = .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogo
nalProjectionOnto x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_orthogonalDecomposition_apply :
    (K.orthogonalDecomposition x).snd = Kᗮ.orthogonalProjectionOnto x := by
  simp
/-
**Submodule.fstL_comp_coe_orthogonalDecomposition** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：fstL_comp_coe_orthogonalDecomposition : WithLp.fstL 2 𝕜 K Kᗮ ∘L K.orthogon
alDecomposition = K.orthogonalProjectionOnto
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.orthogonalDecomposition_apply`：orthogonalDecomposition_apply :
 K.orthogonalDecomposition x = .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogo
nalProjectionOnto x)
· 使用定理 `WithLp.fstL_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) (α : Type u_2) (β : Ty
pe u_3) [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Se
miring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fstL_comp_coe_orthogonalDecomposition :
    WithLp.fstL 2 𝕜 K Kᗮ ∘L K.orthogonalDecomposition = K.orthogonalProjectionOnto := by
  ext; simp
/-
**Submodule.sndL_comp_coe_orthogonalDecomposition** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：sndL_comp_coe_orthogonalDecomposition : WithLp.sndL 2 𝕜 K Kᗮ ∘L K.orthogon
alDecomposition = Kᗮ.orthogonalProjectionOnto
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalDecomposition_apply`：orthogonalDecomposition_apply :
 K.orthogonalDecomposition x = .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogo
nalProjectionOnto x)
· 使用定理 `WithLp.sndL_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) (α : Type u_2) (β : Ty
pe u_3) [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Se
miring …
· 使用定理 `Submodule.starProjection_orthogonal_val`：starProjection_orthogonal_val (
u : E) : Kᗮ.starProjection u = u - K.starProjection u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sndL_comp_coe_orthogonalDecomposition :
    WithLp.sndL 2 𝕜 K Kᗮ ∘L K.orthogonalDecomposition = Kᗮ.orthogonalProjectionOnto := by
  ext; simp

/-- If a subspace `K` of an inner product space `E` admits an orthogonal projection, then the
quotient `E ⧸ K` is isometrically isomorphic to the orthogonal complement `Kᗮ` of `K`. -/
/-
**Submodule.quotientEquivOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientEquivOrthogonal : (E ⧸ K) ≃ₗᵢ[𝕜] ↥Kᗮ where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint

--- 原说明 ---
If a subspace `K` of an inner product space `E` admits an orthogonal projection,
 then the
quotient `E ⧸ K` is isometrically isomorphic to the orthogonal complement `Kᗮ` o
f `K`.
-/
def quotientEquivOrthogonal : (E ⧸ K) ≃ₗᵢ[𝕜] ↥Kᗮ where
  __ := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  norm_map' y := by
    set f := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
    rw [coe_norm, ← norm_orthogonalProjectionOnto_apply Kᗮ (f y).2,
      orthogonalProjectionOnto_orthogonal, coe_norm, starProjection_minimal, eq_comm]
    have h : ‖Quotient.mk (f y).val‖ = sInf ((fun (x : E) ↦ ‖(f y).val + x‖) '' K.toAddSubgroup) :=
      quotient_norm_mk_eq K.toAddSubgroup (f y).1
    convert! h using 2
    · simp [f]
    · rw [sInf_image', ← Equiv.iInf_comp (Equiv.neg K)]
      simp

@[simp]
/-
**Submodule.coe_quotientEquivOrthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_quotientEquivOrthogonal : ⇑K.quotientEquivOrthogonal = K.quotientEquiv
OfIsCompl Kᗮ K.isCompl_orthogonal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotientEquivOrthogonal :
    ⇑K.quotientEquivOrthogonal = K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal :=
  rfl

@[simp]
/-
**Submodule.coe_quotientEquivOrthogonal_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：coe_quotientEquivOrthogonal_symm : ⇑K.quotientEquivOrthogonal.symm = (K.qu
otientEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotientEquivOrthogonal_symm :
    ⇑K.quotientEquivOrthogonal.symm = (K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm :=
  rfl

@[simp]
/-
**Submodule.toLinearEquiv_quotientEquivOrthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Sub
module`。
形式化陈述：toLinearEquiv_quotientEquivOrthogonal : (quotientEquivOrthogonal K).toLine
arEquiv = K.quotientEquivOfIsCompl _ K.isCompl_orthogonal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearEquiv_quotientEquivOrthogonal :
    (quotientEquivOrthogonal K).toLinearEquiv = K.quotientEquivOfIsCompl _ K.isCompl_orthogonal :=
  rfl
/-
**Submodule.quotientEquivOrthogonal_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quotientEquivOrthogonal_mk (x : E) (hx : x in Kᗮ) : K.quotientEquivOrthogo
nal (Quotient.mk x) = ⟨x, hx⟩
参数：x : E；hx : x in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.quotientEquivOfIsCompl_apply_mk_right`：quotientEquivOfIsCompl_
apply_mk_right (h : IsCompl p q) (x : q) : quotientEquivOfIsCompl p q h (Quotien
t.mk x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quotientEquivOrthogonal_mk (x : E) (hx : x ∈ Kᗮ) :
    K.quotientEquivOrthogonal (Quotient.mk x) = ⟨x, hx⟩ := by
  simp [← K.quotientEquivOfIsCompl_apply_mk_right K.isCompl_orthogonal ⟨x, hx⟩]
/-
**Submodule.quotientEquivOrthogonal_symm_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：quotientEquivOrthogonal_symm_eq_mk (x : E) (hx : x in Kᗮ) : K.quotientEqui
vOrthogonal.symm ⟨x, hx⟩ = Quotient.mk x
参数：x : E；hx : x in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.quotientEquivOfIsCompl_symm_apply`：∀ {R : Type u_1} [inst : Ri
ng R] {E : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (p
 q : Submodule R E) (h : IsCompl …
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quotientEquivOrthogonal_symm_eq_mk (x : E) (hx : x ∈ Kᗮ) :
    K.quotientEquivOrthogonal.symm ⟨x, hx⟩ = Quotient.mk x := by
  simp
/-
**Submodule.instQuotientInnerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：instQuotientInnerProductSpace : InnerProductSpace 𝕜 (E ⧸ K) where inner x 
y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instQuotientInnerProductSpace :
    InnerProductSpace 𝕜 (E ⧸ K) where
  inner x y := ⟪K.quotientEquivOrthogonal x, K.quotientEquivOrthogonal y⟫_𝕜
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y r := by rw [map_smul, inner_smul_left]
  conj_inner_symm x y := inner_conj_symm _ _
  norm_sq_eq_re_inner y := by rw [inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]

@[simp]
/-
**Submodule.inner_quotient_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inner_quotient_eq (x y : E ⧸ K) : ⟪x, y⟫_𝕜 = ⟪K.quotientEquivOrthogonal x,
 K.quotientEquivOrthogonal y⟫_𝕜
参数：x y : E ⧸ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inner_quotient_eq (x y : E ⧸ K) :
    ⟪x, y⟫_𝕜 = ⟪K.quotientEquivOrthogonal x, K.quotientEquivOrthogonal y⟫_𝕜 :=
  rfl
/-
**Submodule.Quotient.inner_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [inst_3 : K.HasOr
thogonalProjection] (x y : E),   x ∈ Kᗮ → y ∈ Kᗮ → inner 𝕜 (Submodule.Quotient.m
k x) (Submodule.Quotient.mk y) = inner 𝕜 x y
参数：K : Submodule 𝕜 E；x y : E；Submodule.Quotient.mk x；Submodule.Quotient.mk y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.quotientEquivOrthogonal_mk`：quotientEquivOrthogonal_mk (x : E)
 (hx : x in Kᗮ) : K.quotientEquivOrthogonal (Quotient.mk x) = ⟨x, hx⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Quotient.inner_mk_mk (x y : E) (hx : x ∈ Kᗮ) (hy : y ∈ Kᗮ) :
    ⟪Quotient.mk (p := K) x, Quotient.mk y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  simp [K.quotientEquivOrthogonal_mk x hx, K.quotientEquivOrthogonal_mk y hy]

end Submodule

end

