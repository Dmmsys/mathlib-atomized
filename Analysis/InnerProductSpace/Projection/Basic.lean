/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# The orthogonal projection

Given a nonempty subspace `K` of an inner product space `E` such that `K`
admits an orthogonal projection, this file constructs
`K.orthogonalProjectionOnto : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`. This map
satisfies: for any point `u` in `E`, the point `v = K.orthogonalProjectionOnto u` in `K`
minimizes the distance `‖u - v‖` to `u`.

This file also defines `K.starProjection : E →L[𝕜] E` which is the
orthogonal projection of `E` onto `K` but as a map from `E` to `E` instead of `E` to `K`.

Basic API for `orthogonalProjectionOnto` and `starProjection` is developed.

## References

The orthogonal projection construction is adapted from
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs ℝ _ _

namespace Submodule

/-- A subspace `K : Submodule 𝕜 E` has an orthogonal projection if every vector `v : E` admits an
orthogonal projection to `K`. -/
/-
**Submodule.HasOrthogonalProjection** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submodule`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     [inst : RCLike 𝕜] → [inst_1 : Norm
edAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → Submodule 𝕜 E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subspace `K : Submodule 𝕜 E` has an orthogonal projection if every vector `v :
 E` admits an
orthogonal projection to `K`.
-/
class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : ∃ w ∈ K, v - w ∈ Kᗮ

variable (K : Submodule 𝕜 E)
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] :
    K.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases K.exists_norm_eq_iInf_of_complete_subspace (completeSpace_coe_iff_isComplete.mp ‹_›) v
      with ⟨w, hwK, hw⟩
    refine ⟨w, hwK, (K.mem_orthogonal' _).2 ?_⟩
    rwa [← K.norm_eq_iInf_iff_inner_eq_zero hwK]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.HasOrthogonalProjection] : Kᗮ.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_sub_cancel]
    exact K.le_orthogonal_orthogonal hwK
/-
**Submodule.HasOrthogonalProjection.map_linearIsometryEquiv** 是 Mathlib 中的一个定理，位
于命名空间 `Submodule.HasOrthogonalProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.HasOrthogonalP
rojection] {E' : Type u_4} [inst_4 : NormedAddCommGroup E']   [inst_5 : InnerPro
ductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E'), (Submodule.map (↑f.toLinearEquiv) K).HasOrtho
gonalProjection
参数：K : Submodule 𝕜 E；f : E ≃ₗᵢ[𝕜] E'；Submodule.map (↑f.toLinearEquiv) K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.exists_orthogonal`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {inst : RCLike 𝕜} {inst_1 : NormedAddCommGroup E} {inst_2 : InnerPr
oductSpace 𝕜 E}   {K : Submodule 𝕜 E} [se…
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance HasOrthogonalProjection.map_linearIsometryEquiv [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')).HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.forall_mem_image.2 fun u hu ↦ ?_⟩
    simp [← f.symm.inner_map_map, hw u hu]
/-
**Submodule.HasOrthogonalProjection.map_linearIsometryEquiv'** 是 Mathlib 中的一个定理，
位于命名空间 `Submodule.HasOrthogonalProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.HasOrthogonalP
rojection] {E' : Type u_4} [inst_4 : NormedAddCommGroup E']   [inst_5 : InnerPro
ductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E'), (Submodule.map (↑f.toLinearIsometry) K).HasOr
thogonalProjection
参数：K : Submodule 𝕜 E；f : E ≃ₗᵢ[𝕜] E'；Submodule.map (↑f.toLinearIsometry) K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.map_linearIsometryEquiv`：∀ {𝕜 : Type u
_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : I
nnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
-/
instance HasOrthogonalProjection.map_linearIsometryEquiv' [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearIsometry : E →ₗ[𝕜] E')).HasOrthogonalProjection :=
  HasOrthogonalProjection.map_linearIsometryEquiv K f
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : Submodule 𝕜 E).HasOrthogonalProjection := ⟨fun v ↦ ⟨v, trivial, by simp⟩⟩
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : ClosedSubmodule 𝕜 E) [CompleteSpace E] : K.HasOrthogonalProjection := by
  let := K.isClosed'
  infer_instance

/-- If `K` admits an orthogonal projection, `K` and `Kᗮ` are complements of each other. -/
/-
**Submodule.isCompl_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isCompl_orthogonal [K.HasOrthogonalProjection] : IsCompl K Kᗮ where disjoi
nt
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.orthogonal_disjoint`：orthogonal_disjoint : Disjoint K Kᗮ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.codisjoint_iff_exists_add_eq`：codisjoint_iff_exists_add_eq : C
odisjoint p p' ↔ forall z, exists x y, x in p ∧ y in p' ∧ x + y = z
· 使用定理 `Submodule.HasOrthogonalProjection.exists_orthogonal`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {inst : RCLike 𝕜} {inst_1 : NormedAddCommGroup E} {inst_2 : InnerPr
oductSpace 𝕜 E}   {K : Submodule 𝕜 E} [se…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
If `K` admits an orthogonal projection, `K` and `Kᗮ` are complements of each oth
er.
-/
theorem isCompl_orthogonal [K.HasOrthogonalProjection] : IsCompl K Kᗮ where
  disjoint := K.orthogonal_disjoint
  codisjoint := K.codisjoint_iff_exists_add_eq.mpr fun z ↦
    have ⟨w, hw, hzw⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) z
    ⟨w, z - w, hw, hzw, add_sub_cancel w z⟩
/-
**Submodule.norm_projection_orthogonal_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_projection_orthogonal_le [K.HasOrthogonalProjection] (x : E) : ‖K.pro
jection Kᗮ K.isCompl_orthogonal x‖ <= ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.projection_add_projection_eq_self`：projection_add_projection_e
q_self (hpq : IsCompl p q) (x : E) : (p.projection q hpq) x + (q.projection p hp
q.symm) x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `sq_le_sq₀`：sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <=
 b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`：norm_add_sq_eq_norm
_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) : ‖x + y‖ * ‖x + y‖ 
= ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal`：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in
 K, ⟪u, v⟫ = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem norm_projection_orthogonal_le [K.HasOrthogonalProjection] (x : E) :
    ‖K.projection Kᗮ K.isCompl_orthogonal x‖ ≤ ‖x‖ := by
  conv_rhs => rw [← projection_add_projection_eq_self K.isCompl_orthogonal x]
  simp [← sq_le_sq₀ (norm_nonneg _), sq, mul_nonneg,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (K.mem_orthogonal _ |>.mp _ _ _)]
/-
**Submodule.isTopCompl_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isTopCompl_orthogonal [K.HasOrthogonalProjection] : IsTopCompl K Kᗮ where 
isCompl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `AddMonoidHomClass.continuous_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [i
nst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Submodule.norm_projection_orthogonal_le`：norm_projection_orthogonal_le [
K.HasOrthogonalProjection] (x : E) : ‖K.projection Kᗮ K.isCompl_orthogonal x‖ <=
 ‖x‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem isTopCompl_orthogonal [K.HasOrthogonalProjection] : IsTopCompl K Kᗮ where
  isCompl := K.isCompl_orthogonal
  continuous_projection := AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ by
    grw [norm_projection_orthogonal_le, one_mul]

noncomputable section

section orthogonalProjection

variable [K.HasOrthogonalProjection]

/-- The orthogonal projection onto a subspace. -/
/-
**Submodule.orthogonalProjectionOnto** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto : E ->L[𝕜] K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isTopCompl_orthogonal`：isTopCompl_orthogonal [K.HasOrthogonalP
rojection] : IsTopCompl K Kᗮ where isCompl

--- 原说明 ---
The orthogonal projection onto a subspace.
-/
def orthogonalProjectionOnto : E →L[𝕜] K := K.projectionOntoL Kᗮ K.isTopCompl_orthogonal

/-- The orthogonal projection onto a subspace. -/
/-
**Submodule.orthogonalProjection** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     [inst : RCLike 𝕜] →       [inst_1 
: NormedAddCommGroup E] →         [inst_2 : InnerProductSpace 𝕜 E] → (K : Submod
ule 𝕜 E) → [K.HasOrthogonalProjection] → E →L[𝕜] ↥K
参数：K : Submodule 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal projection onto a subspace.
-/
@[deprecated orthogonalProjectionOnto (since := "2026-05-05")] abbrev orthogonalProjection :
    E →L[𝕜] K := K.orthogonalProjectionOnto

variable {K}

/-- The orthogonal projection onto a subspace as a map from the full space to itself,
as opposed to `Submodule.orthogonalProjectionOnto`, which maps into the subtype. This
version is important as it satisfies `IsStarProjection`. -/
/-
**Submodule.starProjection** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : E ->L[𝕜] 
E
参数：U : Submodule 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal projection onto a subspace as a map from the full space to itself
,
as opposed to `Submodule.orthogonalProjectionOnto`, which maps into the subtype.
 This
version is important as it satisfies `IsStarProjection`.
-/
def starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →L[𝕜] E := U.subtypeL ∘L U.orthogonalProjectionOnto

/-- The orthogonal projection onto a complete subspace, as an
unbundled function. This definition is only intended for use in
setting up the bundled version `orthogonalProjection` and should not
be used once that is defined. -/
@[deprecated "Please use `orthogonalProjectionOnto` or `starProjection`." (since := "2026-06-10")]
/-
**Submodule.orthogonalProjectionFn** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionFn (x : E) : E
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal projection onto a complete subspace, as an
unbundled function. This definition is only intended for use in
setting up the bundled version `orthogonalProjection` and should not
be used once that is defined.
-/
abbrev orthogonalProjectionFn (x : E) : E := K.starProjection x

@[deprecated "Please use `orthogonalProjectionOnto` or `starProjection`." (since := "2026-06-10")]
/-
**Submodule.orthogonalProjectionFn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionFn_eq (v : E) : K.orthogonalProjectionFn v = (K.orthog
onalProjectionOnto v : E)
参数：v : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orthogonalProjectionFn_eq (v : E) :
    K.orthogonalProjectionFn v = (K.orthogonalProjectionOnto v : E) := rfl
/-
**Submodule.starProjection_apply** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : 
E) : U.starProjection v = U.orthogonalProjectionOnto v
参数：U : Submodule 𝕜 E；v : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma starProjection_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) :
    U.starProjection v = U.orthogonalProjectionOnto v := rfl

@[simp]
/-
**Submodule.coe_orthogonalProjectionOnto_apply** 是 Mathlib 中的一个引理，位于命名空间 `Submod
ule`。
形式化陈述：coe_orthogonalProjectionOnto_apply (U : Submodule 𝕜 E) [U.HasOrthogonalPro
jection] (v : E) : U.orthogonalProjectionOnto v = U.starProjection v
参数：U : Submodule 𝕜 E；v : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_orthogonalProjectionOnto_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) :
     U.orthogonalProjectionOnto v = U.starProjection v := rfl

@[deprecated (since := "2026-05-05")]
alias coe_orthogonalProjection_apply := coe_orthogonalProjectionOnto_apply

@[simp]
/-
**Submodule.starProjection_apply_mem** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_apply_mem (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (
x : E) : U.starProjection x in U
参数：U : Submodule 𝕜 E；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma starProjection_apply_mem (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    U.starProjection x ∈ U := by
  simp only [starProjection_apply, SetLike.coe_mem]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_mem := starProjection_apply_mem

/-- The characterization of the orthogonal projection. -/
@[simp]
/-
**Submodule.starProjection_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_inner_eq_zero (v w : E) (hw : w in K) : ⟪v - K.starProjecti
on v, w⟫ = 0
参数：v w : E；hw : w in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0

--- 原说明 ---
The characterization of the orthogonal projection.
-/
theorem starProjection_inner_eq_zero (v w : E) (hw : w ∈ K) : ⟪v - K.starProjection v, w⟫ = 0 := by
  suffices v - K.projection Kᗮ K.isCompl_orthogonal v ∈ Kᗮ from inner_eq_zero_symm.mp <| this w hw
  simp [← projection_eq_self_sub_projection]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_inner_eq_zero :=
  starProjection_inner_eq_zero

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`. -/
@[simp]
/-
**Submodule.sub_starProjection_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：sub_starProjection_mem_orthogonal (v : E) : v - K.starProjection v in Kᗮ
参数：v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
· 使用定理 `Submodule.starProjection_inner_eq_zero`：starProjection_inner_eq_zero (v 
w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0

--- 原说明 ---
The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`.
-/
theorem sub_starProjection_mem_orthogonal (v : E) : v - K.starProjection v ∈ Kᗮ := by
  intro w hw
  rw [inner_eq_zero_symm]
  exact starProjection_inner_eq_zero _ _ hw

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
/-
**Submodule.eq_starProjection_of_mem_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：eq_starProjection_of_mem_of_inner_eq_zero {u v : E} (hvm : v in K) (hvo : 
forall w in K, ⟪u - v, w⟫ = 0) : K.starProjection u = v
参数：hvm : v in K；hvo : forall w in K, ⟪u - v, w⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `Submodule.starProjection_inner_eq_zero`：starProjection_inner_eq_zero (v 
w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a

--- 原说明 ---
The orthogonal projection is the unique point in `K` with the
orthogonality property.
-/
theorem eq_starProjection_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : K.starProjection u = v := by
  have hvs : K.starProjection u - v ∈ K := K.sub_mem (coe_mem _) hvm
  have houv : ⟪u - v - (u - K.starProjection u), K.starProjection u - v⟫ = 0 := by
    rw [inner_sub_left, starProjection_inner_eq_zero u _ hvs, hvo _ hvs, sub_zero]
  rwa [sub_sub_sub_cancel_left, inner_self_eq_zero, sub_eq_zero] at houv

@[deprecated (since := "2026-06-10")] alias eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero :=
  eq_starProjection_of_mem_of_inner_eq_zero

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
/-
**Submodule.eq_starProjection_of_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：eq_starProjection_of_mem_orthogonal {u v : E} (hv : v in K) (hvo : u - v i
n Kᗮ) : K.starProjection u = v
参数：hv : v in K；hvo : u - v in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`：eq_starProjection_o
f_mem_of_inner_eq_zero {u v : E} (hvm : v in K) (hvo : forall w in K, ⟪u - v, w⟫
 = 0) : K.starProjection u = v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0

--- 原说明 ---
A point in `K` with the orthogonality property (here characterized in terms of `
Kᗮ`) must be the
orthogonal projection.
-/
theorem eq_starProjection_of_mem_orthogonal {u v : E} (hv : v ∈ K)
    (hvo : u - v ∈ Kᗮ) : K.starProjection u = v :=
  eq_starProjection_of_mem_of_inner_eq_zero hv <| (Submodule.mem_orthogonal' _ _).1 hvo

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
/-
**Submodule.eq_starProjection_of_mem_orthogonal'** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：eq_starProjection_of_mem_orthogonal' {u v z : E} (hv : v in K) (hz : z in 
Kᗮ) (hu : u = v + z) : K.starProjection u = v
参数：hv : v in K；hz : z in Kᗮ；hu : u = v + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_starProjection_of_mem_orthogonal`：eq_starProjection_of_mem_
orthogonal {u v : E} (hv : v in K) (hvo : u - v in Kᗮ) : K.starProjection u = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b

--- 原说明 ---
A point in `K` with the orthogonality property (here characterized in terms of `
Kᗮ`) must be the
orthogonal projection.
-/
theorem eq_starProjection_of_mem_orthogonal' {u v z : E}
    (hv : v ∈ K) (hz : z ∈ Kᗮ) (hu : u = v + z) : K.starProjection u = v :=
  eq_starProjection_of_mem_orthogonal hv (by simpa [hu])

@[simp]
/-
**Submodule.starProjection_orthogonal_val** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_orthogonal_val (u : E) : Kᗮ.starProjection u = u - K.starPr
ojection u
参数：u : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_starProjection_of_mem_orthogonal'`：eq_starProjection_of_mem
_orthogonal' {u v z : E} (hv : v in K) (hz : z in Kᗮ) (hu : u = v + z) : K.starP
rojection u = v
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem starProjection_orthogonal_val (u : E) :
    Kᗮ.starProjection u = u - K.starProjection u :=
  eq_starProjection_of_mem_orthogonal' (sub_starProjection_mem_orthogonal _)
    (K.le_orthogonal_orthogonal (K.orthogonalProjectionOnto u).2) <| (sub_add_cancel _ _).symm
/-
**Submodule.orthogonalProjectionOnto_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：orthogonalProjectionOnto_orthogonal (u : E) : Kᗮ.orthogonalProjectionOnto 
u = ⟨u - K.starProjection u, sub_starProjection_mem_orthogonal _⟩
参数：u : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ
· 使用定理 `Submodule.starProjection_orthogonal_val`：starProjection_orthogonal_val (
u : E) : Kᗮ.starProjection u = u - K.starProjection u
-/
theorem orthogonalProjectionOnto_orthogonal (u : E) :
    Kᗮ.orthogonalProjectionOnto u =
      ⟨u - K.starProjection u, sub_starProjection_mem_orthogonal _⟩ :=
  Subtype.ext <| starProjection_orthogonal_val _

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonal := orthogonalProjectionOnto_orthogonal
/-
**Submodule.starProjection_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_orthogonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] 
: Uᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - U.starProjection
参数：U : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalProjectionOnto_orthogonal`：orthogonalProjectionOnto_
orthogonal (u : E) : Kᗮ.orthogonalProjectionOnto u = ⟨u - K.starProjection u, su
b_starProjection_mem_orthogonal _⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma starProjection_orthogonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - U.starProjection := by
  ext
  simp only [starProjection, ContinuousLinearMap.comp_apply,
    orthogonalProjectionOnto_orthogonal]
  simp
/-
**Submodule.starProjection_orthogonal'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_orthogonal' (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
 : Uᗮ.starProjection = 1 - U.starProjection
参数：U : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.starProjection_orthogonal`：starProjection_orthogonal (U : Subm
odule 𝕜 E) [U.HasOrthogonalProjection] : Uᗮ.starProjection = ContinuousLinearMap
.id 𝕜 E - U.starProjectio…
-/
lemma starProjection_orthogonal' (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = 1 - U.starProjection := starProjection_orthogonal U

/-- The orthogonal projection of `y` on `U` minimizes the distance `‖y - x‖` for `x ∈ U`. -/
/-
**Submodule.starProjection_minimal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_minimal {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (y 
: E) : ‖y - U.starProjection y‖ = ⨅ x : U, ‖y - x‖
参数：y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.starProjection_apply`：starProjection_apply (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] (v : E) : U.starProjection v = U.orthogonalProjecti
onOnto v
· 使用定理 `Submodule.norm_eq_iInf_iff_inner_eq_zero`：norm_eq_iInf_iff_inner_eq_zero
 {u : E} {v : E} (hv : v in K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ forall w in K, ⟪
u - v, w⟫ = 0
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Submodule.starProjection_inner_eq_zero`：starProjection_inner_eq_zero (v 
w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0

--- 原说明 ---
The orthogonal projection of `y` on `U` minimizes the distance `‖y - x‖` for `x 
∈ U`.
-/
theorem starProjection_minimal {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (y : E) :
    ‖y - U.starProjection y‖ = ⨅ x : U, ‖y - x‖ := by
  rw [starProjection_apply, U.norm_eq_iInf_iff_inner_eq_zero (Submodule.coe_mem _)]
  exact starProjection_inner_eq_zero _

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
/-
**Submodule.orthogonalProjectionOnto_mem_subspace_eq_self** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjec
tionOnto v = v
参数：v : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`：eq_starProjection_o
f_mem_of_inner_eq_zero {u v : E} (hvm : v in K) (hvo : forall w in K, ⟪u - v, w⟫
 = 0) : K.starProjection u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The orthogonal projection sends elements of `K` to themselves.
-/
theorem orthogonalProjectionOnto_mem_subspace_eq_self (v : K) :
    K.orthogonalProjectionOnto v = v := by
  ext
  apply eq_starProjection_of_mem_of_inner_eq_zero <;> simp

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_mem_subspace_eq_self := orthogonalProjectionOnto_mem_subspace_eq_self

@[simp]
/-
**Submodule.starProjection_mem_subspace_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：starProjection_mem_subspace_eq_self (v : K) : K.starProjection v = v
参数：v : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`：orthogonalProje
ctionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjectionOnto v = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem starProjection_mem_subspace_eq_self (v : K) :
    K.starProjection v = v := by simp [starProjection_apply]

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
/-
**Submodule.starProjection_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_eq_self_iff {v : E} : K.starProjection v = v ↔ v in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`：eq_starProjection_o
f_mem_of_inner_eq_zero {u v : E} (hvm : v in K) (hvo : forall w in K, ⟪u - v, w⟫
 = 0) : K.starProjection u = v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A point equals its orthogonal projection if and only if it lies in the subspace.
-/
theorem starProjection_eq_self_iff {v : E} : K.starProjection v = v ↔ v ∈ K := by
  refine ⟨fun h => ?_, fun h => eq_starProjection_of_mem_of_inner_eq_zero h ?_⟩
  · rw [← h]
    simp
  · simp

variable (K) in
@[simp]
/-
**Submodule.isIdempotentElem_starProjection** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：isIdempotentElem_starProjection : IsIdempotentElem K.starProjection
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isIdempotentElem_starProjection : IsIdempotentElem K.starProjection :=
  ContinuousLinearMap.ext fun x ↦ starProjection_eq_self_iff.mpr <| by simp

@[simp]
/-
**Submodule.range_starProjection** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：range_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : U.s
tarProjection.range = U
参数：U : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
-/
lemma range_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.range = U := by
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ coe_mem (U.orthogonalProjectionOnto y),
    fun h ↦ ⟨x, starProjection_eq_self_iff.mpr h⟩⟩
/-
**Submodule.starProjection_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_top : (⊤ : Submodule 𝕜 E).starProjection = ContinuousLinear
Map.id 𝕜 E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Submodule.instHasOrthogonalProjectionTop`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E],   ⊤.HasOrthogonalProject…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
· 使用定理 `trivial`：True
-/
lemma starProjection_top : (⊤ : Submodule 𝕜 E).starProjection = ContinuousLinearMap.id 𝕜 E := by
  ext
  exact starProjection_eq_self_iff.mpr trivial
/-
**Submodule.starProjection_top'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_top' : (⊤ : Submodule 𝕜 E).starProjection = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.starProjection_top`：starProjection_top : (⊤ : Submodule 𝕜 E).s
tarProjection = ContinuousLinearMap.id 𝕜 E
-/
lemma starProjection_top' : (⊤ : Submodule 𝕜 E).starProjection = 1 :=
  starProjection_top

@[simp]
/-
**Submodule.orthogonalProjectionOnto_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：orthogonalProjectionOnto_eq_zero_iff {v : E} : K.orthogonalProjectionOnto 
v = 0 ↔ v in Kᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.eq_starProjection_of_mem_orthogonal`：eq_starProjection_of_mem_
orthogonal {u v : E} (hv : v in K) (hvo : u - v in Kᗮ) : K.starProjection u = v
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem orthogonalProjectionOnto_eq_zero_iff {v : E} :
    K.orthogonalProjectionOnto v = 0 ↔ v ∈ Kᗮ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext <| eq_starProjection_of_mem_orthogonal
    (zero_mem _) ?_⟩
  · rw [← sub_zero v, ← coe_zero (p := K), ← h]
    exact sub_starProjection_mem_orthogonal (K := K) v
  · simpa

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_eq_zero_iff := orthogonalProjectionOnto_eq_zero_iff

@[simp]
/-
**Submodule.ker_orthogonalProjectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_orthogonalProjectionOnto : K.orthogonalProjectionOnto.ker = Kᗮ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Submodule.orthogonalProjectionOnto_eq_zero_iff`：orthogonalProjectionOnto
_eq_zero_iff {v : E} : K.orthogonalProjectionOnto v = 0 ↔ v in Kᗮ
-/
theorem ker_orthogonalProjectionOnto : K.orthogonalProjectionOnto.ker = Kᗮ := by
  ext; exact orthogonalProjectionOnto_eq_zero_iff

@[deprecated (since := "2026-05-05")] alias ker_orthogonalProjection := ker_orthogonalProjectionOnto

open ContinuousLinearMap in
@[simp]
/-
**Submodule.ker_starProjection** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：ker_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : U.sta
rProjection.ker = Uᗮ
参数：U : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsIdempotentElem.ker_eq_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {E : Type u_7} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module S E]   {p
 : E →ₗ[S] E}, IsIdempotentEl…
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …
· 使用引理 `Submodule.isIdempotentElem_starProjection`：isIdempotentElem_starProjecti
on : IsIdempotentElem K.starProjection
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.range_starProjection`：range_starProjection (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] : U.starProjection.range = U
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Submodule.starProjection_orthogonal`：starProjection_orthogonal (U : Subm
odule 𝕜 E) [U.HasOrthogonalProjection] : Uᗮ.starProjection = ContinuousLinearMap
.id 𝕜 E - U.starProjectio…
· 使用定理 `ContinuousLinearMap.toLinearMap_sub`：toLinearMap_sub (f g : M ->SL[σ₁₂] 
M₂) : (↑(f - g) : M ->ₛₗ[σ₁₂] M₂) = f - g
· 使用定理 `ContinuousLinearMap.coe_id`：coe_id : (ContinuousLinearMap.id R₁ M₁ : M₁ 
->ₗ[R₁] M₁) = LinearMap.id
-/
lemma ker_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.ker = Uᗮ := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range U.isIdempotentElem_starProjection.toLinearMap,
    ← range_starProjection Uᗮ, starProjection_orthogonal, toLinearMap_sub, coe_id]
/-
**Submodule._root_.LinearIsometry.map_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometry.map_starProjection {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] [(p.map f.toLinearMap).HasOrthogonalProjection]
    (x : E) : f (p.starProjection x) = (p.map f.toLinearMap).starProjection (f x) := by
  refine (eq_starProjection_of_mem_of_inner_eq_zero ?_ fun y hy => ?_).symm
  · refine Submodule.apply_coe_mem_map _ _
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [← f.map_sub, f.inner_map_map, starProjection_inner_eq_zero x x' hx']
/-
**Submodule._root_.LinearIsometry.map_starProjection'** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometry.map_starProjection' {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection]
    [(p.map (f : E →ₗ[𝕜] E')).HasOrthogonalProjection] (x : E) :
    f (p.starProjection x) = (p.map (f : E →ₗ[𝕜] E')).starProjection (f x) :=
  have : (p.map f.toLinearMap).HasOrthogonalProjection := ‹_›
  f.map_starProjection p x

/-- Orthogonal projection onto the `Submodule.map` of a subspace. -/
/-
**Submodule.starProjection_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddC
ommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') 
(p : Submodule 𝕜 E) [p.HasOrthogonalProjection] (x : E') : (p.map (f.toLinearEqu
iv : E ->ₗ[𝕜] E')).starProjection x = f (p.starProjection (f.symm x))
参数：f : E ≃ₗᵢ[𝕜] E'；p : Submodule 𝕜 E；x : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `Submodule.HasOrthogonalProjection.map_linearIsometryEquiv'`：∀ {𝕜 : Type 
u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : 
InnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometry.map_starProjection'`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {
E : Type u_4} {E' : Type u_5} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
AddCommGroup E'] [inst_3…

--- 原说明 ---
Orthogonal projection onto the `Submodule.map` of a subspace.
-/
theorem starProjection_map_apply {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] (x : E') :
    (p.map (f.toLinearEquiv : E →ₗ[𝕜] E')).starProjection x =
      f (p.starProjection (f.symm x)) := by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using!
    (f.toLinearIsometry.map_starProjection' p (f.symm x)).symm

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
/-
**Submodule.orthogonalProjectionOnto_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_bot : (⊥ : Submodule 𝕜 E).orthogonalProjectionOnt
o = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Submodule.bot_ext`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x y : ↥⊥),   x = y

--- 原说明 ---
The orthogonal projection onto the trivial submodule is the zero map.
-/
theorem orthogonalProjectionOnto_bot : (⊥ : Submodule 𝕜 E).orthogonalProjectionOnto = 0 := by ext

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_bot := orthogonalProjectionOnto_bot

@[simp]
/-
**Submodule.starProjection_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：starProjection_bot : (⊥ : Submodule 𝕜 E).starProjection = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.starProjection.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : R
CLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (U :
 Submodule 𝕜 E) [in…
· 使用定理 `Submodule.orthogonalProjectionOnto_bot`：orthogonalProjectionOnto_bot : (
⊥ : Submodule 𝕜 E).orthogonalProjectionOnto = 0
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
-/
lemma starProjection_bot : (⊥ : Submodule 𝕜 E).starProjection = 0 := by
  rw [starProjection, orthogonalProjectionOnto_bot, ContinuousLinearMap.comp_zero]

variable (K)

/-- The orthogonal projection has norm `≤ 1`. -/
/-
**Submodule.orthogonalProjectionOnto_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：orthogonalProjectionOnto_norm_le : ‖K.orthogonalProjectionOnto‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `Submodule.isTopCompl_orthogonal`：isTopCompl_orthogonal [K.HasOrthogonalP
rojection] : IsTopCompl K Kᗮ where isCompl
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The orthogonal projection has norm `≤ 1`.
-/
theorem orthogonalProjectionOnto_norm_le : ‖K.orthogonalProjectionOnto‖ ≤ 1 := by
  refine K.orthogonalProjectionOnto.opNorm_le_bound zero_le_one ?_
  simp [orthogonalProjectionOnto, projectionOntoL, norm_projection_orthogonal_le]

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_norm_le := orthogonalProjectionOnto_norm_le
/-
**Submodule.starProjection_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_norm_le : ‖K.starProjection‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.orthogonalProjectionOnto_norm_le`：orthogonalProjectionOnto_nor
m_le : ‖K.orthogonalProjectionOnto‖ <= 1
-/
theorem starProjection_norm_le : ‖K.starProjection‖ ≤ 1 :=
  K.orthogonalProjectionOnto_norm_le
/-
**Submodule.norm_orthogonalProjectionOnto_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：norm_orthogonalProjectionOnto_apply {v : E} (hv : v in K) : ‖orthogonalPro
jectionOnto K v‖ = ‖v‖
参数：hv : v in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
-/
theorem norm_orthogonalProjectionOnto_apply {v : E} (hv : v ∈ K) :
    ‖orthogonalProjectionOnto K v‖ = ‖v‖ :=
  congr(‖$(K.starProjection_eq_self_iff.mpr hv)‖)

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply := norm_orthogonalProjectionOnto_apply
/-
**Submodule.norm_starProjection_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_starProjection_apply {v : E} (hv : v in K) : ‖K.starProjection v‖ = ‖
v‖
参数：hv : v in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.norm_orthogonalProjectionOnto_apply`：norm_orthogonalProjection
Onto_apply {v : E} (hv : v in K) : ‖orthogonalProjectionOnto K v‖ = ‖v‖
-/
theorem norm_starProjection_apply {v : E} (hv : v ∈ K) :
    ‖K.starProjection v‖ = ‖v‖ :=
  norm_orthogonalProjectionOnto_apply _ hv

/-- The orthogonal projection onto a closed subspace is norm non-increasing. -/
/-
**Submodule.norm_orthogonalProjectionOnto_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule`。
形式化陈述：norm_orthogonalProjectionOnto_apply_le (v : E) : ‖orthogonalProjectionOnto
 K v‖ <= ‖v‖
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Submodule.orthogonalProjectionOnto_norm_le`：orthogonalProjectionOnto_nor
m_le : ‖K.orthogonalProjectionOnto‖ <= 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The orthogonal projection onto a closed subspace is norm non-increasing.
-/
theorem norm_orthogonalProjectionOnto_apply_le (v : E) :
    ‖orthogonalProjectionOnto K v‖ ≤ ‖v‖ := by calc
  ‖orthogonalProjectionOnto K v‖ ≤ ‖orthogonalProjectionOnto K‖ * ‖v‖ :=
    K.orthogonalProjectionOnto.le_opNorm _
  _ ≤ 1 * ‖v‖ := by gcongr; exact orthogonalProjectionOnto_norm_le K
  _ = _ := by simp

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection_apply_le := norm_orthogonalProjectionOnto_apply_le
/-
**Submodule.norm_starProjection_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_starProjection_apply_le (v : E) : ‖K.starProjection v‖ <= ‖v‖
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.norm_orthogonalProjectionOnto_apply_le`：norm_orthogonalProject
ionOnto_apply_le (v : E) : ‖orthogonalProjectionOnto K v‖ <= ‖v‖
-/
theorem norm_starProjection_apply_le (v : E) :
    ‖K.starProjection v‖ ≤ ‖v‖ := K.norm_orthogonalProjectionOnto_apply_le v

/-- The orthogonal projection onto a closed subspace is a `1`-Lipschitz map. -/
/-
**Submodule.lipschitzWith_orthogonalProjectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule`。
形式化陈述：lipschitzWith_orthogonalProjectionOnto : LipschitzWith 1 (orthogonalProjec
tionOnto K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.lipschitzWith_of_opNorm_le`：∀ {𝕜 : Type u_1} {𝕜₂ : T
ype u_2} {E : Type u_4} {F : Type u_5} [inst : SeminormedAddCommGroup E]   [inst
_1 : SeminormedAddCommGroup F] [inst…
· 使用定理 `Submodule.orthogonalProjectionOnto_norm_le`：orthogonalProjectionOnto_nor
m_le : ‖K.orthogonalProjectionOnto‖ <= 1

--- 原说明 ---
The orthogonal projection onto a closed subspace is a `1`-Lipschitz map.
-/
theorem lipschitzWith_orthogonalProjectionOnto :
    LipschitzWith 1 (orthogonalProjectionOnto K) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le K.orthogonalProjectionOnto_norm_le

@[deprecated (since := "2026-05-05")]
alias lipschitzWith_orthogonalProjection := lipschitzWith_orthogonalProjectionOnto
/-
**Submodule.lipschitzWith_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：lipschitzWith_starProjection : LipschitzWith 1 K.starProjection
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.lipschitzWith_of_opNorm_le`：∀ {𝕜 : Type u_1} {𝕜₂ : T
ype u_2} {E : Type u_4} {F : Type u_5} [inst : SeminormedAddCommGroup E]   [inst
_1 : SeminormedAddCommGroup F] [inst…
· 使用定理 `Submodule.starProjection_norm_le`：starProjection_norm_le : ‖K.starProjec
tion‖ <= 1
-/
theorem lipschitzWith_starProjection :
    LipschitzWith 1 K.starProjection :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le K.starProjection_norm_le

/-- The operator norm of the orthogonal projection onto a nontrivial subspace is `1`. -/
/-
**Submodule.norm_orthogonalProjectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_orthogonalProjectionOnto (hK : K != ⊥) : ‖K.orthogonalProjectionOnto‖
 = 1
参数：hK : K != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.orthogonalProjectionOnto_norm_le`：orthogonalProjectionOnto_nor
m_le : ‖K.orthogonalProjectionOnto‖ <= 1
· 使用定理 `Submodule.exists_mem_ne_zero_of_ne_bot`：exists_mem_ne_zero_of_ne_bot {p 
: Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.norm_orthogonalProjectionOnto_apply`：norm_orthogonalProjection
Onto_apply {v : E} (hv : v in K) : ‖orthogonalProjectionOnto K v‖ = ‖v‖
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousLinearMap.ratio_le_opNorm`：ratio_le_opNorm : ‖f x‖ / ‖x‖ <= ‖f
‖

--- 原说明 ---
The operator norm of the orthogonal projection onto a nontrivial subspace is `1`
.
-/
theorem norm_orthogonalProjectionOnto (hK : K ≠ ⊥) :
    ‖K.orthogonalProjectionOnto‖ = 1 := by
  refine le_antisymm K.orthogonalProjectionOnto_norm_le ?_
  obtain ⟨x, hxK, hx_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  simpa [K.norm_orthogonalProjectionOnto_apply hxK, norm_eq_zero, hx_ne_zero]
    using K.orthogonalProjectionOnto.ratio_le_opNorm x

@[deprecated (since := "2026-05-05")]
alias norm_orthogonalProjection := norm_orthogonalProjectionOnto
/-
**Submodule.norm_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_starProjection (hK : K != ⊥) : ‖K.starProjection‖ = 1
参数：hK : K != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.norm_orthogonalProjectionOnto`：norm_orthogonalProjectionOnto (
hK : K != ⊥) : ‖K.orthogonalProjectionOnto‖ = 1
-/
theorem norm_starProjection (hK : K ≠ ⊥) :
    ‖K.starProjection‖ = 1 :=
  K.norm_orthogonalProjectionOnto hK

variable (𝕜)
/-
**Submodule.smul_starProjection_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_starProjection_singleton {v : E} (w : E) : ((‖v‖ ^ 2 : Real) : 𝕜) • (
𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v
参数：w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`：eq_starProjection_o
f_mem_of_inner_eq_zero {u v : E} (hvm : v in K) (hvo : forall w in K, ⟪u - v, w⟫
 = 0) : K.starProjection u = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_left`：mem_orthogonal_single
ton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem smul_starProjection_singleton {v : E} (w : E) :
    ((‖v‖ ^ 2 : ℝ) : 𝕜) • (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v := by
  suffices ((𝕜 ∙ v).starProjection (((‖v‖ : 𝕜) ^ 2) • w)) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm]

/-- Formula for orthogonal projection onto a single vector. -/
/-
**Submodule.starProjection_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_singleton {v : E} (w : E) : (𝕜 ∙ v).starProjection w = (⟪v,
 w⟫ / ((‖v‖ ^ 2 : Real) : 𝕜)) • v
参数：w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Submodule.starProjection.congr_simp`：∀ {𝕜 : Type u_1} {E : Type u_2} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  (U U_1 : Submodule 𝕜 E)…
· 使用引理 `Submodule.starProjection_bot`：starProjection_bot : (⊥ : Submodule 𝕜 E).s
tarProjection = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Submodule.smul_starProjection_singleton`：smul_starProjection_singleton {
v : E} (w : E) : ((‖v‖ ^ 2 : Real) : 𝕜) • (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for orthogonal projection onto a single vector.
-/
theorem starProjection_singleton {v : E} (w : E) :
    (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : ℝ) : 𝕜)) • v := by
  by_cases hv : v = 0
  · rw [hv]
    simp [Submodule.span_zero_singleton 𝕜]
  have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
  have key :
    (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : ℝ) : 𝕜)) • (𝕜 ∙ v).starProjection w =
      (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [mul_smul, smul_starProjection_singleton 𝕜 w, -map_pow]
  convert! key using 1 <;> match_scalars <;> field_simp [hv']

/-- Formula for orthogonal projection onto a single unit vector. -/
/-
**Submodule.starProjection_unit_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) : (𝕜 ∙ v).sta
rProjection w = ⟪v, w⟫ • v
参数：hv : ‖v‖ = 1；w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_starProjection_singleton`：smul_starProjection_singleton {
v : E} (w : E) : ((‖v‖ ^ 2 : Real) : 𝕜) • (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Formula for orthogonal projection onto a single unit vector.
-/
theorem starProjection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) :
    (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v := by
  rw [← smul_starProjection_singleton 𝕜 w]
  simp [hv]

end orthogonalProjection

variable {K}

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
/-
**Submodule.exists_add_mem_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：exists_add_mem_mem_orthogonal [K.HasOrthogonalProjection] (v : E) : exists
 y in K, exists z in Kᗮ, v = y + z
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` 
and `Kᗮ`.
-/
theorem exists_add_mem_mem_orthogonal [K.HasOrthogonalProjection] (v : E) :
    ∃ y ∈ K, ∃ z ∈ Kᗮ, v = y + z :=
  ⟨K.orthogonalProjectionOnto v, Subtype.coe_prop _, v - K.orthogonalProjectionOnto v,
    sub_starProjection_mem_orthogonal _, by simp⟩

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
/-
**Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal** 是 Mathlib 中的一个定理，
位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjectio
n] {v : E} (hv : v in Kᗮ) : K.orthogonalProjectionOnto v = 0
参数：hv : v in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.orthogonalProjectionOnto_eq_zero_iff`：orthogonalProjectionOnto
_eq_zero_iff {v : E} : K.orthogonalProjectionOnto v = 0 ↔ v in Kᗮ

--- 原说明 ---
The orthogonal projection onto `K` of an element of `Kᗮ` is zero.
-/
theorem orthogonalProjectionOnto_apply_of_mem_orthogonal
    [K.HasOrthogonalProjection] {v : E} (hv : v ∈ Kᗮ) : K.orthogonalProjectionOnto v = 0 :=
  orthogonalProjectionOnto_eq_zero_iff.mpr hv

@[deprecated (since := "2026-05-06")] alias
orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero :=
  orthogonalProjectionOnto_apply_of_mem_orthogonal

/-- The projection into `U` from an orthogonal submodule `V` is the zero map. -/
/-
**Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL** 是 Mathlib 中的一个定理，位于
命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E} [inst_3 : U.Has
OrthogonalProjection], U ⟂ V → U.orthogonalProjectionOnto ∘SL V.subtypeL = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal`：orthogonalPr
ojectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjection] {v : E} (hv : v
 in Kᗮ) : K.orthogonalProjectionOnto v = 0
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The projection into `U` from an orthogonal submodule `V` is the zero map.
-/
theorem IsOrtho.orthogonalProjectionOnto_comp_subtypeL {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : U ⟂ V) : U.orthogonalProjectionOnto ∘L V.subtypeL = 0 := by
  ext v; simp [orthogonalProjectionOnto_apply_of_mem_orthogonal <| h.symm v.prop]

@[deprecated (since := "2026-05-05")]
alias IsOrtho.orthogonalProjection_comp_subtypeL := IsOrtho.orthogonalProjectionOnto_comp_subtypeL
/-
**Submodule.IsOrtho.starProjection_comp_starProjection** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E} [inst_3 : U.Has
OrthogonalProjection] [inst_4 : V.HasOrthogonalProjection],   U ⟂ V → U.starProj
ection ∘SL V.starProjection = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL`：∀ {𝕜 : Type u_
1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : In
nerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E} […
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
-/
theorem IsOrtho.starProjection_comp_starProjection {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    U.starProjection ∘L V.starProjection = 0 := calc
  _ = U.subtypeL ∘L (U.orthogonalProjectionOnto ∘L V.subtypeL) ∘L V.orthogonalProjectionOnto := by
      simp only [starProjection, ContinuousLinearMap.comp_assoc]
    _ = 0 := by simp [h.orthogonalProjectionOnto_comp_subtypeL]

/-- The projection into `U` from `V` is the zero map if and only if `U` and `V` are orthogonal. -/
/-
**Submodule.orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff** 是 Mathlib 中的一个定
理，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E} [
U.HasOrthogonalProjection] : U.orthogonalProjectionOnto ∘L V.subtypeL = 0 ↔ U ⟂ 
V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.starProjection_apply`：starProjection_apply (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] (v : E) : U.starProjection v = U.orthogonalProjecti
onOnto v
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Submodule.starProjection_inner_eq_zero`：starProjection_inner_eq_zero (v 
w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0
· 使用定理 `Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL`：∀ {𝕜 : Type u_
1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : In
nerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E} […

--- 原说明 ---
The projection into `U` from `V` is the zero map if and only if `U` and `V` are 
orthogonal.
-/
theorem orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : U.orthogonalProjectionOnto ∘L V.subtypeL = 0 ↔ U ⟂ V := by
  refine ⟨fun h u hu v hv ↦ ?_, Submodule.IsOrtho.orthogonalProjectionOnto_comp_subtypeL⟩
  convert starProjection_inner_eq_zero v u hu
  have : U.orthogonalProjectionOnto v = 0 := DFunLike.congr_fun h (⟨_, hv⟩ : V)
  rw [starProjection_apply, this, Submodule.coe_zero, sub_zero]

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_comp_subtypeL_eq_zero_iff :=
  orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff

/-- `U.starProjection ∘ V.starProjection = 0` iff `U` and `V` are pairwise orthogonal. -/
/-
**Submodule.starProjection_comp_starProjection_eq_zero_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Submodule`。
形式化陈述：starProjection_comp_starProjection_eq_zero_iff {U V : Submodule 𝕜 E} [U.Ha
sOrthogonalProjection] [V.HasOrthogonalProjection] : U.starProjection ∘L V.starP
rojection = 0 ↔ U ⟂ V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff`：orthogonal
ProjectionOnto_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E} [U.HasOrthogonalP
rojection] : U.orthogonalProjectionOnto ∘L V.subty…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.subtypeL_apply`：subtypeL_apply (p : Submodule R M) (x : p) : p
.subtypeL x = x
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`：orthogonalProje
ctionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjectionOnto v = v
· 使用定理 `Submodule.IsOrtho.starProjection_comp_starProjection`：∀ {𝕜 : Type u_1} {
E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   {U V : Submodule 𝕜 E} […

--- 原说明 ---
`U.starProjection ∘ V.starProjection = 0` iff `U` and `V` are pairwise orthogona
l.
-/
theorem starProjection_comp_starProjection_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection ∘L V.starProjection = 0 ↔ U ⟂ V := by
  refine ⟨fun h => ?_, fun h => h.starProjection_comp_starProjection⟩
  rw [← orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff]
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, subtypeL_apply,
    starProjection_apply, zero_apply, coe_eq_zero] at h ⊢
  intro x
  simpa using h (x : E)

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
/-
**Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_orthogonal_apply_eq_zero [Kᗮ.HasOrthogonalProject
ion] {v : E} (hv : v in K) : Kᗮ.orthogonalProjectionOnto v = 0
参数：hv : v in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal`：orthogonalPr
ojectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjection] {v : E} (hv : v
 in Kᗮ) : K.orthogonalProjectionOnto v = 0
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ

--- 原说明 ---
The orthogonal projection onto `Kᗮ` of an element of `K` is zero.
-/
theorem orthogonalProjectionOnto_orthogonal_apply_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v ∈ K) : Kᗮ.orthogonalProjectionOnto v = 0 :=
  orthogonalProjectionOnto_apply_of_mem_orthogonal (K.le_orthogonal_orthogonal hv)

@[deprecated (since := "2026-05-06")] alias orthogonalProjection_orthogonal_apply_eq_zero :=
  orthogonalProjectionOnto_orthogonal_apply_eq_zero
/-
**Submodule.starProjection_orthogonal_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `S
ubmodule`。
形式化陈述：starProjection_orthogonal_apply_eq_zero [Kᗮ.HasOrthogonalProjection] {v : 
E} (hv : v in K) : Kᗮ.starProjection v = 0
参数：hv : v in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.starProjection_apply`：starProjection_apply (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] (v : E) : U.starProjection v = U.orthogonalProjecti
onOnto v
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero`：orthogonalP
rojectionOnto_orthogonal_apply_eq_zero [Kᗮ.HasOrthogonalProjection] {v : E} (hv 
: v in K) : Kᗮ.orthogonalProjectionOnto v = 0
-/
theorem starProjection_orthogonal_apply_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v ∈ K) :
    Kᗮ.starProjection v = 0 := by
  rw [starProjection_apply, coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonal_apply_eq_zero hv

/-- If `U ≤ V`, then projecting on `V` and then on `U` is the same as projecting on `U`. -/
/-
**Submodule.orthogonalProjectionOnto_starProjection_of_le** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_starProjection_of_le {U V : Submodule 𝕜 E} [U.Has
OrthogonalProjection] [V.HasOrthogonalProjection] (h : U <= V) (x : E) : U.ortho
gonalProjectionOnto (V.starProjection x) = U.orthogonalProjectionOnto x
参数：h : U <= V；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal`：orthogonalPr
ojectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjection] {v : E} (hv : v
 in Kᗮ) : K.orthogonalProjectionOnto v = 0
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ

--- 原说明 ---
If `U ≤ V`, then projecting on `V` and then on `U` is the same as projecting on 
`U`.
-/
theorem orthogonalProjectionOnto_starProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    U.orthogonalProjectionOnto (V.starProjection x) = U.orthogonalProjectionOnto x :=
  Eq.symm <| by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Submodule.orthogonal_le h (sub_starProjection_mem_orthogonal x))

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_starProjection_of_le := orthogonalProjectionOnto_starProjection_of_le
/-
**Submodule.starProjection_comp_starProjection_of_le** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule`。
形式化陈述：starProjection_comp_starProjection_of_le {U V : Submodule 𝕜 E} [U.HasOrtho
gonalProjection] [V.HasOrthogonalProjection] (h : U <= V) : U.starProjection ∘L 
V.starProjection = U.starProjection
参数：h : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.starProjection.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : R
CLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (U :
 Submodule 𝕜 E) [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.orthogonalProjectionOnto_starProjection_of_le`：orthogonalProje
ctionOnto_starProjection_of_le {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
 [V.HasOrthogonalProjection] (h : U <= V) (x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem starProjection_comp_starProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) :
    U.starProjection ∘L V.starProjection = U.starProjection := ContinuousLinearMap.ext fun _ => by
  nth_rw 1 [starProjection]
  simp [orthogonalProjectionOnto_starProjection_of_le h]

open ContinuousLinearMap in
/-
**Submodule._root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_
range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : p.range.HasOrthogonalProjection :=
  have := hp.isClosed_range.completeSpace_coe
  .ofCompleteSpace _

open LinearMap in
/-
**Submodule._root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range
** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range
    {p : E →ₗ[𝕜] E} (hp : p.IsSymmetricProjection) :
    (range p).HasOrthogonalProjection :=
  ⟨fun v => ⟨p v, by
    simp [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric,
      ← Module.End.mul_apply, hp.isIdempotentElem.eq]⟩⟩

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
/-
**Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero** 是 
Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (v : E) : 
(𝕜 ∙ v)ᗮ.orthogonalProjectionOnto v = 0
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero`：orthogonalP
rojectionOnto_orthogonal_apply_eq_zero [Kᗮ.HasOrthogonalProjection] {v : E} (hv 
: v in K) : Kᗮ.orthogonalProjectionOnto v = 0
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x

--- 原说明 ---
The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero.
-/
theorem orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
  orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (Submodule.mem_span_singleton_self v)

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_orthogonalComplement_singleton_eq_zero :=
  orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero
/-
**Submodule.starProjection_orthogonalComplement_singleton_eq_zero** 是 Mathlib 中的
一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_orthogonalComplement_singleton_eq_zero (v : E) : (𝕜 ∙ v)ᗮ.s
tarProjection v = 0
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.starProjection_apply`：starProjection_apply (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] (v : E) : U.starProjection v = U.orthogonalProjecti
onOnto v
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zer
o`：orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (v : E) : (𝕜 
∙ v)ᗮ.orthogonalProjectionOnto v = 0
-/
theorem starProjection_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.starProjection v = 0 := by
  rw [starProjection_apply, coe_eq_zero]
  exact orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v

/-- If the orthogonal projection to `K` is well-defined, then a vector splits as the sum of its
orthogonal projections onto a complete submodule `K` and onto the orthogonal complement of `K`. -/
/-
**Submodule.starProjection_add_starProjection_orthogonal** 是 Mathlib 中的一个定理，位于命名
空间 `Submodule`。
形式化陈述：starProjection_add_starProjection_orthogonal [K.HasOrthogonalProjection] (
w : E) : K.starProjection w + Kᗮ.starProjection w = w
参数：w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.starProjection_orthogonal_val`：starProjection_orthogonal_val (
u : E) : Kᗮ.starProjection u = u - K.starProjection u
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the orthogonal projection to `K` is well-defined, then a vector splits as the
 sum of its
orthogonal projections onto a complete submodule `K` and onto the orthogonal com
plement of `K`.
-/
theorem starProjection_add_starProjection_orthogonal [K.HasOrthogonalProjection]
    (w : E) : K.starProjection w + Kᗮ.starProjection w = w := by
  simp

/-- The Pythagorean theorem, for an orthogonal projection. -/
/-
**Submodule.norm_sq_eq_add_norm_sq_projection** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [S.HasOrthog
onalProjection] : ‖x‖ ^ 2 = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalP
rojectionOnto x‖ ^ 2
参数：x : E；S : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.starProjection_add_starProjection_orthogonal`：starProjection_a
dd_starProjection_orthogonal [K.HasOrthogonalProjection] (w : E) : K.starProject
ion w + Kᗮ.starProjection w = w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`：norm_add_sq_eq_norm
_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) : ‖x + y‖ * ‖x + y‖ 
= ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal`：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in
 K, ⟪u, v⟫ = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The Pythagorean theorem, for an orthogonal projection.
-/
theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 :=
  calc
    ‖x‖ ^ 2 = ‖S.starProjection x + Sᗮ.starProjection x‖ ^ 2 := by
      rw [starProjection_add_starProjection_orthogonal]
    _ = ‖S.orthogonalProjectionOnto x‖ ^ 2 + ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 := by
      simp only [sq]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ <|
        (S.mem_orthogonal _).1 (Sᗮ.orthogonalProjectionOnto x).2 _ (S.orthogonalProjectionOnto x).2
/-
**Submodule.norm_sq_eq_add_norm_sq_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：norm_sq_eq_add_norm_sq_starProjection (x : E) (S : Submodule 𝕜 E) [S.HasOr
thogonalProjection] : ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖
 ^ 2
参数：x : E；S : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.norm_sq_eq_add_norm_sq_projection`：norm_sq_eq_add_norm_sq_proj
ection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] : ‖x‖ ^ 2 = ‖S.or
thogonalProjectionOnto x‖ ^ 2 + ‖…
-/
theorem norm_sq_eq_add_norm_sq_starProjection (x : E) (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 :=
  norm_sq_eq_add_norm_sq_projection x S
/-
**Submodule.mem_iff_norm_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_iff_norm_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection
] (v : E) : v in U ↔ ‖U.starProjection v‖ = ‖v‖
参数：U : Submodule 𝕜 E；v : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.norm_starProjection_apply`：norm_starProjection_apply {v : E} (
hv : v in K) : ‖K.starProjection v‖ = ‖v‖
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.starProjection_orthogonal_val`：starProjection_orthogonal_val (
u : E) : Kᗮ.starProjection u = u - K.starProjection u
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submodule.norm_sq_eq_add_norm_sq_starProjection`：norm_sq_eq_add_norm_sq_
starProjection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] : ‖x‖ ^ 2
 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.sta…
-/
theorem mem_iff_norm_starProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : E) :
    v ∈ U ↔ ‖U.starProjection v‖ = ‖v‖ := by
  refine ⟨fun h => norm_starProjection_apply _ h, fun h => ?_⟩
  simpa [h, sub_eq_zero, eq_comm (a := v), starProjection_eq_self_iff] using
    U.norm_sq_eq_add_norm_sq_starProjection v

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
/-
**Submodule.id_eq_sum_starProjection_self_orthogonalComplement** 是 Mathlib 中的一个定
理，位于命名空间 `Submodule`。
形式化陈述：id_eq_sum_starProjection_self_orthogonalComplement [K.HasOrthogonalProject
ion] : ContinuousLinearMap.id 𝕜 E = K.starProjection + Kᗮ.starProjection
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.starProjection_add_starProjection_orthogonal`：starProjection_a
dd_starProjection_orthogonal [K.HasOrthogonalProjection] (w : E) : K.starProject
ion w + Kᗮ.starProjection w = w

--- 原说明 ---
In a complete space `E`, the projection maps onto a complete subspace `K` and it
s orthogonal
complement sum to the identity.
-/
theorem id_eq_sum_starProjection_self_orthogonalComplement [K.HasOrthogonalProjection] :
    ContinuousLinearMap.id 𝕜 E =
      K.starProjection + Kᗮ.starProjection := by
  ext w
  exact (K.starProjection_add_starProjection_orthogonal w).symm

-- The priority should be higher than `Submodule.coe_inner`.
@[simp high]
/-
**Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right** 是 Mathlib 中的一个定理，位于
命名空间 `Submodule`。
形式化陈述：inner_orthogonalProjectionOnto_eq_of_mem_right [K.HasOrthogonalProjection]
 (u : K) (v : E) : ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪v, u⟫
参数：u : K；v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.coe_inner`：Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) :
 ⟪x, y⟫ = ⟪(x : E), ↑y⟫
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.starProjection_inner_eq_zero`：starProjection_inner_eq_zero (v 
w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem inner_orthogonalProjectionOnto_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪v, u⟫ :=
  calc
    ⟪K.orthogonalProjectionOnto v, u⟫ = ⟪K.starProjection v, u⟫ := K.coe_inner _ _
    _ = ⟪K.starProjection v, u⟫ + ⟪v - K.starProjection v, u⟫ := by
      rw [starProjection_inner_eq_zero _ _ (Submodule.coe_mem _), add_zero]
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel]

@[deprecated (since := "2026-05-05")]
alias inner_orthogonalProjection_eq_of_mem_right := inner_orthogonalProjectionOnto_eq_of_mem_right

-- The priority should be higher than `Submodule.coe_inner`.
@[simp high]
/-
**Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule`。
形式化陈述：inner_orthogonalProjectionOnto_eq_of_mem_left [K.HasOrthogonalProjection] 
(u : K) (v : E) : ⟪u, K.orthogonalProjectionOnto v⟫ = ⟪(u : E), v⟫
参数：u : K；v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right`：inner_orthogon
alProjectionOnto_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) : ⟪
K.orthogonalProjectionOnto v, u⟫ = ⟪v, u⟫
-/
theorem inner_orthogonalProjectionOnto_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪u, K.orthogonalProjectionOnto v⟫ = ⟪(u : E), v⟫ := by
  rw [← inner_conj_symm, ← inner_conj_symm (u : E), inner_orthogonalProjectionOnto_eq_of_mem_right]

@[deprecated (since := "2026-05-05")]
alias inner_orthogonalProjection_eq_of_mem_left := inner_orthogonalProjectionOnto_eq_of_mem_left

variable (K)

/-- The orthogonal projection is self-adjoint. -/
/-
**Submodule.inner_starProjection_left_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：inner_starProjection_left_eq_right [K.HasOrthogonalProjection] (u v : E) :
 ⟪K.starProjection u, v⟫ = ⟪u, K.starProjection v⟫
参数：u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right`：inner_orthogon
alProjectionOnto_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) : ⟪
K.orthogonalProjectionOnto v, u⟫ = ⟪v, u⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The orthogonal projection is self-adjoint.
-/
theorem inner_starProjection_left_eq_right [K.HasOrthogonalProjection] (u v : E) :
    ⟪K.starProjection u, v⟫ = ⟪u, K.starProjection v⟫ := by
  simp_rw [starProjection_apply, ← inner_orthogonalProjectionOnto_eq_of_mem_left,
    inner_orthogonalProjectionOnto_eq_of_mem_right]

/-- The orthogonal projection is symmetric. -/
/-
**Submodule.starProjection_isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：starProjection_isSymmetric [K.HasOrthogonalProjection] : (K.starProjection
 : E ->ₗ[𝕜] E).IsSymmetric
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.inner_starProjection_left_eq_right`：inner_starProjection_left_
eq_right [K.HasOrthogonalProjection] (u v : E) : ⟪K.starProjection u, v⟫ = ⟪u, K
.starProjection v⟫

--- 原说明 ---
The orthogonal projection is symmetric.
-/
theorem starProjection_isSymmetric [K.HasOrthogonalProjection] :
    (K.starProjection : E →ₗ[𝕜] E).IsSymmetric :=
  inner_starProjection_left_eq_right K

open ContinuousLinearMap in
/-- `U.starProjection` is a symmetric projection. -/
@[simp]
/-
**Submodule.isSymmetricProjection_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：isSymmetricProjection_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalP
rojection] : U.starProjection.IsSymmetricProjection
参数：U : Submodule 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …
· 使用引理 `Submodule.isIdempotentElem_starProjection`：isIdempotentElem_starProjecti
on : IsIdempotentElem K.starProjection
· 使用定理 `Submodule.starProjection_isSymmetric`：starProjection_isSymmetric [K.HasO
rthogonalProjection] : (K.starProjection : E ->ₗ[𝕜] E).IsSymmetric

--- 原说明 ---
`U.starProjection` is a symmetric projection.
-/
theorem isSymmetricProjection_starProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.IsSymmetricProjection :=
  ⟨U.isIdempotentElem_starProjection.toLinearMap, U.starProjection_isSymmetric⟩

open LinearMap in
/-- An operator is a symmetric projection if and only if it is an orthogonal projection. -/
/-
**Submodule._root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_ran
ge** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An operator is a symmetric projection if and only if it is an orthogonal project
ion.
-/
theorem _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range {p : E →ₗ[𝕜] E} :
    p.IsSymmetricProjection ↔ ∃ (_ : (LinearMap.range p).HasOrthogonalProjection),
    p = (LinearMap.range p).starProjection := by
  refine ⟨fun hp ↦ ?_, fun ⟨h, hp⟩ ↦ hp ▸ isSymmetricProjection_starProjection _⟩
  have : (LinearMap.range p).HasOrthogonalProjection := hp.hasOrthogonalProjection_range
  refine ⟨this, Eq.symm ?_⟩
  ext x
  refine Submodule.eq_starProjection_of_mem_orthogonal (by simp) ?_
  rw [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric]
  simpa using congr($hp.isIdempotentElem.mul_one_sub_self x)
/-
**Submodule._root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection** 是
 Mathlib 中的一个引理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection {p : E →ₗ[𝕜] E} :
    p.IsSymmetricProjection
      ↔ ∃ (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection), p = K.starProjection :=
  ⟨fun h ↦ ⟨LinearMap.range p, p.isSymmetricProjection_iff_eq_coe_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; exact isSymmetricProjection_starProjection _⟩
/-
**Submodule.starProjection_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：starProjection_apply_eq_zero_iff [K.HasOrthogonalProjection] {v : E} : K.s
tarProjection v = 0 ↔ v in Kᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
· 使用定理 `Submodule.inner_starProjection_left_eq_right`：inner_starProjection_left_
eq_right [K.HasOrthogonalProjection] (u v : E) : ⟪K.starProjection u, v⟫ = ⟪u, K
.starProjection v⟫
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal`：orthogonalPr
ojectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjection] {v : E} (hv : v
 in Kᗮ) : K.orthogonalProjectionOnto v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem starProjection_apply_eq_zero_iff [K.HasOrthogonalProjection] {v : E} :
    K.starProjection v = 0 ↔ v ∈ Kᗮ := by
  refine ⟨fun h w hw => ?_, fun hv => ?_⟩
  · rw [← starProjection_eq_self_iff.mpr hw, inner_starProjection_left_eq_right, h,
      inner_zero_right]
  · simp [starProjection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hv]

open RCLike
/-
**Submodule.re_inner_starProjection_eq_normSq** 是 Mathlib 中的一个引理，位于命名空间 `Submodu
le`。
形式化陈述：re_inner_starProjection_eq_normSq [K.HasOrthogonalProjection] (v : E) : re
 ⟪K.starProjection v, v⟫ = ‖K.orthogonalProjectionOnto v‖ ^ 2
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.starProjection_apply`：starProjection_apply (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] (v : E) : U.starProjection v = U.orthogonalProjecti
onOnto v
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_tw
o`：re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x 
y : E) : re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖…
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `Submodule.coe_norm`：coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module
 𝕜 E] {s : Submodule 𝕜 E} (x : s) : ‖x‖ = ‖(x : E)‖
· 使用定理 `mul_sub_one`：mul_sub_one (a b : α) : a * (b - 1) = a * b - a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 33 条，此处仅展示前 30 条）
-/
lemma re_inner_starProjection_eq_normSq [K.HasOrthogonalProjection] (v : E) :
    re ⟪K.starProjection v, v⟫ = ‖K.orthogonalProjectionOnto v‖ ^ 2 := by
  rw [starProjection_apply,
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    div_eq_iff (NeZero.ne' 2).symm, pow_two, add_sub_assoc, ← eq_sub_iff_add_eq', coe_norm,
    ← mul_sub_one, show (2 : ℝ) - 1 = 1 by norm_num, mul_one, sub_eq_iff_eq_add', norm_sub_rev]
  simpa [sq, add_comm] using K.norm_sq_eq_add_norm_sq_starProjection v

@[deprecated norm_sq_eq_add_norm_sq_starProjection (since := "2026-06-10")]
/-
**Submodule.orthogonalProjectionFn_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：orthogonalProjectionFn_norm_sq [K.HasOrthogonalProjection] (v : E) : ‖v‖ *
 ‖v‖ = ‖v - K.orthogonalProjectionFn v‖ * ‖v - K.orthogonalProjectionFn v‖ + ‖K.
orthogonalProjectionFn v‖ * ‖K.orthogonalProjectionFn v‖
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.starProjection_orthogonal_val`：starProjection_orthogonal_val (
u : E) : Kᗮ.starProjection u = u - K.starProjection u
· 使用定理 `Submodule.norm_sq_eq_add_norm_sq_starProjection`：norm_sq_eq_add_norm_sq_
starProjection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] : ‖x‖ ^ 2
 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.sta…
-/
theorem orthogonalProjectionFn_norm_sq [K.HasOrthogonalProjection] (v : E) :
    ‖v‖ * ‖v‖ = ‖v - K.orthogonalProjectionFn v‖ * ‖v - K.orthogonalProjectionFn v‖ +
      ‖K.orthogonalProjectionFn v‖ * ‖K.orthogonalProjectionFn v‖ := by
  simpa [sq, add_comm] using K.norm_sq_eq_add_norm_sq_starProjection v
/-
**Submodule.re_inner_starProjection_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：re_inner_starProjection_nonneg [K.HasOrthogonalProjection] (v : E) : 0 <= 
re ⟪K.starProjection v, v⟫
参数：v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.re_inner_starProjection_eq_normSq`：re_inner_starProjection_eq_
normSq [K.HasOrthogonalProjection] (v : E) : re ⟪K.starProjection v, v⟫ = ‖K.ort
hogonalProjectionOnto v‖ ^ 2
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma re_inner_starProjection_nonneg [K.HasOrthogonalProjection] (v : E) :
    0 ≤ re ⟪K.starProjection v, v⟫ := by
  rw [re_inner_starProjection_eq_normSq K v]
  exact sq_nonneg ‖K.orthogonalProjectionOnto v‖

end

end Submodule

