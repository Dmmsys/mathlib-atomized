/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Continuity and Von Neumann boundedness

This file proves that for two topological vector spaces `E` and `F` over nontrivially normed fields,
if `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous
(this is `LinearMap.continuous_of_locally_bounded`).

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

@[expose] public section


open TopologicalSpace Bornology Filter Topology Pointwise

variable {𝕜 𝕜' E F : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [AddCommGroup F] [TopologicalSpace F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
variable [NormedField 𝕜'] [Module 𝕜' F]
variable {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

/-- Construct a continuous linear map from a linear map `f : E →ₛₗ[σ] F` and the existence of a
neighborhood of zero that gets mapped into a bounded set in `F`. -/
/-
**LinearMap.clmOfExistsBoundedImage** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.clmOfExistsBoundedImage [IsTopologicalAddGroup F] (f : E ->ₛₗ[σ]
 F) (h : exists V in 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)) : E ->SL[σ]
 F
参数：f : E ->ₛₗ[σ] F；h : exists V in 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V
)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear map from a linear map `f : E →ₛₗ[σ] F` and the exi
stence of a
neighborhood of zero that gets mapped into a bounded set in `F`.
-/
def LinearMap.clmOfExistsBoundedImage [IsTopologicalAddGroup F] (f : E →ₛₗ[σ] F)
    (h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)) : E →SL[σ] F :=
  ⟨f, by
    -- It suffices to show that `f` is continuous at `0`.
    refine continuous_of_continuousAt_zero f ?_
    rw [continuousAt_def, f.map_zero]
    intro U hU
    -- Continuity means that `U ∈ 𝓝 0` implies that `f ⁻¹' U ∈ 𝓝 0`.
    rcases h with ⟨V, hV, h⟩
    rcases (h hU).exists_pos with ⟨r, hr, h⟩
    rcases NormedField.exists_lt_norm 𝕜 r with ⟨x, hx⟩
    specialize h (σ x) (by simpa using hx.le)
    -- After unfolding all the definitions, we know that `f '' V ⊆ σ x • U`. We use this to show the
    -- inclusion `x⁻¹ • V ⊆ f⁻¹' U`.
    have x_ne := norm_pos_iff.mp (hr.trans hx)
    have : x⁻¹ • V ⊆ f ⁻¹' U :=
      calc
        x⁻¹ • V ⊆ x⁻¹ • f ⁻¹' f '' V := Set.smul_set_mono (Set.subset_preimage_image (⇑f) V)
        _ ⊆ x⁻¹ • f ⁻¹' (σ x • U) := Set.smul_set_mono (Set.preimage_mono h)
        _ = f ⁻¹' U := by rw [x_ne.isUnit.preimage_smul_setₛₗ _, inv_smul_smul₀ x_ne _]
    -- Using this inclusion, it suffices to show that `x⁻¹ • V` is in `𝓝 0`, which is trivial.
    grw [← this]
    rwa [set_smul_mem_nhds_zero_iff (inv_ne_zero x_ne)]⟩
/-
**LinearMap.clmOfExistsBoundedImage_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.clmOfExistsBoundedImage_coe [IsTopologicalAddGroup F] {f : E ->ₛ
ₗ[σ] F} {h : exists V in 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)} : (f.cl
mOfExistsBoundedImage h : E ->ₛₗ[σ] F) = f
参数：0 : E；f '' V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.clmOfExistsBoundedImage_coe [IsTopologicalAddGroup F] {f : E →ₛₗ[σ] F}
    {h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)} :
    (f.clmOfExistsBoundedImage h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
/-
**LinearMap.clmOfExistsBoundedImage_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.clmOfExistsBoundedImage_apply [IsTopologicalAddGroup F] {f : E -
>ₛₗ[σ] F} {h : exists V in 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)} {x : 
E} : f.clmOfExistsBoundedImage h x = f x
参数：0 : E；f '' V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.clmOfExistsBoundedImage_apply [IsTopologicalAddGroup F] {f : E →ₛₗ[σ] F}
    {h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)} {x : E} :
    f.clmOfExistsBoundedImage h x = f x :=
  rfl

variable [FirstCountableTopology E]
/-
**LinearMap.continuousAt_zero_of_locally_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuousAt_zero_of_locally_bounded (f : E ->ₛₗ[σ] F) (hf : for
all s, IsVonNBounded 𝕜 s -> IsVonNBounded 𝕜' (f '' s)) : ContinuousAt f 0
参数：f : E ->ₛₗ[σ] F；hf : forall s, IsVonNBounded 𝕜 s -> IsVonNBounded 𝕜' (f '' s)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt_one`：exists_norm_lt_one : exists x : α, 0 < ‖
x‖ ∧ ‖x‖ < 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Filter.HasBasis.exists_antitone_subbasis`：∀ {α : Type u_1} {ι' : Sort u_
5} {f : Filter α} [h : f.IsCountablyGenerated] {p : ι' → Prop} {s : ι' → Set α},
   f.HasBasis p s → ∃ x, (∀ (i…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `trivial`：True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_mem_nhds_smul₀`：∀ {α : Type u_2} {G₀ : Type u_6} [inst : GroupWithZ
ero G₀] [inst_1 : MulAction G₀ α] [inst_2 : TopologicalSpace α]   [ContinuousCon
stSMul G₀…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 73 条，此处仅展示前 30 条）
-/
theorem LinearMap.continuousAt_zero_of_locally_bounded (f : E →ₛₗ[σ] F)
    (hf : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜' (f '' s)) : ContinuousAt f 0 := by
  -- We pick `c : 𝕜` nonzero of norm `< 1`.
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  have c_ne := norm_pos_iff.mp hc0
  -- We use a fast decreasing balanced basis for 0 : E, and reformulate continuity in terms of
  -- this basis
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩
  simp only [_root_.id] at bE
  have bE' : (𝓝 (0 : E)).HasBasis (fun _ ↦ True) (fun n : ℕ ↦ (c ^ n) • b n) := by
    refine bE.1.to_hasBasis' ?_ ?_
    · intro n _
      use n
      exact ⟨trivial, (bE1 n).2 _ (by grw [norm_pow, hc1, one_pow])⟩
    · intro n _
      simpa using smul_mem_nhds_smul₀ (pow_ne_zero n c_ne) (bE1 n).1
  simp_rw [ContinuousAt, map_zero, bE'.tendsto_left_iff, true_and, Set.MapsTo]
  -- Assume that f is not continuous at 0
  by_contra! h
  rcases h with ⟨V, hV, h⟩
  -- There exists `u : ℕ → E` such that for all `n : ℕ` we have `u n ∈ c ^ n • b n` and
  -- `f (u n) ∉ V`, with `V` some neighborhood of `0` in `F`.
  choose! u hu hu' using h
  -- The sequence `fun n ↦ c ^ (-n) • u n` converges to `0`
  have h_tendsto : Tendsto (fun n : ℕ => (c ^ n)⁻¹ • u n) atTop (𝓝 (0 : E)) := by
    apply bE.tendsto
    intro n
    simpa only [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero n c_ne)] using hu n
  -- The range of `fun n ↦ c ^ (-n) • u n` is von Neumann bounded
  have h_bounded : IsVonNBounded 𝕜 (Set.range fun n : ℕ => (c ^ n)⁻¹ • u n) :=
    h_tendsto.isVonNBounded_range 𝕜
  -- Hence, by assumption, the range of `fun n ↦ (σ c) ^ (-n) • f (u n)` is von Neumann bounded
  specialize hf _ h_bounded
  simp only [← Set.range_comp', LinearMap.map_smulₛₗ, map_inv₀, map_pow] at hf
  -- Since `fun n ↦ (σ c) ^ n` tends to zero, this implies that `f ∘ u` converges to zero.
  have : Tendsto (f ∘ u) atTop (𝓝 0) := by
    have : Tendsto (fun n ↦ σ c ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hc1)
    have := hf.smul_tendsto_zero (.of_forall fun n ↦ Set.mem_range_self n) this
    exact this.congr fun n ↦ by simp [c_ne]
  -- But this is a contradiction.
  refine frequently_false (atTop : Filter ℕ) <| Eventually.frequently ?_
  filter_upwards [this.eventually_mem hV] using hu'

/-- If `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous. -/
/-
**LinearMap.continuous_of_locally_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_of_locally_bounded [IsTopologicalAddGroup F] (f : E -
>ₛₗ[σ] F) (hf : forall s, IsVonNBounded 𝕜 s -> IsVonNBounded 𝕜' (f '' s)) : Cont
inuous f
参数：f : E ->ₛₗ[σ] F；hf : forall s, IsVonNBounded 𝕜 s -> IsVonNBounded 𝕜' (f '' s)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_continuousAt_zero`：∀ {G : Type w} [inst : TopologicalSpace
 G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {M : Type u_1}   {hom : Type
 u_2} [inst_3 : AddZe…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.continuousAt_zero_of_locally_bounded`：LinearMap.continuousAt_z
ero_of_locally_bounded (f : E ->ₛₗ[σ] F) (hf : forall s, IsVonNBounded 𝕜 s -> Is
VonNBounded 𝕜' (f '' s)) : Continuou…

--- 原说明 ---
If `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is
 continuous.
-/
theorem LinearMap.continuous_of_locally_bounded [IsTopologicalAddGroup F] (f : E →ₛₗ[σ] F)
    (hf : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜' (f '' s)) : Continuous f :=
  continuous_of_continuousAt_zero f (f.continuousAt_zero_of_locally_bounded hf)

end NontriviallyNormedField

