/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.UniformConvergence

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `UniformOnFun.continuousSMul_induced_of_image_bounded` : let `E` be a TVS, `𝔖 : Set (Set α)` and
  `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any `S ∈ 𝔖` by any `u ∈ H` is bounded (in the
  sense of `Bornology.IsVonNBounded`), then `H`, equipped with the topology induced from
  `α →ᵤ[𝔖] E`, is a TVS.

## Implementation notes

Like in `Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean`, we use the type aliases
`UniformFun` (denoted `α →ᵤ β`) and `UniformOnFun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/

public section

open Filter Topology
open scoped Pointwise UniformConvergence Uniformity

section Module

variable (𝕜 α E H : Type*) {hom : Type*} [NormedField 𝕜] [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace H] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul 𝕜 E] {𝔖 : Set <| Set α}
  [FunLike hom H (α → E)] [LinearMapClass hom 𝕜 H (α → E)]

set_option backward.isDefEq.respectTransparency false in
/-- Let `E` be a topological vector space over a normed field `𝕜`, let `α` be any type.
Let `H` be a submodule of `α →ᵤ E` such that the range of each `f ∈ H` is von Neumann bounded.
Then `H` is a topological vector space over `𝕜`,
i.e., the pointwise scalar multiplication is continuous in both variables.

For convenience we require that `H` is a vector space over `𝕜`
with a topology induced by `UniformFun.ofFun ∘ φ`, where `φ : H →ₗ[𝕜] (α → E)`. -/
/-
**UniformFun.continuousSMul_induced_of_range_bounded** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：UniformFun.continuousSMul_induced_of_range_bounded (φ : hom) (hφ : IsInduc
ing (ofFun ∘ φ)) (h : forall u : H, Bornology.IsVonNBounded 𝕜 (Set.range (φ u)))
 : ContinuousSMul 𝕜 H
参数：φ : hom；hφ : IsInducing (ofFun ∘ φ)；h : forall u : H, Bornology.IsVonNBounded
 𝕜 (Set.range (φ u))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.topologicalAddGroup`：∀ {G : Type w} {H : Type x} [in
st : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Ty
pe u_1}   [inst_3 : AddGroup …
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `instIsUniformAddGroupUniformFun`：∀ {α : Type u_1} {G : Type u_2} [inst :
 AddGroup G] [inst_1 : UniformSpace G] [IsUniformAddGroup G],   IsUniformAddGrou
p (UniformFun α G)
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `UniformFun.hasBasis_nhds_zero`：∀ {α : Type u_1} {G : Type u_2} [inst : A
ddGroup G] [inst_1 : UniformSpace G] [IsUniformAddGroup G],   (nhds 0).HasBasis 
(fun V => V ∈ nhds …
· 使用定理 `ContinuousSMul.of_basis_zero`：∀ {R : Type u_1} {M : Type u_2} [inst : Ri
ng R] [inst_1 : TopologicalSpace R] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {ι : …
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_subset_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {
s : Set α} {t u : Set β}, s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Let `E` be a topological vector space over a normed field `𝕜`, let `α` be any ty
pe.
Let `H` be a submodule of `α →ᵤ E` such that the range of each `f ∈ H` is von Ne
umann bounded.
Then `H` is a topological vector space over `𝕜`,
i.e., the pointwise scalar multiplication is continuous in both variables.

For convenience we require that `H` is a vector space over `𝕜`
with a topology induced by `UniformFun.ofFun ∘ φ`, where `φ : H →ₗ[𝕜] (α → E)`.
-/
lemma UniformFun.continuousSMul_induced_of_range_bounded (φ : hom)
    (hφ : IsInducing (ofFun ∘ φ)) (h : ∀ u : H, Bornology.IsVonNBounded 𝕜 (Set.range (φ u))) :
    ContinuousSMul 𝕜 H := by
  have : IsTopologicalAddGroup H :=
    let ofFun' : (α → E) →+ (α →ᵤ E) := AddMonoidHom.id _
    IsInducing.topologicalAddGroup (ofFun'.comp (φ : H →+ (α → E))) hφ
  have hb : (𝓝 (0 : H)).HasBasis (· ∈ 𝓝 (0 : E)) fun V ↦ {u | ∀ x, φ u x ∈ V} := by
    simp only [hφ.nhds_eq_comap, Function.comp_apply, map_zero]
    exact UniformFun.hasBasis_nhds_zero.comap _
  apply ContinuousSMul.of_basis_zero hb
  · intro U hU
    have : Tendsto (fun x : 𝕜 × E ↦ x.1 • x.2) (𝓝 0) (𝓝 0) :=
      continuous_smul.tendsto' _ _ (zero_smul _ _)
    rcases ((Filter.basis_sets _).prod_nhds (Filter.basis_sets _)).tendsto_left_iff.1 this U hU
      with ⟨⟨V, W⟩, ⟨hV, hW⟩, hVW⟩
    refine ⟨V, hV, W, hW, Set.smul_subset_iff.2 fun a ha u hu x ↦ ?_⟩
    rw [map_smul]
    exact hVW (Set.mk_mem_prod ha (hu x))
  · intro c U hU
    have : Tendsto (c • · : E → E) (𝓝 0) (𝓝 0) :=
      (continuous_const_smul c).tendsto' _ _ (smul_zero _)
    refine ⟨_, this hU, fun u hu x ↦ ?_⟩
    simpa only [map_smul] using! hu x
  · intro u U hU
    simp only [Set.mem_ofPred_eq, map_smul, Pi.smul_apply]
    simpa only [Set.mapsTo_range_iff] using (h u hU).eventually_nhds_zero (mem_of_mem_nhds hU)

/-- Let `E` be a TVS, `𝔖 : Set (Set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `Bornology.IsVonNBounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

For convenience, we don't literally ask for `H : Submodule (α →ᵤ[𝔖] E)`. Instead, we prove the
result for any vector space `H` equipped with a linear inducing to `α →ᵤ[𝔖] E`, which is often
easier to use. We also state the `Submodule` version as
`UniformOnFun.continuousSMul_submodule_of_image_bounded`. -/
/-
**UniformOnFun.continuousSMul_induced_of_image_bounded** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：UniformOnFun.continuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInd
ucing (ofFun 𝔖 ∘ φ)) (h : forall u : H, forall s in 𝔖, Bornology.IsVonNBounded 𝕜
 ((φ u : α -> E) '' s)) : ContinuousSMul 𝕜 H
参数：φ : hom；hφ : IsInducing (ofFun 𝔖 ∘ φ)；h : forall u : H, forall s in 𝔖, Bornol
ogy.IsVonNBounded 𝕜 ((φ u : α -> E) '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformOnFun.topologicalSpace_eq`：∀ (α : Type u_1) (β : Type u_2) [inst 
: UniformSpace β] (𝔖 : Set (Set α)),   UniformOnFun.topologicalSpace α β 𝔖 =    
 ⨅ s ∈ 𝔖,       Topolo…
· 使用定理 `induced_iInf`：induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} : 
(⨅ i, t i).induced g = ⨅ i, (t i).induced g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `continuousSMul_iInf`：continuousSMul_iInf {ts' : ι -> TopologicalSpace X}
 (h : forall i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i,
 ts' i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `UniformFun.continuousSMul_induced_of_range_bounded`：UniformFun.continuou
sSMul_induced_of_range_bounded (φ : hom) (hφ : IsInducing (ofFun ∘ φ)) (h : fora
ll u : H, Bornology.IsVonNBounded 𝕜 (Set…
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…

--- 原说明 ---
Let `E` be a TVS, `𝔖 : Set (Set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the i
mage of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `Bornology.IsVonNBounded`), t
hen `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

For convenience, we don't literally ask for `H : Submodule (α →ᵤ[𝔖] E)`. Instead
, we prove the
result for any vector space `H` equipped with a linear inducing to `α →ᵤ[𝔖] E`, 
which is often
easier to use. We also state the `Submodule` version as
`UniformOnFun.continuousSMul_submodule_of_image_bounded`.
-/
lemma UniformOnFun.continuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ))
    (h : ∀ u : H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 ((φ u : α → E) '' s)) :
    ContinuousSMul 𝕜 H := by
  obtain rfl := hφ.eq_induced; clear hφ
  simp +instances only [induced_iInf, UniformOnFun.topologicalSpace_eq, induced_compose]
  refine continuousSMul_iInf fun s ↦ continuousSMul_iInf fun hs ↦ ?_
  let : TopologicalSpace H :=
    .induced (UniformFun.ofFun ∘ s.domRestrict ∘ φ) (UniformFun.topologicalSpace s E)
  set φ' : H →ₗ[𝕜] (s → E) :=
    { toFun := s.domRestrict ∘ φ,
      map_smul' := fun c x ↦ by exact congr_arg s.domRestrict (map_smul φ c x),
      map_add' := fun x y ↦ by exact congr_arg s.domRestrict (map_add φ x y) }
  refine UniformFun.continuousSMul_induced_of_range_bounded 𝕜 s E H φ' ⟨rfl⟩ fun u ↦ ?_
  simpa only [Set.image_eq_range] using! h u s hs

/-- Let `E` be a TVS, `𝔖 : Set (Set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `Bornology.IsVonNBounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

If you have a hard time using this lemma, try the one above instead. -/
/-
**UniformOnFun.continuousSMul_submodule_of_image_bounded** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：UniformOnFun.continuousSMul_submodule_of_image_bounded (H : Submodule 𝕜 (α
 ->ᵤ[𝔖] E)) (h : forall u in H, forall s in 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s
)) : @ContinuousSMul 𝕜 H _ _ ((UniformOnFun.topologicalSpace α E 𝔖).induced ((↑)
 : H -> α ->ᵤ[𝔖] E))
参数：H : Submodule 𝕜 (α ->ᵤ[𝔖] E)；h : forall u in H, forall s in 𝔖, Bornology.IsVo
nNBounded 𝕜 (u '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformOnFun.continuousSMul_induced_of_image_bounded`：UniformOnFun.conti
nuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ)) (h 
: forall u : H, forall s in 𝔖, Bornology.I…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)

--- 原说明 ---
Let `E` be a TVS, `𝔖 : Set (Set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the i
mage of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `Bornology.IsVonNBounded`), t
hen `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

If you have a hard time using this lemma, try the one above instead.
-/
theorem UniformOnFun.continuousSMul_submodule_of_image_bounded (H : Submodule 𝕜 (α →ᵤ[𝔖] E))
    (h : ∀ u ∈ H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s)) :
    @ContinuousSMul 𝕜 H _ _ ((UniformOnFun.topologicalSpace α E 𝔖).induced ((↑) : H → α →ᵤ[𝔖] E)) :=
  UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H
    (LinearMap.id.domRestrict H : H →ₗ[𝕜] α → E) IsInducing.subtypeVal fun ⟨u, hu⟩ => h u hu

end Module

