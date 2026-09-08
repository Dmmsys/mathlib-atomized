/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Lagrange multipliers

In this file we formalize the
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) method of solving
conditional extremum problems: if a function `φ` has a local extremum at `x₀` on the set
`f ⁻¹' {f x₀}`, `f x = (f₀ x, ..., fₙ₋₁ x)`, then the differentials of `fₖ` and `φ` are linearly
dependent. First we formulate a geometric version of this theorem which does not rely on the
target space being `ℝⁿ`, then restate it in terms of coordinates.

## TODO

Formalize Karush-Kuhn-Tucker theorem

## Tags

lagrange multiplier, local extremum

-/

public section


open Filter Set

open scoped Topology Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {φ : E → ℝ} {x₀ : E}
  {f' : E →L[ℝ] F} {φ' : StrongDual ℝ E}

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then the linear map `x ↦ (f' x, φ' x)` is not surjective. -/
/-
**IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt (hextr : IsLocalExtrOn φ {
x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀) (hφ' : HasStrictFDerivAt φ
 φ' x₀) : (f'.prod φ').range != ⊤
参数：hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀；hf' : HasStrictFDerivAt f f' x₀；h
φ' : HasStrictFDerivAt φ φ' x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.map_inf_principal_preimage`：map_inf_principal_preimage {f : α -> 
β} {s : Set β} {l : Filter α} : map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s
· 使用定理 `HasStrictFDerivAt.map_nhds_eq_of_surj`：map_nhds_eq_of_surj [CompleteSpac
e E] [CompleteSpace F] {f : E -> F} {f' : E ->L[𝕜] F} {a : E} (hf : HasStrictFDe
rivAt f (f' : E ->L[𝕜] F) a…
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `map_snd_nhdsWithin`：map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Pro
d.fst ⁻¹' {x.1}] x) = 𝓝 x.2
· 使用定理 `IsLocalExtrOn.not_nhds_le_map`：IsLocalExtrOn.not_nhds_le_map [Topologica
lSpace β] (hf : IsLocalExtrOn f s a) [NeBot (𝓝[<] f a)] [NeBot (𝓝[>] f a)] : ¬𝓝 
(f a) <= map f (𝓝[s…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x
 | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the c
odomain of `f` is
a complete space, then the linear map `x ↦ (f' x, φ' x)` is not surjective.
-/
theorem IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) : (f'.prod φ').range ≠ ⊤ := by
  intro htop
  set fφ := fun x => (f x, φ x)
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀) := by
    change map (Prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀)
    rw [← map_map, nhdsWithin, map_inf_principal_preimage,
      (hf'.prodMk hφ').map_nhds_eq_of_surj htop]
    exact map_snd_nhdsWithin _
  exact hextr.not_nhds_le_map A.ge

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then there exist `Λ : dual ℝ F` and `Λ₀ : ℝ` such that `(Λ, Λ₀) ≠ 0` and
`Λ (f' x) + Λ₀ • φ' x = 0` for all `x`. -/
/-
**IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt (hextr : IsLocalExtrO
n φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀) (hφ' : HasStrictFDeri
vAt φ φ' x₀) : exists (Λ : Module.Dual Real F) (Λ₀ : Real), (Λ, Λ₀) != 0 ∧ foral
l x, Λ (f' x) + Λ₀ • φ' x = 0
参数：hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀；hf' : HasStrictFDerivAt f f' x₀；h
φ' : HasStrictFDerivAt φ φ' x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_le_ker_of_lt_top`：Submodule.exists_le_ker_of_lt_top (p 
: Submodule K V) (hp : p < ⊤) : exists (f : V ->ₗ[K] K), f != 0 ∧ p <= ker f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt`：IsLocalExtrOn.range_ne_
top_of_hasStrictFDerivAt (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : Ha
sStrictFDerivAt f f' x₀) (hφ' : HasSt…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.map_ne_zero_iff`：map_ne_zero_iff {x : M} : e x != 0 ↔ x != 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.coprodEquiv_apply`：∀ {R : Type u} {M : Type v} {M₂ : Type w} {
M₃ : Type y} (S : Type u_3) [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 
: AddCommMonoid M…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0

--- 原说明 ---
Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x
 | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the c
odomain of `f` is
a complete space, then there exist `Λ : dual ℝ F` and `Λ₀ : ℝ` such that `(Λ, Λ₀
) ≠ 0` and
`Λ (f' x) + Λ₀ • φ' x = 0` for all `x`.
-/
theorem IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ∃ (Λ : Module.Dual ℝ F) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, Λ (f' x) + Λ₀ • φ' x = 0 := by
  rcases Submodule.exists_le_ker_of_lt_top _
      (lt_top_iff_ne_top.2 <| hextr.range_ne_top_of_hasStrictFDerivAt hf' hφ') with
    ⟨Λ', h0, hΛ'⟩
  set e : ((F →ₗ[ℝ] ℝ) × ℝ) ≃ₗ[ℝ] F × ℝ →ₗ[ℝ] ℝ :=
    ((LinearEquiv.refl ℝ (F →ₗ[ℝ] ℝ)).prodCongr (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm).trans
      (LinearMap.coprodEquiv ℝ)
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩
  refine ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, fun x => ?_⟩
  convert! LinearMap.congr_fun (LinearMap.range_le_ker_iff.1 hΛ') x using 1
    -- squeezed `simp [mul_comm]` to speed up elaboration

  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [e, smul_eq_mul, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.coprodEquiv_apply,
    ContinuousLinearMap.coe_prod, LinearMap.coprod_comp_prod, LinearMap.add_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, LinearMap.coe_smulRight,
    Module.End.one_apply, mul_comm]

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, and both `f : E → ℝ` and `φ` are strictly differentiable at `x₀`, then there exist
`a b : ℝ` such that `(a, b) ≠ 0` and `a • f' + b • φ' = 0`. -/
/-
**IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d {f : E -> Real} {
f' : StrongDual Real E} (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : Has
StrictFDerivAt f f' x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) : exists a b : Real, (
a, b) != 0 ∧ a • f' + b • φ' = 0
参数：hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀；hf' : HasStrictFDerivAt f f' x₀；h
φ' : HasStrictFDerivAt φ φ' x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt`：IsLocalExtrOn.exis
ts_linear_map_of_hasStrictFDerivAt (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀)
 (hf' : HasStrictFDerivAt f f' x₀) (hφ' : …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…

--- 原说明 ---
Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x
 | f x = f x₀}`
at `x₀`, and both `f : E → ℝ` and `φ` are strictly differentiable at `x₀`, then 
there exist
`a b : ℝ` such that `(a, b) ≠ 0` and `a • f' + b • φ' = 0`.
-/
theorem IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d {f : E → ℝ} {f' : StrongDual ℝ E}
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) : ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • f' + b • φ' = 0 := by
  obtain ⟨Λ, Λ₀, hΛ, hfΛ⟩ := hextr.exists_linear_map_of_hasStrictFDerivAt hf' hφ'
  refine ⟨Λ 1, Λ₀, ?_, ?_⟩
  · contrapose hΛ
    simp only [Prod.mk_eq_zero] at hΛ ⊢
    refine ⟨LinearMap.ext fun x => ?_, hΛ.2⟩
    simpa [hΛ.1] using Λ.map_smul x 1
  · ext x
    have H₁ : Λ (f' x) = f' x * Λ 1 := by
      simpa only [mul_one, smul_eq_mul] using Λ.map_smul (f' x) 1
    have H₂ : f' x * Λ 1 + Λ₀ * φ' x = 0 := by simpa only [smul_eq_mul, H₁] using hfΛ x
    simpa [mul_comm] using H₂

/-- Lagrange multipliers theorem, 1d version. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : StrongDual ℝ E` are linearly dependent:
there exist `Λ : ι → ℝ` and `Λ₀ : ℝ`, `(Λ, Λ₀) ≠ 0`, such that `∑ i, Λ i • f' i + Λ₀ • φ' = 0`.

See also `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt` for a version that
states `¬LinearIndependent ℝ _` instead of existence of `Λ` and `Λ₀`. -/
/-
**IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt {ι : Type*} [Fintype
 ι] {f : ι -> E -> Real} {f' : ι -> StrongDual Real E} (hextr : IsLocalExtrOn φ 
{x | forall i, f i x = f i x₀} x₀) (hf' : forall i, HasStrictFDerivAt (f i) (f' 
i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) : exists (Λ : ι -> Real) (Λ₀ : Real), (
Λ, Λ₀) != 0 ∧ (∑ i, Λ i • f' i) + Λ₀ • φ' = 0
参数：hextr : IsLocalExtrOn φ {x | forall i, f i x = f i x₀} x₀；hf' : forall i, Has
StrictFDerivAt (f i) (f' i) x₀；hφ' : HasStrictFDerivAt φ φ' x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt`：IsLocalExtrOn.exis
ts_linear_map_of_hasStrictFDerivAt (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀)
 (hf' : HasStrictFDerivAt f f' x₀) (hφ' : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `LinearEquiv.piRing_symm_apply`：piRing_symm_apply (f : ι -> M) (g : ι -> 
R) : (piRing R M ι S).symm f g = ∑ i, g i • f i
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Lagrange multipliers theorem, 1d version. Let `f : ι → E → ℝ` be a finite family
 of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i 
x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `
x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : StrongDual ℝ E` are linearly 
dependent:
there exist `Λ : ι → ℝ` and `Λ₀ : ℝ`, `(Λ, Λ₀) ≠ 0`, such that `∑ i, Λ i • f' i 
+ Λ₀ • φ' = 0`.

See also `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt` for a version tha
t
states `¬LinearIndependent ℝ _` instead of existence of `Λ` and `Λ₀`.
-/
theorem IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt {ι : Type*} [Fintype ι]
    {f : ι → E → ℝ} {f' : ι → StrongDual ℝ E} (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀)
    (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ (∑ i, Λ i • f' i) + Λ₀ • φ' = 0 := by
  let := Classical.decEq ι
  replace hextr : IsLocalExtrOn φ {x | (fun i => f i x) = fun i => f i x₀} x₀ := by
    simpa only [funext_iff] using hextr
  rcases hextr.exists_linear_map_of_hasStrictFDerivAt (hasStrictFDerivAt_pi.2 fun i => hf' i)
      hφ' with
    ⟨Λ, Λ₀, h0, hsum⟩
  rcases (LinearEquiv.piRing ℝ ℝ ι ℝ).symm.surjective Λ with ⟨Λ, rfl⟩
  refine ⟨Λ, Λ₀, ?_, ?_⟩
  · simpa only [Ne, Prod.ext_iff, LinearEquiv.map_eq_zero_iff, Prod.fst_zero] using! h0
  · ext x; simpa [mul_comm] using hsum x

/-- Lagrange multipliers theorem. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : StrongDual ℝ E` are linearly dependent.

See also `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` for a version that
that states existence of Lagrange multipliers `Λ` and `Λ₀` instead of using
`¬LinearIndependent ℝ _` -/
/-
**IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt {ι : Type*} [Finite ι]
 {f : ι -> E -> Real} {f' : ι -> StrongDual Real E} (hextr : IsLocalExtrOn φ {x 
| forall i, f i x = f i x₀} x₀) (hf' : forall i, HasStrictFDerivAt (f i) (f' i) 
x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) : ¬LinearIndependent Real (Option.elim' φ'
 f' : Option ι -> StrongDual Real E)
参数：hextr : IsLocalExtrOn φ {x | forall i, f i x = f i x₀} x₀；hf' : forall i, Has
StrictFDerivAt (f i) (f' i) x₀；hφ' : HasStrictFDerivAt φ φ' x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`：IsLocalExtrOn.exi
sts_multipliers_of_hasStrictFDerivAt {ι : Type*} [Fintype ι] {f : ι -> E -> Real
} {f' : ι -> StrongDual Real E} (hextr : Is…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Lagrange multipliers theorem. Let `f : ι → E → ℝ` be a finite family of function
s.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i 
x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `
x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : StrongDual ℝ E` are linearly 
dependent.

See also `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` for a version t
hat
that states existence of Lagrange multipliers `Λ` and `Λ₀` instead of using
`¬LinearIndependent ℝ _`
-/
theorem IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt {ι : Type*} [Finite ι] {f : ι → E → ℝ}
    {f' : ι → StrongDual ℝ E} (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀)
    (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ¬LinearIndependent ℝ (Option.elim' φ' f' : Option ι → StrongDual ℝ E) := by
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]; push Not
  rcases hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
  refine ⟨Option.elim' Λ₀ Λ, ?_, ?_⟩
  · simpa [add_comm] using hΛf
  · simpa only [funext_iff, not_and_or, or_comm, Option.exists, Prod.mk_eq_zero, Ne,
      not_forall] using! hΛ
