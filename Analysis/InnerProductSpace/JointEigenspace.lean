/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Analysis.InnerProductSpace.Semisimple

/-! # Joint eigenspaces of commuting symmetric operators

This file collects various decomposition results for joint eigenspaces of commuting
symmetric operators on a finite-dimensional inner product space.

## Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that in finite dimensions
  if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `Commute A B` imply that
  `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
  `eigenspace B μ ⊓ eigenspace A ν`
* `LinearMap.IsSymmetric.iSup_iInf_eigenspace_eq_top_of_commute` establishes that in finite
  dimensions, the indexed supremum of the joint eigenspaces of a commuting tuple of symmetric
  linear operators equals `⊤`
* `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute` establishes the
  analogous result to `LinearMap.IsSymmetric.directSum_isInternal_of_commute` for commuting
  tuples of symmetric operators.

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

symmetric operator, simultaneous eigenspaces, joint eigenspaces

-/

public section

open Module.End

namespace LinearMap

namespace IsSymmetric

variable {𝕜 E n m : Type*}

open Submodule

section RCLike

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {α : 𝕜} {A B : E →ₗ[𝕜] E} {T : n → Module.End 𝕜 E}

/-- The joint eigenspaces of a pair of symmetric operators form an
`OrthogonalFamily`. -/
/-
**LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace** 是 Mathlib 中
的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.Is
Symmetric) : OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspa
ce B i.1 : Submodule 𝕜 E)) fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtyp
eₗᵢ
参数：hA : A.IsSymmetric；hB : B.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthogonalFamily.of_pairwise`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RC
Like 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : 
Type u_4} {V : ι →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Ne.eq_def`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `OrthogonalFamily.pairwise`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Typ
e u_4} {V : ι →…
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`：orthogonalFamily_eig
enspaces (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun
 μ => (eigenspace T μ).subtypeₗᵢ

--- 原说明 ---
The joint eigenspaces of a pair of symmetric operators form an
`OrthogonalFamily`.
-/
theorem orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
      fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1, hv2⟩ ↦ by
    obtain (h₁ | h₂) : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

/-- The joint eigenspaces of a family of symmetric operators form an
`OrthogonalFamily`. -/
/-
**LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalFamily_iInf_eigenspaces (hT : forall i, (T i).IsSymmetric) : Ort
hogonalFamily 𝕜 (fun γ : n -> 𝕜 => (⨅ j, eigenspace (T j) (γ j) : Submodule 𝕜 E)
) fun γ : n -> 𝕜 => (⨅ j, eigenspace (T j) (γ j)).subtypeₗᵢ
参数：hT : forall i, (T i).IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`：orthogonalFamily_eig
enspaces (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun
 μ => (eigenspace T μ).subtypeₗᵢ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The joint eigenspaces of a family of symmetric operators form an
`OrthogonalFamily`.
-/
theorem orthogonalFamily_iInf_eigenspaces (hT : ∀ i, (T i).IsSymmetric) :
    OrthogonalFamily 𝕜 (fun γ : n → 𝕜 ↦ (⨅ j, eigenspace (T j) (γ j) : Submodule 𝕜 E))
      fun γ : n → 𝕜 ↦ (⨅ j, eigenspace (T j) (γ j)).subtypeₗᵢ := by
  intro f g hfg Ef Eg
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hfg
  have H := orthogonalFamily_eigenspaces (hT a) ha
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (g _)).mp Eg.2 _

variable [FiniteDimensional 𝕜 E]

open IsFinitelySemisimple

/-- If A and B are commuting symmetric operators on a finite-dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace. -/
/-
**LinearMap.IsSymmetric.iSup_eigenspace_inf_eigenspace_of_commute** 是 Mathlib 中的
一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：iSup_eigenspace_inf_eigenspace_of_commute (hB : B.IsSymmetric) (hAB : Comm
ute A B) : (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α
参数：hB : B.IsSymmetric；hAB : Commute A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.inf_genEigenspace`：∀ {R : Type v} {M : Type w} [inst : CommRin
g R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.End R 
M) (p : Submodule…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot`：orth
ogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) : (⨆ μ, eigenspace
 T μ)ᗮ = ⊥
· 使用定理 `LinearMap.IsSymmetric.restrict_invariant`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…

--- 原说明 ---
If A and B are commuting symmetric operators on a finite-dimensional inner produ
ct space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that
 eigenspace.
-/
theorem iSup_eigenspace_inf_eigenspace_of_commute (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [← Submodule.map_iSup,
    (eigenspace A α).inf_genEigenspace _ (mapsTo_genEigenspace_of_comm hAB α 1)]
  congr 1
  simpa only [genEigenspace_eq_eigenspace, Submodule.orthogonal_eq_bot_iff]
    using orthogonalComplement_iSup_eigenspaces_eq_bot <|
      hB.restrict_invariant <| mapsTo_genEigenspace_of_comm hAB α 1

/-- If A and B are commuting symmetric operators acting on a finite-dimensional inner product space,
then the simultaneous eigenspaces of A and B exhaust the space. -/
/-
**LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute** 
是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute (hA : A.IsSymmetric)
 (hB : B.IsSymmetric) (hAB : Commute A B) : (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspa
ce B γ) = ⊤
参数：hA : A.IsSymmetric；hB : B.IsSymmetric；hAB : Commute A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.IsSymmetric.iSup_eigenspace_inf_eigenspace_of_commute`：iSup_ei
genspace_inf_eigenspace_of_commute (hB : B.IsSymmetric) (hAB : Commute A B) : (⨆
 γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.orthogonal_eq_bot_iff`：orthogonal_eq_bot_iff [K.HasOrthogonalP
rojection] : Kᗮ = ⊥ ↔ K = ⊤
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot`：orth
ogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) : (⨆ μ, eigenspace
 T μ)ᗮ = ⊥

--- 原说明 ---
If A and B are commuting symmetric operators acting on a finite-dimensional inne
r product space,
then the simultaneous eigenspaces of A and B exhaust the space.
-/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspace B γ) = ⊤ := by
  simpa [iSup_eigenspace_inf_eigenspace_of_commute hB hAB] using
    Submodule.orthogonal_eq_bot_iff.mp <| hA.orthogonalComplement_iSup_eigenspaces_eq_bot

/-- Given a commuting pair of symmetric linear operators on a finite-dimensional inner product
space, the space decomposes as an internal direct sum of simultaneous eigenspaces of these
operators. -/
/-
**LinearMap.IsSymmetric.directSum_isInternal_of_commute** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.IsSymmetric`。
形式化陈述：directSum_isInternal_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric) 
(hAB : Commute A B) : DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2
 ⊓ eigenspace B i.1))
参数：hA : A.IsSymmetric；hB : B.IsSymmetric；hAB : Commute A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrthogonalFamily.isInternal_iff`：OrthogonalFamily.isInternal_iff [Decida
bleEq ι] [FiniteDimensional 𝕜 E] {V : ι -> Submodule 𝕜 E} (hV : OrthogonalFamily
 𝕜 (fun i => V i) fun…
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`：orthog
onalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
 OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonal_eq_bot_iff`：orthogonal_eq_bot_iff [K.HasOrthogonalP
rojection] : Kᗮ = ⊥ ↔ K = ⊤
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_comm
ute`：iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute (hA : A.IsSymmetric) 
(hB : B.IsSymmetric) (hAB : Commute A B) : (⨆ α, ⨆ γ, eigenspace …

--- 原说明 ---
Given a commuting pair of symmetric linear operators on a finite-dimensional inn
er product
space, the space decomposes as an internal direct sum of simultaneous eigenspace
s of these
operators.
-/
theorem directSum_isInternal_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : Commute A B) :
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)) := by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB

open scoped Function -- required for scoped `on` notation

/-- A commuting family of symmetric linear maps on a finite-dimensional inner
product space is simultaneously diagonalizable. -/
/-
**LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.IsSymmetric`。
形式化陈述：iSup_iInf_eq_top_of_commute {ι : Type*} {T : ι -> E ->ₗ[𝕜] E} (hT : forall
 i, (T i).IsSymmetric) (h : Pairwise (Commute on T)) : ⨆ χ : ι -> 𝕜, ⨅ i, eigens
pace (T i) (χ i) = ⊤
参数：hT : forall i, (T i).IsSymmetric；h : Pairwise (Commute on T)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`：∀ {R : T
ype u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : 
_root_.Module R M]   {f : Module.End R M}, f.IsFinit…
· 使用定理 `LinearMap.IsSymmetric.isFinitelySemisimple`：isFinitelySemisimple : T.IsF
initelySemisimple
· 使用定理 `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq
_top_of_commute`：iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_t
op_of_commute [FiniteDimensional K M] (f : ι -> Module.End K M) (h : Pairwise…
· 使用定理 `Submodule.orthogonal_eq_bot_iff`：orthogonal_eq_bot_iff [K.HasOrthogonalP
rojection] : Kᗮ = ⊥ ↔ K = ⊤
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot`：orth
ogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) : (⨆ μ, eigenspace
 T μ)ᗮ = ⊥

--- 原说明 ---
A commuting family of symmetric linear maps on a finite-dimensional inner
product space is simultaneously diagonalizable.
-/
theorem iSup_iInf_eq_top_of_commute {ι : Type*} {T : ι → E →ₗ[𝕜] E}
    (hT : ∀ i, (T i).IsSymmetric) (h : Pairwise (Commute on T)) :
    ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i) (χ i) = ⊤ :=
  calc
  _ = ⨆ χ : ι → 𝕜, ⨅ i, maxGenEigenspace (T i) (χ i) :=
    congr(⨆ χ : ι → 𝕜, ⨅ i,
      $(maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) (χ _))).symm
  _ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T h fun _ ↦ by
    rw [← orthogonal_eq_bot_iff,
      congr(⨆ μ, $(maxGenEigenspace_eq_eigenspace (isFinitelySemisimple <| hT _) μ)),
      (hT _).orthogonalComplement_iSup_eigenspaces_eq_bot]

/-- In finite dimensions, given a commuting family of symmetric linear operators, the inner
product space on which they act decomposes as an internal direct sum of joint eigenspaces. -/
/-
**LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute** 是 Mathlib 中的一
个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：directSum_isInternal_of_pairwise_commute [DecidableEq (n -> 𝕜)] (hT : fora
ll i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) : DirectSum.IsInternal (
fun α : n -> 𝕜 => ⨅ j, eigenspace (T j) (α j))
参数：n -> 𝕜；hT : forall i, (T i).IsSymmetric；hC : Pairwise (Commute on T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthogonalFamily.isInternal_iff`：OrthogonalFamily.isInternal_iff [Decida
bleEq ι] [FiniteDimensional 𝕜 E] {V : ι -> Submodule 𝕜 E} (hV : OrthogonalFamily
 𝕜 (fun i => V i) fun…
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces`：orthogonalFamil
y_iInf_eigenspaces (hT : forall i, (T i).IsSymmetric) : OrthogonalFamily 𝕜 (fun 
γ : n -> 𝕜 => (⨅ j, eigenspace (T j) (γ j) : …
· 使用定理 `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`：iSup_iInf_eq_top_of_c
ommute {ι : Type*} {T : ι -> E ->ₗ[𝕜] E} (hT : forall i, (T i).IsSymmetric) (h :
 Pairwise (Commute on T)) : ⨆ χ : ι -> …
· 使用定理 `Submodule.top_orthogonal_eq_bot`：top_orthogonal_eq_bot : (⊤ : Submodule 
𝕜 E)ᗮ = ⊥

--- 原说明 ---
In finite dimensions, given a commuting family of symmetric linear operators, th
e inner
product space on which they act decomposes as an internal direct sum of joint ei
genspaces.
-/
theorem directSum_isInternal_of_pairwise_commute [DecidableEq (n → 𝕜)]
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) :
    DirectSum.IsInternal (fun α : n → 𝕜 ↦ ⨅ j, eigenspace (T j) (α j)) := by
  rw [OrthogonalFamily.isInternal_iff]
  · rw [iSup_iInf_eq_top_of_commute hT hC, top_orthogonal_eq_bot]
  · exact orthogonalFamily_iInf_eigenspaces hT

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute :=
  directSum_isInternal_of_pairwise_commute

end RCLike

end IsSymmetric

end LinearMap

