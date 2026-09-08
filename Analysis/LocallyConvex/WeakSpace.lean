/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! # Closures of convex sets in locally convex spaces

This file contains the standard result that if `E` is a vector space with two locally convex
topologies, then the closure of a convex set is the same in either topology, provided they have the
same collection of continuous linear functionals. In particular, the weak closure of a convex set
in a locally convex space coincides with the closure in the original topology.
Of course, we phrase this in terms of linear maps between locally convex spaces, rather than
creating two separate topologies on the same space.
-/

public section

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]
variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F]

set_option backward.isDefEq.respectTransparency.types false in
variable (𝕜) in
/-- If `E` is a locally convex space over `𝕜` (with `RCLike 𝕜`), and `s : Set E` is `ℝ`-convex, then
the closure of `s` and the weak closure of `s` coincide. More precisely, the topological closure
commutes with `toWeakSpace 𝕜 E`.

This holds more generally for any linear equivalence `e : E ≃ₗ[𝕜] F` between locally convex spaces
such that precomposition with `e` and `e.symm` preserves continuity of linear functionals. See
`LinearEquiv.image_closure_of_convex`. -/
/-
**Convex.toWeakSpace_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.toWeakSpace_closure {s : Set E} (hs : Convex Real s) : (toWeakSpace
 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s)
参数：hs : Convex Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousOn.image_closure`：ContinuousOn.image_closure (hf : ContinuousO
n f (closure s)) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.image_compl`：∀ {α : Type u_3} {β : Type u_4} (f : α ≃ β) (s : Set 
α), ⇑f '' sᶜ = (⇑f '' s)ᶜ
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RCLike.geometric_hahn_banach_closed_point`：geometric_hahn_banach_closed_
point (hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s) : exists (f : Stro
ngDual 𝕜 E) (u : Real), (forall…
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `WeakBilin.eval_continuous`：eval_continuous (y : F) : Continuous fun x : 
WeakBilin B => B x y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `E` is a locally convex space over `𝕜` (with `RCLike 𝕜`), and `s : Set E` is 
`ℝ`-convex, then
the closure of `s` and the weak closure of `s` coincide. More precisely, the top
ological closure
commutes with `toWeakSpace 𝕜 E`.

This holds more generally for any linear equivalence `e : E ≃ₗ[𝕜] F` between loc
ally convex spaces
such that precomposition with `e` and `e.symm` preserves continuity of linear fu
nctionals. See
`LinearEquiv.image_closure_of_convex`.
-/
theorem Convex.toWeakSpace_closure {s : Set E} (hs : Convex ℝ s) :
    (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s) := by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx ↦ ?_)
  obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s) |>.symm.subset hx
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨f, u, hus, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    hs.closure isClosed_closure (by simpa using hx)
  let f' : StrongDual 𝕜 (WeakSpace 𝕜 E) :=
    { toLinearMap := (f : E →ₗ[𝕜] 𝕜).comp ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E →ₗ[𝕜] E)
      cont := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip _ }
  have hux' : u < RCLike.reCLM.comp (f'.restrictScalars ℝ) (toWeakSpace 𝕜 E x) := by simpa [f']
  have hus' : closure (toWeakSpace 𝕜 E '' s) ⊆
      {y | RCLike.reCLM.comp (f'.restrictScalars ℝ) y ≤ u} := by
    refine closure_minimal ?_ <| isClosed_le (by fun_prop) (by fun_prop)
    rintro - ⟨y, hy, rfl⟩
    simpa [f'] using (hus y <| subset_closure hy).le
  exact (hux'.not_ge <| hus' ·)

open ComplexOrder in
/-
**toWeakSpace_closedConvexHull_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toWeakSpace_closedConvexHull_eq {s : Set E} : (toWeakSpace 𝕜 E) '' (closed
ConvexHull 𝕜 s) = closedConvexHull 𝕜 (toWeakSpace 𝕜 E '' s)
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closedConvexHull_eq_closure_convexHull`：closedConvexHull_eq_closure_conv
exHull {s : Set E} : closedConvexHull 𝕜 s = closure (convexHull 𝕜 s)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Convex.toWeakSpace_closure`：Convex.toWeakSpace_closure {s : Set E} (hs :
 Convex Real s) : (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E ''
 s)
· 使用定理 `Convex.lift`：Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s)
 : Convex R s
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `LinearMap.image_convexHull`：LinearMap.image_convexHull (f : E ->ₗ[𝕜] F) 
(s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
-/
theorem toWeakSpace_closedConvexHull_eq {s : Set E} :
    (toWeakSpace 𝕜 E) '' (closedConvexHull 𝕜 s) = closedConvexHull 𝕜 (toWeakSpace 𝕜 E '' s) := by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜),
    ((convex_convexHull 𝕜 s).lift ℝ).toWeakSpace_closure _, closedConvexHull_eq_closure_convexHull]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap s

/-- If `e : E →ₗ[𝕜] F` is a linear map between locally convex spaces, and `f ∘ e` is continuous
for every continuous linear functional `f : StrongDual 𝕜 F`, then `e` commutes with the closure on
convex sets. -/
/-
**LinearMap.image_closure_of_convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.image_closure_of_convex {s : Set E} (hs : Convex Real s) (e : E 
->ₗ[𝕜] F) (he : forall f : StrongDual 𝕜 F, Continuous (e.dualMap f)) : e '' (clo
sure s) subseteq closure (e '' s)
参数：hs : Convex Real s；e : E ->ₗ[𝕜] F；he : forall f : StrongDual 𝕜 F, Continuous 
(e.dualMap f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `WeakBilin.continuous_of_continuous_eval`：continuous_of_continuous_eval [
TopologicalSpace α] {g : α -> WeakBilin B} (h : forall y, Continuous fun a => B 
(g a) y) : Continuous g
· 使用定理 `WeakBilin.eval_continuous`：eval_continuous (y : F) : Continuous fun x : 
WeakBilin B => B x y
· 使用定理 `Convex.linear_image`：Convex.linear_image (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜]
 F) : Convex 𝕜 (f '' s)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Convex.toWeakSpace_closure`：Convex.toWeakSpace_closure {s : Set E} (hs :
 Convex Real s) : (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E ''
 s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `ContinuousOn.image_closure`：ContinuousOn.image_closure (hf : ContinuousO
n f (closure s)) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
If `e : E →ₗ[𝕜] F` is a linear map between locally convex spaces, and `f ∘ e` is
 continuous
for every continuous linear functional `f : StrongDual 𝕜 F`, then `e` commutes w
ith the closure on
convex sets.
-/
theorem LinearMap.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E →ₗ[𝕜] F)
    (he : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f)) :
    e '' (closure s) ⊆ closure (e '' s) := by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex ℝ (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective, h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toWeakSpace_closure 𝕜, LinearEquiv.symm_apply_apply]
      using he'.continuousOn.image_closure (s := toWeakSpace 𝕜 E '' s)
  exact WeakBilin.continuous_of_continuous_eval _ fun f ↦ WeakBilin.eval_continuous _ ({
      toLinearMap := e.dualMap f
      cont := by dsimp; fun_prop } : StrongDual 𝕜 E)

/-- If `e` is a linear isomorphism between two locally convex spaces, and `e` induces (via
precomposition) an isomorphism between their continuous duals, then `e` commutes with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeakSpace_closure`. -/
/-
**LinearEquiv.image_closure_of_convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.image_closure_of_convex {s : Set E} (hs : Convex Real s) (e : 
E ≃ₗ[𝕜] F) (he₁ : forall f : StrongDual 𝕜 F, Continuous (e.dualMap f)) (he₂ : fo
rall f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)) : e '' (closure s) = clo
sure (e '' s)
参数：hs : Convex Real s；e : E ≃ₗ[𝕜] F；he₁ : forall f : StrongDual 𝕜 F, Continuous 
(e.dualMap f)；he₂ : forall f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.image_closure_of_convex`：LinearMap.image_closure_of_convex {s 
: Set E} (hs : Convex Real s) (e : E ->ₗ[𝕜] F) (he : forall f : StrongDual 𝕜 F, 
Continuous (e.dualMap f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Convex.linear_image`：Convex.linear_image (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜]
 F) : Convex 𝕜 (f '' s)

--- 原说明 ---
If `e` is a linear isomorphism between two locally convex spaces, and `e` induce
s (via
precomposition) an isomorphism between their continuous duals, then `e` commutes
 with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeak
Space_closure`.
-/
theorem LinearEquiv.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (he₁ : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f))
    (he₂ : ∀ f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)) :
    e '' (closure s) = closure (e '' s) := by
  refine le_antisymm ((e : E →ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F →ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E →ₗ[𝕜] F)) he₂

/-- If `e` is a linear isomorphism between two locally convex spaces, and `e` induces (via
precomposition) an isomorphism between their continuous duals, then `e` commutes with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeakSpace_closure`. -/
/-
**LinearEquiv.image_closure_of_convex'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.image_closure_of_convex' {s : Set E} (hs : Convex Real s) (e :
 E ≃ₗ[𝕜] F) (e_dual : StrongDual 𝕜 F ≃ StrongDual 𝕜 E) (he : forall f : StrongDu
al 𝕜 F, (e_dual f : E ->ₗ[𝕜] 𝕜) = e.dualMap f) : e '' (closure s) = closure (e '
' s)
参数：hs : Convex Real s；e : E ≃ₗ[𝕜] F；e_dual : StrongDual 𝕜 F ≃ StrongDual 𝕜 E；he 
: forall f : StrongDual 𝕜 F, (e_dual f : E ->ₗ[𝕜] 𝕜) = e.dualMap f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.dualMap_apply`：LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (
g : Dual R M₂) (x : M₁) : f.dualMap g x = g (f x)
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.image_closure_of_convex`：LinearEquiv.image_closure_of_convex
 {s : Set E} (hs : Convex Real s) (e : E ≃ₗ[𝕜] F) (he₁ : forall f : StrongDual 𝕜
 F, Continuous (e.dualMap…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…

--- 原说明 ---
If `e` is a linear isomorphism between two locally convex spaces, and `e` induce
s (via
precomposition) an isomorphism between their continuous duals, then `e` commutes
 with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeak
Space_closure`.
-/
theorem LinearEquiv.image_closure_of_convex' {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (e_dual : StrongDual 𝕜 F ≃ StrongDual 𝕜 E)
    (he : ∀ f : StrongDual 𝕜 F, (e_dual f : E →ₗ[𝕜] 𝕜) = e.dualMap f) :
    e '' (closure s) = closure (e '' s) := by
  have he' (f : StrongDual 𝕜 E) : (e_dual.symm f : F →ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : StrongDual 𝕜 E) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
    ext x
    conv_rhs => rw [LinearEquiv.dualMap_apply, ContinuousLinearMap.coe_coe, this]
    simp
  refine e.image_closure_of_convex hs ?_ ?_
  · simpa [← he] using fun f ↦ map_continuous (e_dual f)
  · simpa [← he'] using fun f ↦ map_continuous (e_dual.symm f)

/-- The weak topology on a space with separating dual is T2 (Hausdorff). -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak topology on a space with separating dual is T2 (Hausdorff).
-/
instance {R V : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]
    [ContinuousAdd R] [ContinuousConstSMul R R] [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [SeparatingDual R V] : T2Space (WeakSpace R V) :=
  (WeakBilin.isEmbedding (B := (topDualPairing R V).flip) fun _ _ h => by
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := R) hne
    exact hf (DFunLike.congr_fun h f)).t2Space
