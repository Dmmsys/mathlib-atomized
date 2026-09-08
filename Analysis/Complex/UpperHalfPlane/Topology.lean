/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Topology on the upper half plane

In this file we introduce a `TopologicalSpace` structure on the upper half plane and provide
various instances.
-/

@[expose] public section

noncomputable section

open Complex Filter Function Set TopologicalSpace Topology

open scoped ComplexConjugate

namespace UpperHalfPlane

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace ℍ :=
  .induced UpperHalfPlane.coe inferInstance

@[fun_prop]
/-
**UpperHalfPlane.isEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isEmbedding_coe : IsEmbedding ((↑) : ℍ -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isEmbedding_induced`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [t : TopologicalSpace Y], Function.Injective f → Topology.IsEmbeddin
g f
· 使用定理 `UpperHalfPlane.coe_injective`：coe_injective : Function.Injective UpperHa
lfPlane.coe
-/
theorem isEmbedding_coe : IsEmbedding ((↑) : ℍ → ℂ) :=
  coe_injective.isEmbedding_induced
/-
**UpperHalfPlane.isOpenEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℍ -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : ℍ -
> Complex)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.range_coe`：range_coe : Set.range UpperHalfPlane.coe = ℍₒ
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℍ → ℂ) :=
  ⟨isEmbedding_coe, by simp [isOpen_upperHalfPlaneSet]⟩

@[fun_prop]
/-
**UpperHalfPlane.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：continuous_coe : Continuous ((↑) : ℍ -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `UpperHalfPlane.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : ℍ -
> Complex)
-/
theorem continuous_coe : Continuous ((↑) : ℍ → ℂ) :=
  isEmbedding_coe.continuous

@[fun_prop]
/-
**UpperHalfPlane.continuous_re** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：continuous_re : Continuous re
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
-/
theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe

@[fun_prop]
/-
**UpperHalfPlane.continuous_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：continuous_im : Continuous im
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
-/
theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe

@[fun_prop]
/-
**UpperHalfPlane._root_.Continuous.upperHalfPlaneMk** 是 Mathlib 中的一个定理，位于命名空间 `U
pperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.upperHalfPlaneMk {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (hf₀ : ∀ x, 0 < (f x).im) :
    Continuous fun x ↦ mk (f x) (hf₀ x) :=
  isEmbedding_coe.continuous_iff.mpr hf
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SecondCountableTopology ℍ :=
  secondCountableTopology_induced ..
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T3Space ℍ := isEmbedding_coe.t3Space
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T4Space ℍ := inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContractibleSpace ℍ := by
  rw [isEmbedding_coe.toHomeomorph.trans (.setCongr range_coe) |>.contractibleSpace_iff]
  exact (convex_halfSpace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyPathConnectedSpace ℍ := isOpenEmbedding_coe.locallyPathConnectedSpace
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoncompactSpace ℍ where
  noncompact_univ h := by
    have : IsCompact (Complex.im ⁻¹' Ioi 0) := by
      simpa [isEmbedding_coe.isCompact_iff] using! h
    simpa [closure_preimage_im] using! congr(0 ∈ $this.isClosed.closure_eq)
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyCompactSpace ℍ :=
  isOpenEmbedding_coe.locallyCompactSpace

/-- Each element of `GL(2, ℝ)` defines a continuous map `ℍ → ℍ`. -/
/-
**UpperHalfPlane.instContinuousGLSMul** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`
。
形式化陈述：instContinuousGLSMul : ContinuousConstSMul (GL (Fin 2) Real) ℍ where conti
nuous_const_smul g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Complex.continuous_conj`：Continuous ⇑(starRingEnd ℂ)
· 使用定理 `Continuous.div`：Continuous.div (hf : Continuous f) (hg : Continuous g) (
h₀ : forall x, g x != 0) : Continuous (f / g)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0

--- 原说明 ---
Each element of `GL(2, ℝ)` defines a continuous map `ℍ → ℍ`.
-/
instance instContinuousGLSMul : ContinuousConstSMul (GL (Fin 2) ℝ) ℍ where
  continuous_const_smul g := by
    simp_rw [continuous_induced_rng (f := UpperHalfPlane.coe), Function.comp_def,
      UpperHalfPlane.coe_smul, UpperHalfPlane.σ]
    refine .comp ?_ ?_
    · split_ifs
      exacts [continuous_id, continuous_conj]
    · refine .div ?_ ?_ (fun x ↦ denom_ne_zero g x) <;>
      exact (continuous_const.mul continuous_coe).add continuous_const

section strips

/-- The vertical strip of width `A` and height `B`, defined by elements whose real part has absolute
value less than or equal to `A` and imaginary part is at least `B`. -/
/-
**UpperHalfPlane.verticalStrip** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：verticalStrip (A B : Real)
参数：A B : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical strip of width `A` and height `B`, defined by elements whose real p
art has absolute
value less than or equal to `A` and imaginary part is at least `B`.
-/
def verticalStrip (A B : ℝ) := {z : ℍ | |z.re| ≤ A ∧ B ≤ z.im}
/-
**UpperHalfPlane.mem_verticalStrip_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：mem_verticalStrip_iff (A B : Real) (z : ℍ) : z in verticalStrip A B ↔ |z.r
e| <= A ∧ B <= z.im
参数：A B : Real；z : ℍ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_verticalStrip_iff (A B : ℝ) (z : ℍ) : z ∈ verticalStrip A B ↔ |z.re| ≤ A ∧ B ≤ z.im :=
  Iff.rfl

@[gcongr]
/-
**UpperHalfPlane.verticalStrip_mono** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：verticalStrip_mono {A B A' B' : Real} (hA : A <= A') (hB : B' <= B) : vert
icalStrip A B subseteq verticalStrip A' B'
参数：hA : A <= A'；hB : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma verticalStrip_mono {A B A' B' : ℝ} (hA : A ≤ A') (hB : B' ≤ B) :
    verticalStrip A B ⊆ verticalStrip A' B' := by
  rintro z ⟨hzre, hzim⟩
  exact ⟨hzre.trans hA, hB.trans hzim⟩
/-
**UpperHalfPlane.verticalStrip_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：verticalStrip_mono_left {A A'} (h : A <= A') (B) : verticalStrip A B subse
teq verticalStrip A' B
参数：h : A <= A'；B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.verticalStrip_mono`：verticalStrip_mono {A B A' B' : Real}
 (hA : A <= A') (hB : B' <= B) : verticalStrip A B subseteq verticalStrip A' B'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma verticalStrip_mono_left {A A'} (h : A ≤ A') (B) : verticalStrip A B ⊆ verticalStrip A' B :=
  verticalStrip_mono h le_rfl
/-
**UpperHalfPlane.verticalStrip_anti_right** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPl
ane`。
形式化陈述：verticalStrip_anti_right (A) {B B'} (h : B' <= B) : verticalStrip A B subs
eteq verticalStrip A B'
参数：A；h : B' <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.verticalStrip_mono`：verticalStrip_mono {A B A' B' : Real}
 (hA : A <= A') (hB : B' <= B) : verticalStrip A B subseteq verticalStrip A' B'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma verticalStrip_anti_right (A) {B B'} (h : B' ≤ B) : verticalStrip A B ⊆ verticalStrip A B' :=
  verticalStrip_mono le_rfl h
/-
**UpperHalfPlane.subset_verticalStrip_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 `Up
perHalfPlane`。
形式化陈述：subset_verticalStrip_of_isCompact {K : Set ℍ} (hK : IsCompact K) : exists 
A B : Real, 0 < B ∧ K subseteq verticalStrip A B
参数：hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Real.zero_lt_one`：0 < 1
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G], …
· 使用定理 `UpperHalfPlane.continuous_re`：continuous_re : Continuous re
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `UpperHalfPlane.continuous_im`：continuous_im : Continuous im
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isMaxOn_iff`：isMaxOn_iff : IsMaxOn f s a ↔ forall x in s, f x <= f a
· 使用定理 `isMinOn_iff`：isMinOn_iff : IsMinOn f s a ↔ forall x in s, f a <= f x
-/
lemma subset_verticalStrip_of_isCompact {K : Set ℍ} (hK : IsCompact K) :
    ∃ A B : ℝ, 0 < B ∧ K ⊆ verticalStrip A B := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, Real.zero_lt_one, empty_subset _⟩
  obtain ⟨u, _, hu⟩ := hK.exists_isMaxOn hne (_root_.continuous_abs.comp continuous_re).continuousOn
  obtain ⟨v, _, hv⟩ := hK.exists_isMinOn hne continuous_im.continuousOn
  exact ⟨|re u|, im v, v.im_pos, fun k hk ↦ ⟨isMaxOn_iff.mp hu _ hk, isMinOn_iff.mp hv _ hk⟩⟩
/-
**UpperHalfPlane.ModularGroup_T_zpow_mem_verticalStrip** 是 Mathlib 中的一个定理，位于命名空间
 `UpperHalfPlane`。
形式化陈述：ModularGroup_T_zpow_mem_verticalStrip (z : ℍ) {N : Nat} (hn : 0 < N) : exi
sts n : Int, ModularGroup.T ^ (N * n) • z in verticalStrip N z.im
参数：z : ℍ；hn : 0 < N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.modular_T_zpow_smul`：modular_T_zpow_smul (z : ℍ) (n : Int
) : ModularGroup.T ^ n • z = (n : Real) +ᵥ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 48 条，此处仅展示前 30 条）
-/
theorem ModularGroup_T_zpow_mem_verticalStrip (z : ℍ) {N : ℕ} (hn : 0 < N) :
    ∃ n : ℤ, ModularGroup.T ^ (N * n) • z ∈ verticalStrip N z.im := by
  let n := Int.floor (z.re / N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, by simp⟩
  have h : (N * (-n : ℝ) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [n, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h, add_comm]
  simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  have hnn : (0 : ℝ) < (N : ℝ) := by norm_cast at *
  have h2 : z.re + -(N * n) = z.re - n * N := by ring
  rw [h2, abs_eq_self.2 (Int.sub_floor_div_mul_nonneg (z.re : ℝ) hnn)]
  apply (Int.sub_floor_div_mul_lt (z.re : ℝ) hnn).le

end strips

section ofComplex

/-- A section `ℂ → ℍ` of the natural inclusion map, bundled as an `OpenPartialHomeomorph`. -/
/-
**UpperHalfPlane.ofComplex** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：ofComplex : OpenPartialHomeomorph Complex ℍ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A section `ℂ → ℍ` of the natural inclusion map, bundled as an `OpenPartialHomeom
orph`.
-/
def ofComplex : OpenPartialHomeomorph ℂ ℍ := (isOpenEmbedding_coe.toOpenPartialHomeomorph _).symm

/-- Extend a function on `ℍ` arbitrarily to a function on all of `ℂ`. -/
scoped notation "↑ₕ" f => f ∘ ofComplex

@[simp]
/-
**UpperHalfPlane.ofComplex_apply** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：ofComplex_apply (z : ℍ) : ofComplex (z : Complex) = z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv`：toOpenPartial
Homeomorph_left_inv {x : X} : (h.toOpenPartialHomeomorph f).symm (f x) = x
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma ofComplex_apply (z : ℍ) : ofComplex (z : ℂ) = z :=
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ..
/-
**UpperHalfPlane.ofComplex_apply_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：ofComplex_apply_eq_ite (w : Complex) : ofComplex w = if hw : 0 < w.im then
 ⟨w, hw⟩ else Classical.choice inferInstance
参数：w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
lemma ofComplex_apply_eq_ite (w : ℂ) :
    ofComplex w = if hw : 0 < w.im then ⟨w, hw⟩ else Classical.choice inferInstance := by
  split_ifs with hw
  · exact ofComplex_apply ⟨w, hw⟩
  · change (Function.invFunOn UpperHalfPlane.coe Set.univ w) = _
    simp only [invFunOn, dite_eq_right_iff, mem_univ, true_and]
    rintro ⟨a, rfl⟩
    exact (a.im_pos.not_ge (by simpa using hw)).elim
/-
**UpperHalfPlane.ofComplex_apply_of_im_pos** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：ofComplex_apply_of_im_pos {z : Complex} (hz : 0 < z.im) : ofComplex z = ⟨z
, hz⟩
参数：hz : 0 < z.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
-/
lemma ofComplex_apply_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    ofComplex z = ⟨z, hz⟩ :=
  ofComplex_apply ⟨z, hz⟩
/-
**UpperHalfPlane.ofComplex_apply_of_im_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：ofComplex_apply_of_im_nonpos {w : Complex} (hw : w.im <= 0) : ofComplex w 
= Classical.choice inferInstance
参数：hw : w.im <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply_eq_ite`：ofComplex_apply_eq_ite (w : Compl
ex) : ofComplex w = if hw : 0 < w.im then ⟨w, hw⟩ else Classical.choice inferIns
tance
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma ofComplex_apply_of_im_nonpos {w : ℂ} (hw : w.im ≤ 0) :
    ofComplex w = Classical.choice inferInstance := by
  simp [ofComplex_apply_eq_ite w, hw]
/-
**UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Uppe
rHalfPlane`。
形式化陈述：ofComplex_apply_eq_of_im_nonpos {w w' : Complex} (hw : w.im <= 0) (hw' : w
'.im <= 0) : ofComplex w = ofComplex w'
参数：hw : w.im <= 0；hw' : w'.im <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_nonpos`：ofComplex_apply_of_im_nonpo
s {w : Complex} (hw : w.im <= 0) : ofComplex w = Classical.choice inferInstance
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofComplex_apply_eq_of_im_nonpos {w w' : ℂ} (hw : w.im ≤ 0) (hw' : w'.im ≤ 0) :
    ofComplex w = ofComplex w' := by
  simp [ofComplex_apply_of_im_nonpos, hw, hw']
/-
**UpperHalfPlane.comp_ofComplex** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：comp_ofComplex (f : ℍ -> Complex) (z : ℍ) : (↑ₕf) z = f z
参数：f : ℍ -> Complex；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
-/
lemma comp_ofComplex (f : ℍ → ℂ) (z : ℍ) : (↑ₕf) z = f z :=
  congrArg _ <| ofComplex_apply z
/-
**UpperHalfPlane.comp_ofComplex_of_im_pos** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPl
ane`。
形式化陈述：comp_ofComplex_of_im_pos (f : ℍ -> Complex) (z : Complex) (hz : 0 < z.im) 
: (↑ₕf) z = f ⟨z, hz⟩
参数：f : ℍ -> Complex；z : Complex；hz : 0 < z.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
-/
lemma comp_ofComplex_of_im_pos (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im) : (↑ₕf) z = f ⟨z, hz⟩ :=
  congrArg _ <| ofComplex_apply ⟨z, hz⟩
/-
**UpperHalfPlane.comp_ofComplex_of_im_le_zero** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：comp_ofComplex_of_im_le_zero (f : ℍ -> Complex) (z z' : Complex) (hz : z.i
m <= 0) (hz' : z'.im <= 0) : (↑ₕf) z = (↑ₕf) z'
参数：f : ℍ -> Complex；z z' : Complex；hz : z.im <= 0；hz' : z'.im <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_nonpos`：ofComplex_apply_of_im_nonpo
s {w : Complex} (hw : w.im <= 0) : ofComplex w = Classical.choice inferInstance
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_ofComplex_of_im_le_zero (f : ℍ → ℂ) (z z' : ℂ) (hz : z.im ≤ 0) (hz' : z'.im ≤ 0) :
    (↑ₕf) z = (↑ₕf) z' := by
  simp [ofComplex_apply_of_im_nonpos, hz, hz']
/-
**UpperHalfPlane.eventuallyEq_coe_comp_ofComplex** 是 Mathlib 中的一个引理，位于命名空间 `Uppe
rHalfPlane`。
形式化陈述：eventuallyEq_coe_comp_ofComplex {z : Complex} (hz : 0 < z.im) : UpperHalfP
lane.coe ∘ ofComplex =ᶠ[𝓝 z] id
参数：hz : 0 < z.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_pos`：ofComplex_apply_of_im_pos {z :
 Complex} (hz : 0 < z.im) : ofComplex z = ⟨z, hz⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eventuallyEq_coe_comp_ofComplex {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.coe ∘ ofComplex =ᶠ[𝓝 z] id := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with x hx
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hx, id_eq]

@[fun_prop]
/-
**UpperHalfPlane.continuousOn_ofComplex_I_mul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：continuousOn_ofComplex_I_mul : ContinuousOn (fun t : Real => ofComplex (I 
* t)) (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `UpperHalfPlane.ofComplex_apply_eq_ite`：ofComplex_apply_eq_ite (w : Compl
ex) : ofComplex w = if hw : 0 < w.im then ⟨w, hw⟩ else Classical.choice inferIns
tance
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.congr`：Continuous.congr {g : X -> Y} (h : Continuous f) (h' :
 forall x, f x = g x) : Continuous g
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma continuousOn_ofComplex_I_mul :
    ContinuousOn (fun t : ℝ ↦ ofComplex (I * t)) (Set.Ioi 0) := by
  simp only [ofComplex_apply_eq_ite, continuousOn_iff_continuous_domRestrict,
    continuous_induced_rng]
  have : Continuous (fun t : ℝ ↦ Complex.I * t) := by fun_prop
  exact (this.comp continuous_subtype_val).congr (by simp +contextual)
/-
**UpperHalfPlane.J_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：J_smul (τ : ℍ) : J • τ = ofComplex (-(conj ↑τ))
参数：τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.coe_J_smul`：coe_J_smul (τ : ℍ) : (↑(J • τ) : Complex) = -
conj ↑τ
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_pos`：ofComplex_apply_of_im_pos {z :
 Complex} (hz : 0 < z.im) : ofComplex z = ⟨z, hz⟩
-/
lemma J_smul (τ : ℍ) : J • τ = ofComplex (-(conj ↑τ)) := by
  ext
  rw [coe_J_smul, ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]

end ofComplex

section IsOpenMap

/-
**UpperHalfPlane.isOpenMap_re** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isOpenMap_re : IsOpenMap re
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Complex.isOpenMap_re`：isOpenMap_re : IsOpenMap re
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
-/
lemma isOpenMap_re : IsOpenMap re :=
  Complex.isOpenMap_re.comp isOpenEmbedding_coe.isOpenMap
/-
**UpperHalfPlane.isOpenMap_im** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isOpenMap_im : IsOpenMap im
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Complex.isOpenMap_im`：isOpenMap_im : IsOpenMap im
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
-/
lemma isOpenMap_im : IsOpenMap im :=
  Complex.isOpenMap_im.comp isOpenEmbedding_coe.isOpenMap
/-
**UpperHalfPlane.isOpenMap_norm** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isOpenMap_norm : IsOpenMap (fun τ : ℍ => ‖(τ : Complex)‖)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map_iff_exists_image`：mem_map_iff_exists_image : t in map m f
 ↔ exists s in f, m '' s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topolo
gy.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 86 条，此处仅展示前 30 条）
-/
lemma isOpenMap_norm : IsOpenMap (fun τ : ℍ ↦ ‖(τ : ℂ)‖) := by
  refine .of_nhds_le fun τ U hU ↦ ?_
  obtain ⟨s, hs, hs'⟩ := Filter.mem_map_iff_exists_image.mp hU
  simp_rw [← isOpenEmbedding_coe.image_mem_nhds, Metric.mem_nhds_iff] at hs ⊢
  obtain ⟨ε, hεpos, hεs⟩ := hs
  refine ⟨ε, hεpos, subset_trans (fun r hr ↦ ?_) hs'⟩
  have hr' : 0 ≤ r := by
    by_contra! hr'
    rw [mem_ball_iff_norm, Real.norm_eq_abs, abs_lt] at hr
    have : ‖(τ : ℂ)‖ < ε := by linarith
    have : 0 ∈ Metric.ball (τ : ℂ) ε := by rwa [mem_ball_iff_norm', sub_zero]
    simpa [UpperHalfPlane.ne_zero] using hεs this
  have : r / ‖(τ : ℂ)‖ * (τ : ℂ) ∈ Metric.ball (τ : ℂ) ε := by
    rwa [mem_ball_iff_norm,
      show r / ‖(τ : ℂ)‖ * (τ : ℂ) - τ = ↑(r / ‖(τ : ℂ)‖ - 1) * (τ : ℂ) by simp; ring,
      norm_mul, norm_real, ← norm_norm (τ : ℂ), ← norm_mul, sub_mul, norm_norm, one_mul,
      div_mul_cancel₀ _ (by simpa using τ.ne_zero), ← mem_ball_iff_norm]
  obtain ⟨ξ, hξs, hξτ⟩ := Set.mem_of_mem_of_subset this hεs
  use ξ, hξs
  simp_rw [hξτ, norm_mul, norm_div, norm_real, norm_norm]
  rw [div_mul_cancel₀ _ (by simpa using τ.ne_zero), Real.norm_of_nonneg hr']

end IsOpenMap

end UpperHalfPlane

