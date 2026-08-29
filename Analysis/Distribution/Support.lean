/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.Distribution

/-! # Support of distributions

We define the support of a distribution, `dsupport u`, as the intersection of all closed sets for
which `u` vanishes on the complement.
For this we also define a predicate `IsVanishingOn` that asserts that a map `f : F → V` vanishes on
`s : Set α` if for all `u : F` with `tsupport u ⊆ s` it follows that `f u = 0`.

These definitions work independently of a specific class of distributions (classical, tempered, or
compactly supported) and all basic properties are proved in an abstract setting using `FunLike`.

## Main definitions
* `IsVanishingOn`: A distribution vanishes on a set if it acts trivially on all test functions
  supported in that subset.
* `dsupport`: The support of a distribution is the intersection of all closed sets for which that
  distribution vanishes on the complement of the set.

## Main statements
* `dsupport_delta`: The support of the delta distribution is a single point. Available for tempered
  and classical distributions.

-/

@[expose] public noncomputable section

variable {ι α β 𝕜 E F F₁ F₂ R V : Type*}

open scoped Topology

namespace Distribution

section IsVanishingOn

variable [FunLike F α β] [TopologicalSpace α] [Zero β]

variable {f g : F -> V} {s s₁ s₂ : Set α}

/-! ### Vanishing of distributions -/

section Zero

variable [Zero V]

/-- A distribution `f` vanishes on a set `s` if it vanishes for all test functions `u` with
`tsupport u ⊆ s`.

To make this definition work for all types of distributions, we define it for any function from
a `FunLike` type to a type with zero. -/
@[fun_prop]
/--
Definition of `IsVanishingOn` / `IsVanishingOn` 的定义

English:
definition IsVanishingOn
  signature: (f : F -> V) (s : Set α)
  body: forall (u : F), tsupport u subseteq s -> f u = 0

@[gcongr]

中文:
定义 IsVanishingOn
  签名: (f : F -> V) (s : Set α)
  定义体: forall (u : F), tsupport u subseteq s -> f u = 0

@[gcongr]

Depends on / 依赖: subseteq, tsupport
-/
def IsVanishingOn (f : F -> V) (s : Set α) : Prop :=
    forall (u : F), tsupport u subseteq s -> f u = 0

@[gcongr]
/--
theorem `IsVanishingOn.mono` / 定理 `IsVanishingOn.mono`

English:
theorem IsVanishingOn.mono
  given: ⦃s₁ s₂
  statement: Set α⦄ (hs : s₂ subseteq s₁) (hf : IsVanishingOn f s₁) :
  proof: (hf · <| ·.trans hs)

中文:
定理 IsVanishingOn.mono
  条件: ⦃s₁ s₂
  结论: Set α⦄ (hs : s₂ subseteq s₁) (hf : IsVanishingOn f s₁) :
  证明: (hf · <| ·.trans hs)
-/
theorem IsVanishingOn.mono ⦃s₁ s₂ : Set α⦄ (hs : s₂ subseteq s₁) (hf : IsVanishingOn f s₁) :
    IsVanishingOn f s₂ :=
  (hf · <| ·.trans hs)

/--
theorem `not_isVanishingOn_mono` / 定理 `not_isVanishingOn_mono`

English:
theorem not_isVanishingOn_mono
  given: ⦃s₁ s₂
  statement: Set α⦄ (hs : s₁ subseteq s₂) (hf : ¬ IsVanishingOn f s₁) :
  proof: (hf <| ·.mono hs)

中文:
定理 not_isVanishingOn_mono
  条件: ⦃s₁ s₂
  结论: Set α⦄ (hs : s₁ subseteq s₂) (hf : ¬ IsVanishingOn f s₁) :
  证明: (hf <| ·.mono hs)
-/
theorem not_isVanishingOn_mono ⦃s₁ s₂ : Set α⦄ (hs : s₁ subseteq s₂) (hf : ¬ IsVanishingOn f s₁) :
    ¬ IsVanishingOn f s₂ :=
  (hf <| ·.mono hs)

/--
theorem `not_isVanishingOn_iff` / 定理 `not_isVanishingOn_iff`

English:
theorem not_isVanishingOn_iff
  proof: by
  simp [IsVanishingOn]

中文:
定理 not_isVanishingOn_iff
  证明: by
  simp [IsVanishingOn]

Depends on / 依赖: IsVanishingOn
-/
theorem not_isVanishingOn_iff :
    ¬ IsVanishingOn f s ↔ exists u : F, tsupport u subseteq s ∧ f u != 0 := by
  simp [IsVanishingOn]

end Zero

end IsVanishingOn

section dsupport

/-! ### Support -/

section Zero

variable [FunLike F α β] [TopologicalSpace α] [Zero β] [Zero V]

variable {f g : F -> V} {s s₁ s₂ : Set α}

/--
Definition of `dsupport` / `dsupport` 的定义

English:
definition dsupport
  signature: (f : F -> V)
  body: ⋂₀ { s | IsVanishingOn f sᶜ ∧ IsClosed s}

中文:
定义 dsupport
  签名: (f : F -> V)
  定义体: ⋂₀ { s | IsVanishingOn f sᶜ ∧ IsClosed s}

Depends on / 依赖: IsClosed, IsVanishingOn
-/
def dsupport (f : F -> V) : Set α := ⋂₀ { s | IsVanishingOn f sᶜ ∧ IsClosed s}

/--
theorem `mem_dsupport_iff` / 定理 `mem_dsupport_iff`

English:
theorem mem_dsupport_iff
  given: (x : α)
  proof: by
  simp [dsupport]

中文:
定理 mem_dsupport_iff
  条件: (x : α)
  证明: by
  simp [dsupport]

Depends on / 依赖: dsupport
-/
theorem mem_dsupport_iff (x : α) :
    x in dsupport f ↔ forall (s : Set α), IsVanishingOn f sᶜ -> IsClosed s -> x in s := by
  simp [dsupport]

/--
theorem `dsupport_compl_eq` / 定理 `dsupport_compl_eq`

English:
theorem dsupport_compl_eq
  statement: (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a }
  proof: by
  simp [dsupport, Set.compl_sInter, Set.compl_image_ofPred]

@[simp high]

中文:
定理 dsupport_compl_eq
  结论: (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a }
  证明: by
  simp [dsupport, Set.compl_sInter, Set.compl_image_ofPred]

@[simp high]

Depends on / 依赖: Set.compl_image_ofPred, Set.compl_sInter, compl_image_ofPred, compl_sInter, dsupport
-/
theorem dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a } := by
  simp [dsupport, Set.compl_sInter, Set.compl_image_ofPred]

@[simp high]
/--
theorem `notMem_dsupport_iff` / 定理 `notMem_dsupport_iff`

English:
theorem notMem_dsupport_iff
  given: (x : α)
  proof: by
  simp [← Set.mem_compl_iff, dsupport_compl_eq, Set.mem_sUnion, and_assoc]

中文:
定理 notMem_dsupport_iff
  条件: (x : α)
  证明: by
  simp [← Set.mem_compl_iff, dsupport_compl_eq, Set.mem_sUnion, and_assoc]

Depends on / 依赖: Set.mem_compl_iff, Set.mem_sUnion, and_assoc, dsupport_compl_eq, mem_compl_iff, mem_sUnion
-/
theorem notMem_dsupport_iff (x : α) :
    x ∉ (dsupport f) ↔ exists (s : Set α), IsVanishingOn f s ∧ IsOpen s ∧ x in s := by
  simp [← Set.mem_compl_iff, dsupport_compl_eq, Set.mem_sUnion, and_assoc]

/--
theorem `mem_dsupport_iff_not_isVanishingOn` / 定理 `mem_dsupport_iff_not_isVanishingOn`

English:
theorem mem_dsupport_iff_not_isVanishingOn
  given: (x : α)
  proof: by
  grind only [notMem_dsupport_iff]

中文:
定理 mem_dsupport_iff_not_isVanishingOn
  条件: (x : α)
  证明: by
  grind only [notMem_dsupport_iff]

Depends on / 依赖: notMem_dsupport_iff
-/
theorem mem_dsupport_iff_not_isVanishingOn (x : α) :
    x in dsupport f ↔ forall s, x in s -> IsOpen s -> ¬ IsVanishingOn f s := by
  grind only [notMem_dsupport_iff]

/--
theorem `mem_dsupport_iff_forall_exists_ne` / 定理 `mem_dsupport_iff_forall_exists_ne`

English:
theorem mem_dsupport_iff_forall_exists_ne
  given: (x : α)
  proof: by
  simp_rw [mem_dsupport_iff_not_isVanishingOn, not_isVanishingOn_iff]

中文:
定理 mem_dsupport_iff_forall_exists_ne
  条件: (x : α)
  证明: by
  simp_rw [mem_dsupport_iff_not_isVanishingOn, not_isVanishingOn_iff]

Depends on / 依赖: mem_dsupport_iff_not_isVanishingOn, not_isVanishingOn_iff, simp_rw
-/
theorem mem_dsupport_iff_forall_exists_ne (x : α) :
    x in dsupport f ↔ forall s, x in s -> IsOpen s -> exists u : F, tsupport u subseteq s ∧ f u != 0 := by
  simp_rw [mem_dsupport_iff_not_isVanishingOn, not_isVanishingOn_iff]

/--
theorem `mem_dsupport_iff_frequently` / 定理 `mem_dsupport_iff_frequently`

English:
theorem mem_dsupport_iff_frequently
  given: {x : α}
  proof: by
  rw [nhds_basis_opens x |>.frequently_smallSets not_isVanishingOn_mono]
  simpa using mem_dsupport_iff_not_isVanishingOn x

中文:
定理 mem_dsupport_iff_frequently
  条件: {x : α}
  证明: by
  rw [nhds_basis_opens x |>.frequently_smallSets not_isVanishingOn_mono]
  simpa using mem_dsupport_iff_not_isVanishingOn x

Depends on / 依赖: frequently_smallSets, mem_dsupport_iff_not_isVanishingOn, nhds_basis_opens, not_isVanishingOn_mono
-/
theorem mem_dsupport_iff_frequently {x : α} :
    x in dsupport f ↔ existsᶠ u in (𝓝 x).smallSets, ¬ IsVanishingOn f u := by
  rw [nhds_basis_opens x |>.frequently_smallSets not_isVanishingOn_mono]
  simpa using mem_dsupport_iff_not_isVanishingOn x

/--
theorem `_root_.Filter.HasBasis.mem_dsupport` / 定理 `_root_.Filter.HasBasis.mem_dsupport`

English:
theorem _root_.Filter.HasBasis.mem_dsupport
  statement: {ι : Sort*} {p : ι -> Prop}
  proof: by
  rw [mem_dsupport_iff_frequently]
  exact hl.frequently_smallSets not_isVanishingOn_mono

中文:
定理 _root_.Filter.HasBasis.mem_dsupport
  结论: {ι : Sort*} {p : ι -> 命题}
  证明: by
  rw [mem_dsupport_iff_frequently]
  exact hl.frequently_smallSets not_isVanishingOn_mono

Depends on / 依赖: frequently_smallSets, hl.frequently_smallSets, mem_dsupport_iff_frequently, not_isVanishingOn_mono
-/
theorem _root_.Filter.HasBasis.mem_dsupport {ι : Sort*} {p : ι -> Prop}
    {s : ι -> Set α} {x : α} (hl : (𝓝 x).HasBasis p s) :
    x in dsupport f ↔ forall (i : ι), p i -> ¬ IsVanishingOn f (s i) := by
  rw [mem_dsupport_iff_frequently]
  exact hl.frequently_smallSets not_isVanishingOn_mono

/--
theorem `notMem_dsupport_iff_eventually` / 定理 `notMem_dsupport_iff_eventually`

English:
theorem notMem_dsupport_iff_eventually
  given: {x : α}
  proof: by
  simp [mem_dsupport_iff_frequently]

中文:
定理 notMem_dsupport_iff_eventually
  条件: {x : α}
  证明: by
  simp [mem_dsupport_iff_frequently]

Depends on / 依赖: mem_dsupport_iff_frequently
-/
theorem notMem_dsupport_iff_eventually {x : α} :
    x ∉ dsupport f ↔ forallᶠ u in (𝓝 x).smallSets, IsVanishingOn f u := by
  simp [mem_dsupport_iff_frequently]

/--
theorem `_root_.Filter.HasBasis.notMem_dsupport` / 定理 `_root_.Filter.HasBasis.notMem_dsupport`

English:
theorem _root_.Filter.HasBasis.notMem_dsupport
  statement: {ι : Sort*} {p : ι -> Prop}
  proof: by
  simp [hl.mem_dsupport]

@[gcongr only]

中文:
定理 _root_.Filter.HasBasis.notMem_dsupport
  结论: {ι : Sort*} {p : ι -> 命题}
  证明: by
  simp [hl.mem_dsupport]

@[gcongr only]

Depends on / 依赖: hl.mem_dsupport, mem_dsupport
-/
theorem _root_.Filter.HasBasis.notMem_dsupport {ι : Sort*} {p : ι -> Prop}
    {s : ι -> Set α} {x : α} (hl : (𝓝 x).HasBasis p s) :
    x ∉ dsupport f ↔ exists i, p i ∧ IsVanishingOn f (s i) := by
  simp [hl.mem_dsupport]

@[gcongr only]
/--
theorem `dsupport_subset_dsupport` / 定理 `dsupport_subset_dsupport`

English:
theorem dsupport_subset_dsupport
  proof: Set.sInter_mono fun s ⟨g_van, s_cl⟩ => ⟨h sᶜ s_cl.isOpen_compl g_van, s_cl⟩

@[grind .]

中文:
定理 dsupport_subset_dsupport
  证明: Set.sInter_mono fun s ⟨g_van, s_cl⟩ => ⟨h sᶜ s_cl.isOpen_compl g_van, s_cl⟩

@[grind .]

Depends on / 依赖: Set.sInter_mono, g_van, isOpen_compl, sInter_mono, s_cl, s_cl.isOpen_compl
-/
theorem dsupport_subset_dsupport
    (h : forall (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s) :
    dsupport f subseteq dsupport g :=
  Set.sInter_mono fun s ⟨g_van, s_cl⟩ => ⟨h sᶜ s_cl.isOpen_compl g_van, s_cl⟩

@[grind .]
/--
theorem `isClosed_dsupport` / 定理 `isClosed_dsupport`

English:
theorem isClosed_dsupport
  statement: IsClosed (dsupport f)
  proof: by
  grind [dsupport, isClosed_sInter]

中文:
定理 isClosed_dsupport
  结论: IsClosed (dsupport f)
  证明: by
  grind [dsupport, isClosed_sInter]

Depends on / 依赖: dsupport, isClosed_sInter
-/
theorem isClosed_dsupport : IsClosed (dsupport f) := by
  grind [dsupport, isClosed_sInter]

/--
theorem `IsVanishingOn.disjoint_dsupport` / 定理 `IsVanishingOn.disjoint_dsupport`

English:
theorem IsVanishingOn.disjoint_dsupport
  given: (h : IsVanishingOn f s) (s_open : IsOpen s)
  proof: by
  rw [← Set.subset_compl_iff_disjoint_right]; rw [dsupport_compl_eq]
  exact Set.subset_sUnion_of_mem ⟨h, s_open⟩

中文:
定理 IsVanishingOn.disjoint_dsupport
  条件: (h : IsVanishingOn f s) (s_open : IsOpen s)
  证明: by
  rw [← Set.subset_compl_iff_disjoint_right]; rw [dsupport_compl_eq]
  exact Set.subset_sUnion_of_mem ⟨h, s_open⟩

Depends on / 依赖: Set.subset_compl_iff_disjoint_right, Set.subset_sUnion_of_mem, dsupport_compl_eq, s_open, subset_compl_iff_disjoint_right, subset_sUnion_of_mem
-/
theorem IsVanishingOn.disjoint_dsupport (h : IsVanishingOn f s) (s_open : IsOpen s) :
    Disjoint s (dsupport f) := by
  rw [← Set.subset_compl_iff_disjoint_right]; rw [dsupport_compl_eq]
  exact Set.subset_sUnion_of_mem ⟨h, s_open⟩

end Zero

end dsupport

section normed

variable [FunLike F α β] [PseudoMetricSpace α] [Zero β] [Zero V]

variable {f : F -> V}

/--
theorem `compl_dsupport_eq_sUnion_isBounded` / 定理 `compl_dsupport_eq_sUnion_isBounded`

English:
theorem compl_dsupport_eq_sUnion_isBounded
  proof: by
  ext x
  grind [(Metric.hasBasis_nhds_isOpen_isBounded x).notMem_dsupport]

中文:
定理 compl_dsupport_eq_sUnion_isBounded
  证明: by
  ext x
  grind [(Metric.hasBasis_nhds_isOpen_isBounded x).notMem_dsupport]

Depends on / 依赖: Metric, Metric.hasBasis_nhds_isOpen_isBounded, hasBasis_nhds_isOpen_isBounded, notMem_dsupport
-/
theorem compl_dsupport_eq_sUnion_isBounded :
    (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a ∧ Bornology.IsBounded a } := by
  ext x
  grind [(Metric.hasBasis_nhds_isOpen_isBounded x).notMem_dsupport]

end normed

/-! ## Tempered distributions -/

open SchwartzMap Distribution TemperedDistribution

namespace TemperedDistribution

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Complex F]

variable {f : 𝓢'(E, F)} {s : Set E}

namespace IsVanishingOn

open scoped Topology

@[fun_prop]
/--
theorem `smulLeftCLM` / 定理 `smulLeftCLM`

English:
theorem smulLeftCLM
  given: (hf : IsVanishingOn f s) {g : E -> Complex} (hg : g.HasTemperateGrowth)
  proof: by
  intro u hu
  apply hf ((SchwartzMap.smulLeftCLM Complex g) u)
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_right g u).trans hu

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.IsVanishingOn.smulLeftCLM :=
  Distribution.TemperedDistribution.IsVanishingOn

中文:
定理 smulLeftCLM
  条件: (hf : IsVanishingOn f s) {g : E -> Complex} (hg : g.HasTemperateGrowth)
  证明: by
  intro u hu
  apply hf ((SchwartzMap.smulLeftCLM Complex g) u)
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_right g u).trans hu

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.IsVanishingOn.smulLeftCLM :=
  Distribution.TemperedDistribution.IsVanishingOn

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM, SchwartzMap.smulLeftCLM_apply, smulLeftCLM, smulLeftCLM_apply, tsupport_smul_subset_right
-/
theorem smulLeftCLM (hf : IsVanishingOn f s) {g : E -> Complex} (hg : g.HasTemperateGrowth) :
    IsVanishingOn (smulLeftCLM F g f) s := by
  intro u hu
  apply hf ((SchwartzMap.smulLeftCLM Complex g) u)
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_right g u).trans hu

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.IsVanishingOn.smulLeftCLM :=
  Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM

open LineDeriv

@[fun_prop]
/--
theorem `lineDerivOp` / 定理 `lineDerivOp`

English:
theorem lineDerivOp
  given: (hf : IsVanishingOn f s) (m : E)
  proof: by
  intro u hu
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
exact hf (∂_{m} u) (tsupport_fderiv_apply_subset Real m).trans hu

@[fun_prop]

中文:
定理 lineDerivOp
  条件: (hf : IsVanishingOn f s) (m : E)
  证明: by
  intro u hu
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
exact hf (∂_{m} u) (tsupport_fderiv_apply_subset Real m).trans hu

@[fun_prop]

Depends on / 依赖: TemperedDistribution, TemperedDistribution.lineDerivOp_apply_apply, lineDerivOp_apply_apply, map_neg, neg_eq_zero, tsupport_fderiv_apply_subset
-/
theorem lineDerivOp (hf : IsVanishingOn f s) (m : E) :
    IsVanishingOn (∂_{m} f : 𝓢'(E, F)) s := by
  intro u hu
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
exact hf (∂_{m} u) (tsupport_fderiv_apply_subset Real m).trans hu

@[fun_prop]
/--
theorem `iteratedLineDerivOp` / 定理 `iteratedLineDerivOp`

English:
theorem iteratedLineDerivOp
  given: {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E)
  proof: by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]

中文:
定理 iteratedLineDerivOp
  条件: {n : 自然数} (hf : IsVanishingOn f s) (m : Fin n -> E)
  证明: by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]

Depends on / 依赖: Fin.tail, lineDerivOp
-/
theorem iteratedLineDerivOp {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E) :
    IsVanishingOn (∂^{m} f : 𝓢'(E, F)) s := by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]
/--
theorem `_root_.TemperedDistribution.isVanishingOn_delta` / 定理 `_root_.TemperedDistribution.isVanishingOn_delta`

English:
theorem _root_.TemperedDistribution.isVanishingOn_delta
  given: (x : E)
  proof: by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

中文:
定理 _root_.TemperedDistribution.isVanishingOn_delta
  条件: (x : E)
  证明: by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

Depends on / 依赖: Set.subset_compl_singleton_iff, image_eq_zero_of_notMem_tsupport, subset_compl_singleton_iff
-/
theorem _root_.TemperedDistribution.isVanishingOn_delta (x : E) :
    IsVanishingOn (TemperedDistribution.delta x) {x}ᶜ := by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

end IsVanishingOn

section Support

/--
theorem `dsupport_smulLeftCLM_subset` / 定理 `dsupport_smulLeftCLM_subset`

English:
theorem dsupport_smulLeftCLM_subset
  given: {g : E -> Complex} (hg : g.HasTemperateGrowth)
  proof: by
  gcongr; fun_prop

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.dsupport_smulLeftCLM_subset :=
  Distribution.TemperedDistribution.dsupport_smulLeftCLM_subset

中文:
定理 dsupport_smulLeftCLM_subset
  条件: {g : E -> Complex} (hg : g.HasTemperateGrowth)
  证明: by
  gcongr; fun_prop

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.dsupport_smulLeftCLM_subset :=
  Distribution.TemperedDistribution.dsupport_smulLeftCLM_subset

Depends on / 依赖: fun_prop
-/
theorem dsupport_smulLeftCLM_subset {g : E -> Complex} (hg : g.HasTemperateGrowth) :
    dsupport (smulLeftCLM F g f) subseteq dsupport f := by
  gcongr; fun_prop

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.dsupport_smulLeftCLM_subset :=
  Distribution.TemperedDistribution.dsupport_smulLeftCLM_subset

open LineDeriv

/--
theorem `dsupport_lineDerivOp_subset` / 定理 `dsupport_lineDerivOp_subset`

English:
theorem dsupport_lineDerivOp_subset
  given: (m : E)
  statement: dsupport (∂_{m} f : 𝓢'(E, F)) subseteq dsupport f
  proof: by
  gcongr; fun_prop

中文:
定理 dsupport_lineDerivOp_subset
  条件: (m : E)
  结论: dsupport (∂_{m} f : 𝓢'(E, F)) subseteq dsupport f
  证明: by
  gcongr; fun_prop

Depends on / 依赖: fun_prop
-/
theorem dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓢'(E, F)) subseteq dsupport f := by
  gcongr; fun_prop

/--
theorem `dsupport_iteratedLineDerivOp_subset` / 定理 `dsupport_iteratedLineDerivOp_subset`

English:
theorem dsupport_iteratedLineDerivOp_subset
  given: {n : Nat} (m : Fin n -> E)
  proof: by
  gcongr; fun_prop

中文:
定理 dsupport_iteratedLineDerivOp_subset
  条件: {n : 自然数} (m : Fin n -> E)
  证明: by
  gcongr; fun_prop

Depends on / 依赖: fun_prop
-/
theorem dsupport_iteratedLineDerivOp_subset {n : Nat} (m : Fin n -> E) :
    dsupport (∂^{m} f : 𝓢'(E, F)) subseteq dsupport f := by
  gcongr; fun_prop

/--
theorem `dsupport_delta` / 定理 `dsupport_delta`

English:
theorem dsupport_delta
  given: [FiniteDimensional Real E] (x : E)
  proof: by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hx hs
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((IsOpen.mem_n

中文:
定理 dsupport_delta
  条件: [FiniteDimensional 实数 E] (x : E)
  证明: by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hx hs
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((IsOpen.mem_n

Depends on / 依赖: Complex.ofRe, Complex.ofRealCLM, HasCompactSupport, IsOpen, IsOpen.mem_nhds_iff, T1Space, T1Space.t1, comp_left, exists_contDiff_tsupport_subset, isVanishingOn_delta, mem_dsupport_iff, mem_dsupport_iff_forall_exists_ne, mem_nhds_iff, ofRealCLM, subset_antisymm, subseteq, toSchwartzMap, tsupport, tsupport_comp_subset
-/
theorem dsupport_delta [FiniteDimensional Real E] (x : E) :
    dsupport (TemperedDistribution.delta x) = {x} := by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hx hs
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((IsOpen.mem_nhds_iff hs).mpr hx)
  have h₁' : tsupport (Complex.ofRealCLM ∘ u) subseteq s := (tsupport_comp_subset rfl _).trans h₁
  have h₂' : HasCompactSupport (Complex.ofRealCLM ∘ u) := h₂.comp_left rfl
  use h₂'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp h₃)
  exact ⟨h₁', by simp [h₄]⟩

end Support

end TemperedDistribution

/-! ## Classical distributions -/

open TopologicalSpace Distributions

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module Real F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul Real F]
  {n : Nat∞}

variable {f : 𝓓'(Ω, F)} {s : Set E}

namespace IsVanishingOn

open scoped Topology

open LineDeriv

@[fun_prop]
/--
theorem `lineDerivOp` / 定理 `lineDerivOp`

English:
theorem lineDerivOp
  given: (hf : IsVanishingOn f s) (m : E)
  proof: by
  intro u hu
  simp only [Distribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
exact hf (∂_{m} u) (tsupport_fderiv_apply_subset Real m).trans hu

@[fun_prop]

中文:
定理 lineDerivOp
  条件: (hf : IsVanishingOn f s) (m : E)
  证明: by
  intro u hu
  simp only [Distribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
exact hf (∂_{m} u) (tsupport_fderiv_apply_subset Real m).trans hu

@[fun_prop]

Depends on / 依赖: Distribution, Distribution.lineDerivOp_apply_apply, lineDerivOp_apply_apply, map_neg, neg_eq_zero, tsupport_fderiv_apply_subset
-/
theorem lineDerivOp (hf : IsVanishingOn f s) (m : E) :
    IsVanishingOn (∂_{m} f : 𝓓'(Ω, F)) s := by
  intro u hu
  simp only [Distribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
exact hf (∂_{m} u) (tsupport_fderiv_apply_subset Real m).trans hu

@[fun_prop]
/--
theorem `iteratedLineDerivOp` / 定理 `iteratedLineDerivOp`

English:
theorem iteratedLineDerivOp
  given: {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E)
  proof: by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]

中文:
定理 iteratedLineDerivOp
  条件: {n : 自然数} (hf : IsVanishingOn f s) (m : Fin n -> E)
  证明: by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]

Depends on / 依赖: Fin.tail, lineDerivOp
-/
theorem iteratedLineDerivOp {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E) :
    IsVanishingOn (∂^{m} f : 𝓓'(Ω, F)) s := by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]
/--
theorem `_root_.Distribution.isVanishingOn_delta` / 定理 `_root_.Distribution.isVanishingOn_delta`

English:
theorem _root_.Distribution.isVanishingOn_delta
  given: (x : E)
  proof: by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

中文:
定理 _root_.Distribution.isVanishingOn_delta
  条件: (x : E)
  证明: by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

Depends on / 依赖: Set.subset_compl_singleton_iff, image_eq_zero_of_notMem_tsupport, subset_compl_singleton_iff
-/
theorem _root_.Distribution.isVanishingOn_delta (x : E) :
    IsVanishingOn (Distribution.delta x : 𝓓'^{n}(Ω, Real)) {x}ᶜ := by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

end IsVanishingOn

section Support

open LineDeriv

/--
theorem `dsupport_lineDerivOp_subset` / 定理 `dsupport_lineDerivOp_subset`

English:
theorem dsupport_lineDerivOp_subset
  given: (m : E)
  statement: dsupport (∂_{m} f : 𝓓'(Ω, F)) subseteq dsupport f
  proof: by
  gcongr; fun_prop

中文:
定理 dsupport_lineDerivOp_subset
  条件: (m : E)
  结论: dsupport (∂_{m} f : 𝓓'(Ω, F)) subseteq dsupport f
  证明: by
  gcongr; fun_prop

Depends on / 依赖: fun_prop
-/
theorem dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓓'(Ω, F)) subseteq dsupport f := by
  gcongr; fun_prop

/--
theorem `dsupport_iteratedLineDerivOp_subset` / 定理 `dsupport_iteratedLineDerivOp_subset`

English:
theorem dsupport_iteratedLineDerivOp_subset
  given: {n : Nat} (m : Fin n -> E)
  proof: by
  gcongr; fun_prop

中文:
定理 dsupport_iteratedLineDerivOp_subset
  条件: {n : 自然数} (m : Fin n -> E)
  证明: by
  gcongr; fun_prop

Depends on / 依赖: fun_prop
-/
theorem dsupport_iteratedLineDerivOp_subset {n : Nat} (m : Fin n -> E) :
    dsupport (∂^{m} f : 𝓓'(Ω, F)) subseteq dsupport f := by
  gcongr; fun_prop

/--
theorem `dsupport_delta` / 定理 `dsupport_delta`

English:
theorem dsupport_delta
  given: [FiniteDimensional Real E] (x : E) (hx : x in Ω)
  proof: by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hxs hs
  set t := s inter Ω
  have ht : IsOpen t := hs.inter Ω.isOpen
  have htx : x in t := Set.mem

中文:
定理 dsupport_delta
  条件: [FiniteDimensional 实数 E] (x : E) (hx : x in Ω)
  证明: by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hxs hs
  set t := s inter Ω
  have ht : IsOpen t := hs.inter Ω.isOpen
  have htx : x in t := Set.mem

Depends on / 依赖: IsOpen, IsOpen.mem_nhds_iff, Set.mem_inter, T1Space, T1Space.t1, exists_contDiff_tsupport_subset, hs.inter, isOpen, isVanishingOn_delta, mem_dsupport_iff, mem_dsupport_iff_forall_exists_ne, mem_inter, mem_nhds_iff, subset_antisymm
-/
theorem dsupport_delta [FiniteDimensional Real E] (x : E) (hx : x in Ω) :
    dsupport (Distribution.delta x : 𝓓'^{n}(Ω, Real)) = {x} := by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hxs hs
  set t := s inter Ω
  have ht : IsOpen t := hs.inter Ω.isOpen
  have htx : x in t := Set.mem_inter hxs hx
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := n) ((IsOpen.mem_nhds_iff ht).mpr htx)
  exact ⟨⟨u, h₃, h₂, by aesop⟩, ⟨by aesop, by simp [h₄]⟩⟩

end Support

end Distribution
