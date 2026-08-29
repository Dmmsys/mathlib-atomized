/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace

/-!
# Ideals of continuous functions

For a topological semiring `R` and a topological space `X` there is a Galois connection between
`Ideal C(X, R)` and `Set X` given by sending each `I : Ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : Set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `ContinuousMap.setOfIdeal` and
`ContinuousMap.idealOfSet`. As long as `R` is Hausdorff, `ContinuousMap.setOfIdeal I` is open,
and if, in addition, `X` is locally compact, then `ContinuousMap.setOfIdeal s` is closed.

When `R = 𝕜` with `RCLike 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, 𝕜)`. Because we do not have a bundled type of closed ideals,
we simply register this as a Galois insertion between `Ideal C(X, 𝕜)` and `opens X`, which is
`ContinuousMap.idealOpensGI`. Consequently, the maximal ideals of `C(X, 𝕜)` are precisely those
ideals corresponding to (complements of) singletons in `X`.

In addition, when `X` is locally compact and `𝕜` is a nontrivial topological integral domain, then
there is a natural continuous map from `X` to `WeakDual.characterSpace 𝕜 C(X, 𝕜)` given by point
evaluation, which is herein called `WeakDual.CharacterSpace.continuousMapEval`. Again, when `X` is
compact Hausdorff and `RCLike 𝕜`, more can be obtained. In particular, in that context this map is
bijective, and since the domain is compact and the codomain is Hausdorff, it is a homeomorphism,
herein called `WeakDual.CharacterSpace.homeoEval`.

## Main definitions

* `ContinuousMap.idealOfSet`: ideal of functions which vanish on the complement of a set.
* `ContinuousMap.setOfIdeal`: complement of the set on which all functions in the ideal vanish.
* `ContinuousMap.opensOfIdeal`: `ContinuousMap.setOfIdeal` as a term of `opens X`.
* `ContinuousMap.idealOpensGI`: The Galois insertion `ContinuousMap.opensOfIdeal` and
  `fun s ↦ ContinuousMap.idealOfSet ↑s`.
* `WeakDual.CharacterSpace.continuousMapEval`: the natural continuous map from a locally compact
  topological space `X` to the `WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point
  evaluation at `x`, with modest hypothesis on `𝕜`.
* `WeakDual.CharacterSpace.homeoEval`: this is `WeakDual.CharacterSpace.continuousMapEval`
  upgraded to a homeomorphism when `X` is compact Hausdorff and `RCLike 𝕜`.

## Main statements

* `ContinuousMap.idealOfSet_ofIdeal_eq_closure`: when `X` is compact Hausdorff and
  `RCLike 𝕜`, `idealOfSet 𝕜 (setOfIdeal I) = I.closure` for any ideal `I : Ideal C(X, 𝕜)`.
* `ContinuousMap.setOfIdeal_ofSet_eq_interior`: when `X` is compact Hausdorff and `RCLike 𝕜`,
  `setOfIdeal (idealOfSet 𝕜 s) = interior s` for any `s : Set X`.
* `ContinuousMap.ideal_isMaximal_iff`: when `X` is compact Hausdorff and `RCLike 𝕜`, a closed
  ideal of `C(X, 𝕜)` is maximal if and only if it is `idealOfSet 𝕜 {x}ᶜ` for some `x : X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`ContinuousMap.idealOpensGI`.

## Tags

ideal, continuous function, compact, Hausdorff
-/

@[expose] public section


open scoped NNReal

namespace ContinuousMap

open TopologicalSpace

section IsTopologicalRing

variable {X R : Type*} [TopologicalSpace X] [Semiring R]
variable [TopologicalSpace R] [IsTopologicalSemiring R]
variable (R)

/--
Definition of `idealOfSet` / `idealOfSet` 的定义

English:
definition idealOfSet
  signature: (s : Set X)
  body: {f : C(X, R) | forall x in sᶜ, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf x hx := mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)

中文:
定义 idealOfSet
  签名: (s : 集合 X)
  定义体: {f : C(X, R) | forall x in sᶜ, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf x hx := mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)
-/
def idealOfSet (s : Set X) : Ideal C(X, R) where
  carrier := {f : C(X, R) | forall x in sᶜ, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf x hx := mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)

/--
theorem `idealOfSet_closed` / 定理 `idealOfSet_closed`

English:
theorem idealOfSet_closed
  given: [T2Space R] (s : Set X)
  proof: by
  simp only [idealOfSet, Submodule.coe_set_mk, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

中文:
定理 idealOfSet_closed
  条件: [T2空间 R] (s : 集合 X)
  证明: by
  simp only [idealOfSet, Submodule.coe_set_mk, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

Depends on / 依赖: Set.ofPred_forall, Submodule, Submodule.coe_set_mk, coe_set_mk, continuous_const, continuous_eval_const, idealOfSet, isClosed_eq, isClosed_iInter, ofPred_forall
-/
theorem idealOfSet_closed [T2Space R] (s : Set X) :
    IsClosed (idealOfSet R s : Set C(X, R)) := by
  simp only [idealOfSet, Submodule.coe_set_mk, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

variable {R}

/--
theorem `mem_idealOfSet` / 定理 `mem_idealOfSet`

English:
theorem mem_idealOfSet
  given: {s : Set X} {f : C(X, R)}
  proof: by
  convert! Iff.rfl

中文:
定理 mem_idealOfSet
  条件: {s : 集合 X} {f : C(X, R)}
  证明: by
  convert! Iff.rfl

Depends on / 依赖: Iff.rfl, convert
-/
theorem mem_idealOfSet {s : Set X} {f : C(X, R)} :
    f in idealOfSet R s ↔ forall ⦃x : X⦄, x in sᶜ -> f x = 0 := by
  convert! Iff.rfl

/--
theorem `notMem_idealOfSet` / 定理 `notMem_idealOfSet`

English:
theorem notMem_idealOfSet
  given: {s : Set X} {f : C(X, R)}
  statement: f ∉ idealOfSet R s ↔ exists x in sᶜ, f x != 0
  proof: by
  simp_rw [mem_idealOfSet]; push Not; rfl

中文:
定理 notMem_idealOfSet
  条件: {s : 集合 X} {f : C(X, R)}
  结论: f ∉ idealOfSet R s ↔ 存在 x in sᶜ, f x != 0
  证明: by
  simp_rw [mem_idealOfSet]; push Not; rfl

Depends on / 依赖: mem_idealOfSet, simp_rw
-/
theorem notMem_idealOfSet {s : Set X} {f : C(X, R)} : f ∉ idealOfSet R s ↔ exists x in sᶜ, f x != 0 := by
  simp_rw [mem_idealOfSet]; push Not; rfl

/--
Definition of `setOfIdeal` / `setOfIdeal` 的定义

English:
definition setOfIdeal
  signature: (I : Ideal C(X, R))
  body: {x : X | forall f in I, (f : C(X, R)) x = 0}ᶜ

中文:
定义 setOfIdeal
  签名: (I : 理想 C(X, R))
  定义体: {x : X | forall f in I, (f : C(X, R)) x = 0}ᶜ
-/
def setOfIdeal (I : Ideal C(X, R)) : Set X :=
  {x : X | forall f in I, (f : C(X, R)) x = 0}ᶜ

/--
theorem `notMem_setOfIdeal` / 定理 `notMem_setOfIdeal`

English:
theorem notMem_setOfIdeal
  given: {I : Ideal C(X, R)} {x : X}
  proof: by
  rw [← Set.mem_compl_iff]; rw [setOfIdeal]; rw [compl_compl]; rw [Set.mem_ofPred]

中文:
定理 notMem_setOfIdeal
  条件: {I : 理想 C(X, R)} {x : X}
  证明: by
  rw [← Set.mem_compl_iff]; rw [setOfIdeal]; rw [compl_compl]; rw [Set.mem_ofPred]

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred, compl_compl, mem_compl_iff, mem_ofPred, setOfIdeal
-/
theorem notMem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∉ setOfIdeal I ↔ forall ⦃f : C(X, R)⦄, f in I -> f x = 0 := by
  rw [← Set.mem_compl_iff]; rw [setOfIdeal]; rw [compl_compl]; rw [Set.mem_ofPred]

/--
theorem `mem_setOfIdeal` / 定理 `mem_setOfIdeal`

English:
theorem mem_setOfIdeal
  given: {I : Ideal C(X, R)} {x : X}
  proof: by
  simp_rw [setOfIdeal, Set.mem_compl_iff, Set.mem_ofPred]; push Not; rfl

中文:
定理 mem_setOfIdeal
  条件: {I : 理想 C(X, R)} {x : X}
  证明: by
  simp_rw [setOfIdeal, Set.mem_compl_iff, Set.mem_ofPred]; push Not; rfl

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred, mem_compl_iff, mem_ofPred, setOfIdeal, simp_rw
-/
theorem mem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x in setOfIdeal I ↔ exists f in I, (f : C(X, R)) x != 0 := by
  simp_rw [setOfIdeal, Set.mem_compl_iff, Set.mem_ofPred]; push Not; rfl

/--
theorem `setOfIdeal_open` / 定理 `setOfIdeal_open`

English:
theorem setOfIdeal_open
  given: [T2Space R] (I : Ideal C(X, R))
  statement: IsOpen (setOfIdeal I)
  proof: by
  simp only [setOfIdeal, Set.ofPred_forall, isOpen_compl_iff]
  exact
    isClosed_iInter fun f =>
      isClosed_iInter fun _ => isClosed_eq (map_continuous f) continuous_const

中文:
定理 setOfIdeal_open
  条件: [T2空间 R] (I : 理想 C(X, R))
  结论: 是开集 (setOfIdeal I)
  证明: by
  simp only [setOfIdeal, Set.ofPred_forall, isOpen_compl_iff]
  exact
    isClosed_iInter fun f =>
      isClosed_iInter fun _ => isClosed_eq (map_continuous f) continuous_const

Depends on / 依赖: Set.ofPred_forall, continuous_const, isClosed_eq, isClosed_iInter, isOpen_compl_iff, map_continuous, ofPred_forall, setOfIdeal
-/
theorem setOfIdeal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (setOfIdeal I) := by
  simp only [setOfIdeal, Set.ofPred_forall, isOpen_compl_iff]
  exact
    isClosed_iInter fun f =>
      isClosed_iInter fun _ => isClosed_eq (map_continuous f) continuous_const

/-- The open set `ContinuousMap.setOfIdeal I` realized as a term of `opens X`. -/
@[simps]
/--
Definition of `opensOfIdeal` / `opensOfIdeal` 的定义

English:
definition opensOfIdeal
  signature: [T2Space R] (I : Ideal C(X, R))
  body: ⟨setOfIdeal I, setOfIdeal_open I⟩

@[simp]

中文:
定义 opensOfIdeal
  签名: [T2空间 R] (I : 理想 C(X, R))
  定义体: ⟨setOfIdeal I, setOfIdeal_open I⟩

@[simp]

Depends on / 依赖: setOfIdeal, setOfIdeal_open
-/
def opensOfIdeal [T2Space R] (I : Ideal C(X, R)) : Opens X :=
  ⟨setOfIdeal I, setOfIdeal_open I⟩

@[simp]
/--
theorem `setOfTop_eq_univ` / 定理 `setOfTop_eq_univ`

English:
theorem setOfTop_eq_univ
  given: [Nontrivial R]
  statement: setOfIdeal (⊤ : Ideal C(X, R)) = Set.univ
  proof: Set.univ_subset_iff.mp fun _ _ => mem_setOfIdeal.mpr ⟨1, Submodule.mem_top, one_ne_zero⟩

@[simp]

中文:
定理 setOfTop_eq_univ
  条件: [非平凡 R]
  结论: setOfIdeal (⊤ : 理想 C(X, R)) = 集合.univ
  证明: Set.univ_subset_iff.mp fun _ _ => mem_setOfIdeal.mpr ⟨1, Submodule.mem_top, one_ne_zero⟩

@[simp]

Depends on / 依赖: Set.univ_subset_iff.mp, Submodule, Submodule.mem_top, mem_setOfIdeal, mem_setOfIdeal.mpr, mem_top, one_ne_zero, univ_subset_iff
-/
theorem setOfTop_eq_univ [Nontrivial R] : setOfIdeal (⊤ : Ideal C(X, R)) = Set.univ :=
  Set.univ_subset_iff.mp fun _ _ => mem_setOfIdeal.mpr ⟨1, Submodule.mem_top, one_ne_zero⟩

@[simp]
/--
theorem `idealOfEmpty_eq_bot` / 定理 `idealOfEmpty_eq_bot`

English:
theorem idealOfEmpty_eq_bot
  statement: idealOfSet R (∅ : Set X) = ⊥
  proof: Ideal.ext fun f => by
    simp only [mem_idealOfSet, Set.compl_empty, Set.mem_univ, forall_true_left, Ideal.mem_bot,
      DFunLike.ext_iff, zero_apply]

@[simp]

中文:
定理 idealOfEmpty_eq_bot
  结论: idealOfSet R (∅ : 集合 X) = ⊥
  证明: Ideal.ext fun f => by
    simp only [mem_idealOfSet, Set.compl_empty, Set.mem_univ, forall_true_left, Ideal.mem_bot,
      DFunLike.ext_iff, zero_apply]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Ideal.ext, Ideal.mem_bot, Set.compl_empty, Set.mem_univ, compl_empty, ext_iff, forall_true_left, mem_bot, mem_idealOfSet, mem_univ, zero_apply
-/
theorem idealOfEmpty_eq_bot : idealOfSet R (∅ : Set X) = ⊥ :=
  Ideal.ext fun f => by
    simp only [mem_idealOfSet, Set.compl_empty, Set.mem_univ, forall_true_left, Ideal.mem_bot,
      DFunLike.ext_iff, zero_apply]

@[simp]
/--
theorem `mem_idealOfSet_compl_singleton` / 定理 `mem_idealOfSet_compl_singleton`

English:
theorem mem_idealOfSet_compl_singleton
  given: (x : X) (f : C(X, R))
  proof: by
  simp only [mem_idealOfSet, compl_compl, Set.mem_singleton_iff, forall_eq]

中文:
定理 mem_idealOfSet_compl_singleton
  条件: (x : X) (f : C(X, R))
  证明: by
  simp only [mem_idealOfSet, compl_compl, Set.mem_singleton_iff, forall_eq]

Depends on / 依赖: Set.mem_singleton_iff, compl_compl, forall_eq, mem_idealOfSet, mem_singleton_iff
-/
theorem mem_idealOfSet_compl_singleton (x : X) (f : C(X, R)) :
    f in idealOfSet R ({x}ᶜ : Set X) ↔ f x = 0 := by
  simp only [mem_idealOfSet, compl_compl, Set.mem_singleton_iff, forall_eq]

variable (X R)

/--
theorem `ideal_gc` / 定理 `ideal_gc`

English:
theorem ideal_gc
  statement: GaloisConnection (setOfIdeal : Ideal C(X, R) -> Set X) (idealOfSet R)
  proof: by
  refine fun I s => ⟨fun h f hf => ?_, fun h x hx => ?_⟩
  · by_contra h'
    rcases notMem_idealOfSet.mp h' with ⟨x, hx, hfx⟩
    exact hfx (notMem_setOfIdeal.mp (mt (@h x) hx) hf)
  · obtain ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
    by_contra hx'
    exact notMem_idealOfSet.mpr ⟨x, hx', hfx⟩ (h 

中文:
定理 ideal_gc
  结论: GaloisConnection (setOfIdeal : 理想 C(X, R) -> 集合 X) (idealOfSet R)
  证明: by
  refine fun I s => ⟨fun h f hf => ?_, fun h x hx => ?_⟩
  · by_contra h'
    rcases notMem_idealOfSet.mp h' with ⟨x, hx, hfx⟩
    exact hfx (notMem_setOfIdeal.mp (mt (@h x) hx) hf)
  · obtain ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
    by_contra hx'
    exact notMem_idealOfSet.mpr ⟨x, hx', hfx⟩ (h 

Depends on / 依赖: mem_setOfIdeal, mem_setOfIdeal.mp, notMem_idealOfSet, notMem_idealOfSet.mp, notMem_idealOfSet.mpr, notMem_setOfIdeal, notMem_setOfIdeal.mp
-/
theorem ideal_gc : GaloisConnection (setOfIdeal : Ideal C(X, R) -> Set X) (idealOfSet R) := by
  refine fun I s => ⟨fun h f hf => ?_, fun h x hx => ?_⟩
  · by_contra h'
    rcases notMem_idealOfSet.mp h' with ⟨x, hx, hfx⟩
    exact hfx (notMem_setOfIdeal.mp (mt (@h x) hx) hf)
  · obtain ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
    by_contra hx'
    exact notMem_idealOfSet.mpr ⟨x, hx', hfx⟩ (h hf)

end IsTopologicalRing

section RCLike

open RCLike

variable {X 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]

/--
theorem `exists_mul_le_one_eqOn_ge` / 定理 `exists_mul_le_one_eqOn_ge`

English:
theorem exists_mul_le_one_eqOn_ge
  given: (f : C(X, Real>=0)) {c : Real>=0} (hc : 0 < c)
  proof: ⟨{ toFun := (f ⊔ const X c)⁻¹
      continuous_toFun :=
        ((map_continuous f).sup <| map_continuous _).inv₀ fun _ => (hc.trans_le le_sup_right).ne' },
    fun x =>
    (inv_mul_le_iff₀ (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
    fun x hx => by
    simpa only [

中文:
定理 存在_mul_le_one_eqOn_ge
  条件: (f : C(X, 实数>=0)) {c : 实数>=0} (hc : 0 < c)
  证明: ⟨{ toFun := (f ⊔ const X c)⁻¹
      continuous_toFun :=
        ((map_continuous f).sup <| map_continuous _).inv₀ fun _ => (hc.trans_le le_sup_right).ne' },
    fun x =>
    (inv_mul_le_iff₀ (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
    fun x hx => by
    simpa only [

Depends on / 依赖: Function, Function.const_apply, Pi.inv_apply, Pi.one_apply, Pi.sup_apply, Set.mem_ofPred.mp, coe_const, coe_mk, const_apply, continuous_toFun, hc.trans_le, inv_apply, le_sup_left, le_sup_right, map_continuous, mem_ofPred, mul_apply, mul_one, ne_eq, one_apply
-/
theorem exists_mul_le_one_eqOn_ge (f : C(X, Real>=0)) {c : Real>=0} (hc : 0 < c) :
    exists g : C(X, Real>=0), (forall x : X, (g * f) x <= 1) ∧ {x : X | c <= f x}.EqOn (g * f) 1 :=
  ⟨{ toFun := (f ⊔ const X c)⁻¹
      continuous_toFun :=
        ((map_continuous f).sup <| map_continuous _).inv₀ fun _ => (hc.trans_le le_sup_right).ne' },
    fun x =>
    (inv_mul_le_iff₀ (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
    fun x hx => by
    simpa only [coe_const, mul_apply, coe_mk, Pi.inv_apply, Pi.sup_apply,
      Function.const_apply, sup_eq_left.mpr (Set.mem_ofPred.mp hx), ne_eq, Pi.one_apply]
      using inv_mul_cancel₀ (hc.trans_le hx).ne' ⟩

variable [CompactSpace X] [T2Space X]

@[simp]
/--
theorem `idealOfSet_ofIdeal_eq_closure` / 定理 `idealOfSet_ofIdeal_eq_closure`

English:
theorem idealOfSet_ofIdeal_eq_closure
  given: (I : Ideal C(X, 𝕜))
  proof: by
  /- Since `idealOfSet 𝕜 (setOfIdeal I)` is closed and contains `I`, it contains `I.closure`.
    For the reverse inclusion, given `f ∈ idealOfSet 𝕜 (setOfIdeal I)` and `(ε : ℝ≥0) > 0` it
    suffices to show that `f` is within `ε` of `I`. -/
  refine le_antisymm ?_
      ((idealOfSet_closed 𝕜 <|

中文:
定理 idealOfSet_ofIdeal_eq_closure
  条件: (I : 理想 C(X, 𝕜))
  证明: by
  /- Since `idealOfSet 𝕜 (setOfIdeal I)` is closed and contains `I`, it contains `I.closure`.
    For the reverse inclusion, given `f ∈ idealOfSet 𝕜 (setOfIdeal I)` and `(ε : ℝ≥0) > 0` it
    suffices to show that `f` is within `ε` of `I`. -/
  refine le_antisymm ?_
      ((idealOfSet_closed 𝕜 <|
-/
theorem idealOfSet_ofIdeal_eq_closure (I : Ideal C(X, 𝕜)) :
    idealOfSet 𝕜 (setOfIdeal I) = I.closure := by
  /- Since `idealOfSet 𝕜 (setOfIdeal I)` is closed and contains `I`, it contains `I.closure`.
    For the reverse inclusion, given `f ∈ idealOfSet 𝕜 (setOfIdeal I)` and `(ε : ℝ≥0) > 0` it
    suffices to show that `f` is within `ε` of `I`. -/
  refine le_antisymm ?_
      ((idealOfSet_closed 𝕜 <| setOfIdeal I).closure_subset_iff.mpr fun f hf x hx =>
        notMem_setOfIdeal.mp hx hf)
  refine (fun f hf => Metric.mem_closure_iff.mpr fun ε hε => ?_)
  lift ε to Real>=0 using hε.lt.le
  replace hε := show (0 : Real>=0) < ε from hε
  simp_rw [dist_nndist]
  norm_cast
  -- Let `t := {x : X | ε / 2 ≤ ‖f x‖₊}}` which is closed and disjoint from `set_of_ideal I`.
  set t := {x : X | ε / 2 <= ‖f x‖₊}
  have ht : IsClosed t := isClosed_le continuous_const (map_continuous f).nnnorm
  have htI : Disjoint t (setOfIdeal I)ᶜ := by
    refine Set.subset_compl_iff_disjoint_left.mp fun x hx => ?_
    simpa only [t, Set.mem_ofPred, Set.mem_compl_iff, not_le] using!
      (nnnorm_eq_zero.mpr (mem_idealOfSet.mp hf hx)).trans_lt (half_pos hε)
  /- It suffices to produce `g : C(X, ℝ≥0)` which takes values in `[0,1]` and is constantly `1` on
    `t` such that when composed with the natural embedding of `ℝ≥0` into `𝕜` lies in the ideal `I`.
    Indeed, then `‖f - f * ↑g‖ ≤ ‖f * (1 - ↑g)‖ ≤ ⨆ ‖f * (1 - ↑g) x‖`. When `x ∉ t`, `‖f x‖ < ε / 2`
    and `‖(1 - ↑g) x‖ ≤ 1`, and when `x ∈ t`, `(1 - ↑g) x = 0`, and clearly `f * ↑g ∈ I`. -/
  suffices
    exists g : C(X, Real>=0), (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g in I ∧ (forall x, g x <= 1) ∧ t.EqOn g 1 by
    obtain ⟨g, hgI, hg, hgt⟩ := this
    refine ⟨f * (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g, I.mul_mem_left f hgI, ?_⟩
    rw [nndist_eq_nnnorm]
    refine (nnnorm_lt_iff _ hε).2 fun x => ?_
    simp only [coe_sub, coe_mul, Pi.sub_apply, Pi.mul_apply]
    by_cases hx : x in t
    · simpa only [hgt hx, comp_apply, Pi.one_apply, ContinuousMap.coe_coe, algebraMapCLM_apply,
        map_one, mul_one, sub_self, nnnorm_zero] using! hε
    · refine lt_of_le_of_lt ?_ (half_lt_self hε)
      have :=
        calc
          ‖((1 - (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g) x : 𝕜)‖₊ =
              ‖1 - algebraMap Real>=0 𝕜 (g x)‖₊ := by
            simp only [coe_sub, coe_one, coe_comp, ContinuousMap.coe_coe, Pi.sub_apply,
              Pi.one_apply, Function.comp_apply, algebraMapCLM_apply]
          _ = ‖algebraMap Real>=0 𝕜 (1 - g x)‖₊ := by
            simp only [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, NNReal.coe_sub (hg x),
              NNReal.coe_one, sub_smul, one_smul]
          _ <= 1 := (nnnorm_algebraMap_nnreal 𝕜 (1 - g x)).trans_le tsub_le_self
      calc
        ‖f x - f x * (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g x‖₊ =
            ‖f x * (1 - (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g) x‖₊ := by
          simp only [mul_sub, coe_sub, coe_one, Pi.sub_apply, Pi.one_apply, mul_one]
        _ <= ε / 2 * ‖(1 - (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g) x‖₊ :=
          ((nnnorm_mul_le _ _).trans
            (mul_le_mul_left (not_le.mp <| show ¬ε / 2 <= ‖f x‖₊ from hx).le _))
        _ <= ε / 2 := by simpa only [mul_one] using! mul_le_mul_right this _
  /- There is some `g' : C(X, ℝ≥0)` which is strictly positive on `t` such that the composition
    `↑g` with the natural embedding of `ℝ≥0` into `𝕜` lies in `I`. This follows from compactness of
    `t` and that we can do it in any neighborhood of a point `x ∈ t`. Indeed, since `x ∈ t`, then
    `fₓ x ≠ 0` for some `fₓ ∈ I` and so `fun y ↦ ‖(star fₓ * fₓ) y‖₊` is strictly positive in a
    neighborhood of `y`. Moreover, `(‖(star fₓ * fₓ) y‖₊ : 𝕜) = (star fₓ * fₓ) y`, so composition of
    this map with the natural embedding is just `star fₓ * fₓ ∈ I`. -/
  have : exists g' : C(X, Real>=0), (algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g' in I ∧ forall x in t, 0 < g' x := by
    refine ht.isCompact.induction_on ?_ ?_ ?_ ?_
    · refine ⟨0, ?_, fun x hx => False.elim hx⟩
      convert! I.zero_mem
      ext
      simp only [comp_apply, zero_apply, ContinuousMap.coe_coe, map_zero]
    · rintro s₁ s₂ hs ⟨g, hI, hgt⟩; exact ⟨g, hI, fun x hx => hgt x (hs hx)⟩
    · rintro s₁ s₂ ⟨g₁, hI₁, hgt₁⟩ ⟨g₂, hI₂, hgt₂⟩
      refine ⟨g₁ + g₂, ?_, fun x hx => ?_⟩
      · convert! I.add_mem hI₁ hI₂
        ext y
        simp
      · rcases hx with (hx | hx)
        · simpa using add_lt_add_of_lt_of_le (hgt₁ x hx) zero_le
        · simpa using add_lt_add_of_le_of_lt zero_le (hgt₂ x hx)
    · intro x hx
      replace hx := htI.subset_compl_right hx
      rw [compl_compl]; rw [mem_setOfIdeal] at hx
      obtain ⟨g, hI, hgx⟩ := hx
      have := (map_continuous g).continuousAt.eventually_ne hgx
      refine
        ⟨{y : X | g y != 0} inter t,
          mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨_, this, Set.Subset.rfl⟩,
          ⟨⟨fun x => ‖g x‖₊ ^ 2, (map_continuous g).nnnorm.fun_pow 2⟩, ?_, fun x hx =>
            pow_pos (norm_pos_iff.mpr hx.1) 2⟩⟩
      convert! I.mul_mem_left (star g) hI
      ext
      simp only [comp_apply, coe_mk, algebraMapCLM_apply, map_pow,
        mul_apply, star_apply, star_def]
      simp only [RCLike.conj_mul]
      rfl
  /- Get the function `g'` which is guaranteed to exist above. By the extreme value theorem and
    compactness of `t`, there is some `0 < c` such that `c ≤ g' x` for all `x ∈ t`. Then by
    `exists_mul_le_one_eqOn_ge` there is some `g` for which `g * g'` is the desired function. -/
  obtain ⟨g', hI', hgt'⟩ := this
  obtain ⟨c, hc, hgc'⟩ : exists c > 0, t subseteq {y | c <= g' y} :=
    t.eq_empty_or_nonempty.elim
      (fun ht' => ⟨1, zero_lt_one, fun y hy => False.elim (by rwa [ht'] at hy)⟩) fun ht' =>
      let ⟨x, hx, hx'⟩ := ht.isCompact.exists_isMinOn ht' (map_continuous g').continuousOn
      ⟨g' x, hgt' x hx, hx'⟩
  obtain ⟨g, hg, hgc⟩ := exists_mul_le_one_eqOn_ge g' hc
  refine ⟨g * g', ?_, hg, hgc.mono hgc'⟩
  convert! I.mul_mem_left ((algebraMapCLM Real>=0 𝕜 : C(Real>=0, 𝕜)).comp g) hI'
  ext
  simp only [coe_algebraMapCLM, comp_apply, mul_apply, ContinuousMap.coe_coe, map_mul]

/--
theorem `idealOfSet_ofIdeal_isClosed` / 定理 `idealOfSet_ofIdeal_isClosed`

English:
theorem idealOfSet_ofIdeal_isClosed
  given: {I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜)))
  proof: (idealOfSet_ofIdeal_eq_closure I).trans (Ideal.ext <| Set.ext_iff.mp hI.closure_eq)

中文:
定理 idealOfSet_ofIdeal_isClosed
  条件: {I : 理想 C(X, 𝕜)} (hI : 是闭集 (I : 集合 C(X, 𝕜)))
  证明: (idealOfSet_ofIdeal_eq_closure I).trans (Ideal.ext <| Set.ext_iff.mp hI.closure_eq)

Depends on / 依赖: Ideal.ext, Set.ext_iff.mp, closure_eq, ext_iff, hI.closure_eq, idealOfSet_ofIdeal_eq_closure
-/
theorem idealOfSet_ofIdeal_isClosed {I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜))) :
    idealOfSet 𝕜 (setOfIdeal I) = I :=
  (idealOfSet_ofIdeal_eq_closure I).trans (Ideal.ext <| Set.ext_iff.mp hI.closure_eq)

variable (𝕜)

@[simp]
/--
theorem `setOfIdeal_ofSet_eq_interior` / 定理 `setOfIdeal_ofSet_eq_interior`

English:
theorem setOfIdeal_ofSet_eq_interior
  given: (s : Set X)
  statement: setOfIdeal (idealOfSet 𝕜 s) = interior s
  proof: by
  refine
    Set.Subset.antisymm
      ((setOfIdeal_open (idealOfSet 𝕜 s)).subset_interior_iff.mpr fun x hx =>
        let ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
        Set.notMem_compl_iff.mp (mt (@hf x) hfx))
      fun x hx => ?_
  -- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is z

中文:
定理 setOfIdeal_ofSet_eq_interior
  条件: (s : 集合 X)
  结论: setOfIdeal (idealOfSet 𝕜 s) = interior s
  证明: by
  refine
    Set.Subset.antisymm
      ((setOfIdeal_open (idealOfSet 𝕜 s)).subset_interior_iff.mpr fun x hx =>
        let ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
        Set.notMem_compl_iff.mp (mt (@hf x) hfx))
      fun x hx => ?_
  -- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is z

Depends on / 依赖: Set.Subset.antisymm, Set.notMem_compl_iff.mp, Subset, antisymm, idealOfSet, mem_setOfIdeal, mem_setOfIdeal.mp, notMem_compl_iff, setOfIdeal_open, subset_interior_iff, subset_interior_iff.mpr
-/
theorem setOfIdeal_ofSet_eq_interior (s : Set X) : setOfIdeal (idealOfSet 𝕜 s) = interior s := by
  refine
    Set.Subset.antisymm
      ((setOfIdeal_open (idealOfSet 𝕜 s)).subset_interior_iff.mpr fun x hx =>
        let ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
        Set.notMem_compl_iff.mp (mt (@hf x) hfx))
      fun x hx => ?_
  -- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is zero on `sᶜ` and `f x ≠ 0`.
  rw [← compl_compl (interior s)]; rw [← closure_compl] at hx
  simp_rw [mem_setOfIdeal, mem_idealOfSet]
  /- Apply Urysohn's lemma to get `g : C(X, ℝ)` which is zero on `sᶜ` and `g x ≠ 0`, then compose
    with the natural embedding `ℝ ↪ 𝕜` to produce the desired `f`. -/
  obtain ⟨g, hgs, hgx : Set.EqOn g 1 {x}, -⟩ :=
    exists_continuous_zero_one_of_isClosed isClosed_closure isClosed_singleton
      (Set.disjoint_singleton_right.mpr hx)
  exact
    ⟨⟨fun x => g x, continuous_ofReal.comp (map_continuous g)⟩, by
      simpa only [coe_mk, ofReal_eq_zero] using! fun x hx => hgs (subset_closure hx), by
      simpa only [coe_mk, hgx (Set.mem_singleton x), Pi.one_apply, RCLike.ofReal_one] using!
        one_ne_zero⟩

/--
theorem `setOfIdeal_ofSet_of_isOpen` / 定理 `setOfIdeal_ofSet_of_isOpen`

English:
theorem setOfIdeal_ofSet_of_isOpen
  given: {s : Set X} (hs : IsOpen s)
  statement: setOfIdeal (idealOfSet 𝕜 s) = s
  proof: (setOfIdeal_ofSet_eq_interior 𝕜 s).trans hs.interior_eq

中文:
定理 setOfIdeal_ofSet_of_isOpen
  条件: {s : 集合 X} (hs : 是开集 s)
  结论: setOfIdeal (idealOfSet 𝕜 s) = s
  证明: (setOfIdeal_ofSet_eq_interior 𝕜 s).trans hs.interior_eq

Depends on / 依赖: hs.interior_eq, interior_eq, setOfIdeal_ofSet_eq_interior
-/
theorem setOfIdeal_ofSet_of_isOpen {s : Set X} (hs : IsOpen s) : setOfIdeal (idealOfSet 𝕜 s) = s :=
  (setOfIdeal_ofSet_eq_interior 𝕜 s).trans hs.interior_eq

variable (X) in
/-- The Galois insertion `ContinuousMap.opensOfIdeal : Ideal C(X, 𝕜) → Opens X` and
`fun s ↦ ContinuousMap.idealOfSet ↑s`. -/
@[simps]
/--
Definition of `idealOpensGI` / `idealOpensGI` 的定义

English:
definition idealOpensGI
  signature: :
  body: opensOfIdeal I.closure
  gc I s := ideal_gc X 𝕜 I s
  le_l_u s := (setOfIdeal_ofSet_of_isOpen 𝕜 s.isOpen).ge
  choice_eq I hI :=
congr_arg _
      Ideal.ext
        (Set.ext_iff.mp
          (isClosed_of_closure_subset <|
              (idealOfSet_ofIdeal_eq_closure I ▸ hI : I.closure <= I)).closure

中文:
定义 idealOpensGI
  签名: :
  定义体: opensOfIdeal I.closure
  gc I s := ideal_gc X 𝕜 I s
  le_l_u s := (setOfIdeal_ofSet_of_isOpen 𝕜 s.isOpen).ge
  choice_eq I hI :=
congr_arg _
      Ideal.ext
        (Set.ext_iff.mp
          (isClosed_of_closure_subset <|
              (idealOfSet_ofIdeal_eq_closure I ▸ hI : I.closure <= I)).closure

Depends on / 依赖: I.closure, closure, opensOfIdeal
-/
def idealOpensGI :
    GaloisInsertion (opensOfIdeal : Ideal C(X, 𝕜) -> Opens X) fun s => idealOfSet 𝕜 s where
  choice I _ := opensOfIdeal I.closure
  gc I s := ideal_gc X 𝕜 I s
  le_l_u s := (setOfIdeal_ofSet_of_isOpen 𝕜 s.isOpen).ge
  choice_eq I hI :=
congr_arg _
      Ideal.ext
        (Set.ext_iff.mp
          (isClosed_of_closure_subset <|
              (idealOfSet_ofIdeal_eq_closure I ▸ hI : I.closure <= I)).closure_eq)

/--
theorem `idealOfSet_isMaximal_iff` / 定理 `idealOfSet_isMaximal_iff`

English:
theorem idealOfSet_isMaximal_iff
  given: (s : Opens X)
  proof: by
  rw [Ideal.isMaximal_def]
  refine (idealOpensGI X 𝕜).isCoatom_iff (fun I hI => ?_) s
  rw [← Ideal.isMaximal_def] at hI
  exact idealOfSet_ofIdeal_isClosed inferInstance

中文:
定理 idealOfSet_isMaximal_iff
  条件: (s : Opens X)
  证明: by
  rw [Ideal.isMaximal_def]
  refine (idealOpensGI X 𝕜).isCoatom_iff (fun I hI => ?_) s
  rw [← Ideal.isMaximal_def] at hI
  exact idealOfSet_ofIdeal_isClosed inferInstance

Depends on / 依赖: Ideal.isMaximal_def, idealOfSet_ofIdeal_isClosed, idealOpensGI, isCoatom_iff, isMaximal_def
-/
theorem idealOfSet_isMaximal_iff (s : Opens X) :
    (idealOfSet 𝕜 (s : Set X)).IsMaximal ↔ IsCoatom s := by
  rw [Ideal.isMaximal_def]
  refine (idealOpensGI X 𝕜).isCoatom_iff (fun I hI => ?_) s
  rw [← Ideal.isMaximal_def] at hI
  exact idealOfSet_ofIdeal_isClosed inferInstance

/--
theorem `idealOf_compl_singleton_isMaximal` / 定理 `idealOf_compl_singleton_isMaximal`

English:
theorem idealOf_compl_singleton_isMaximal
  given: (x : X)
  statement: (idealOfSet 𝕜 ({x}ᶜ : Set X)).IsMaximal
  proof: (idealOfSet_isMaximal_iff 𝕜 _).mpr Opens.isCoatom_iff.mpr ⟨x, rfl⟩

中文:
定理 idealOf_compl_singleton_isMaximal
  条件: (x : X)
  结论: (idealOfSet 𝕜 ({x}ᶜ : 集合 X)).是极大
  证明: (idealOfSet_isMaximal_iff 𝕜 _).mpr Opens.isCoatom_iff.mpr ⟨x, rfl⟩

Depends on / 依赖: Opens.isCoatom_iff.mpr, idealOfSet_isMaximal_iff, isCoatom_iff
-/
theorem idealOf_compl_singleton_isMaximal (x : X) : (idealOfSet 𝕜 ({x}ᶜ : Set X)).IsMaximal :=
(idealOfSet_isMaximal_iff 𝕜 _).mpr Opens.isCoatom_iff.mpr ⟨x, rfl⟩

variable {𝕜}

/--
theorem `setOfIdeal_eq_compl_singleton` / 定理 `setOfIdeal_eq_compl_singleton`

English:
theorem setOfIdeal_eq_compl_singleton
  given: (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal]
  proof: by
  have h : (idealOfSet 𝕜 (setOfIdeal I)).IsMaximal :=
    (idealOfSet_ofIdeal_isClosed (inferInstance : IsClosed (I : Set C(X, 𝕜)))).symm ▸ hI
  obtain ⟨x, hx⟩ := Opens.isCoatom_iff.1 ((idealOfSet_isMaximal_iff 𝕜 (opensOfIdeal I)).1 h)
  exact ⟨x, congr_arg (fun (s : Opens X) => (s : Set X)) hx⟩

中文:
定理 setOfIdeal_eq_compl_singleton
  条件: (I : 理想 C(X, 𝕜)) [hI : I.是极大]
  证明: by
  have h : (idealOfSet 𝕜 (setOfIdeal I)).IsMaximal :=
    (idealOfSet_ofIdeal_isClosed (inferInstance : IsClosed (I : Set C(X, 𝕜)))).symm ▸ hI
  obtain ⟨x, hx⟩ := Opens.isCoatom_iff.1 ((idealOfSet_isMaximal_iff 𝕜 (opensOfIdeal I)).1 h)
  exact ⟨x, congr_arg (fun (s : Opens X) => (s : Set X)) hx⟩

Depends on / 依赖: IsClosed, IsMaximal, Opens.isCoatom_iff, congr_arg, idealOfSet, idealOfSet_isMaximal_iff, idealOfSet_ofIdeal_isClosed, isCoatom_iff, opensOfIdeal, setOfIdeal
-/
theorem setOfIdeal_eq_compl_singleton (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal] :
    exists x : X, setOfIdeal I = {x}ᶜ := by
  have h : (idealOfSet 𝕜 (setOfIdeal I)).IsMaximal :=
    (idealOfSet_ofIdeal_isClosed (inferInstance : IsClosed (I : Set C(X, 𝕜)))).symm ▸ hI
  obtain ⟨x, hx⟩ := Opens.isCoatom_iff.1 ((idealOfSet_isMaximal_iff 𝕜 (opensOfIdeal I)).1 h)
  exact ⟨x, congr_arg (fun (s : Opens X) => (s : Set X)) hx⟩

/--
theorem `ideal_isMaximal_iff` / 定理 `ideal_isMaximal_iff`

English:
theorem ideal_isMaximal_iff
  given: (I : Ideal C(X, 𝕜)) [hI : IsClosed (I : Set C(X, 𝕜))]
  proof: by
  refine
    ⟨?_, fun h =>
      let ⟨x, hx⟩ := h
      hx ▸ idealOf_compl_singleton_isMaximal 𝕜 x⟩
  intro hI'
  obtain ⟨x, hx⟩ := setOfIdeal_eq_compl_singleton I
  exact
    ⟨x, by
      simpa only [idealOfSet_ofIdeal_eq_closure, I.closure_eq_of_isClosed hI] using
        congr_arg (idealOfSet 

中文:
定理 ideal_isMaximal_iff
  条件: (I : 理想 C(X, 𝕜)) [hI : 是闭集 (I : 集合 C(X, 𝕜))]
  证明: by
  refine
    ⟨?_, fun h =>
      let ⟨x, hx⟩ := h
      hx ▸ idealOf_compl_singleton_isMaximal 𝕜 x⟩
  intro hI'
  obtain ⟨x, hx⟩ := setOfIdeal_eq_compl_singleton I
  exact
    ⟨x, by
      simpa only [idealOfSet_ofIdeal_eq_closure, I.closure_eq_of_isClosed hI] using
        congr_arg (idealOfSet 

Depends on / 依赖: I.closure_eq_of_isClosed, closure_eq_of_isClosed, congr_arg, hx.symm, idealOfSet, idealOfSet_ofIdeal_eq_closure, idealOf_compl_singleton_isMaximal, setOfIdeal_eq_compl_singleton
-/
theorem ideal_isMaximal_iff (I : Ideal C(X, 𝕜)) [hI : IsClosed (I : Set C(X, 𝕜))] :
    I.IsMaximal ↔ exists x : X, idealOfSet 𝕜 {x}ᶜ = I := by
  refine
    ⟨?_, fun h =>
      let ⟨x, hx⟩ := h
      hx ▸ idealOf_compl_singleton_isMaximal 𝕜 x⟩
  intro hI'
  obtain ⟨x, hx⟩ := setOfIdeal_eq_compl_singleton I
  exact
    ⟨x, by
      simpa only [idealOfSet_ofIdeal_eq_closure, I.closure_eq_of_isClosed hI] using
        congr_arg (idealOfSet 𝕜) hx.symm⟩

end RCLike

end ContinuousMap

namespace WeakDual

namespace CharacterSpace

open Function ContinuousMap

variable (X 𝕜 : Type*) [TopologicalSpace X]

section ContinuousMapEval

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
variable [Nontrivial 𝕜] [NoZeroDivisors 𝕜]

/--
Definition of `continuousMapEval` / `continuousMapEval` 的定义

English:
definition continuousMapEval
  signature: : C(X, characterSpace 𝕜 C(X, 𝕜)) where
  body: ⟨{ toFun := fun f => f x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }, by
        rw [CharacterSpace.eq_set_map_one_map_mul]; exact ⟨rfl, fun f g => rfl⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_of_continuous_eval map_continuous) _

@[simp]

中文:
定义 continuousMapEval
  签名: : C(X, characterSpace 𝕜 C(X, 𝕜)) where
  定义体: ⟨{ toFun := fun f => f x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }, by
        rw [CharacterSpace.eq_set_map_one_map_mul]; exact ⟨rfl, fun f g => rfl⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_of_continuous_eval map_continuous) _

@[simp]

Depends on / 依赖: CharacterSpace, CharacterSpace.eq_set_map_one_map_mul, Continuous, Continuous.subtype_mk, continuous_of_continuous_eval, continuous_toFun, eq_set_map_one_map_mul, map_add, map_continuous, map_smul, subtype_mk
-/
def continuousMapEval : C(X, characterSpace 𝕜 C(X, 𝕜)) where
  toFun x :=
    ⟨{ toFun := fun f => f x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }, by
        rw [CharacterSpace.eq_set_map_one_map_mul]; exact ⟨rfl, fun f g => rfl⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_of_continuous_eval map_continuous) _

@[simp]
/--
theorem `continuousMapEval_apply_apply` / 定理 `continuousMapEval_apply_apply`

English:
theorem continuousMapEval_apply_apply
  given: (x : X) (f : C(X, 𝕜))
  statement: continuousMapEval X 𝕜 x f = f x
  proof: rfl

中文:
定理 continuousMapEval_apply_apply
  条件: (x : X) (f : C(X, 𝕜))
  结论: continuousMapEval X 𝕜 x f = f x
  证明: rfl
-/
theorem continuousMapEval_apply_apply (x : X) (f : C(X, 𝕜)) : continuousMapEval X 𝕜 x f = f x :=
  rfl

end ContinuousMapEval

variable [CompactSpace X] [T2Space X] [RCLike 𝕜]

/--
theorem `continuousMapEval_bijective` / 定理 `continuousMapEval_bijective`

English:
theorem continuousMapEval_bijective
  statement: Bijective (continuousMapEval X 𝕜)
  proof: by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · contrapose! hxy
    rcases exists_continuous_zero_one_of_isClosed (isClosed_singleton : _root_.IsClosed {x})
        (isClosed_singleton : _root_.IsClosed {y}) (Set.disjoint_singleton.mpr hxy) with
      ⟨f, fx, fy, -⟩
    rw [DFunLike.ne_iff]
    use

中文:
定理 continuousMapEval_bijective
  结论: 双射 (continuousMapEval X 𝕜)
  证明: by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · contrapose! hxy
    rcases exists_continuous_zero_one_of_isClosed (isClosed_singleton : _root_.IsClosed {x})
        (isClosed_singleton : _root_.IsClosed {y}) (Set.disjoint_singleton.mpr hxy) with
      ⟨f, fx, fy, -⟩
    rw [DFunLike.ne_iff]
    use

Depends on / 依赖: ContinuousMap, ContinuousMap.comp_apply, DFunLike, DFunLike.ne_iff, IsClosed, RCLike, RCLike.continuous_ofReal, RCLike.ofReal_inj, Set.disjoint_singleton.mpr, Set.mem, Set.mem_singleton, _root_, _root_.IsClosed, coe_mk, comp_apply, continuousMapEval_apply_apply, continuous_ofReal, contrapose, disjoint_singleton, exists_continuous_zero_one_of_isClosed
-/
theorem continuousMapEval_bijective : Bijective (continuousMapEval X 𝕜) := by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · contrapose! hxy
    rcases exists_continuous_zero_one_of_isClosed (isClosed_singleton : _root_.IsClosed {x})
        (isClosed_singleton : _root_.IsClosed {y}) (Set.disjoint_singleton.mpr hxy) with
      ⟨f, fx, fy, -⟩
    rw [DFunLike.ne_iff]
    use (⟨fun (x : Real) => (x : 𝕜), RCLike.continuous_ofReal⟩ : C(Real, 𝕜)).comp f
    simpa only [continuousMapEval_apply_apply, ContinuousMap.comp_apply, coe_mk, Ne,
      RCLike.ofReal_inj] using
      ((fx (Set.mem_singleton x)).symm ▸ (fy (Set.mem_singleton y)).symm ▸ zero_ne_one : f x != f y)
  · obtain ⟨x, hx⟩ := (ideal_isMaximal_iff (RingHom.ker φ)).mp inferInstance
refine ⟨x, CharacterSpace.ext_ker Ideal.ext fun f => ?_⟩
    simpa only [RingHom.mem_ker, continuousMapEval_apply_apply, mem_idealOfSet_compl_singleton,
      RingHom.mem_ker] using SetLike.ext_iff.mp hx f

/--
Definition of `homeoEval` / `homeoEval` 的定义

English:
definition homeoEval
  signature: : X ≃ₜ characterSpace 𝕜 C(X, 𝕜)
  body: @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    { Equiv.ofBijective _ (continuousMapEval_bijective X 𝕜) with toFun := continuousMapEval X 𝕜 }
    (map_continuous (continuousMapEval X 𝕜))

中文:
定义 homeoEval
  签名: : X ≃ₜ characterSpace 𝕜 C(X, 𝕜)
  定义体: @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    { Equiv.ofBijective _ (continuousMapEval_bijective X 𝕜) with toFun := continuousMapEval X 𝕜 }
    (map_continuous (continuousMapEval X 𝕜))

Depends on / 依赖: Continuous, Continuous.homeoOfEquivCompactToT2, Equiv.ofBijective, continuousMapEval, continuousMapEval_bijective, homeoOfEquivCompactToT2, map_continuous, ofBijective
-/
noncomputable def homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜) :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    { Equiv.ofBijective _ (continuousMapEval_bijective X 𝕜) with toFun := continuousMapEval X 𝕜 }
    (map_continuous (continuousMapEval X 𝕜))

end CharacterSpace

end WeakDual
