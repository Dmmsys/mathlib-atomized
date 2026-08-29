/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Theory of topological modules

We use the class `ContinuousSMul` for topological (semi) modules and topological vector spaces.
-/

@[expose] public section

assert_not_exists Cardinal TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [Module R M]

/--
theorem `ContinuousSMul.of_nhds_zero` / 定理 `ContinuousSMul.of_nhds_zero`

English:
theorem ContinuousSMul.of_nhds_zero
  statement: [IsTopologicalRing R] [IsTopologicalAddGroup M]
  proof: by
    rw [← nhds_prod_eq] at hmul
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.smul : R ->+ M ->+ M) ?_ ?_ ?_ <;>
      simpa [ContinuousAt]

中文:
定理 连续标量乘法.of_nhds_zero
  结论: [是拓扑环 R] [是拓扑加群 M]
  证明: by
    rw [← nhds_prod_eq] at hmul
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.smul : R ->+ M ->+ M) ?_ ?_ ?_ <;>
      simpa [ContinuousAt]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.smul, ContinuousAt, nhds_prod_eq
-/
theorem ContinuousSMul.of_nhds_zero [IsTopologicalRing R] [IsTopologicalAddGroup M]
    (hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0))
    (hmulleft : forall m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0))
    (hmulright : forall a : R, Tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : ContinuousSMul R M where
  continuous_smul := by
    rw [← nhds_prod_eq] at hmul
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.smul : R ->+ M ->+ M) ?_ ?_ ?_ <;>
      simpa [ContinuousAt]

variable (R M) in
omit [TopologicalSpace R] in
/--
theorem `ContinuousNeg.of_continuousConstSMul` / 定理 `ContinuousNeg.of_continuousConstSMul`

English:
theorem ContinuousNeg.of_continuousConstSMul
  given: [ContinuousConstSMul R M]
  statement: ContinuousNeg M where
  proof: by simpa using continuous_const_smul (T := M) (-1 : R)

中文:
定理 连续取负.of_continuousConstSMul
  条件: [连续常数标量乘法 R M]
  结论: 连续取负 M where
  证明: by simpa using continuous_const_smul (T := M) (-1 : R)

Depends on / 依赖: continuous_const_smul
-/
theorem ContinuousNeg.of_continuousConstSMul [ContinuousConstSMul R M] : ContinuousNeg M where
  continuous_neg := by simpa using continuous_const_smul (T := M) (-1 : R)

end

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]

/--
theorem `Submodule.eq_top_of_nonempty_interior'` / 定理 `Submodule.eq_top_of_nonempty_interior'`

English:
theorem Submodule.eq_top_of_nonempty_interior'
  statement: [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
  proof: by
  rcases hs with ⟨y, hy⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [mem_interior_iff_mem_nhds] at hy
  have : Tendsto (fun c : R => y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + 0)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).zero_smul_const _)
  rw [add_zero] at this
  obtain ⟨_, hu : y + _ • _ in s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (Filter.mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y in ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

中文:
定理 子模.eq_top_of_nonempty_interior'
  结论: [NeBot (𝓝[{ x : R | 是单位 x }] 0)]
  证明: by
  rcases hs with ⟨y, hy⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [mem_interior_iff_mem_nhds] at hy
  have : Tendsto (fun c : R => y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + 0)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).zero_smul_const _)
  rw [add_zero] at this
  obtain ⟨_, hu : y + _ • _ in s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (Filter.mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y in ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

Depends on / 依赖: Filter, Filter.mem_map, IsUnit, Submodule, Submodule.eq_top_iff, Tendsto, add_mem_iff_right, add_zero, eq_top_iff, inter_mem, mem_interior_iff_mem_nhds, mem_map, mem_of_mem_nhds, nonempty_of_mem, s.add_mem_iff_right, self_mem_nhdsWithin, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_id, tendsto_nhdsWithin_of_tendsto_nhds
-/
theorem Submodule.eq_top_of_nonempty_interior' [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
    (s : Submodule R M) (hs : (interior (s : Set M)).Nonempty) : s = ⊤ := by
  rcases hs with ⟨y, hy⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [mem_interior_iff_mem_nhds] at hy
  have : Tendsto (fun c : R => y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + 0)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).zero_smul_const _)
  rw [add_zero] at this
  obtain ⟨_, hu : y + _ • _ in s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (Filter.mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y in ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

variable (R M) [IsDomain R]

/--
theorem `Module.punctured_nhds_neBot` / 定理 `Module.punctured_nhds_neBot`

English:
theorem Module.punctured_nhds_neBot
  statement: [Nontrivial M] [NeBot (𝓝[!=] (0 : R))] [Module.IsTorsionFree R M]
  proof: by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices Tendsto (fun c : R => x + c • y) (𝓝[!=] 0) (𝓝[!=] x) from this.neBot
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 <| ?_)
  · convert! tendsto_const_nhds.add ((@tendsto_id R _).zero_smul_const y)
    rw [add_zero]
  · intro c hc
    simpa [hy] using hc

中文:
定理 模.punctured_nhds_neBot
  结论: [非平凡 M] [NeBot (𝓝[!=] (0 : R))] [模.是无挠 R M]
  证明: by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices Tendsto (fun c : R => x + c • y) (𝓝[!=] 0) (𝓝[!=] x) from this.neBot
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 <| ?_)
  · convert! tendsto_const_nhds.add ((@tendsto_id R _).zero_smul_const y)
    rw [add_zero]
  · intro c hc
    simpa [hy] using hc

Depends on / 依赖: Tendsto, Tendsto.inf, add_zero, convert, exists_ne, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_id, tendsto_principal_principal, this.neBot, zero_smul_const
-/
theorem Module.punctured_nhds_neBot [Nontrivial M] [NeBot (𝓝[!=] (0 : R))] [Module.IsTorsionFree R M]
    (x : M) : NeBot (𝓝[!=] x) := by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices Tendsto (fun c : R => x + c • y) (𝓝[!=] 0) (𝓝[!=] x) from this.neBot
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 <| ?_)
  · convert! tendsto_const_nhds.add ((@tendsto_id R _).zero_smul_const y)
    rw [add_zero]
  · intro c hc
    simpa [hy] using hc

end

section LatticeOps

variable {R S M₁ M₂ M₂' : Type*} {φ : R -> S} [SMul R M₁] [SMul R M₂] [SMul S M₂']
  [u : TopologicalSpace R] [u' : TopologicalSpace S]
  {t : TopologicalSpace M₂} {t' : TopologicalSpace M₂'}
  [ContinuousSMul R M₂] [ContinuousSMul S M₂']
  {F : Type*} [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂] (f : F)
  {F' : Type*} [FunLike F' M₁ M₂'] [MulActionSemiHomClass F' φ M₁ M₂'] (f' : F')

/--
theorem `continuousSMul_inducedₛₗ` / 定理 `continuousSMul_inducedₛₗ`

English:
theorem continuousSMul_inducedₛₗ
  given: (hφ : Continuous φ)
  statement: @ContinuousSMul R M₁ _ u (t'.induced f')
  proof: let _ : TopologicalSpace M₁ := t'.induced f'
  IsInducing.continuousSMul ⟨rfl⟩ hφ (map_smulₛₗ f' _ _)

中文:
定理 continuousSMul_inducedₛₗ
  条件: (hφ : 连续 φ)
  结论: @连续标量乘法 R M₁ _ u (t'.induced f')
  证明: let _ : TopologicalSpace M₁ := t'.induced f'
  IsInducing.continuousSMul ⟨rfl⟩ hφ (map_smulₛₗ f' _ _)

Depends on / 依赖: IsInducing, IsInducing.continuousSMul, TopologicalSpace, continuousSMul, induced
-/
theorem continuousSMul_inducedₛₗ (hφ : Continuous φ) : @ContinuousSMul R M₁ _ u (t'.induced f') :=
  let _ : TopologicalSpace M₁ := t'.induced f'
  IsInducing.continuousSMul ⟨rfl⟩ hφ (map_smulₛₗ f' _ _)

/--
theorem `continuousSMul_induced` / 定理 `continuousSMul_induced`

English:
theorem continuousSMul_induced
  statement: @ContinuousSMul R M₁ _ u (t.induced f)
  proof: continuousSMul_inducedₛₗ f continuous_id

中文:
定理 continuousSMul_induced
  结论: @连续标量乘法 R M₁ _ u (t.induced f)
  证明: continuousSMul_inducedₛₗ f continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f) :=
  continuousSMul_inducedₛₗ f continuous_id

end LatticeOps

/--
lemma `TopologicalSpace.IsSeparable.span` / 引理 `TopologicalSpace.IsSeparable.span`

English:
lemma TopologicalSpace.IsSeparable.span
  statement: {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M]
  proof: by
  rw [Submodule.span_eq_iUnion_nat]
  refine .iUnion fun n => .image ?_ ?_
  · have : IsSeparable {f : Fin n -> R × M | forall (i : Fin n), f i in Set.univ ×ˢ s} := by
      apply isSeparable_pi (fun i => .prod (.of_separableSpace Set.univ) hs)
    rwa [Set.univ_prod] at this
  · apply continuous_finsetSum _ (fun i _ => ?_)
    exact (continuous_fst.comp (continuous_apply i)).smul (continuous_snd.comp (continuous_apply i))

中文:
引理 拓扑空间.是可分.span
  结论: {R M : 类型} [加法交换幺半群 M] [半环 R] [模 R M]
  证明: by
  rw [Submodule.span_eq_iUnion_nat]
  refine .iUnion fun n => .image ?_ ?_
  · have : IsSeparable {f : Fin n -> R × M | forall (i : Fin n), f i in Set.univ ×ˢ s} := by
      apply isSeparable_pi (fun i => .prod (.of_separableSpace Set.univ) hs)
    rwa [Set.univ_prod] at this
  · apply continuous_finsetSum _ (fun i _ => ?_)
    exact (continuous_fst.comp (continuous_apply i)).smul (continuous_snd.comp (continuous_apply i))

Depends on / 依赖: IsSeparable, Set.univ, Set.univ_prod, Submodule, Submodule.span_eq_iUnion_nat, continuous_apply, continuous_finsetSum, continuous_fst, continuous_fst.comp, continuous_snd, continuous_snd.comp, iUnion, isSeparable_pi, of_separableSpace, span_eq_iUnion_nat, univ_prod
-/
lemma TopologicalSpace.IsSeparable.span {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M]
    [TopologicalSpace M] [TopologicalSpace R] [SeparableSpace R]
    [ContinuousAdd M] [ContinuousSMul R M] {s : Set M} (hs : IsSeparable s) :
    IsSeparable (Submodule.span R s : Set M) := by
  rw [Submodule.span_eq_iUnion_nat]
  refine .iUnion fun n => .image ?_ ?_
  · have : IsSeparable {f : Fin n -> R × M | forall (i : Fin n), f i in Set.univ ×ˢ s} := by
      apply isSeparable_pi (fun i => .prod (.of_separableSpace Set.univ) hs)
    rwa [Set.univ_prod] at this
  · apply continuous_finsetSum _ (fun i _ => ?_)
    exact (continuous_fst.comp (continuous_apply i)).smul (continuous_snd.comp (continuous_apply i))

namespace Submodule

/--
Instance `topologicalAddGroup` / 实例 `topologicalAddGroup`

English:
instance topologicalAddGroup
  signature: {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  body: inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup)

中文:
实例 topologicalAddGroup
  签名: {R M : 类型} [环 R] [加法交换群 M] [模 R M]
  定义体: inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup)

Depends on / 依赖: IsTopologicalAddGroup, S.toAddSubgroup, toAddSubgroup
-/
instance topologicalAddGroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (S : Submodule R M) : IsTopologicalAddGroup S :=
  inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup)

end Submodule

section closure

variable {R : Type u} {M : Type v} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousConstSMul R M]

/--
theorem `Submodule.mapsTo_smul_closure` / 定理 `Submodule.mapsTo_smul_closure`

English:
theorem Submodule.mapsTo_smul_closure
  given: (s : Submodule R M) (c : R)
  proof: have : Set.MapsTo (c • ·) (s : Set M) s := fun _ h => s.smul_mem c h
  this.closure (continuous_const_smul c)

中文:
定理 子模.mapsTo_smul_closure
  条件: (s : 子模 R M) (c : R)
  证明: have : Set.MapsTo (c • ·) (s : Set M) s := fun _ h => s.smul_mem c h
  this.closure (continuous_const_smul c)

Depends on / 依赖: MapsTo, Set.MapsTo, closure, continuous_const_smul, s.smul_mem, smul_mem, this.closure
-/
theorem Submodule.mapsTo_smul_closure (s : Submodule R M) (c : R) :
    Set.MapsTo (c • ·) (closure s : Set M) (closure s) :=
  have : Set.MapsTo (c • ·) (s : Set M) s := fun _ h => s.smul_mem c h
  this.closure (continuous_const_smul c)

/--
theorem `Submodule.smul_closure_subset` / 定理 `Submodule.smul_closure_subset`

English:
theorem Submodule.smul_closure_subset
  given: (s : Submodule R M) (c : R)
  proof: (s.mapsTo_smul_closure c).image_subset

中文:
定理 子模.smul_closure_subset
  条件: (s : 子模 R M) (c : R)
  证明: (s.mapsTo_smul_closure c).image_subset

Depends on / 依赖: image_subset, mapsTo_smul_closure, s.mapsTo_smul_closure
-/
theorem Submodule.smul_closure_subset (s : Submodule R M) (c : R) :
    c • closure (s : Set M) subseteq closure (s : Set M) :=
  (s.mapsTo_smul_closure c).image_subset

variable [ContinuousAdd M]

/--
Definition of `Submodule.topologicalClosure` / `Submodule.topologicalClosure` 的定义

English:
definition Submodule.topologicalClosure
  signature: (s : Submodule R M)
  body: { s.toAddSubmonoid.topologicalClosure with
    smul_mem' := s.mapsTo_smul_closure }

@[simp, norm_cast]

中文:
定义 子模.topologicalClosure
  签名: (s : 子模 R M)
  定义体: { s.toAddSubmonoid.topologicalClosure with
    smul_mem' := s.mapsTo_smul_closure }

@[simp, norm_cast]

Depends on / 依赖: mapsTo_smul_closure, s.mapsTo_smul_closure, s.toAddSubmonoid.topologicalClosure, smul_mem, toAddSubmonoid, topologicalClosure
-/
def Submodule.topologicalClosure (s : Submodule R M) : Submodule R M :=
  { s.toAddSubmonoid.topologicalClosure with
    smul_mem' := s.mapsTo_smul_closure }

@[simp, norm_cast]
/--
theorem `Submodule.topologicalClosure_coe` / 定理 `Submodule.topologicalClosure_coe`

English:
theorem Submodule.topologicalClosure_coe
  given: (s : Submodule R M)
  proof: rfl

中文:
定理 子模.topologicalClosure_coe
  条件: (s : 子模 R M)
  证明: rfl
-/
theorem Submodule.topologicalClosure_coe (s : Submodule R M) :
    (s.topologicalClosure : Set M) = closure (s : Set M) :=
  rfl

/--
theorem `Submodule.le_topologicalClosure` / 定理 `Submodule.le_topologicalClosure`

English:
theorem Submodule.le_topologicalClosure
  given: (s : Submodule R M)
  statement: s <= s.topologicalClosure
  proof: subset_closure

中文:
定理 子模.le_topologicalClosure
  条件: (s : 子模 R M)
  结论: s <= s.topologicalClosure
  证明: subset_closure

Depends on / 依赖: subset_closure
-/
theorem Submodule.le_topologicalClosure (s : Submodule R M) : s <= s.topologicalClosure :=
  subset_closure

/--
theorem `Submodule.closure_subset_topologicalClosure_span` / 定理 `Submodule.closure_subset_topologicalClosure_span`

English:
theorem Submodule.closure_subset_topologicalClosure_span
  given: (s : Set M)
  proof: by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono subset_span

中文:
定理 子模.closure_subset_topologicalClosure_span
  条件: (s : 集合 M)
  证明: by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono subset_span

Depends on / 依赖: Submodule, Submodule.topologicalClosure_coe, closure_mono, subset_span, topologicalClosure_coe
-/
theorem Submodule.closure_subset_topologicalClosure_span (s : Set M) :
    closure s subseteq (span R s).topologicalClosure := by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono subset_span

/--
theorem `Submodule.isClosed_topologicalClosure` / 定理 `Submodule.isClosed_topologicalClosure`

English:
theorem Submodule.isClosed_topologicalClosure
  given: (s : Submodule R M)
  proof: isClosed_closure

中文:
定理 子模.isClosed_topologicalClosure
  条件: (s : 子模 R M)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem Submodule.isClosed_topologicalClosure (s : Submodule R M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

/--
theorem `Submodule.topologicalClosure_minimal` / 定理 `Submodule.topologicalClosure_minimal`

English:
theorem Submodule.topologicalClosure_minimal
  statement: (s : Submodule R M) {t : Submodule R M} (h : s <= t)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 子模.topologicalClosure_minimal
  结论: (s : 子模 R M) {t : 子模 R M} (h : s <= t)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem Submodule.topologicalClosure_minimal (s : Submodule R M) {t : Submodule R M} (h : s <= t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `Submodule.topologicalClosure_mono` / 定理 `Submodule.topologicalClosure_mono`

English:
theorem Submodule.topologicalClosure_mono
  given: {s : Submodule R M} {t : Submodule R M} (h : s <= t)
  proof: closure_mono h

中文:
定理 子模.topologicalClosure_mono
  条件: {s : 子模 R M} {t : 子模 R M} (h : s <= t)
  证明: closure_mono h

Depends on / 依赖: closure_mono
-/
theorem Submodule.topologicalClosure_mono {s : Submodule R M} {t : Submodule R M} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  closure_mono h

/--
theorem `IsClosed.submodule_topologicalClosure_eq` / 定理 `IsClosed.submodule_topologicalClosure_eq`

English:
theorem IsClosed.submodule_topologicalClosure_eq
  given: {s : Submodule R M} (hs : IsClosed (s : Set M))
  proof: SetLike.ext' hs.closure_eq

中文:
定理 是闭集.submodule_topologicalClosure_eq
  条件: {s : 子模 R M} (hs : 是闭集 (s : 集合 M))
  证明: SetLike.ext' hs.closure_eq

Depends on / 依赖: SetLike, SetLike.ext, closure_eq, hs.closure_eq
-/
theorem IsClosed.submodule_topologicalClosure_eq {s : Submodule R M} (hs : IsClosed (s : Set M)) :
    s.topologicalClosure = s :=
  SetLike.ext' hs.closure_eq

/--
theorem `Submodule.dense_iff_topologicalClosure_eq_top` / 定理 `Submodule.dense_iff_topologicalClosure_eq_top`

English:
theorem Submodule.dense_iff_topologicalClosure_eq_top
  given: {s : Submodule R M}
  proof: by
  rw [← SetLike.coe_set_eq]; rw [dense_iff_closure_eq]
  simp

中文:
定理 子模.dense_iff_topologicalClosure_eq_top
  条件: {s : 子模 R M}
  证明: by
  rw [← SetLike.coe_set_eq]; rw [dense_iff_closure_eq]
  simp

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq, dense_iff_closure_eq
-/
theorem Submodule.dense_iff_topologicalClosure_eq_top {s : Submodule R M} :
    Dense (s : Set M) ↔ s.topologicalClosure = ⊤ := by
  rw [← SetLike.coe_set_eq]; rw [dense_iff_closure_eq]
  simp

/--
Instance `Submodule.topologicalClosure.completeSpace` / 实例 `Submodule.topologicalClosure.completeSpace`

English:
instance Submodule.topologicalClosure.completeSpace
  signature: {M' : Type*} [AddCommMonoid M'] [Module R M']
  body: isClosed_closure.completeSpace_coe

中文:
实例 子模.topologicalClosure.completeSpace
  签名: {M' : 类型} [加法交换幺半群 M'] [模 R M']
  定义体: isClosed_closure.completeSpace_coe

Depends on / 依赖: completeSpace_coe, isClosed_closure, isClosed_closure.completeSpace_coe
-/
instance Submodule.topologicalClosure.completeSpace {M' : Type*} [AddCommMonoid M'] [Module R M']
    [UniformSpace M'] [ContinuousAdd M'] [ContinuousConstSMul R M'] [CompleteSpace M']
    (U : Submodule R M') : CompleteSpace U.topologicalClosure :=
  isClosed_closure.completeSpace_coe

/--
theorem `Submodule.isClosed_or_dense_of_isCoatom` / 定理 `Submodule.isClosed_or_dense_of_isCoatom`

English:
theorem Submodule.isClosed_or_dense_of_isCoatom
  given: (s : Submodule R M) (hs : IsCoatom s)
  proof: by
  refine (hs.le_iff.mp s.le_topologicalClosure).symm.imp ?_ dense_iff_topologicalClosure_eq_top.mpr
  exact fun h => h ▸ isClosed_closure

中文:
定理 子模.isClosed_or_dense_of_isCoatom
  条件: (s : 子模 R M) (hs : IsCoatom s)
  证明: by
  refine (hs.le_iff.mp s.le_topologicalClosure).symm.imp ?_ dense_iff_topologicalClosure_eq_top.mpr
  exact fun h => h ▸ isClosed_closure

Depends on / 依赖: dense_iff_topologicalClosure_eq_top, dense_iff_topologicalClosure_eq_top.mpr, hs.le_iff.mp, isClosed_closure, le_iff, le_topologicalClosure, s.le_topologicalClosure, symm.imp
-/
theorem Submodule.isClosed_or_dense_of_isCoatom (s : Submodule R M) (hs : IsCoatom s) :
    IsClosed (s : Set M) ∨ Dense (s : Set M) := by
  refine (hs.le_iff.mp s.le_topologicalClosure).symm.imp ?_ dense_iff_topologicalClosure_eq_top.mpr
  exact fun h => h ▸ isClosed_closure

end closure

section CompleteSpace

instance {R M : Type*} [Semiring R] [AddCommMonoid M] [UniformSpace M] [Module R M]
    [CompleteSpace M] (K : Submodule R M) [c : IsClosed (K : Set M)] : CompleteSpace K :=
  IsComplete.completeSpace_coe (c.isComplete)

end CompleteSpace

namespace Submodule

variable {ι R : Type*} {M : ι -> Type*} [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
  [forall i, TopologicalSpace (M i)] [DecidableEq ι]

/--
theorem `closure_coe_iSup_map_single` / 定理 `closure_coe_iSup_map_single`

English:
theorem closure_coe_iSup_map_single
  given: (s : forall i, Submodule R (M i))
  proof: by
  rw [← closure_pi_set]
refine (closure_mono ?_).antisymm closure_minimal ?_ isClosed_closure
· exact SetLike.coe_mono iSup_map_single_le
  · simp only [Set.subset_def, mem_closure_iff]
    intro x hx U hU hxU
    rcases isOpen_pi_iff.mp hU x hxU with ⟨t, V, hV, hVU⟩
    refine ⟨∑ i in t, Pi.single i (x i), hVU ?_, ?_⟩
    · simp_all [Finset.sum_pi_single]
· exact sum_mem fun i hi => mem_iSup_of_mem i mem_map_of_mem hx _ Set.mem_univ _

中文:
定理 closure_coe_iSup_map_single
  条件: (s : 对任意 i, 子模 R (M i))
  证明: by
  rw [← closure_pi_set]
refine (closure_mono ?_).antisymm closure_minimal ?_ isClosed_closure
· exact SetLike.coe_mono iSup_map_single_le
  · simp only [Set.subset_def, mem_closure_iff]
    intro x hx U hU hxU
    rcases isOpen_pi_iff.mp hU x hxU with ⟨t, V, hV, hVU⟩
    refine ⟨∑ i in t, Pi.single i (x i), hVU ?_, ?_⟩
    · simp_all [Finset.sum_pi_single]
· exact sum_mem fun i hi => mem_iSup_of_mem i mem_map_of_mem hx _ Set.mem_univ _

Depends on / 依赖: Finset, Finset.sum_pi_single, Pi.single, Set.mem_univ, Set.subset_def, SetLike, SetLike.coe_mono, antisymm, closure_minimal, closure_mono, closure_pi_set, coe_mono, iSup_map_single_le, isClosed_closure, isOpen_pi_iff, isOpen_pi_iff.mp, mem_closure_iff, mem_iSup_of_mem, mem_map_of_mem, mem_univ
-/
theorem closure_coe_iSup_map_single (s : forall i, Submodule R (M i)) :
    closure (↑(⨆ i, (s i).map (LinearMap.single R M i)) : Set (forall i, M i)) =
      Set.univ.pi fun i => closure (s i) := by
  rw [← closure_pi_set]
refine (closure_mono ?_).antisymm closure_minimal ?_ isClosed_closure
· exact SetLike.coe_mono iSup_map_single_le
  · simp only [Set.subset_def, mem_closure_iff]
    intro x hx U hU hxU
    rcases isOpen_pi_iff.mp hU x hxU with ⟨t, V, hV, hVU⟩
    refine ⟨∑ i in t, Pi.single i (x i), hVU ?_, ?_⟩
    · simp_all [Finset.sum_pi_single]
· exact sum_mem fun i hi => mem_iSup_of_mem i mem_map_of_mem hx _ Set.mem_univ _

/--
theorem `topologicalClosure_iSup_map_single` / 定理 `topologicalClosure_iSup_map_single`

English:
theorem topologicalClosure_iSup_map_single
  statement: [forall i, ContinuousAdd (M i)]
  proof: SetLike.coe_injective closure_coe_iSup_map_single _

中文:
定理 topologicalClosure_iSup_map_single
  结论: [对任意 i, 连续加法 (M i)]
  证明: SetLike.coe_injective closure_coe_iSup_map_single _

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_coe_iSup_map_single, coe_injective
-/
theorem topologicalClosure_iSup_map_single [forall i, ContinuousAdd (M i)]
    [forall i, ContinuousConstSMul R (M i)] (s : forall i, Submodule R (M i)) :
    topologicalClosure (⨆ i, (s i).map (LinearMap.single R M i)) =
      pi Set.univ fun i => (s i).topologicalClosure :=
SetLike.coe_injective closure_coe_iSup_map_single _

end Submodule

section Pi

/--
theorem `LinearMap.continuous_on_pi` / 定理 `LinearMap.continuous_on_pi`

English:
theorem LinearMap.continuous_on_pi
  statement: {ι : Type*} {R : Type*} {M : Type*} [Finite ι] [Semiring R]
  proof: by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι -> R) -> M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    fun_prop

中文:
定理 线性映射.continuous_on_pi
  结论: {ι : 类型} {R : 类型} {M : 类型} [有限 ι] [半环 R]
  证明: by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι -> R) -> M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    fun_prop

Depends on / 依赖: classical, nonempty_fintype
-/
theorem LinearMap.continuous_on_pi {ι : Type*} {R : Type*} {M : Type*} [Finite ι] [Semiring R]
    [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (f : (ι -> R) ->ₗ[R] M) : Continuous f := by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι -> R) -> M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    fun_prop

end Pi

section PointwiseLimits

variable {M₁ M₂ α R S : Type*} [TopologicalSpace M₂] [T2Space M₂] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module S M₂] [ContinuousConstSMul S M₂]

variable [ContinuousAdd M₂] {σ : R ->+* S} {l : Filter α}

/-- Constructs a bundled linear map from a function and a proof that this function belongs to the
closure of the set of linear maps. -/
@[simps -fullyApplied]
/--
Definition of `linearMapOfMemClosureRangeCoe` / `linearMapOfMemClosureRangeCoe` 的定义

English:
definition linearMapOfMemClosureRangeCoe
  signature: (f : M₁ -> M₂)
  body: { addMonoidHomOfMemClosureRangeCoe f hf with
    map_smul' := (isClosed_setOfPred_map_smul M₁ M₂ σ).closure_subset_iff.2
      (Set.range_subset_iff.2 map_smulₛₗ) hf }

中文:
定义 linearMapOfMemClosureRangeCoe
  签名: (f : M₁ -> M₂)
  定义体: { addMonoidHomOfMemClosureRangeCoe f hf with
    map_smul' := (isClosed_setOfPred_map_smul M₁ M₂ σ).closure_subset_iff.2
      (Set.range_subset_iff.2 map_smulₛₗ) hf }

Depends on / 依赖: Set.range_subset_iff, addMonoidHomOfMemClosureRangeCoe, closure_subset_iff, isClosed_setOfPred_map_smul, map_smul, range_subset_iff
-/
def linearMapOfMemClosureRangeCoe (f : M₁ -> M₂)
    (hf : f in closure (Set.range ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂))) : M₁ ->ₛₗ[σ] M₂ :=
  { addMonoidHomOfMemClosureRangeCoe f hf with
    map_smul' := (isClosed_setOfPred_map_smul M₁ M₂ σ).closure_subset_iff.2
      (Set.range_subset_iff.2 map_smulₛₗ) hf }

/-- Construct a bundled linear map from a pointwise limit of linear maps -/
@[simps! -fullyApplied]
/--
Definition of `linearMapOfTendsto` / `linearMapOfTendsto` 的定义

English:
definition linearMapOfTendsto
  signature: (f : M₁ -> M₂) (g : α -> M₁ ->ₛₗ[σ] M₂) [l.NeBot]
  body: linearMapOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => Set.mem_range_self _

中文:
定义 linearMapOfTendsto
  签名: (f : M₁ -> M₂) (g : α -> M₁ ->ₛₗ[σ] M₂) [l.NeBot]
  定义体: linearMapOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => Set.mem_range_self _

Depends on / 依赖: Eventually, Eventually.of_forall, Set.mem_range_self, linearMapOfMemClosureRangeCoe, mem_closure_of_tendsto, mem_range_self, of_forall
-/
def linearMapOfTendsto (f : M₁ -> M₂) (g : α -> M₁ ->ₛₗ[σ] M₂) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ ->ₛₗ[σ] M₂ :=
linearMapOfMemClosureRangeCoe f
mem_closure_of_tendsto h Eventually.of_forall fun _ => Set.mem_range_self _

variable (M₁ M₂ σ)

/--
theorem `LinearMap.isClosed_range_coe` / 定理 `LinearMap.isClosed_range_coe`

English:
theorem LinearMap.isClosed_range_coe
  statement: IsClosed (Set.range ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂))
  proof: isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩

中文:
定理 线性映射.isClosed_range_coe
  结论: 是闭集 (集合.range ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂))
  证明: isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩

Depends on / 依赖: isClosed_of_closure_subset, linearMapOfMemClosureRangeCoe
-/
theorem LinearMap.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩

end PointwiseLimits

section Quotient

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (S : Submodule R M)

/--
Instance `_root_.QuotientModule.Quotient.topologicalSpace` / 实例 `_root_.QuotientModule.Quotient.topologicalSpace`

English:
instance _root_.QuotientModule.Quotient.topologicalSpace
  signature: : TopologicalSpace (M ⧸ S)
  body: inferInstanceAs (TopologicalSpace (Quotient S.quotientRel))

中文:
实例 _root_.QuotientModule.商.topologicalSpace
  签名: : 拓扑空间 (M ⧸ S)
  定义体: inferInstanceAs (TopologicalSpace (Quotient S.quotientRel))

Depends on / 依赖: Quotient, S.quotientRel, TopologicalSpace, quotientRel
-/
instance _root_.QuotientModule.Quotient.topologicalSpace : TopologicalSpace (M ⧸ S) :=
  inferInstanceAs (TopologicalSpace (Quotient S.quotientRel))

/--
theorem `isOpenMap_mkQ` / 定理 `isOpenMap_mkQ`

English:
theorem isOpenMap_mkQ
  given: [ContinuousAdd M]
  statement: IsOpenMap S.mkQ
  proof: QuotientAddGroup.isOpenMap_coe

中文:
定理 isOpenMap_mkQ
  条件: [连续加法 M]
  结论: 是开映射 S.mkQ
  证明: QuotientAddGroup.isOpenMap_coe

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.isOpenMap_coe, isOpenMap_coe
-/
theorem isOpenMap_mkQ [ContinuousAdd M] : IsOpenMap S.mkQ :=
  QuotientAddGroup.isOpenMap_coe

/--
theorem `isOpenQuotientMap_mkQ` / 定理 `isOpenQuotientMap_mkQ`

English:
theorem isOpenQuotientMap_mkQ
  given: [ContinuousAdd M]
  statement: IsOpenQuotientMap S.mkQ
  proof: QuotientAddGroup.isOpenQuotientMap_mk

中文:
定理 isOpenQuotientMap_mkQ
  条件: [连续加法 M]
  结论: 是OpenQuotient映射 S.mkQ
  证明: QuotientAddGroup.isOpenQuotientMap_mk

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.isOpenQuotientMap_mk, isOpenQuotientMap_mk
-/
theorem isOpenQuotientMap_mkQ [ContinuousAdd M] : IsOpenQuotientMap S.mkQ :=
  QuotientAddGroup.isOpenQuotientMap_mk

/--
theorem `isQuotientMap_mkQ` / 定理 `isQuotientMap_mkQ`

English:
theorem isQuotientMap_mkQ
  statement: IsQuotientMap S.mkQ
  proof: isQuotientMap_quot_mk

@[continuity, fun_prop]

中文:
定理 isQuotientMap_mkQ
  结论: 是商映射 S.mkQ
  证明: isQuotientMap_quot_mk

@[continuity, fun_prop]

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem isQuotientMap_mkQ : IsQuotientMap S.mkQ := isQuotientMap_quot_mk

@[continuity, fun_prop]
/--
theorem `continuous_mkQ` / 定理 `continuous_mkQ`

English:
theorem continuous_mkQ
  statement: Continuous S.mkQ
  proof: continuous_quot_mk

中文:
定理 continuous_mkQ
  结论: 连续 S.mkQ
  证明: continuous_quot_mk

Depends on / 依赖: continuous_quot_mk
-/
theorem continuous_mkQ : Continuous S.mkQ := continuous_quot_mk

/--
Instance `topologicalAddGroup_quotient` / 实例 `topologicalAddGroup_quotient`

English:
instance topologicalAddGroup_quotient
  signature: [IsTopologicalAddGroup M]
  body: inferInstanceAs IsTopologicalAddGroup (M ⧸ S.toAddSubgroup)

中文:
实例 topologicalAddGroup_quotient
  签名: [是拓扑加群 M]
  定义体: inferInstanceAs IsTopologicalAddGroup (M ⧸ S.toAddSubgroup)

Depends on / 依赖: IsTopologicalAddGroup, S.toAddSubgroup, toAddSubgroup
-/
instance topologicalAddGroup_quotient [IsTopologicalAddGroup M] : IsTopologicalAddGroup (M ⧸ S) :=
inferInstanceAs IsTopologicalAddGroup (M ⧸ S.toAddSubgroup)

/--
Instance `continuousSMul_quotient` / 实例 `continuousSMul_quotient`

English:
instance continuousSMul_quotient
  signature: [TopologicalSpace R] [IsTopologicalAddGroup M]
  body: by
    rw [← (IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact continuous_quot_mk.comp continuous_smul

中文:
实例 continuousSMul_quotient
  签名: [拓扑空间 R] [是拓扑加群 M]
  定义体: by
    rw [← (IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact continuous_quot_mk.comp continuous_smul

Depends on / 依赖: IsOpenQuotientMap, IsOpenQuotientMap.id.prodMap, S.isOpenQuotientMap_mkQ, continuous_comp_iff, continuous_quot_mk, continuous_quot_mk.comp, continuous_smul, isOpenQuotientMap_mkQ, prodMap
-/
instance continuousSMul_quotient [TopologicalSpace R] [IsTopologicalAddGroup M]
    [ContinuousSMul R M] : ContinuousSMul R (M ⧸ S) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact continuous_quot_mk.comp continuous_smul

/--
Instance `t3_quotient_of_isClosed` / 实例 `t3_quotient_of_isClosed`

English:
instance t3_quotient_of_isClosed
  signature: [IsTopologicalAddGroup M] [IsClosed (S : Set M)]
  body: letI : IsClosed (S.toAddSubgroup : Set M) := ‹_›
  QuotientAddGroup.instT3Space S.toAddSubgroup

中文:
实例 t3_quotient_of_isClosed
  签名: [是拓扑加群 M] [是闭集 (S : 集合 M)]
  定义体: letI : IsClosed (S.toAddSubgroup : Set M) := ‹_›
  QuotientAddGroup.instT3Space S.toAddSubgroup

Depends on / 依赖: IsClosed, QuotientAddGroup, QuotientAddGroup.instT3Space, S.toAddSubgroup, instT3Space, toAddSubgroup
-/
instance t3_quotient_of_isClosed [IsTopologicalAddGroup M] [IsClosed (S : Set M)] :
    T3Space (M ⧸ S) :=
  letI : IsClosed (S.toAddSubgroup : Set M) := ‹_›
  QuotientAddGroup.instT3Space S.toAddSubgroup

end Submodule

end Quotient
