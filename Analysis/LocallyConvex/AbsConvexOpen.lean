/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Convex.Gauge

/-!
# Absolutely convex open sets

A set `s` in a commutative monoid `E` equipped with a topology is said to be an absolutely convex
open set if it is absolutely convex and open. When `E` is a topological additive group, the topology
coincides with the topology induced by the family of seminorms arising as gauges of absolutely
convex open neighborhoods of zero.

## Main definitions

* `AbsConvexOpenSets`: sets which are absolutely convex and open
* `gaugeSeminormFamily`: the seminorm family induced by all open absolutely convex neighborhoods
  of zero.

## Main statements

* `with_gaugeSeminormFamily`: the topology of a locally convex space is induced by the family
  `gaugeSeminormFamily`.
* `LocallyConvexSpace.toPolynormableSpace`: a locally convex space is polynormable

-/

@[expose] public section

open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E : Type*}

section AbsolutelyConvexSets

variable [TopologicalSpace E] [AddCommMonoid E] [SeminormedRing 𝕜]
variable [SMul 𝕜 E]
variable (𝕜 E) [PartialOrder 𝕜]

/--
Definition of `AbsConvexOpenSets` / `AbsConvexOpenSets` 的定义

English:
definition AbsConvexOpenSets
  body: { s : Set E // (0 : E) in s ∧ IsOpen s ∧ AbsConvex 𝕜 s }

中文:
定义 AbsConvexOpenSets
  定义体: { s : Set E // (0 : E) in s ∧ IsOpen s ∧ AbsConvex 𝕜 s }

Depends on / 依赖: AbsConvex, IsOpen
-/
def AbsConvexOpenSets :=
  { s : Set E // (0 : E) in s ∧ IsOpen s ∧ AbsConvex 𝕜 s }

/--
Instance `AbsConvexOpenSets.instCoeOut` / 实例 `AbsConvexOpenSets.instCoeOut`

English:
instance AbsConvexOpenSets.instCoeOut
  signature: : CoeOut (AbsConvexOpenSets 𝕜 E) (Set E)
  body: ⟨Subtype.val⟩

中文:
实例 AbsConvexOpenSets.instCoeOut
  签名: : CoeOut (AbsConvexOpenSets 𝕜 E) (集合 E)
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
noncomputable instance AbsConvexOpenSets.instCoeOut : CoeOut (AbsConvexOpenSets 𝕜 E) (Set E) :=
  ⟨Subtype.val⟩

namespace AbsConvexOpenSets

variable {𝕜 E}

/--
theorem `coe_zero_mem` / 定理 `coe_zero_mem`

English:
theorem coe_zero_mem
  given: (s : AbsConvexOpenSets 𝕜 E)
  statement: (0 : E) in (s : Set E)
  proof: s.2.1

中文:
定理 coe_zero_mem
  条件: (s : AbsConvexOpenSets 𝕜 E)
  结论: (0 : E) in (s : 集合 E)
  证明: s.2.1
-/
theorem coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) in (s : Set E) :=
  s.2.1

/--
theorem `coe_isOpen` / 定理 `coe_isOpen`

English:
theorem coe_isOpen
  given: (s : AbsConvexOpenSets 𝕜 E)
  statement: IsOpen (s : Set E)
  proof: s.2.2.1

中文:
定理 coe_isOpen
  条件: (s : AbsConvexOpenSets 𝕜 E)
  结论: 是开集 (s : 集合 E)
  证明: s.2.2.1
-/
theorem coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E) :=
  s.2.2.1

/--
theorem `coe_nhds` / 定理 `coe_nhds`

English:
theorem coe_nhds
  given: (s : AbsConvexOpenSets 𝕜 E)
  statement: (s : Set E) in 𝓝 (0 : E)
  proof: s.coe_isOpen.mem_nhds s.coe_zero_mem

中文:
定理 coe_nhds
  条件: (s : AbsConvexOpenSets 𝕜 E)
  结论: (s : 集合 E) in 𝓝 (0 : E)
  证明: s.coe_isOpen.mem_nhds s.coe_zero_mem

Depends on / 依赖: coe_isOpen, coe_zero_mem, mem_nhds, s.coe_isOpen.mem_nhds, s.coe_zero_mem
-/
theorem coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) in 𝓝 (0 : E) :=
  s.coe_isOpen.mem_nhds s.coe_zero_mem

/--
theorem `coe_balanced` / 定理 `coe_balanced`

English:
theorem coe_balanced
  given: (s : AbsConvexOpenSets 𝕜 E)
  statement: Balanced 𝕜 (s : Set E)
  proof: s.2.2.2.1

中文:
定理 coe_balanced
  条件: (s : AbsConvexOpenSets 𝕜 E)
  结论: Balanced 𝕜 (s : 集合 E)
  证明: s.2.2.2.1
-/
theorem coe_balanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E) :=
  s.2.2.2.1

/--
theorem `coe_convex` / 定理 `coe_convex`

English:
theorem coe_convex
  given: (s : AbsConvexOpenSets 𝕜 E)
  statement: Convex 𝕜 (s : Set E)
  proof: s.2.2.2.2

中文:
定理 coe_convex
  条件: (s : AbsConvexOpenSets 𝕜 E)
  结论: 凸 𝕜 (s : 集合 E)
  证明: s.2.2.2.2
-/
theorem coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex 𝕜 (s : Set E) :=
  s.2.2.2.2

end AbsConvexOpenSets

/--
Instance `AbsConvexOpenSets.instNonempty` / 实例 `AbsConvexOpenSets.instNonempty`

English:
instance AbsConvexOpenSets.instNonempty
  signature: : Nonempty (AbsConvexOpenSets 𝕜 E)
  body: by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

中文:
实例 AbsConvexOpenSets.instNonempty
  签名: : 非空 (AbsConvexOpenSets 𝕜 E)
  定义体: by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

Depends on / 依赖: AbsConvexOpenSets, Set.univ, Subtype, Subtype.exists, balanced_univ, convex_univ, exists_true_iff_nonempty, isOpen_univ, mem_univ
-/
instance AbsConvexOpenSets.instNonempty : Nonempty (AbsConvexOpenSets 𝕜 E) := by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

end AbsolutelyConvexSets

variable [RCLike 𝕜]
variable [AddCommGroup E] [TopologicalSpace E]
variable [Module 𝕜 E] [Module Real E] [IsScalarTower Real 𝕜 E]
variable [ContinuousSMul Real E]
variable (𝕜 E)

open scoped ComplexOrder

/--
Definition of `gaugeSeminormFamily` / `gaugeSeminormFamily` 的定义

English:
definition gaugeSeminormFamily
  signature: : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E)
  body: fun s =>
  gaugeSeminorm s.coe_balanced (s.coe_convex.lift Real) (absorbent_nhds_zero s.coe_nhds)

中文:
定义 gaugeSeminormFamily
  签名: : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E)
  定义体: fun s =>
  gaugeSeminorm s.coe_balanced (s.coe_convex.lift Real) (absorbent_nhds_zero s.coe_nhds)
-/
noncomputable def gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E) := fun s =>
  gaugeSeminorm s.coe_balanced (s.coe_convex.lift Real) (absorbent_nhds_zero s.coe_nhds)

variable {𝕜 E}

/--
theorem `gaugeSeminormFamily_ball` / 定理 `gaugeSeminormFamily_ball`

English:
theorem gaugeSeminormFamily_ball
  given: (s : AbsConvexOpenSets 𝕜 E)
  proof: by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_toFun]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen (s.coe_convex.lift Real) s.coe_zero_mem s.coe_isOpen

中文:
定理 gaugeSeminormFamily_ball
  条件: (s : AbsConvexOpenSets 𝕜 E)
  证明: by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_toFun]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen (s.coe_convex.lift Real) s.coe_zero_mem s.coe_isOpen

Depends on / 依赖: Seminorm, Seminorm.ball_zero_eq, ball_zero_eq, coe_convex, coe_isOpen, coe_zero_mem, gaugeSeminormFamily, gaugeSeminorm_toFun, s.coe_convex.lift, s.coe_isOpen, s.coe_zero_mem, setOfPred_gauge_lt_one_eq_self_of_isOpen, simp_rw
-/
theorem gaugeSeminormFamily_ball (s : AbsConvexOpenSets 𝕜 E) :
    (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E) := by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_toFun]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen (s.coe_convex.lift Real) s.coe_zero_mem s.coe_isOpen

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace 𝕜 E]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `with_gaugeSeminormFamily` / 定理 `with_gaugeSeminormFamily`

English:
theorem with_gaugeSeminormFamily
  statement: WithSeminorms (gaugeSeminormFamily 𝕜 E)
  proof: by
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (nhds_hasBasis_absConvex_open 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs => ?_
  · refine ⟨s, ⟨?_, rfl.subset⟩⟩
    convert! (gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball]; rw [Subtype.coe_mk]
  refine ⟨s, ⟨?_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine
    ⟨mem_iInter₂.mpr fun _ _ => by simp [hr],
      isOpen_biInter_finset fun S _ => ?_,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => (convex_of_nonneg_surjective_algebraMap _
        (fun _ => RCLike.nonneg_iff_exists_ofReal.mp) (Seminorm.convex_ball _ _ _) ..)⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) != 0 := by simp [hr.ne']
  rw [hr']; rw [← Seminorm.smul_ball_zero hr'']; rw [gaugeSeminormFamily_ball]
  exact S.coe_isOpen.smul₀ hr''

中文:
定理 with_gaugeSeminormFamily
  结论: WithSeminorms (gaugeSeminormFamily 𝕜 E)
  证明: by
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (nhds_hasBasis_absConvex_open 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs => ?_
  · refine ⟨s, ⟨?_, rfl.subset⟩⟩
    convert! (gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball]; rw [Subtype.coe_mk]
  refine ⟨s, ⟨?_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine
    ⟨mem_iInter₂.mpr fun _ _ => by simp [hr],
      isOpen_biInter_finset fun S _ => ?_,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => (convex_of_nonneg_surjective_algebraMap _
        (fun _ => RCLike.nonneg_iff_exists_ofReal.mp) (Seminorm.convex_ball _ _ _) ..)⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) != 0 := by simp [hr.ne']
  rw [hr']; rw [← Seminorm.smul_ball_zero hr'']; rw [gaugeSeminormFamily_ball]
  exact S.coe_isOpen.smul₀ hr''

Depends on / 依赖: Seminorm, Seminorm.ball_finset_sup_eq_iInter, SeminormFamily, SeminormFamily.basisSets_iff, SeminormFamily.withSeminorms_of_hasBasis, Subtype, Subtype.coe_mk, ball_finset_sup_eq_iInter, basisSets_iff, basisSets_singleton_mem, coe_mk, convert, gaugeSeminormFamily, gaugeSeminormFamily_ball, nhds_hasBasis_absConvex_open, one_pos, rfl.subset, subset, to_hasBasis, withSeminorms_of_hasBasis
-/
theorem with_gaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E) := by
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (nhds_hasBasis_absConvex_open 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs => ?_
  · refine ⟨s, ⟨?_, rfl.subset⟩⟩
    convert! (gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball]; rw [Subtype.coe_mk]
  refine ⟨s, ⟨?_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine
    ⟨mem_iInter₂.mpr fun _ _ => by simp [hr],
      isOpen_biInter_finset fun S _ => ?_,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => (convex_of_nonneg_surjective_algebraMap _
        (fun _ => RCLike.nonneg_iff_exists_ofReal.mp) (Seminorm.convex_ball _ _ _) ..)⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) != 0 := by simp [hr.ne']
  rw [hr']; rw [← Seminorm.smul_ball_zero hr'']; rw [gaugeSeminormFamily_ball]
  exact S.coe_isOpen.smul₀ hr''

/--
Instance `LocallyConvexSpace.toPolynormableSpace` / 实例 `LocallyConvexSpace.toPolynormableSpace`

English:
instance LocallyConvexSpace.toPolynormableSpace
  signature: : PolynormableSpace 𝕜 E
  body: with_gaugeSeminormFamily.toPolynormableSpace

中文:
实例 LocallyConvex空间.toPolynormableSpace
  签名: : Polynormable空间 𝕜 E
  定义体: with_gaugeSeminormFamily.toPolynormableSpace

Depends on / 依赖: toPolynormableSpace, with_gaugeSeminormFamily, with_gaugeSeminormFamily.toPolynormableSpace
-/
instance LocallyConvexSpace.toPolynormableSpace : PolynormableSpace 𝕜 E :=
  with_gaugeSeminormFamily.toPolynormableSpace
