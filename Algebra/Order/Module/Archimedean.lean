/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Module.Basic

/-!
# Archimedean classes for ordered module

## Main definitions
* `ArchimedeanClass.ball` are `ArchimedeanClass.ballAddSubgroup` as a submodules.
* `ArchimedeanClass.closedBall` are `ArchimedeanClass.closedBallAddSubgroup` as a submodules.
-/

@[expose] public section

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

namespace ArchimedeanClass

@[simp]
/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: (a : M) {k : K} (h : k != 0)
  statement: mk (k • a) = mk a
  proof: by
  have : Nontrivial K := nontrivial_iff.mpr ⟨k, 0, h⟩
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (show 0 < |k| by simpa using h)
  obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
  simp_rw [mk_eq_mk, abs_smul]
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← smul_assoc]
    exact le_smul_of_one_le_left (by simp) hm
  · have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this]
    exact smul_le_smul_of_nonneg_right hn (by simp)

中文:
定理 mk_smul
  条件: (a : M) {k : K} (h : k != 0)
  结论: mk (k • a) = mk a
  证明: by
  have : Nontrivial K := nontrivial_iff.mpr ⟨k, 0, h⟩
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (show 0 < |k| by simpa using h)
  obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
  simp_rw [mk_eq_mk, abs_smul]
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← smul_assoc]
    exact le_smul_of_one_le_left (by simp) hm
  · have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this]
    exact smul_le_smul_of_nonneg_right hn (by simp)

Depends on / 依赖: Archimedean, Archimedean.arch, Nontrivial, abs_smul, le_smul_of_one_le_left, mk_eq_mk, nontrivial_iff, nontrivial_iff.mpr, one_smul, simp_rw, smul_assoc, smul_le_smul_of_nonneg_right
-/
theorem mk_smul (a : M) {k : K} (h : k != 0) : mk (k • a) = mk a := by
  have : Nontrivial K := nontrivial_iff.mpr ⟨k, 0, h⟩
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (show 0 < |k| by simpa using h)
  obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
  simp_rw [mk_eq_mk, abs_smul]
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← smul_assoc]
    exact le_smul_of_one_le_left (by simp) hm
  · have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this]
    exact smul_le_smul_of_nonneg_right hn (by simp)

/--
theorem `mk_le_mk_smul` / 定理 `mk_le_mk_smul`

English:
theorem mk_le_mk_smul
  given: (a : M) (k : K)
  statement: mk a <= mk (k • a)
  proof: by
  obtain rfl | h := eq_or_ne k 0 <;> simp [*]

中文:
定理 mk_le_mk_smul
  条件: (a : M) (k : K)
  结论: mk a <= mk (k • a)
  证明: by
  obtain rfl | h := eq_or_ne k 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
theorem mk_le_mk_smul (a : M) (k : K) : mk a <= mk (k • a) := by
  obtain rfl | h := eq_or_ne k 0 <;> simp [*]

end ArchimedeanClass

namespace FiniteArchimedeanClass

variable (K)

/-- Given an upper set `s` of finite archimedean classes in a linearly ordered module `M` with
Archimedean scalars, all elements belonging to these classes together with 0 form a submodule.

This has the same carrier as `FiniteArchimedeanClass.addSubgroup`. -/
noncomputable
/--
Definition of `submodule` / `submodule` 的定义

English:
definition submodule
  signature: (s : UpperSet (FiniteArchimedeanClass M))
  body: addSubgroup s
smul_mem' k {a} ha ne := s.upper (ArchimedeanClass.mk_le_mk_smul ..)
ha fun eq => ne by simp [ArchimedeanClass.mk_eq_top_iff.mp eq]

中文:
定义 submodule
  签名: (s : 上集 (FiniteArchimedeanClass M))
  定义体: addSubgroup s
smul_mem' k {a} ha ne := s.upper (ArchimedeanClass.mk_le_mk_smul ..)
ha fun eq => ne by simp [ArchimedeanClass.mk_eq_top_iff.mp eq]

Depends on / 依赖: addSubgroup
-/
def submodule (s : UpperSet (FiniteArchimedeanClass M)) : Submodule K M where
  __ := addSubgroup s
smul_mem' k {a} ha ne := s.upper (ArchimedeanClass.mk_le_mk_smul ..)
ha fun eq => ne by simp [ArchimedeanClass.mk_eq_top_iff.mp eq]

/--
theorem `submodule_strictAnti` / 定理 `submodule_strictAnti`

English:
theorem submodule_strictAnti
  statement: StrictAnti (submodule K (M := M))
  proof: addSubgroup_strictAnti

中文:
定理 submodule_strictAnti
  结论: 严格递减 (submodule K (M := M))
  证明: addSubgroup_strictAnti

Depends on / 依赖: addSubgroup_strictAnti
-/
theorem submodule_strictAnti : StrictAnti (submodule K (M := M)) := addSubgroup_strictAnti

/-- An open ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.ballAddSubgroup`'s. -/
noncomputable
/--
Definition of `ball` / `ball` 的定义

English:
abbreviation ball
  signature: (c : FiniteArchimedeanClass M)
  body: submodule K (UpperSet.Ioi c)

中文:
缩写 ball
  签名: (c : FiniteArchimedeanClass M)
  定义体: submodule K (UpperSet.Ioi c)

Depends on / 依赖: UpperSet, UpperSet.Ioi, submodule
-/
abbrev ball (c : FiniteArchimedeanClass M) := submodule K (UpperSet.Ioi c)

/-- A closed ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ici c`.

This has the same carrier as `ArchimedeanClass.closedBallAddSubgroup`'s. -/
noncomputable
/--
Definition of `closedBall` / `closedBall` 的定义

English:
abbreviation closedBall
  signature: (c : FiniteArchimedeanClass M)
  body: submodule K (UpperSet.Ici c)

@[simp]

中文:
缩写 closedBall
  签名: (c : FiniteArchimedeanClass M)
  定义体: submodule K (UpperSet.Ici c)

@[simp]

Depends on / 依赖: UpperSet, UpperSet.Ici, submodule
-/
abbrev closedBall (c : FiniteArchimedeanClass M) := submodule K (UpperSet.Ici c)

@[simp]
/--
theorem `toAddSubgroup_ball` / 定理 `toAddSubgroup_ball`

English:
theorem toAddSubgroup_ball
  given: (c : FiniteArchimedeanClass M)
  proof: rfl

@[simp]

中文:
定理 toAddSubgroup_ball
  条件: (c : FiniteArchimedeanClass M)
  证明: rfl

@[simp]
-/
theorem toAddSubgroup_ball (c : FiniteArchimedeanClass M) :
    (ball K c).toAddSubgroup = ballAddSubgroup c := rfl

@[simp]
/--
theorem `toAddSubgroup_closedBall` / 定理 `toAddSubgroup_closedBall`

English:
theorem toAddSubgroup_closedBall
  given: (c : FiniteArchimedeanClass M)
  proof: rfl

@[simp]

中文:
定理 toAddSubgroup_closedBall
  条件: (c : FiniteArchimedeanClass M)
  证明: rfl

@[simp]
-/
theorem toAddSubgroup_closedBall (c : FiniteArchimedeanClass M) :
    (closedBall K c).toAddSubgroup = closedBallAddSubgroup c := rfl

@[simp]
/--
theorem `mem_ball_iff` / 定理 `mem_ball_iff`

English:
theorem mem_ball_iff
  given: {a : M} {c : FiniteArchimedeanClass M}
  proof: mem_ballAddSubgroup_iff

@[simp]

中文:
定理 mem_ball_iff
  条件: {a : M} {c : FiniteArchimedeanClass M}
  证明: mem_ballAddSubgroup_iff

@[simp]

Depends on / 依赖: mem_ballAddSubgroup_iff
-/
theorem mem_ball_iff {a : M} {c : FiniteArchimedeanClass M} :
    a in ball K c ↔ forall h : a != 0, c < mk a h :=
  mem_ballAddSubgroup_iff

@[simp]
/--
theorem `mem_closedBall_iff` / 定理 `mem_closedBall_iff`

English:
theorem mem_closedBall_iff
  given: {a : M} {c : FiniteArchimedeanClass M}
  proof: mem_closedBallAddSubgroup_iff

中文:
定理 mem_closedBall_iff
  条件: {a : M} {c : FiniteArchimedeanClass M}
  证明: mem_closedBallAddSubgroup_iff

Depends on / 依赖: mem_closedBallAddSubgroup_iff
-/
theorem mem_closedBall_iff {a : M} {c : FiniteArchimedeanClass M} :
    a in closedBall K c ↔ forall h : a != 0, c <= mk a h :=
  mem_closedBallAddSubgroup_iff

/--
theorem `ball_strictAnti` / 定理 `ball_strictAnti`

English:
theorem ball_strictAnti
  statement: StrictAnti (ball (M := M) K)
  proof: ballAddSubgroup_strictAnti

中文:
定理 ball_strictAnti
  结论: 严格递减 (ball (M := M) K)
  证明: ballAddSubgroup_strictAnti

Depends on / 依赖: ballAddSubgroup_strictAnti
-/
theorem ball_strictAnti : StrictAnti (ball (M := M) K) := ballAddSubgroup_strictAnti

/--
theorem `ball_lt_closedBall` / 定理 `ball_lt_closedBall`

English:
theorem ball_lt_closedBall
  given: {c : FiniteArchimedeanClass M}
  statement: ball K c < closedBall K c
  proof: submodule_strictAnti _ Set.Ioi_ssubset_Ici_self

中文:
定理 ball_lt_closedBall
  条件: {c : FiniteArchimedeanClass M}
  结论: ball K c < closedBall K c
  证明: submodule_strictAnti _ Set.Ioi_ssubset_Ici_self

Depends on / 依赖: Ioi_ssubset_Ici_self, Set.Ioi_ssubset_Ici_self, submodule_strictAnti
-/
theorem ball_lt_closedBall {c : FiniteArchimedeanClass M} : ball K c < closedBall K c :=
  submodule_strictAnti _ Set.Ioi_ssubset_Ici_self

end FiniteArchimedeanClass
