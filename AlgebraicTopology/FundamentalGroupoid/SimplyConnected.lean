/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit

/-!
# Simply connected spaces

This file defines simply connected spaces.
A topological space is simply connected if its fundamental groupoid is equivalent to `Unit`.

We also define the corresponding predicate for sets.

## Main theorems
  - `simply_connected_iff_unique_homotopic` - A space is simply connected if and only if it is
    nonempty and there is a unique path up to homotopy between any two points

  - `SimplyConnectedSpace.ofContractible` - A contractible space is simply connected
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A simply connected space is one whose fundamental groupoid is equivalent to `Discrete Unit` -/
@[mk_iff]
/--
Definition of `SimplyConnectedSpace` / `SimplyConnectedSpace` 的定义

English:
class SimplyConnectedSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)

中文:
类 单连通空间
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (1 个):
    - equiv_unit : 非空 (FundamentalGroupoid X ≌ 离散 单元)
-/
class SimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)

@[deprecated (since := "2026-01-08")]
alias simply_connected_def := simplyConnectedSpace_iff

/--
theorem `simply_connected_iff_unique_homotopic` / 定理 `simply_connected_iff_unique_homotopic`

English:
theorem simply_connected_iff_unique_homotopic
  given: (X : Type*) [TopologicalSpace X]
  proof: by
  simp only [simplyConnectedSpace_iff, equiv_punit_iff_unique,
    FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
  intros
  exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩

中文:
定理 simply_connected_iff_unique_homotopic
  条件: (X : 类型) [拓扑空间 X]
  证明: by
  simp only [simplyConnectedSpace_iff, equiv_punit_iff_unique,
    FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
  intros
  exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.nonempty_iff, Nonempty, Nonempty.forall, and_congr_right_iff, equiv_punit_iff_unique, intros, nonempty_iff, simplyConnectedSpace_iff
-/
theorem simply_connected_iff_unique_homotopic (X : Type*) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔
      Nonempty X ∧ forall x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y)) := by
  simp only [simplyConnectedSpace_iff, equiv_punit_iff_unique,
    FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
  intros
  exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩

/--
theorem `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` / 定理 `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`

English:
theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace
  statement: [hY : SimplyConnectedSpace Y]
  proof: ⟨hY.1.map (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).trans⟩

中文:
定理 连续映射.同伦等价.simplyConnectedSpace
  结论: [hY : 单连通空间 Y]
  证明: ⟨hY.1.map (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).trans⟩

Depends on / 依赖: FundamentalGroupoidFunctor, FundamentalGroupoidFunctor.equivOfHomotopyEquiv, equivOfHomotopyEquiv
-/
theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace [hY : SimplyConnectedSpace Y]
    (e : X ≃ₕ Y) : SimplyConnectedSpace X :=
  ⟨hY.1.map (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).trans⟩

/--
theorem `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff` / 定理 `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff`

English:
theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff
  given: (e : X ≃ₕ Y)
  proof: ⟨fun _ => e.symm.simplyConnectedSpace, fun _ => e.simplyConnectedSpace⟩

中文:
定理 连续映射.同伦等价.simplyConnectedSpace_iff
  条件: (e : X ≃ₕ Y)
  证明: ⟨fun _ => e.symm.simplyConnectedSpace, fun _ => e.simplyConnectedSpace⟩

Depends on / 依赖: e.simplyConnectedSpace, e.symm.simplyConnectedSpace, simplyConnectedSpace
-/
theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff (e : X ≃ₕ Y) :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace Y :=
  ⟨fun _ => e.symm.simplyConnectedSpace, fun _ => e.simplyConnectedSpace⟩

namespace SimplyConnectedSpace

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

instance (x y : X) : Subsingleton (Path.Homotopic.Quotient x y) :=
  @Unique.instSubsingleton _ (Nonempty.some (by
    rw [simply_connected_iff_unique_homotopic] at *; tauto))

instance (x : X) : Subsingleton (FundamentalGroup X x) :=
inferInstanceAs Subsingleton (Path.Homotopic.Quotient x x)

instance (priority := 100) : PathConnectedSpace X :=
  let unique_homotopic := (simply_connected_iff_unique_homotopic X).mp inferInstance
  { nonempty := unique_homotopic.1
    joined := fun x y => ⟨(unique_homotopic.2 x y).some.default.out⟩ }

/--
theorem `paths_homotopic` / 定理 `paths_homotopic`

English:
theorem paths_homotopic
  given: {x y : X} (p₁ p₂ : Path x y)
  statement: Path.Homotopic p₁ p₂
  proof: Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x y) _ _ _)

中文:
定理 paths_homotopic
  条件: {x y : X} (p₁ p₂ : 道路 x y)
  结论: 道路.同伦 p₁ p₂
  证明: Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x y) _ _ _)

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient, Quotient, Quotient.eq.mp, Subsingleton, Subsingleton.elim
-/
theorem paths_homotopic {x y : X} (p₁ p₂ : Path x y) : Path.Homotopic p₁ p₂ :=
  Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x y) _ _ _)

instance (priority := 100) ofContractible (Y : Type*) [TopologicalSpace Y] [ContractibleSpace Y] :
    SimplyConnectedSpace Y :=
  haveI : SimplyConnectedSpace Unit := ⟨⟨FundamentalGroupoid.punitEquivDiscretePUnit⟩⟩
  (ContractibleSpace.hequiv Y Unit).some.simplyConnectedSpace

end SimplyConnectedSpace

/--
theorem `simply_connected_iff_paths_homotopic` / 定理 `simply_connected_iff_paths_homotopic`

English:
theorem simply_connected_iff_paths_homotopic
  proof: ⟨by intro; constructor <;> infer_instance, fun h => by
    cases h; rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩

中文:
定理 simply_connected_iff_paths_homotopic
  证明: ⟨by intro; constructor <;> infer_instance, fun h => by
    cases h; rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩

Depends on / 依赖: PathConnectedSpace, PathConnectedSpace.somePath, infer_instance, simply_connected_iff_unique_homotopic, somePath, uniqueOfSubsingleton
-/
theorem simply_connected_iff_paths_homotopic :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ forall x y : Y, Subsingleton (Path.Homotopic.Quotient x y) :=
  ⟨by intro; constructor <;> infer_instance, fun h => by
    cases h; rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩

/--
theorem `simply_connected_iff_paths_homotopic'` / 定理 `simply_connected_iff_paths_homotopic'`

English:
theorem simply_connected_iff_paths_homotopic'
  proof: by
  convert! simply_connected_iff_paths_homotopic (Y := Y)
  simp [Path.Homotopic.Quotient, Setoid.eq_top_iff]; rfl

中文:
定理 simply_connected_iff_paths_homotopic'
  证明: by
  convert! simply_connected_iff_paths_homotopic (Y := Y)
  simp [Path.Homotopic.Quotient, Setoid.eq_top_iff]; rfl

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient, Quotient, Setoid, Setoid.eq_top_iff, convert, eq_top_iff, simply_connected_iff_paths_homotopic
-/
theorem simply_connected_iff_paths_homotopic' :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ forall {x y : Y} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ := by
  convert! simply_connected_iff_paths_homotopic (Y := Y)
  simp [Path.Homotopic.Quotient, Setoid.eq_top_iff]; rfl

set_option backward.isDefEq.respectTransparency false in
open Path.Homotopic.Quotient in
/--
theorem `simply_connected_iff_loops_nullhomotopic` / 定理 `simply_connected_iff_loops_nullhomotopic`

English:
theorem simply_connected_iff_loops_nullhomotopic
  proof: by
  rw [simply_connected_iff_paths_homotopic']
  constructor
  · -- Forward: all paths homotopic implies all loops null-homotopic
    intro ⟨hpc, hall⟩
    exact ⟨hpc, fun x γ => hall γ (Path.refl x)⟩
  · -- Backward: all loops null-homotopic implies all paths homotopic
    intro ⟨hpc, hloops⟩
    refine ⟨hpc, fun {x y} p₁ p₂ => ?_⟩
    -- Work in the quotient where structural steps can be done by simp
    rw [← eq]
    replace hloops : forall (x : Y) (γ : Path x x),
        (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      fun x γ => Quotient.sound (hloops x γ)
    have h : trans ⟦p₁⟧ (symm ⟦p₂⟧) = refl x := by
      simpa using hloops x (p₁.trans p₂.symm)
    calc ⟦p₁⟧
      _ = trans (trans ⟦p₁⟧ (symm ⟦p₂⟧)) ⟦p₂⟧ := by simp
      _ = ⟦p₂⟧ := by grind

中文:
定理 simply_connected_iff_loops_nullhomotopic
  证明: by
  rw [simply_connected_iff_paths_homotopic']
  constructor
  · -- Forward: all paths homotopic implies all loops null-homotopic
    intro ⟨hpc, hall⟩
    exact ⟨hpc, fun x γ => hall γ (Path.refl x)⟩
  · -- Backward: all loops null-homotopic implies all paths homotopic
    intro ⟨hpc, hloops⟩
    refine ⟨hpc, fun {x y} p₁ p₂ => ?_⟩
    -- Work in the quotient where structural steps can be done by simp
    rw [← eq]
    replace hloops : forall (x : Y) (γ : Path x x),
        (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      fun x γ => Quotient.sound (hloops x γ)
    have h : trans ⟦p₁⟧ (symm ⟦p₂⟧) = refl x := by
      simpa using hloops x (p₁.trans p₂.symm)
    calc ⟦p₁⟧
      _ = trans (trans ⟦p₁⟧ (symm ⟦p₂⟧)) ⟦p₂⟧ := by simp
      _ = ⟦p₂⟧ := by grind

Depends on / 依赖: Backward, Forward, Path.refl, hloops, homotopic, simply_connected_iff_paths_homotopic
-/
theorem simply_connected_iff_loops_nullhomotopic :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ forall (x : Y) (γ : Path x x), Path.Homotopic γ (Path.refl x) := by
  rw [simply_connected_iff_paths_homotopic']
  constructor
  · -- Forward: all paths homotopic implies all loops null-homotopic
    intro ⟨hpc, hall⟩
    exact ⟨hpc, fun x γ => hall γ (Path.refl x)⟩
  · -- Backward: all loops null-homotopic implies all paths homotopic
    intro ⟨hpc, hloops⟩
    refine ⟨hpc, fun {x y} p₁ p₂ => ?_⟩
    -- Work in the quotient where structural steps can be done by simp
    rw [← eq]
    replace hloops : forall (x : Y) (γ : Path x x),
        (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      fun x γ => Quotient.sound (hloops x γ)
    have h : trans ⟦p₁⟧ (symm ⟦p₂⟧) = refl x := by
      simpa using hloops x (p₁.trans p₂.symm)
    calc ⟦p₁⟧
      _ = trans (trans ⟦p₁⟧ (symm ⟦p₂⟧)) ⟦p₂⟧ := by simp
      _ = ⟦p₂⟧ := by grind

/-!
### Simply connected sets
-/

/--
Definition of `IsSimplyConnected` / `IsSimplyConnected` 的定义

English:
definition IsSimplyConnected
  signature: (s : Set X)
  body: SimplyConnectedSpace s

中文:
定义 IsSimplyConnected
  签名: (s : 集合 X)
  定义体: SimplyConnectedSpace s

Depends on / 依赖: SimplyConnectedSpace
-/
def IsSimplyConnected (s : Set X) : Prop := SimplyConnectedSpace s

/--
theorem `IsSimplyConnected.simplyConnectedSpace` / 定理 `IsSimplyConnected.simplyConnectedSpace`

English:
theorem IsSimplyConnected.simplyConnectedSpace
  given: {s : Set X} (hs : IsSimplyConnected s)
  proof: hs

中文:
定理 IsSimplyConnected.simplyConnectedSpace
  条件: {s : 集合 X} (hs : IsSimplyConnected s)
  证明: hs
-/
theorem IsSimplyConnected.simplyConnectedSpace {s : Set X} (hs : IsSimplyConnected s) :
    SimplyConnectedSpace s := hs

/--
theorem `IsSimplyConnected.isPathConnected` / 定理 `IsSimplyConnected.isPathConnected`

English:
theorem IsSimplyConnected.isPathConnected
  given: {s : Set X} (hs : IsSimplyConnected s)
  proof: have := hs.simplyConnectedSpace
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance

中文:
定理 IsSimplyConnected.isPathConnected
  条件: {s : 集合 X} (hs : IsSimplyConnected s)
  证明: have := hs.simplyConnectedSpace
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance

Depends on / 依赖: hs.simplyConnectedSpace, isPathConnected_iff_pathConnectedSpace, isPathConnected_iff_pathConnectedSpace.mpr, simplyConnectedSpace
-/
theorem IsSimplyConnected.isPathConnected {s : Set X} (hs : IsSimplyConnected s) :
    IsPathConnected s :=
  have := hs.simplyConnectedSpace
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/--
theorem `IsSimplyConnected.nonempty` / 定理 `IsSimplyConnected.nonempty`

English:
theorem IsSimplyConnected.nonempty
  given: {s : Set X} (hs : IsSimplyConnected s)
  statement: s.Nonempty
  proof: hs.isPathConnected.nonempty

中文:
定理 IsSimplyConnected.nonempty
  条件: {s : 集合 X} (hs : IsSimplyConnected s)
  结论: s.非空
  证明: hs.isPathConnected.nonempty

Depends on / 依赖: hs.isPathConnected.nonempty, isPathConnected, nonempty
-/
theorem IsSimplyConnected.nonempty {s : Set X} (hs : IsSimplyConnected s) : s.Nonempty :=
  hs.isPathConnected.nonempty

/--
theorem `Topology.IsEmbedding.isSimplyConnected_image` / 定理 `Topology.IsEmbedding.isSimplyConnected_image`

English:
theorem Topology.IsEmbedding.isSimplyConnected_image
  statement: {f : X -> Y} (hf : Topology.IsEmbedding f)
  proof: .symm .simplyConnectedSpace_iff .toHomotopyEquiv hf.homeomorphImage s

@[simp]

中文:
定理 拓扑.是嵌入.isSimplyConnected_image
  结论: {f : X -> Y} (hf : 拓扑.是嵌入 f)
  证明: .symm .simplyConnectedSpace_iff .toHomotopyEquiv hf.homeomorphImage s

@[simp]

Depends on / 依赖: hf.homeomorphImage, homeomorphImage, simplyConnectedSpace_iff, toHomotopyEquiv
-/
theorem Topology.IsEmbedding.isSimplyConnected_image {f : X -> Y} (hf : Topology.IsEmbedding f)
    {s : Set X} :
    IsSimplyConnected (f '' s) ↔ IsSimplyConnected s :=
.symm .simplyConnectedSpace_iff .toHomotopyEquiv hf.homeomorphImage s

@[simp]
/--
theorem `Homeomorph.isSimplyConnected_image` / 定理 `Homeomorph.isSimplyConnected_image`

English:
theorem Homeomorph.isSimplyConnected_image
  given: (f : X ≃ₜ Y) {s : Set X}
  proof: f.isEmbedding.isSimplyConnected_image

@[simp]

中文:
定理 同胚.isSimplyConnected_image
  条件: (f : X ≃ₜ Y) {s : 集合 X}
  证明: f.isEmbedding.isSimplyConnected_image

@[simp]

Depends on / 依赖: f.isEmbedding.isSimplyConnected_image, isEmbedding, isSimplyConnected_image
-/
theorem Homeomorph.isSimplyConnected_image (f : X ≃ₜ Y) {s : Set X} :
    IsSimplyConnected (f '' s) ↔ IsSimplyConnected s :=
  f.isEmbedding.isSimplyConnected_image

@[simp]
/--
theorem `Homeomorph.isSimplyConnected_preimage` / 定理 `Homeomorph.isSimplyConnected_preimage`

English:
theorem Homeomorph.isSimplyConnected_preimage
  given: (f : X ≃ₜ Y) {s : Set Y}
  proof: by
  rw [← image_symm]; rw [isSimplyConnected_image]

中文:
定理 同胚.isSimplyConnected_preimage
  条件: (f : X ≃ₜ Y) {s : 集合 Y}
  证明: by
  rw [← image_symm]; rw [isSimplyConnected_image]

Depends on / 依赖: image_symm, isSimplyConnected_image
-/
theorem Homeomorph.isSimplyConnected_preimage (f : X ≃ₜ Y) {s : Set Y} :
    IsSimplyConnected (f ⁻¹' s) ↔ IsSimplyConnected s := by
  rw [← image_symm]; rw [isSimplyConnected_image]

/--
theorem `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` / 定理 `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`

English:
theorem isSimplyConnected_iff_exists_homotopy_refl_forall_mem
  given: {s : Set X}
  proof: by
  rw [IsSimplyConnected]; rw [simply_connected_iff_loops_nullhomotopic]; rw [← isPathConnected_iff_pathConnectedSpace]
  refine .and .rfl ⟨fun h x p hp => ?_, fun h x p => ?_⟩
  · lift x to s using by simpa using hp 0
    rcases h x {
      toFun := fun t => ⟨p t, hp t⟩
      source' := by simp
      target' := by simp
    } with ⟨F⟩
    exact ⟨F.map (.restrict s (.id _)), fun t => (F t).2⟩
  · rcases h x (p.map continuous_subtype_val) (fun t => (p t).2) with ⟨F, hF⟩
    exact ⟨{
      toFun t := ⟨F t, hF t⟩
      map_zero_left := by simp
      map_one_left := by simp
      prop' := by simp
    }⟩

中文:
定理 isSimplyConnected_iff_存在_homotopy_refl_对任意_mem
  条件: {s : 集合 X}
  证明: by
  rw [IsSimplyConnected]; rw [simply_connected_iff_loops_nullhomotopic]; rw [← isPathConnected_iff_pathConnectedSpace]
  refine .and .rfl ⟨fun h x p hp => ?_, fun h x p => ?_⟩
  · lift x to s using by simpa using hp 0
    rcases h x {
      toFun := fun t => ⟨p t, hp t⟩
      source' := by simp
      target' := by simp
    } with ⟨F⟩
    exact ⟨F.map (.restrict s (.id _)), fun t => (F t).2⟩
  · rcases h x (p.map continuous_subtype_val) (fun t => (p t).2) with ⟨F, hF⟩
    exact ⟨{
      toFun t := ⟨F t, hF t⟩
      map_zero_left := by simp
      map_one_left := by simp
      prop' := by simp
    }⟩

Depends on / 依赖: F.map, IsSimplyConnected, continuous_subtype_val, isPathConnected_iff_pathConnectedSpace, map_on, map_zero_left, p.map, restrict, simply_connected_iff_loops_nullhomotopic, source, target
-/
theorem isSimplyConnected_iff_exists_homotopy_refl_forall_mem {s : Set X} :
    IsSimplyConnected s ↔ IsPathConnected s ∧ forall x, forall p : Path x x, (forall t, p t in s) ->
      exists F : p.Homotopy (.refl x), forall t, F t in s := by
  rw [IsSimplyConnected]; rw [simply_connected_iff_loops_nullhomotopic]; rw [← isPathConnected_iff_pathConnectedSpace]
  refine .and .rfl ⟨fun h x p hp => ?_, fun h x p => ?_⟩
  · lift x to s using by simpa using hp 0
    rcases h x {
      toFun := fun t => ⟨p t, hp t⟩
      source' := by simp
      target' := by simp
    } with ⟨F⟩
    exact ⟨F.map (.restrict s (.id _)), fun t => (F t).2⟩
  · rcases h x (p.map continuous_subtype_val) (fun t => (p t).2) with ⟨F, hF⟩
    exact ⟨{
      toFun t := ⟨F t, hF t⟩
      map_zero_left := by simp
      map_one_left := by simp
      prop' := by simp
    }⟩

open scoped Pointwise

@[to_additive (attr := simp)]
/--
theorem `isSimplyConnected_smul_set_iff` / 定理 `isSimplyConnected_smul_set_iff`

English:
theorem isSimplyConnected_smul_set_iff
  statement: {G : Type*} [Group G]
  proof: .isSimplyConnected_image Homeomorph.smul c

@[simp]

中文:
定理 isSimplyConnected_smul_set_iff
  结论: {G : 类型} [群 G]
  证明: .isSimplyConnected_image Homeomorph.smul c

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.smul, isSimplyConnected_image
-/
theorem isSimplyConnected_smul_set_iff {G : Type*} [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {c : G} {s : Set X} :
    IsSimplyConnected (c • s) ↔ IsSimplyConnected s :=
.isSimplyConnected_image Homeomorph.smul c

@[simp]
/--
theorem `isSimplyConnected_smul_set₀_iff` / 定理 `isSimplyConnected_smul_set₀_iff`

English:
theorem isSimplyConnected_smul_set₀_iff
  statement: {G : Type*} [GroupWithZero G] [MulAction G X]
  proof: isSimplyConnected_smul_set_iff (c := Units.mk0 c hc)

中文:
定理 isSimplyConnected_smul_set₀_iff
  结论: {G : 类型} [带零群 G] [乘法作用 G X]
  证明: isSimplyConnected_smul_set_iff (c := Units.mk0 c hc)

Depends on / 依赖: Units.mk0, isSimplyConnected_smul_set_iff
-/
theorem isSimplyConnected_smul_set₀_iff {G : Type*} [GroupWithZero G] [MulAction G X]
    [ContinuousConstSMul G X] {c : G} {s : Set X} (hc : c != 0) :
    IsSimplyConnected (c • s) ↔ IsSimplyConnected s :=
  isSimplyConnected_smul_set_iff (c := Units.mk0 c hc)
