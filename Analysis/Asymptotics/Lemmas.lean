/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Further basic lemmas about asymptotics

-/

public section

open Set Topology Filter NNReal

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : Real} {f : α -> E} {g : α -> F} {k : α -> G}
variable {f' : α -> E'} {g' : α -> F'} {k' : α -> G'}
variable {f'' : α -> E''} {g'' : α -> F''} {k'' : α -> G''}
variable {l l' : Filter α}
@[simp]
/--
theorem `isBigOWith_principal` / 定理 `isBigOWith_principal`

English:
theorem isBigOWith_principal
  given: {s : Set α}
  statement: IsBigOWith c (𝓟 s) f g ↔ forall x in s, ‖f x‖ <= c * ‖g x‖
  proof: by
  rw [IsBigOWith_def]; rw [eventually_principal]

中文:
定理 isBigOWith_principal
  条件: {s : 集合 α}
  结论: IsBigOWith c (𝓟 s) f g ↔ 对任意 x in s, ‖f x‖ <= c * ‖g x‖
  证明: by
  rw [IsBigOWith_def]; rw [eventually_principal]

Depends on / 依赖: IsBigOWith_def, eventually_principal
-/
theorem isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ forall x in s, ‖f x‖ <= c * ‖g x‖ := by
  rw [IsBigOWith_def]; rw [eventually_principal]

/--
theorem `isBigO_principal` / 定理 `isBigO_principal`

English:
theorem isBigO_principal
  given: {s : Set α}
  statement: f =O[𝓟 s] g ↔ exists c, forall x in s, ‖f x‖ <= c * ‖g x‖
  proof: by
  simp_rw [isBigO_iff, eventually_principal]

@[simp]

中文:
定理 isBigO_principal
  条件: {s : 集合 α}
  结论: f =O[𝓟 s] g ↔ 存在 c, 对任意 x in s, ‖f x‖ <= c * ‖g x‖
  证明: by
  simp_rw [isBigO_iff, eventually_principal]

@[simp]

Depends on / 依赖: eventually_principal, isBigO_iff, simp_rw
-/
theorem isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ exists c, forall x in s, ‖f x‖ <= c * ‖g x‖ := by
  simp_rw [isBigO_iff, eventually_principal]

@[simp]
/--
theorem `isLittleO_principal` / 定理 `isLittleO_principal`

English:
theorem isLittleO_principal
  given: {s : Set α}
  statement: f'' =o[𝓟 s] g' ↔ forall x in s, f'' x = 0
  proof: by
  refine ⟨fun h x hx => norm_le_zero_iff.1 ?_, fun h => ?_⟩
  · simp only [isLittleO_iff] at h
    have : Tendsto (fun c : Real => c * ‖g' x‖) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left
        inf_le_left
    apply le_of_tendsto_of_tendsto 

中文:
定理 isLittleO_principal
  条件: {s : 集合 α}
  结论: f'' =o[𝓟 s] g' ↔ 对任意 x in s, f'' x = 0
  证明: by
  refine ⟨fun h x hx => norm_le_zero_iff.1 ?_, fun h => ?_⟩
  · simp only [isLittleO_iff] at h
    have : Tendsto (fun c : Real => c * ‖g' x‖) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left
        inf_le_left
    apply le_of_tendsto_of_tendsto 

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyEq, EventuallyEq.rfl, Tendsto, continuous_const, continuous_id, continuous_id.mul, eventually_nhdsWithin_iff, eventually_principal, inf_le_left, isLittleO_iff, isLittleO_zero, le_of_tendsto_of_tendsto, mono_left, norm_le_zero_iff, of_forall, tendsto, tendsto_const_nhds, zero_mul
-/
theorem isLittleO_principal {s : Set α} : f'' =o[𝓟 s] g' ↔ forall x in s, f'' x = 0 := by
  refine ⟨fun h x hx => norm_le_zero_iff.1 ?_, fun h => ?_⟩
  · simp only [isLittleO_iff] at h
    have : Tendsto (fun c : Real => c * ‖g' x‖) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left
        inf_le_left
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    apply eventually_nhdsWithin_iff.2 (Eventually.of_forall (fun c hc => ?_))
    exact eventually_principal.1 (h hc) x hx
  · apply (isLittleO_zero g' _).congr' ?_ EventuallyEq.rfl
    exact fun x hx => (h x hx).symm

@[simp]
/--
theorem `isBigOWith_top` / 定理 `isBigOWith_top`

English:
theorem isBigOWith_top
  statement: IsBigOWith c ⊤ f g ↔ forall x, ‖f x‖ <= c * ‖g x‖
  proof: by
  rw [IsBigOWith_def]; rw [eventually_top]

@[simp]

中文:
定理 isBigOWith_top
  结论: IsBigOWith c ⊤ f g ↔ 对任意 x, ‖f x‖ <= c * ‖g x‖
  证明: by
  rw [IsBigOWith_def]; rw [eventually_top]

@[simp]

Depends on / 依赖: IsBigOWith_def, eventually_top
-/
theorem isBigOWith_top : IsBigOWith c ⊤ f g ↔ forall x, ‖f x‖ <= c * ‖g x‖ := by
  rw [IsBigOWith_def]; rw [eventually_top]

@[simp]
/--
theorem `isBigO_top` / 定理 `isBigO_top`

English:
theorem isBigO_top
  statement: f =O[⊤] g ↔ exists C, forall x, ‖f x‖ <= C * ‖g x‖
  proof: by
  simp_rw [isBigO_iff, eventually_top]

@[simp]

中文:
定理 isBigO_top
  结论: f =O[⊤] g ↔ 存在 C, 对任意 x, ‖f x‖ <= C * ‖g x‖
  证明: by
  simp_rw [isBigO_iff, eventually_top]

@[simp]

Depends on / 依赖: eventually_top, isBigO_iff, simp_rw
-/
theorem isBigO_top : f =O[⊤] g ↔ exists C, forall x, ‖f x‖ <= C * ‖g x‖ := by
  simp_rw [isBigO_iff, eventually_top]

@[simp]
/--
theorem `isLittleO_top` / 定理 `isLittleO_top`

English:
theorem isLittleO_top
  statement: f'' =o[⊤] g' ↔ forall x, f'' x = 0
  proof: by
  simp only [← principal_univ, isLittleO_principal, mem_univ, forall_true_left]

中文:
定理 isLittleO_top
  结论: f'' =o[⊤] g' ↔ 对任意 x, f'' x = 0
  证明: by
  simp only [← principal_univ, isLittleO_principal, mem_univ, forall_true_left]

Depends on / 依赖: forall_true_left, isLittleO_principal, mem_univ, principal_univ
-/
theorem isLittleO_top : f'' =o[⊤] g' ↔ forall x, f'' x = 0 := by
  simp only [← principal_univ, isLittleO_principal, mem_univ, forall_true_left]

section

variable (F)
variable [One F] [NormOneClass F]

/--
theorem `isBigOWith_const_one` / 定理 `isBigOWith_const_one`

English:
theorem isBigOWith_const_one
  given: (c : E) (l : Filter α)
  proof: by simp [isBigOWith_iff]

中文:
定理 isBigOWith_const_one
  条件: (c : E) (l : 滤子 α)
  证明: by simp [isBigOWith_iff]

Depends on / 依赖: isBigOWith_iff
-/
theorem isBigOWith_const_one (c : E) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun _x : α => c) fun _x => (1 : F) := by simp [isBigOWith_iff]

/--
theorem `isBigO_const_one` / 定理 `isBigO_const_one`

English:
theorem isBigO_const_one
  given: (c : E) (l : Filter α)
  statement: (fun _x : α => c) =O[l] fun _x => (1 : F)
  proof: (isBigOWith_const_one F c l).isBigO

中文:
定理 isBigO_const_one
  条件: (c : E) (l : 滤子 α)
  结论: (fun _x : α => c) =O[l] fun _x => (1 : F)
  证明: (isBigOWith_const_one F c l).isBigO

Depends on / 依赖: isBigO, isBigOWith_const_one
-/
theorem isBigO_const_one (c : E) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => (1 : F) :=
  (isBigOWith_const_one F c l).isBigO

/--
theorem `isLittleO_const_iff_isLittleO_one` / 定理 `isLittleO_const_iff_isLittleO_one`

English:
theorem isLittleO_const_iff_isLittleO_one
  given: {c : F''} (hc : c != 0)
  proof: ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc),
fun h => h.trans_isBigO isBigO_const_const _ hc _⟩

@[simp]

中文:
定理 isLittleO_const_iff_isLittleO_one
  条件: {c : F''} (hc : c != 0)
  证明: ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc),
fun h => h.trans_isBigO isBigO_const_const _ hc _⟩

@[simp]

Depends on / 依赖: h.trans_isBigO, h.trans_isBigOWith, isBigOWith_const_one, isBigO_const_const, norm_pos_iff, trans_isBigO, trans_isBigOWith
-/
theorem isLittleO_const_iff_isLittleO_one {c : F''} (hc : c != 0) :
    (f =o[l] fun _x => c) ↔ f =o[l] fun _x => (1 : F) :=
  ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc),
fun h => h.trans_isBigO isBigO_const_const _ hc _⟩

@[simp]
/--
theorem `isLittleO_one_iff` / 定理 `isLittleO_one_iff`

English:
theorem isLittleO_one_iff
  given: {f : α -> E'''}
  statement: f =o[l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
  proof: by
  simp only [isLittleO_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]

@[simp]

中文:
定理 isLittleO_one_iff
  条件: {f : α -> E'''}
  结论: f =o[l] (fun _x => 1 : α -> F) ↔ 收敛 f l (𝓝 0)
  证明: by
  simp only [isLittleO_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]

@[simp]

Depends on / 依赖: Metric, Metric.mem_closedBall, Metric.nhds_basis_closedBall.tendsto_right_iff, dist_zero_right, isLittleO_iff, mem_closedBall, mul_one, nhds_basis_closedBall, norm_one, tendsto_right_iff
-/
theorem isLittleO_one_iff {f : α -> E'''} : f =o[l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0) := by
  simp only [isLittleO_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]

@[simp]
/--
theorem `isBigO_one_iff` / 定理 `isBigO_one_iff`

English:
theorem isBigO_one_iff
  statement: f =O[l] (fun _x => 1 : α -> F) ↔
  proof: by
  simp only [isBigO_iff, norm_one, mul_one, IsBoundedUnder, IsBounded, eventually_map]

alias ⟨_, _root_.Filter.IsBoundedUnder.isBigO_one⟩ := isBigO_one_iff

@[simp]

中文:
定理 isBigO_one_iff
  结论: f =O[l] (fun _x => 1 : α -> F) ↔
  证明: by
  simp only [isBigO_iff, norm_one, mul_one, IsBoundedUnder, IsBounded, eventually_map]

alias ⟨_, _root_.Filter.IsBoundedUnder.isBigO_one⟩ := isBigO_one_iff

@[simp]

Depends on / 依赖: IsBounded, IsBoundedUnder, eventually_map, isBigO_iff, mul_one, norm_one
-/
theorem isBigO_one_iff : f =O[l] (fun _x => 1 : α -> F) ↔
    IsBoundedUnder (· <= ·) l fun x => ‖f x‖ := by
  simp only [isBigO_iff, norm_one, mul_one, IsBoundedUnder, IsBounded, eventually_map]

alias ⟨_, _root_.Filter.IsBoundedUnder.isBigO_one⟩ := isBigO_one_iff

@[simp]
/--
theorem `isLittleO_one_left_iff` / 定理 `isLittleO_one_left_iff`

English:
theorem isLittleO_one_left_iff
  statement: (fun _x => 1 : α -> F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop
  proof: calc
    (fun _x => 1 : α -> F) =o[l] f ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖(1 : F)‖ <= ‖f x‖ :=
isLittleO_iff_nat_mul_le_aux Or.inl fun _x => by simp only [norm_one, zero_le_one]
    _ ↔ forall n : Nat, True -> forallᶠ x in l, ‖f x‖ in Ici (n : Real) := by
      simp only [norm_one, mul_one, tr

中文:
定理 isLittleO_one_left_iff
  结论: (fun _x => 1 : α -> F) =o[l] f ↔ 收敛 (fun x => ‖f x‖) l atTop
  证明: calc
    (fun _x => 1 : α -> F) =o[l] f ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖(1 : F)‖ <= ‖f x‖ :=
isLittleO_iff_nat_mul_le_aux Or.inl fun _x => by simp only [norm_one, zero_le_one]
    _ ↔ forall n : Nat, True -> forallᶠ x in l, ‖f x‖ in Ici (n : Real) := by
      simp only [norm_one, mul_one, tr

Depends on / 依赖: Or.inl, Tendsto, atTop_hasCountableBasis_of_archimedean, isLittleO_iff_nat_mul_le_aux, mem_Ici, mul_one, norm_one, tendsto_right_iff, tendsto_right_iff.symm, true_imp_iff, zero_le_one
-/
theorem isLittleO_one_left_iff : (fun _x => 1 : α -> F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun _x => 1 : α -> F) =o[l] f ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖(1 : F)‖ <= ‖f x‖ :=
isLittleO_iff_nat_mul_le_aux Or.inl fun _x => by simp only [norm_one, zero_le_one]
    _ ↔ forall n : Nat, True -> forallᶠ x in l, ‖f x‖ in Ici (n : Real) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm

/--
theorem `_root_.Filter.Tendsto.isBigO_one` / 定理 `_root_.Filter.Tendsto.isBigO_one`

English:
theorem _root_.Filter.Tendsto.isBigO_one
  given: {c : E'} (h : Tendsto f' l (𝓝 c))
  proof: h.norm.isBoundedUnder_le.isBigO_one F

中文:
定理 _root_.滤子.收敛.isBigO_one
  条件: {c : E'} (h : 收敛 f' l (𝓝 c))
  证明: h.norm.isBoundedUnder_le.isBigO_one F

Depends on / 依赖: h.norm.isBoundedUnder_le.isBigO_one, isBigO_one, isBoundedUnder_le
-/
theorem _root_.Filter.Tendsto.isBigO_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun _x => 1 : α -> F) :=
  h.norm.isBoundedUnder_le.isBigO_one F

/--
theorem `IsBigO.trans_tendsto_nhds` / 定理 `IsBigO.trans_tendsto_nhds`

English:
theorem IsBigO.trans_tendsto_nhds
  given: (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y))
  proof: hfg.trans hg.isBigO_one F

中文:
定理 IsBigO.trans_tendsto_nhds
  条件: (hfg : f =O[l] g') {y : F'} (hg : 收敛 g' l (𝓝 y))
  证明: hfg.trans hg.isBigO_one F

Depends on / 依赖: hfg.trans, hg.isBigO_one, isBigO_one
-/
theorem IsBigO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun _x => 1 : α -> F) :=
hfg.trans hg.isBigO_one F

/--
lemma `isBigO_one_nhds_ne_iff` / 引理 `isBigO_one_nhds_ne_iff`

English:
lemma isBigO_one_nhds_ne_iff
  given: [TopologicalSpace α] {a : α}
  proof: by
  refine ⟨fun h => ?_, fun h => h.mono nhdsWithin_le_nhds⟩
  simp only [isBigO_one_iff, IsBoundedUnder, IsBounded, eventually_map] at h ⊢
  obtain ⟨c, hc⟩ := h
  use max c ‖f a‖
  filter_upwards [eventually_nhdsWithin_iff.mp hc] with b hb
  rcases eq_or_ne b a with rfl | hb'
  · apply le_max_righ

中文:
引理 isBigO_one_nhds_ne_iff
  条件: [拓扑空间 α] {a : α}
  证明: by
  refine ⟨fun h => ?_, fun h => h.mono nhdsWithin_le_nhds⟩
  simp only [isBigO_one_iff, IsBoundedUnder, IsBounded, eventually_map] at h ⊢
  obtain ⟨c, hc⟩ := h
  use max c ‖f a‖
  filter_upwards [eventually_nhdsWithin_iff.mp hc] with b hb
  rcases eq_or_ne b a with rfl | hb'
  · apply le_max_righ

Depends on / 依赖: IsBounded, IsBoundedUnder, eq_or_ne, eventually_map, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mp, filter_upwards, h.mono, isBigO_one_iff, le_max_left, le_max_right, nhdsWithin_le_nhds
-/
lemma isBigO_one_nhds_ne_iff [TopologicalSpace α] {a : α} :
    f =O[𝓝[!=] a] (fun _ => 1 : α -> F) ↔ f =O[𝓝 a] (fun _ => 1 : α -> F) := by
  refine ⟨fun h => ?_, fun h => h.mono nhdsWithin_le_nhds⟩
  simp only [isBigO_one_iff, IsBoundedUnder, IsBounded, eventually_map] at h ⊢
  obtain ⟨c, hc⟩ := h
  use max c ‖f a‖
  filter_upwards [eventually_nhdsWithin_iff.mp hc] with b hb
  rcases eq_or_ne b a with rfl | hb'
  · apply le_max_right
  · exact (hb hb').trans (le_max_left ..)

end

/--
theorem `isLittleO_const_iff` / 定理 `isLittleO_const_iff`

English:
theorem isLittleO_const_iff
  given: {c : F''} (hc : c != 0)
  proof: (isLittleO_const_iff_isLittleO_one Real hc).trans (isLittleO_one_iff _)

中文:
定理 isLittleO_const_iff
  条件: {c : F''} (hc : c != 0)
  证明: (isLittleO_const_iff_isLittleO_one Real hc).trans (isLittleO_one_iff _)

Depends on / 依赖: isLittleO_const_iff_isLittleO_one, isLittleO_one_iff
-/
theorem isLittleO_const_iff {c : F''} (hc : c != 0) :
    (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isLittleO_const_iff_isLittleO_one Real hc).trans (isLittleO_one_iff _)

/--
theorem `isLittleO_id_const` / 定理 `isLittleO_id_const`

English:
theorem isLittleO_id_const
  given: {c : F''} (hc : c != 0)
  statement: (fun x : E'' => x) =o[𝓝 0] fun _x => c
  proof: (isLittleO_const_iff hc).mpr (continuous_id.tendsto 0)

中文:
定理 isLittleO_id_const
  条件: {c : F''} (hc : c != 0)
  结论: (fun x : E'' => x) =o[𝓝 0] fun _x => c
  证明: (isLittleO_const_iff hc).mpr (continuous_id.tendsto 0)

Depends on / 依赖: continuous_id, continuous_id.tendsto, isLittleO_const_iff, tendsto
-/
theorem isLittleO_id_const {c : F''} (hc : c != 0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c :=
  (isLittleO_const_iff hc).mpr (continuous_id.tendsto 0)

/--
theorem `_root_.Filter.IsBoundedUnder.isBigO_const` / 定理 `_root_.Filter.IsBoundedUnder.isBigO_const`

English:
theorem _root_.Filter.IsBoundedUnder.isBigO_const
  statement: (h : IsBoundedUnder (· <= ·) l (norm ∘ f))
  proof: (h.isBigO_one Real).trans (isBigO_const_const _ hc _)

中文:
定理 _root_.滤子.IsBoundedUnder.isBigO_const
  结论: (h : IsBoundedUnder (· <= ·) l (norm ∘ f))
  证明: (h.isBigO_one Real).trans (isBigO_const_const _ hc _)

Depends on / 依赖: h.isBigO_one, isBigO_const_const, isBigO_one
-/
theorem _root_.Filter.IsBoundedUnder.isBigO_const (h : IsBoundedUnder (· <= ·) l (norm ∘ f))
    {c : F''} (hc : c != 0) : f =O[l] fun _x => c :=
  (h.isBigO_one Real).trans (isBigO_const_const _ hc _)

/--
theorem `isBigO_const_of_tendsto` / 定理 `isBigO_const_of_tendsto`

English:
theorem isBigO_const_of_tendsto
  given: {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c != 0)
  proof: h.norm.isBoundedUnder_le.isBigO_const hc

中文:
定理 isBigO_const_of_tendsto
  条件: {y : E''} (h : 收敛 f'' l (𝓝 y)) {c : F''} (hc : c != 0)
  证明: h.norm.isBoundedUnder_le.isBigO_const hc

Depends on / 依赖: h.norm.isBoundedUnder_le.isBigO_const, isBigO_const, isBoundedUnder_le
-/
theorem isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c != 0) :
    f'' =O[l] fun _x => c :=
  h.norm.isBoundedUnder_le.isBigO_const hc

/--
theorem `IsBigO.isBoundedUnder_le` / 定理 `IsBigO.isBoundedUnder_le`

English:
theorem IsBigO.isBoundedUnder_le
  given: {c : F} (h : f =O[l] fun _x => c)
  proof: let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩

中文:
定理 IsBigO.isBoundedUnder_le
  条件: {c : F} (h : f =O[l] fun _x => c)
  证明: let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩

Depends on / 依赖: eventually_map, h.bound
-/
theorem IsBigO.isBoundedUnder_le {c : F} (h : f =O[l] fun _x => c) :
    IsBoundedUnder (· <= ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩

/--
theorem `isBigO_const_of_ne` / 定理 `isBigO_const_of_ne`

English:
theorem isBigO_const_of_ne
  given: {c : F''} (hc : c != 0)
  proof: ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩

中文:
定理 isBigO_const_of_ne
  条件: {c : F''} (hc : c != 0)
  证明: ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩

Depends on / 依赖: h.isBigO_const, h.isBoundedUnder_le, isBigO_const, isBoundedUnder_le
-/
theorem isBigO_const_of_ne {c : F''} (hc : c != 0) :
    (f =O[l] fun _x => c) ↔ IsBoundedUnder (· <= ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩

/--
theorem `isBigO_const_iff` / 定理 `isBigO_const_iff`

English:
theorem isBigO_const_iff
  given: {c : F''}
  statement: (f'' =O[l] fun _x => c) ↔
  proof: by
  refine ⟨fun h => ⟨fun hc => isBigO_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, ?_⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts [(hcf hc).trans_isBigO (isBigO_zero _ _), hf.isBigO_const hc]

中文:
定理 isBigO_const_iff
  条件: {c : F''}
  结论: (f'' =O[l] fun _x => c) ↔
  证明: by
  refine ⟨fun h => ⟨fun hc => isBigO_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, ?_⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts [(hcf hc).trans_isBigO (isBigO_zero _ _), hf.isBigO_const hc]

Depends on / 依赖: eq_or_ne, exacts, h.isBoundedUnder_le, hf.isBigO_const, isBigO_const, isBigO_zero, isBigO_zero_right_iff, isBoundedUnder_le, trans_isBigO
-/
theorem isBigO_const_iff {c : F''} : (f'' =O[l] fun _x => c) ↔
    (c = 0 -> f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· <= ·) l fun x => ‖f'' x‖ := by
  refine ⟨fun h => ⟨fun hc => isBigO_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, ?_⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts [(hcf hc).trans_isBigO (isBigO_zero _ _), hf.isBigO_const hc]

/--
theorem `isBigO_iff_isBoundedUnder_le_div` / 定理 `isBigO_iff_isBoundedUnder_le_div`

English:
theorem isBigO_iff_isBoundedUnder_le_div
  given: (h : forallᶠ x in l, g'' x != 0)
  proof: by
  simp only [isBigO_iff, IsBoundedUnder, IsBounded, eventually_map]
  exact
    exists_congr fun c =>
eventually_congr h.mono fun x hx => (div_le_iff₀ <| norm_pos_iff.2 hx).symm

中文:
定理 isBigO_iff_isBoundedUnder_le_div
  条件: (h : 对任意ᶠ x in l, g'' x != 0)
  证明: by
  simp only [isBigO_iff, IsBoundedUnder, IsBounded, eventually_map]
  exact
    exists_congr fun c =>
eventually_congr h.mono fun x hx => (div_le_iff₀ <| norm_pos_iff.2 hx).symm

Depends on / 依赖: IsBounded, IsBoundedUnder, eventually_congr, eventually_map, exists_congr, h.mono, isBigO_iff, norm_pos_iff
-/
theorem isBigO_iff_isBoundedUnder_le_div (h : forallᶠ x in l, g'' x != 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· <= ·) l fun x => ‖f x‖ / ‖g'' x‖ := by
  simp only [isBigO_iff, IsBoundedUnder, IsBounded, eventually_map]
  exact
    exists_congr fun c =>
eventually_congr h.mono fun x hx => (div_le_iff₀ <| norm_pos_iff.2 hx).symm

/--
theorem `isBigO_const_left_iff_pos_le_norm` / 定理 `isBigO_const_left_iff_pos_le_norm`

English:
theorem isBigO_const_left_iff_pos_le_norm
  given: {c : E''} (hc : c != 0)
  proof: by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, ?_⟩
    exact hC.bound.mono fun x => (div_le_iff₀' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine IsBigO.of_bound (‖c‖ / b) (hb.mono fun x hx => ?_)
    rw [div_mul_eq_mul_div]; rw

中文:
定理 isBigO_const_left_iff_pos_le_norm
  条件: {c : E''} (hc : c != 0)
  证明: by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, ?_⟩
    exact hC.bound.mono fun x => (div_le_iff₀' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine IsBigO.of_bound (‖c‖ / b) (hb.mono fun x hx => ?_)
    rw [div_mul_eq_mul_div]; rw

Depends on / 依赖: IsBigO, IsBigO.of_bound, div_mul_eq_mul_div, div_pos, exists_pos, h.exists_pos, hC.bound.mono, hb.mono, le_mul_of_one_le_right, mul_div_assoc, norm_nonneg, norm_pos_iff, of_bound, one_le_div
-/
theorem isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c != 0) :
    (fun _x => c) =O[l] f' ↔ exists b, 0 < b ∧ forallᶠ x in l, b <= ‖f' x‖ := by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, ?_⟩
    exact hC.bound.mono fun x => (div_le_iff₀' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine IsBigO.of_bound (‖c‖ / b) (hb.mono fun x hx => ?_)
    rw [div_mul_eq_mul_div]; rw [mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)

/--
theorem `IsBigO.trans_tendsto` / 定理 `IsBigO.trans_tendsto`

English:
theorem IsBigO.trans_tendsto
  given: (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0))
  proof: (isLittleO_one_iff Real).1 hfg.trans_isLittleO (isLittleO_one_iff Real).2 hg

中文:
定理 IsBigO.trans_tendsto
  条件: (hfg : f'' =O[l] g'') (hg : 收敛 g'' l (𝓝 0))
  证明: (isLittleO_one_iff Real).1 hfg.trans_isLittleO (isLittleO_one_iff Real).2 hg

Depends on / 依赖: hfg.trans_isLittleO, isLittleO_one_iff, trans_isLittleO
-/
theorem IsBigO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
(isLittleO_one_iff Real).1 hfg.trans_isLittleO (isLittleO_one_iff Real).2 hg

/--
theorem `IsLittleO.trans_tendsto` / 定理 `IsLittleO.trans_tendsto`

English:
theorem IsLittleO.trans_tendsto
  given: (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0))
  proof: hfg.isBigO.trans_tendsto hg

中文:
定理 IsLittleO.trans_tendsto
  条件: (hfg : f'' =o[l] g'') (hg : 收敛 g'' l (𝓝 0))
  证明: hfg.isBigO.trans_tendsto hg

Depends on / 依赖: hfg.isBigO.trans_tendsto, isBigO, trans_tendsto
-/
theorem IsLittleO.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.isBigO.trans_tendsto hg

/--
lemma `isLittleO_id_one` / 引理 `isLittleO_id_one`

English:
lemma isLittleO_id_one
  given: [One F''] [NeZero (1 : F'')]
  statement: (fun x : E'' => x) =o[𝓝 0] (1 : E'' -> F'')
  proof: isLittleO_id_const one_ne_zero

中文:
引理 isLittleO_id_one
  条件: [幺 F''] [NeZero (1 : F'')]
  结论: (fun x : E'' => x) =o[𝓝 0] (1 : E'' -> F'')
  证明: isLittleO_id_const one_ne_zero

Depends on / 依赖: isLittleO_id_const, one_ne_zero
-/
lemma isLittleO_id_one [One F''] [NeZero (1 : F'')] : (fun x : E'' => x) =o[𝓝 0] (1 : E'' -> F'') :=
  isLittleO_id_const one_ne_zero

/--
theorem `continuousAt_iff_isLittleO` / 定理 `continuousAt_iff_isLittleO`

English:
theorem continuousAt_iff_isLittleO
  statement: {α : Type*} {E : Type*} [NormedRing E] [One F] [NormOneClass F]
  proof: by
  simp [ContinuousAt, ← tendsto_sub_nhds_zero_iff]

中文:
定理 continuousAt_iff_isLittleO
  结论: {α : 类型} {E : 类型} [赋范环 E] [幺 F] [NormOne类 F]
  证明: by
  simp [ContinuousAt, ← tendsto_sub_nhds_zero_iff]

Depends on / 依赖: ContinuousAt, tendsto_sub_nhds_zero_iff
-/
theorem continuousAt_iff_isLittleO {α : Type*} {E : Type*} [NormedRing E] [One F] [NormOneClass F]
    [TopologicalSpace α] {f : α -> E} {x : α} :
    (ContinuousAt f x) ↔ (f · - f x) =o[𝓝 x] (fun (_ : α) => (1 : F)) := by
  simp [ContinuousAt, ← tendsto_sub_nhds_zero_iff]

/--
theorem `_root_.ContinuousAt.isLittleO` / 定理 `_root_.ContinuousAt.isLittleO`

English:
theorem _root_.ContinuousAt.isLittleO
  statement: {α : Type*} {E : Type*} [NormedRing E] [One F]
  proof: continuousAt_iff_isLittleO.mp hcont

中文:
定理 _root_.ContinuousAt.isLittleO
  结论: {α : 类型} {E : 类型} [赋范环 E] [幺 F]
  证明: continuousAt_iff_isLittleO.mp hcont

Depends on / 依赖: continuousAt_iff_isLittleO, continuousAt_iff_isLittleO.mp
-/
theorem _root_.ContinuousAt.isLittleO {α : Type*} {E : Type*} [NormedRing E] [One F]
    [NormOneClass F] [TopologicalSpace α] {f : α -> E} {x : α} (hcont : ContinuousAt f x) :
    (f · - f x) =o[𝓝 x] (fun _ => (1 : F)) :=
  continuousAt_iff_isLittleO.mp hcont

/--
theorem `_root_.ContinuousAt.isBigO` / 定理 `_root_.ContinuousAt.isBigO`

English:
theorem _root_.ContinuousAt.isBigO
  statement: {α : Type*} {E : Type*} [NormedRing E] [One F] [NormOneClass F]
  proof: hcont.isLittleO.isBigO.congr_of_sub.mpr (isBigO_const_one ..)

中文:
定理 _root_.ContinuousAt.isBigO
  结论: {α : 类型} {E : 类型} [赋范环 E] [幺 F] [NormOne类 F]
  证明: hcont.isLittleO.isBigO.congr_of_sub.mpr (isBigO_const_one ..)

Depends on / 依赖: congr_of_sub, hcont.isLittleO.isBigO.congr_of_sub.mpr, isBigO, isBigO_const_one, isLittleO
-/
theorem _root_.ContinuousAt.isBigO {α : Type*} {E : Type*} [NormedRing E] [One F] [NormOneClass F]
    [TopologicalSpace α] {f : α -> E} {x : α} (hcont : ContinuousAt f x) :
    f =O[𝓝 x] (fun _ => (1 : F)) :=
  hcont.isLittleO.isBigO.congr_of_sub.mpr (isBigO_const_one ..)


/--
theorem `IsBigO.of_pow` / 定理 `IsBigO.of_pow`

English:
theorem IsBigO.of_pow
  given: {f : α -> 𝕜} {g : α -> R} {n : Nat} (hn : n != 0) (h : (f ^ n) =O[l] (g ^ n))
  proof: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  obtain ⟨c : Real, hc₀ : 0 <= c, hc : C <= c ^ n⟩ :=
    ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).isBigO

中文:
定理 IsBigO.of_pow
  条件: {f : α -> 𝕜} {g : α -> R} {n : 自然数} (hn : n != 0) (h : (f ^ n) =O[l] (g ^ n))
  证明: by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  obtain ⟨c : Real, hc₀ : 0 <= c, hc : C <= c ^ n⟩ :=
    ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).isBigO

Depends on / 依赖: eventually_ge_atTop, exists_pos, h.exists_pos, hC.of_pow, isBigO, of_pow, tendsto_pow_atTop
-/
theorem IsBigO.of_pow {f : α -> 𝕜} {g : α -> R} {n : Nat} (hn : n != 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  obtain ⟨c : Real, hc₀ : 0 <= c, hc : C <= c ^ n⟩ :=
    ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).isBigO

/--
theorem `IsBigO.pow_of_le_right` / 定理 `IsBigO.pow_of_le_right`

English:
theorem IsBigO.pow_of_le_right
  statement: {f : α -> Real}
  proof: by
  rw [IsBigO_def]
  refine ⟨1, ?_⟩
  rw [IsBigOWith_def]
  exact hf.mono fun x hx => by simp [abs_eq_self.mpr (zero_le_one.trans hx), pow_le_pow_right₀ hx h]

中文:
定理 IsBigO.pow_of_le_right
  结论: {f : α -> 实数}
  证明: by
  rw [IsBigO_def]
  refine ⟨1, ?_⟩
  rw [IsBigOWith_def]
  exact hf.mono fun x hx => by simp [abs_eq_self.mpr (zero_le_one.trans hx), pow_le_pow_right₀ hx h]

Depends on / 依赖: IsBigOWith_def, IsBigO_def, abs_eq_self, abs_eq_self.mpr, hf.mono, zero_le_one, zero_le_one.trans
-/
theorem IsBigO.pow_of_le_right {f : α -> Real}
    (hf : 1 <=ᶠ[l] f) {m n : Nat}
    (h : n <= m) : (f ^ n) =O[l] (f ^ m) := by
  rw [IsBigO_def]
  refine ⟨1, ?_⟩
  rw [IsBigOWith_def]
  exact hf.mono fun x hx => by simp [abs_eq_self.mpr (zero_le_one.trans hx), pow_le_pow_right₀ hx h]

/-! ### Scalar multiplication -/

section SMulConst

variable [Module R E'] [IsBoundedSMul R E']

/--
theorem `IsBigOWith.const_smul_self` / 定理 `IsBigOWith.const_smul_self`

English:
theorem IsBigOWith.const_smul_self
  given: (c' : R)
  proof: isBigOWith_of_le' _ fun _ => norm_smul_le _ _

中文:
定理 IsBigOWith.const_smul_self
  条件: (c' : R)
  证明: isBigOWith_of_le' _ fun _ => norm_smul_le _ _

Depends on / 依赖: isBigOWith_of_le, norm_smul_le
-/
theorem IsBigOWith.const_smul_self (c' : R) :
    IsBigOWith (‖c'‖) l (fun x => c' • f' x) f' :=
  isBigOWith_of_le' _ fun _ => norm_smul_le _ _

/--
theorem `IsBigO.const_smul_self` / 定理 `IsBigO.const_smul_self`

English:
theorem IsBigO.const_smul_self
  given: (c' : R)
  statement: (fun x => c' • f' x) =O[l] f'
  proof: (IsBigOWith.const_smul_self _).isBigO

中文:
定理 IsBigO.const_smul_self
  条件: (c' : R)
  结论: (fun x => c' • f' x) =O[l] f'
  证明: (IsBigOWith.const_smul_self _).isBigO

Depends on / 依赖: IsBigOWith, IsBigOWith.const_smul_self, const_smul_self, isBigO
-/
theorem IsBigO.const_smul_self (c' : R) : (fun x => c' • f' x) =O[l] f' :=
  (IsBigOWith.const_smul_self _).isBigO

/--
theorem `IsBigOWith.const_smul_left` / 定理 `IsBigOWith.const_smul_left`

English:
theorem IsBigOWith.const_smul_left
  given: (h : IsBigOWith c l f' g) (c' : R)
  proof: .trans (.const_smul_self _) h (norm_nonneg _)

中文:
定理 IsBigOWith.const_smul_left
  条件: (h : IsBigOWith c l f' g) (c' : R)
  证明: .trans (.const_smul_self _) h (norm_nonneg _)

Depends on / 依赖: const_smul_self, norm_nonneg
-/
theorem IsBigOWith.const_smul_left (h : IsBigOWith c l f' g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  .trans (.const_smul_self _) h (norm_nonneg _)

/--
theorem `IsBigO.const_smul_left` / 定理 `IsBigO.const_smul_left`

English:
theorem IsBigO.const_smul_left
  given: (h : f' =O[l] g) (c : R)
  statement: (c • f') =O[l] g
  proof: let ⟨_b, hb⟩ := h.isBigOWith
  (hb.const_smul_left _).isBigO

中文:
定理 IsBigO.const_smul_left
  条件: (h : f' =O[l] g) (c : R)
  结论: (c • f') =O[l] g
  证明: let ⟨_b, hb⟩ := h.isBigOWith
  (hb.const_smul_left _).isBigO

Depends on / 依赖: const_smul_left, h.isBigOWith, hb.const_smul_left, isBigO, isBigOWith
-/
theorem IsBigO.const_smul_left (h : f' =O[l] g) (c : R) : (c • f') =O[l] g :=
  let ⟨_b, hb⟩ := h.isBigOWith
  (hb.const_smul_left _).isBigO

/--
theorem `IsLittleO.const_smul_left` / 定理 `IsLittleO.const_smul_left`

English:
theorem IsLittleO.const_smul_left
  given: (h : f' =o[l] g) (c : R)
  statement: (c • f') =o[l] g
  proof: (IsBigO.const_smul_self _).trans_isLittleO h

中文:
定理 IsLittleO.const_smul_left
  条件: (h : f' =o[l] g) (c : R)
  结论: (c • f') =o[l] g
  证明: (IsBigO.const_smul_self _).trans_isLittleO h

Depends on / 依赖: IsBigO, IsBigO.const_smul_self, const_smul_self, trans_isLittleO
-/
theorem IsLittleO.const_smul_left (h : f' =o[l] g) (c : R) : (c • f') =o[l] g :=
  (IsBigO.const_smul_self _).trans_isLittleO h

variable [Module 𝕜 E'] [NormSMulClass 𝕜 E']

/--
theorem `isBigO_const_smul_left` / 定理 `isBigO_const_smul_left`

English:
theorem isBigO_const_smul_left
  given: {c : 𝕜} (hc : c != 0)
  statement: (fun x => c • f' x) =O[l] g ↔ f' =O[l] g
  proof: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_left]
  simp only [norm_smul]
  rw [isBigO_const_mul_left_iff cne0]; rw [isBigO_norm_left]

中文:
定理 isBigO_const_smul_left
  条件: {c : 𝕜} (hc : c != 0)
  结论: (fun x => c • f' x) =O[l] g ↔ f' =O[l] g
  证明: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_left]
  simp only [norm_smul]
  rw [isBigO_const_mul_left_iff cne0]; rw [isBigO_norm_left]

Depends on / 依赖: isBigO_const_mul_left_iff, isBigO_norm_left, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_smul
-/
theorem isBigO_const_smul_left {c : 𝕜} (hc : c != 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g := by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_left]
  simp only [norm_smul]
  rw [isBigO_const_mul_left_iff cne0]; rw [isBigO_norm_left]

/--
theorem `isLittleO_const_smul_left` / 定理 `isLittleO_const_smul_left`

English:
theorem isLittleO_const_smul_left
  given: {c : 𝕜} (hc : c != 0)
  proof: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_left]
  simp only [norm_smul]
  rw [isLittleO_const_mul_left_iff cne0]; rw [isLittleO_norm_left]

中文:
定理 isLittleO_const_smul_left
  条件: {c : 𝕜} (hc : c != 0)
  证明: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_left]
  simp only [norm_smul]
  rw [isLittleO_const_mul_left_iff cne0]; rw [isLittleO_norm_left]

Depends on / 依赖: isLittleO_const_mul_left_iff, isLittleO_norm_left, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_smul
-/
theorem isLittleO_const_smul_left {c : 𝕜} (hc : c != 0) :
    (fun x => c • f' x) =o[l] g ↔ f' =o[l] g := by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_left]
  simp only [norm_smul]
  rw [isLittleO_const_mul_left_iff cne0]; rw [isLittleO_norm_left]

/--
theorem `isBigO_const_smul_right` / 定理 `isBigO_const_smul_right`

English:
theorem isBigO_const_smul_right
  given: {c : 𝕜} (hc : c != 0)
  proof: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_right]
  simp only [norm_smul]
  rw [isBigO_const_mul_right_iff cne0]; rw [isBigO_norm_right]

中文:
定理 isBigO_const_smul_right
  条件: {c : 𝕜} (hc : c != 0)
  证明: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_right]
  simp only [norm_smul]
  rw [isBigO_const_mul_right_iff cne0]; rw [isBigO_norm_right]

Depends on / 依赖: isBigO_const_mul_right_iff, isBigO_norm_right, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_smul
-/
theorem isBigO_const_smul_right {c : 𝕜} (hc : c != 0) :
    (f =O[l] fun x => c • f' x) ↔ f =O[l] f' := by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_right]
  simp only [norm_smul]
  rw [isBigO_const_mul_right_iff cne0]; rw [isBigO_norm_right]

/--
theorem `isLittleO_const_smul_right` / 定理 `isLittleO_const_smul_right`

English:
theorem isLittleO_const_smul_right
  given: {c : 𝕜} (hc : c != 0)
  proof: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_right]
  simp only [norm_smul]
  rw [isLittleO_const_mul_right_iff cne0]; rw [isLittleO_norm_right]

中文:
定理 isLittleO_const_smul_right
  条件: {c : 𝕜} (hc : c != 0)
  证明: by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_right]
  simp only [norm_smul]
  rw [isLittleO_const_mul_right_iff cne0]; rw [isLittleO_norm_right]

Depends on / 依赖: isLittleO_const_mul_right_iff, isLittleO_norm_right, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_smul
-/
theorem isLittleO_const_smul_right {c : 𝕜} (hc : c != 0) :
    (f =o[l] fun x => c • f' x) ↔ f =o[l] f' := by
  have cne0 : ‖c‖ != 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_right]
  simp only [norm_smul]
  rw [isLittleO_const_mul_right_iff cne0]; rw [isLittleO_norm_right]

end SMulConst

section SMul

variable [Module R E'] [IsBoundedSMul R E'] [Module 𝕜' F'] [NormSMulClass 𝕜' F']
variable {k₁ : α -> R} {k₂ : α -> 𝕜'}

/--
theorem `IsBigOWith.smul` / 定理 `IsBigOWith.smul`

English:
theorem IsBigOWith.smul
  given: (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g')
  proof: by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_smul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_smul]; rw [mul_mul_mul_comm]

中文:
定理 IsBigOWith.smul
  条件: (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g')
  证明: by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_smul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_smul]; rw [mul_mul_mul_comm]

Depends on / 依赖: IsBigOWith_def, convert, filter_upwards, le_trans, mul_le_mul, mul_mul_mul_comm, norm_nonneg, norm_smul, norm_smul_le
-/
theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
    IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_smul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_smul]; rw [mul_mul_mul_comm]

/--
theorem `IsBigO.smul` / 定理 `IsBigO.smul`

English:
theorem IsBigO.smul
  given: (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g')
  proof: by
  obtain ⟨c₁, h₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, h₂⟩ := h₂.isBigOWith
  exact (h₁.smul h₂).isBigO

中文:
定理 IsBigO.smul
  条件: (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g')
  证明: by
  obtain ⟨c₁, h₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, h₂⟩ := h₂.isBigOWith
  exact (h₁.smul h₂).isBigO

Depends on / 依赖: isBigO, isBigOWith
-/
theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  obtain ⟨c₁, h₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, h₂⟩ := h₂.isBigOWith
  exact (h₁.smul h₂).isBigO

/--
theorem `IsBigO.smul_isLittleO` / 定理 `IsBigO.smul_isLittleO`

English:
theorem IsBigO.smul_isLittleO
  given: (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g')
  proof: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.smul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

中文:
定理 IsBigO.smul_isLittleO
  条件: (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g')
  证明: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.smul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

Depends on / 依赖: IsLittleO_def, congr_const, div_pos, exists_pos, ne_of_gt
-/
theorem IsBigO.smul_isLittleO (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.smul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

/--
theorem `IsLittleO.smul_isBigO` / 定理 `IsLittleO.smul_isBigO`

English:
theorem IsLittleO.smul_isBigO
  given: (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g')
  proof: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).smul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

中文:
定理 IsLittleO.smul_isBigO
  条件: (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g')
  证明: by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).smul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

Depends on / 依赖: IsLittleO_def, congr_const, div_pos, exists_pos, ne_of_gt
-/
theorem IsLittleO.smul_isBigO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).smul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

/--
theorem `IsLittleO.smul` / 定理 `IsLittleO.smul`

English:
theorem IsLittleO.smul
  given: (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g')
  proof: h₁.smul_isBigO h₂.isBigO

中文:
定理 IsLittleO.smul
  条件: (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g')
  证明: h₁.smul_isBigO h₂.isBigO

Depends on / 依赖: isBigO, smul_isBigO
-/
theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x :=
  h₁.smul_isBigO h₂.isBigO

end SMul

section Prod
variable {ι : Type*}

/--
theorem `IsBigO.listProd` / 定理 `IsBigO.listProd`

English:
theorem IsBigO.listProd
  statement: {L : List ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
  proof: by
  induction L with
  | nil => simp [isBoundedUnder_const]
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons] at hf ⊢
    exact hf.1.mul (ihL hf.2)

中文:
定理 IsBigO.listProd
  结论: {L : 列表 ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
  证明: by
  induction L with
  | nil => simp [isBoundedUnder_const]
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons] at hf ⊢
    exact hf.1.mul (ihL hf.2)

Depends on / 依赖: List.forall_mem_cons, List.map_cons, List.prod_cons, forall_mem_cons, isBoundedUnder_const, map_cons, prod_cons
-/
theorem IsBigO.listProd {L : List ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
    (hf : forall i in L, f i =O[l] g i) :
    (fun x => (L.map (f · x)).prod) =O[l] (fun x => (L.map (g · x)).prod) := by
  induction L with
  | nil => simp [isBoundedUnder_const]
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons] at hf ⊢
    exact hf.1.mul (ihL hf.2)

/--
theorem `IsBigO.multisetProd` / 定理 `IsBigO.multisetProd`

English:
theorem IsBigO.multisetProd
  statement: {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
  proof: by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsBigO.listProd hf

中文:
定理 IsBigO.multisetProd
  结论: {R 𝕜 : 类型} [SeminormedComm环 R] [赋范域 𝕜]
  证明: by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsBigO.listProd hf

Depends on / 依赖: IsBigO, IsBigO.listProd, Quotient, Quotient.mk_surjective, listProd, mk_surjective, mod_cast
-/
theorem IsBigO.multisetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Multiset ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜} (hf : forall i in s, f i =O[l] g i) :
    (fun x => (s.map (f · x)).prod) =O[l] (fun x => (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsBigO.listProd hf

/--
theorem `IsBigO.finsetProd` / 定理 `IsBigO.finsetProd`

English:
theorem IsBigO.finsetProd
  statement: {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
  proof: .multisetProd hf

中文:
定理 IsBigO.finsetProd
  结论: {R 𝕜 : 类型} [SeminormedComm环 R] [赋范域 𝕜]
  证明: .multisetProd hf

Depends on / 依赖: multisetProd
-/
theorem IsBigO.finsetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Finset ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
    (hf : forall i in s, f i =O[l] g i) : (∏ i in s, f i ·) =O[l] (∏ i in s, g i ·) :=
  .multisetProd hf

/--
theorem `IsLittleO.listProd` / 定理 `IsLittleO.listProd`

English:
theorem IsLittleO.listProd
  statement: {L : List ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
  proof: by
  induction L with
  | nil => simp at h₂
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons, List.exists_mem_cons_iff]
      at h₁ h₂ ⊢
    cases h₂ with
| inl hi => exact hi.mul_isBigO .listProd h₁.2
| inr hL => exact h₁.1.mul_isLittleO ihL h₁.2 hL

中文:
定理 IsLittleO.listProd
  结论: {L : 列表 ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
  证明: by
  induction L with
  | nil => simp at h₂
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons, List.exists_mem_cons_iff]
      at h₁ h₂ ⊢
    cases h₂ with
| inl hi => exact hi.mul_isBigO .listProd h₁.2
| inr hL => exact h₁.1.mul_isLittleO ihL h₁.2 hL

Depends on / 依赖: List.exists_mem_cons_iff, List.forall_mem_cons, List.map_cons, List.prod_cons, exists_mem_cons_iff, forall_mem_cons, hi.mul_isBigO, listProd, map_cons, mul_isBigO, mul_isLittleO, prod_cons
-/
theorem IsLittleO.listProd {L : List ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜}
    (h₁ : forall i in L, f i =O[l] g i) (h₂ : exists i in L, f i =o[l] g i) :
    (fun x => (L.map (f · x)).prod) =o[l] (fun x => (L.map (g · x)).prod) := by
  induction L with
  | nil => simp at h₂
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons, List.exists_mem_cons_iff]
      at h₁ h₂ ⊢
    cases h₂ with
| inl hi => exact hi.mul_isBigO .listProd h₁.2
| inr hL => exact h₁.1.mul_isLittleO ihL h₁.2 hL

/--
theorem `IsLittleO.multisetProd` / 定理 `IsLittleO.multisetProd`

English:
theorem IsLittleO.multisetProd
  statement: {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
  proof: by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsLittleO.listProd h₁ h₂

中文:
定理 IsLittleO.multisetProd
  结论: {R 𝕜 : 类型} [SeminormedComm环 R] [赋范域 𝕜]
  证明: by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsLittleO.listProd h₁ h₂

Depends on / 依赖: IsLittleO, IsLittleO.listProd, Quotient, Quotient.mk_surjective, listProd, mk_surjective, mod_cast
-/
theorem IsLittleO.multisetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Multiset ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜} (h₁ : forall i in s, f i =O[l] g i)
    (h₂ : exists i in s, f i =o[l] g i) :
    (fun x => (s.map (f · x)).prod) =o[l] (fun x => (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsLittleO.listProd h₁ h₂

/--
theorem `IsLittleO.finsetProd` / 定理 `IsLittleO.finsetProd`

English:
theorem IsLittleO.finsetProd
  statement: {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
  proof: .multisetProd h₁ h₂

中文:
定理 IsLittleO.finsetProd
  结论: {R 𝕜 : 类型} [SeminormedComm环 R] [赋范域 𝕜]
  证明: .multisetProd h₁ h₂

Depends on / 依赖: multisetProd
-/
theorem IsLittleO.finsetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Finset ι} {f : ι -> α -> R} {g : ι -> α -> 𝕜} (h₁ : forall i in s, f i =O[l] g i)
    (h₂ : exists i in s, f i =o[l] g i) : (∏ i in s, f i ·) =o[l] (∏ i in s, g i ·) :=
  .multisetProd h₁ h₂

end Prod


/--
theorem `IsLittleO.tendsto_div_nhds_zero` / 定理 `IsLittleO.tendsto_div_nhds_zero`

English:
theorem IsLittleO.tendsto_div_nhds_zero
  given: {f g : α -> 𝕜} (h : f =o[l] g)
  proof: (isLittleO_one_iff 𝕜).mp by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_isBigO (isBigO_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]

中文:
定理 IsLittleO.tendsto_div_nhds_zero
  条件: {f g : α -> 𝕜} (h : f =o[l] g)
  证明: (isLittleO_one_iff 𝕜).mp by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_isBigO (isBigO_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]

Depends on / 依赖: div_eq_mul_inv, div_self_le_one, h.mul_isBigO, isBigO_of_le, isBigO_refl, isLittleO_one_iff, mul_isBigO
-/
theorem IsLittleO.tendsto_div_nhds_zero {f g : α -> 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
(isLittleO_one_iff 𝕜).mp by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_isBigO (isBigO_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]

/--
theorem `IsLittleO.tendsto_inv_smul_nhds_zero` / 定理 `IsLittleO.tendsto_inv_smul_nhds_zero`

English:
theorem IsLittleO.tendsto_inv_smul_nhds_zero
  statement: [Module 𝕜 E'] [NormSMulClass 𝕜 E']
  proof: by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero

中文:
定理 IsLittleO.tendsto_inv_smul_nhds_zero
  结论: [模 𝕜 E'] [NormSMul类 𝕜 E']
  证明: by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero

Depends on / 依赖: div_eq_inv_mul, h.norm_norm.tendsto_div_nhds_zero, norm_inv, norm_norm, norm_smul, tendsto_div_nhds_zero, tendsto_zero_iff_norm_tendsto_zero
-/
theorem IsLittleO.tendsto_inv_smul_nhds_zero [Module 𝕜 E'] [NormSMulClass 𝕜 E']
    {f : α -> E'} {g : α -> 𝕜}
    {l : Filter α} (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero

/--
theorem `isLittleO_iff_tendsto'` / 定理 `isLittleO_iff_tendsto'`

English:
theorem isLittleO_iff_tendsto'
  given: {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f x = 0)
  proof: ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (Eventually.of_forall fun _x => one_mul _)⟩

中文:
定理 isLittleO_iff_tendsto'
  条件: {f g : α -> 𝕜} (hgf : 对任意ᶠ x in l, g x = 0 -> f x = 0)
  证明: ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (Eventually.of_forall fun _x => one_mul _)⟩

Depends on / 依赖: Eventually, Eventually.of_forall, IsLittleO, IsLittleO.tendsto_div_nhds_zero, div_mul_cancel_of_imp, hgf.mono, isBigO_refl, isLittleO_one_iff, mul_isBigO, of_forall, one_mul, tendsto_div_nhds_zero
-/
theorem isLittleO_iff_tendsto' {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (Eventually.of_forall fun _x => one_mul _)⟩

/--
theorem `isLittleO_iff_tendsto` / 定理 `isLittleO_iff_tendsto`

English:
theorem isLittleO_iff_tendsto
  given: {f g : α -> 𝕜} (hgf : forall x, g x = 0 -> f x = 0)
  proof: isLittleO_iff_tendsto' (Eventually.of_forall hgf)

alias ⟨_, isLittleO_of_tendsto'⟩ := isLittleO_iff_tendsto'

alias ⟨_, isLittleO_of_tendsto⟩ := isLittleO_iff_tendsto

中文:
定理 isLittleO_iff_tendsto
  条件: {f g : α -> 𝕜} (hgf : 对任意 x, g x = 0 -> f x = 0)
  证明: isLittleO_iff_tendsto' (Eventually.of_forall hgf)

alias ⟨_, isLittleO_of_tendsto'⟩ := isLittleO_iff_tendsto'

alias ⟨_, isLittleO_of_tendsto⟩ := isLittleO_iff_tendsto

Depends on / 依赖: Eventually, Eventually.of_forall, isLittleO_iff_tendsto, of_forall
-/
theorem isLittleO_iff_tendsto {f g : α -> 𝕜} (hgf : forall x, g x = 0 -> f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isLittleO_iff_tendsto' (Eventually.of_forall hgf)

alias ⟨_, isLittleO_of_tendsto'⟩ := isLittleO_iff_tendsto'

alias ⟨_, isLittleO_of_tendsto⟩ := isLittleO_iff_tendsto

/--
theorem `isLittleO_const_left_of_ne` / 定理 `isLittleO_const_left_of_ne`

English:
theorem isLittleO_const_left_of_ne
  given: {c : E''} (hc : c != 0)
  proof: by
  simp only [← isLittleO_one_left_iff Real]
  exact ⟨(isBigO_const_const (1 : Real) hc l).trans_isLittleO,
    (isBigO_const_one Real c l).trans_isLittleO⟩

@[simp]

中文:
定理 isLittleO_const_left_of_ne
  条件: {c : E''} (hc : c != 0)
  证明: by
  simp only [← isLittleO_one_left_iff Real]
  exact ⟨(isBigO_const_const (1 : Real) hc l).trans_isLittleO,
    (isBigO_const_one Real c l).trans_isLittleO⟩

@[simp]

Depends on / 依赖: isBigO_const_const, isBigO_const_one, isLittleO_one_left_iff, trans_isLittleO
-/
theorem isLittleO_const_left_of_ne {c : E''} (hc : c != 0) :
    (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop := by
  simp only [← isLittleO_one_left_iff Real]
  exact ⟨(isBigO_const_const (1 : Real) hc l).trans_isLittleO,
    (isBigO_const_one Real c l).trans_isLittleO⟩

@[simp]
/--
theorem `isLittleO_const_left` / 定理 `isLittleO_const_left`

English:
theorem isLittleO_const_left
  given: {c : E''}
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [isLittleO_zero, true_or]
  · simp only [hc, false_or, isLittleO_const_left_of_ne hc]; rfl

@[simp high] -- Increase priority so that this triggers before `isLittleO_const_left`

中文:
定理 isLittleO_const_left
  条件: {c : E''}
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [isLittleO_zero, true_or]
  · simp only [hc, false_or, isLittleO_const_left_of_ne hc]; rfl

@[simp high] -- Increase priority so that this triggers before `isLittleO_const_left`

Depends on / 依赖: eq_or_ne, false_or, isLittleO_const_left_of_ne, isLittleO_zero, true_or
-/
theorem isLittleO_const_left {c : E''} :
    (fun _x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [isLittleO_zero, true_or]
  · simp only [hc, false_or, isLittleO_const_left_of_ne hc]; rfl

@[simp high] -- Increase priority so that this triggers before `isLittleO_const_left`
/--
theorem `isLittleO_const_const_iff` / 定理 `isLittleO_const_const_iff`

English:
theorem isLittleO_const_const_iff
  given: [NeBot l] {d : E''} {c : F''}
  proof: by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [isLittleO_const_left, or_iff_left_iff_imp]
  exact fun h => (this h).elim

@[simp]

中文:
定理 isLittleO_const_const_iff
  条件: [NeBot l] {d : E''} {c : F''}
  证明: by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [isLittleO_const_left, or_iff_left_iff_imp]
  exact fun h => (this h).elim

@[simp]

Depends on / 依赖: Function, Function.const, Tendsto, isLittleO_const_left, not_tendsto_atTop_of_tendsto_nhds, or_iff_left_iff_imp, tendsto_const_nhds
-/
theorem isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun _x => d) =o[l] fun _x => c) ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [isLittleO_const_left, or_iff_left_iff_imp]
  exact fun h => (this h).elim

@[simp]
/--
theorem `isLittleO_pure` / 定理 `isLittleO_pure`

English:
theorem isLittleO_pure
  given: {x}
  statement: f'' =o[pure x] g'' ↔ f'' x = 0
  proof: calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff

中文:
定理 isLittleO_pure
  条件: {x}
  结论: f'' =o[pure x] g'' ↔ f'' x = 0
  证明: calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff

Depends on / 依赖: isLittleO_congr, isLittleO_const_const_iff
-/
theorem isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff

/--
theorem `isLittleO_const_id_cobounded` / 定理 `isLittleO_const_id_cobounded`

English:
theorem isLittleO_const_id_cobounded
  given: (c : F'')
  proof: isLittleO_const_left.2 .inr tendsto_norm_cobounded_atTop

中文:
定理 isLittleO_const_id_cobounded
  条件: (c : F'')
  证明: isLittleO_const_left.2 .inr tendsto_norm_cobounded_atTop

Depends on / 依赖: isLittleO_const_left, tendsto_norm_cobounded_atTop
-/
theorem isLittleO_const_id_cobounded (c : F'') :
    (fun _ => c) =o[Bornology.cobounded E''] id :=
isLittleO_const_left.2 .inr tendsto_norm_cobounded_atTop

/--
theorem `isLittleO_const_id_atTop` / 定理 `isLittleO_const_id_atTop`

English:
theorem isLittleO_const_id_atTop
  given: (c : E'')
  statement: (fun _x : Real => c) =o[atTop] id
  proof: isLittleO_const_left.2 Or.inr tendsto_abs_atTop_atTop

中文:
定理 isLittleO_const_id_atTop
  条件: (c : E'')
  结论: (fun _x : 实数 => c) =o[atTop] id
  证明: isLittleO_const_left.2 Or.inr tendsto_abs_atTop_atTop

Depends on / 依赖: Or.inr, isLittleO_const_left, tendsto_abs_atTop_atTop
-/
theorem isLittleO_const_id_atTop (c : E'') : (fun _x : Real => c) =o[atTop] id :=
isLittleO_const_left.2 Or.inr tendsto_abs_atTop_atTop

/--
theorem `isLittleO_const_id_atBot` / 定理 `isLittleO_const_id_atBot`

English:
theorem isLittleO_const_id_atBot
  given: (c : E'')
  statement: (fun _x : Real => c) =o[atBot] id
  proof: isLittleO_const_left.2 Or.inr tendsto_abs_atBot_atTop

中文:
定理 isLittleO_const_id_atBot
  条件: (c : E'')
  结论: (fun _x : 实数 => c) =o[atBot] id
  证明: isLittleO_const_left.2 Or.inr tendsto_abs_atBot_atTop

Depends on / 依赖: Or.inr, isLittleO_const_left, tendsto_abs_atBot_atTop
-/
theorem isLittleO_const_id_atBot (c : E'') : (fun _x : Real => c) =o[atBot] id :=
isLittleO_const_left.2 Or.inr tendsto_abs_atBot_atTop

/-! ### Relation between `f = o(g)` and `g / f → ∞` -/

section div_tendsto_infty

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α -> 𝕜}

/--
theorem `IsLittleO.of_tendsto_div_atTop` / 定理 `IsLittleO.of_tendsto_div_atTop`

English:
theorem IsLittleO.of_tendsto_div_atTop
  given: (h : Tendsto (fun x => g x / f x) l atTop)
  statement: f =o[l] g
  proof: by
  apply Asymptotics.isLittleO_of_tendsto'
  · apply (Filter.Tendsto.eventually_ge_atTop h 1).mono
    intro x h h0
    simp only [h0, zero_div] at h
    grind
  · convert! Tendsto.comp tendsto_inv_atTop_zero h
    simp

中文:
定理 IsLittleO.of_tendsto_div_atTop
  条件: (h : 收敛 (fun x => g x / f x) l atTop)
  结论: f =o[l] g
  证明: by
  apply Asymptotics.isLittleO_of_tendsto'
  · apply (Filter.Tendsto.eventually_ge_atTop h 1).mono
    intro x h h0
    simp only [h0, zero_div] at h
    grind
  · convert! Tendsto.comp tendsto_inv_atTop_zero h
    simp

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_of_tendsto, Filter, Filter.Tendsto.eventually_ge_atTop, Tendsto, Tendsto.comp, convert, eventually_ge_atTop, isLittleO_of_tendsto, tendsto_inv_atTop_zero, zero_div
-/
theorem IsLittleO.of_tendsto_div_atTop (h : Tendsto (fun x => g x / f x) l atTop) : f =o[l] g := by
  apply Asymptotics.isLittleO_of_tendsto'
  · apply (Filter.Tendsto.eventually_ge_atTop h 1).mono
    intro x h h0
    simp only [h0, zero_div] at h
    grind
  · convert! Tendsto.comp tendsto_inv_atTop_zero h
    simp

/--
theorem `IsLittleO.of_tendsto_div_atBot` / 定理 `IsLittleO.of_tendsto_div_atBot`

English:
theorem IsLittleO.of_tendsto_div_atBot
  given: (h : Tendsto (fun x => g x / f x) l atBot)
  statement: f =o[l] g
  proof: by
  refine IsLittleO.of_neg_left (IsLittleO.of_tendsto_div_atTop ?_)
  rw [← tendsto_neg_atBot_iff]
  convert h
  simp [div_neg_eq_neg_div]

中文:
定理 IsLittleO.of_tendsto_div_atBot
  条件: (h : 收敛 (fun x => g x / f x) l atBot)
  结论: f =o[l] g
  证明: by
  refine IsLittleO.of_neg_left (IsLittleO.of_tendsto_div_atTop ?_)
  rw [← tendsto_neg_atBot_iff]
  convert h
  simp [div_neg_eq_neg_div]

Depends on / 依赖: IsLittleO, IsLittleO.of_neg_left, IsLittleO.of_tendsto_div_atTop, convert, div_neg_eq_neg_div, of_neg_left, of_tendsto_div_atTop, tendsto_neg_atBot_iff
-/
theorem IsLittleO.of_tendsto_div_atBot (h : Tendsto (fun x => g x / f x) l atBot) : f =o[l] g := by
  refine IsLittleO.of_neg_left (IsLittleO.of_tendsto_div_atTop ?_)
  rw [← tendsto_neg_atBot_iff]
  convert h
  simp [div_neg_eq_neg_div]

end div_tendsto_infty

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `NormedField`. -/

section ExistsMulEq

variable {u v : α -> 𝕜}

/--
theorem `isBigOWith_of_eq_mul` / 定理 `isBigOWith_of_eq_mul`

English:
theorem isBigOWith_of_eq_mul
  statement: {u v : α -> R} (φ : α -> R) (hφ : forallᶠ x in l, ‖φ x‖ <= c)
  proof: by
  simp only [IsBigOWith_def]
  refine h.symm.rw (fun x a => ‖a‖ <= c * ‖v x‖) (hφ.mono fun x hx => ?_)
  simp only [Pi.mul_apply]
  refine (norm_mul_le _ _).trans ?_
  gcongr

中文:
定理 isBigOWith_of_eq_mul
  结论: {u v : α -> R} (φ : α -> R) (hφ : 对任意ᶠ x in l, ‖φ x‖ <= c)
  证明: by
  simp only [IsBigOWith_def]
  refine h.symm.rw (fun x a => ‖a‖ <= c * ‖v x‖) (hφ.mono fun x hx => ?_)
  simp only [Pi.mul_apply]
  refine (norm_mul_le _ _).trans ?_
  gcongr

Depends on / 依赖: IsBigOWith_def, Pi.mul_apply, h.symm.rw, mul_apply, norm_mul_le
-/
theorem isBigOWith_of_eq_mul {u v : α -> R} (φ : α -> R) (hφ : forallᶠ x in l, ‖φ x‖ <= c)
    (h : u =ᶠ[l] φ * v) :
    IsBigOWith c l u v := by
  simp only [IsBigOWith_def]
  refine h.symm.rw (fun x a => ‖a‖ <= c * ‖v x‖) (hφ.mono fun x hx => ?_)
  simp only [Pi.mul_apply]
  refine (norm_mul_le _ _).trans ?_
  gcongr

/--
theorem `isBigOWith_iff_exists_eq_mul` / 定理 `isBigOWith_iff_exists_eq_mul`

English:
theorem isBigOWith_iff_exists_eq_mul
  given: (hc : 0 <= c)
  proof: by
  constructor
  · intro h
    use fun x => u x / v x
    refine ⟨Eventually.mono h.bound fun y hy => ?_, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_le_mul₀ (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact isBigOWith_of_eq_mul φ hφ h

中文:
定理 isBigOWith_iff_存在_eq_mul
  条件: (hc : 0 <= c)
  证明: by
  constructor
  · intro h
    use fun x => u x / v x
    refine ⟨Eventually.mono h.bound fun y hy => ?_, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_le_mul₀ (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact isBigOWith_of_eq_mul φ hφ h

Depends on / 依赖: Eventually, Eventually.mono, eventually_mul_div_cancel, h.bound, h.eventually_mul_div_cancel.symm, isBigOWith_of_eq_mul, norm_nonneg
-/
theorem isBigOWith_iff_exists_eq_mul (hc : 0 <= c) :
    IsBigOWith c l u v ↔ exists φ : α -> 𝕜, (forallᶠ x in l, ‖φ x‖ <= c) ∧ u =ᶠ[l] φ * v := by
  constructor
  · intro h
    use fun x => u x / v x
    refine ⟨Eventually.mono h.bound fun y hy => ?_, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_le_mul₀ (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact isBigOWith_of_eq_mul φ hφ h

/--
theorem `IsBigOWith.exists_eq_mul` / 定理 `IsBigOWith.exists_eq_mul`

English:
theorem IsBigOWith.exists_eq_mul
  given: (h : IsBigOWith c l u v) (hc : 0 <= c)
  proof: (isBigOWith_iff_exists_eq_mul hc).mp h

中文:
定理 IsBigOWith.存在_eq_mul
  条件: (h : IsBigOWith c l u v) (hc : 0 <= c)
  证明: (isBigOWith_iff_exists_eq_mul hc).mp h

Depends on / 依赖: isBigOWith_iff_exists_eq_mul
-/
theorem IsBigOWith.exists_eq_mul (h : IsBigOWith c l u v) (hc : 0 <= c) :
    exists φ : α -> 𝕜, (forallᶠ x in l, ‖φ x‖ <= c) ∧ u =ᶠ[l] φ * v :=
  (isBigOWith_iff_exists_eq_mul hc).mp h

/--
theorem `isBigO_iff_exists_eq_mul` / 定理 `isBigO_iff_exists_eq_mul`

English:
theorem isBigO_iff_exists_eq_mul
  proof: by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact isBigO_iff_isBigOWith.2 ⟨c, isBigOWith_of_eq_mul φ hφ huvφ⟩

alias ⟨IsBigO.exists_eq_mul, _⟩ := isBigO_

中文:
定理 isBigO_iff_存在_eq_mul
  证明: by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact isBigO_iff_isBigOWith.2 ⟨c, isBigOWith_of_eq_mul φ hφ huvφ⟩

alias ⟨IsBigO.exists_eq_mul, _⟩ := isBigO_

Depends on / 依赖: exists_eq_mul, exists_nonneg, h.exists_nonneg, hc.exists_eq_mul, isBigOWith_of_eq_mul, isBigO_iff_isBigOWith
-/
theorem isBigO_iff_exists_eq_mul :
    u =O[l] v ↔ exists φ : α -> 𝕜, l.IsBoundedUnder (· <= ·) (norm ∘ φ) ∧ u =ᶠ[l] φ * v := by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact isBigO_iff_isBigOWith.2 ⟨c, isBigOWith_of_eq_mul φ hφ huvφ⟩

alias ⟨IsBigO.exists_eq_mul, _⟩ := isBigO_iff_exists_eq_mul

/--
theorem `isLittleO_iff_exists_eq_mul` / 定理 `isLittleO_iff_exists_eq_mul`

English:
theorem isLittleO_iff_exists_eq_mul
  proof: by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · simp only [IsLittleO_def]
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddGroup.tendsto_nhds_zero] at hφ
    exact isBigOWith_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ

中文:
定理 isLittleO_iff_存在_eq_mul
  证明: by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · simp only [IsLittleO_def]
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddGroup.tendsto_nhds_zero] at hφ
    exact isBigOWith_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ

Depends on / 依赖: IsLittleO_def, NormedAddGroup, NormedAddGroup.tendsto_nhds_zero, eventually_mul_div_cancel, h.eventually_mul_div_cancel.symm, h.tendsto_div_nhds_zero, isBigOWith_of_eq_mul, le_of_lt, tendsto_div_nhds_zero, tendsto_nhds_zero
-/
theorem isLittleO_iff_exists_eq_mul :
    u =o[l] v ↔ exists φ : α -> 𝕜, Tendsto φ l (𝓝 0) ∧ u =ᶠ[l] φ * v := by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · simp only [IsLittleO_def]
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddGroup.tendsto_nhds_zero] at hφ
    exact isBigOWith_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ

alias ⟨IsLittleO.exists_eq_mul, _⟩ := isLittleO_iff_exists_eq_mul

end ExistsMulEq


/--
theorem `div_isBoundedUnder_of_isBigO` / 定理 `div_isBoundedUnder_of_isBigO`

English:
theorem div_isBoundedUnder_of_isBigO
  given: {α : Type*} {l : Filter α} {f g : α -> 𝕜} (h : f =O[l] g)
  proof: by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine ⟨c, eventually_map.2 (hc.bound.mono fun x hx => ?_)⟩
  rw [norm_div]
  exact div_le_of_le_mul₀ (norm_nonneg _) h₀ hx

中文:
定理 div_isBoundedUnder_of_isBigO
  条件: {α : 类型} {l : 滤子 α} {f g : α -> 𝕜} (h : f =O[l] g)
  证明: by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine ⟨c, eventually_map.2 (hc.bound.mono fun x hx => ?_)⟩
  rw [norm_div]
  exact div_le_of_le_mul₀ (norm_nonneg _) h₀ hx

Depends on / 依赖: eventually_map, exists_nonneg, h.exists_nonneg, hc.bound.mono, norm_div, norm_nonneg
-/
theorem div_isBoundedUnder_of_isBigO {α : Type*} {l : Filter α} {f g : α -> 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· <= ·) l fun x => ‖f x / g x‖ := by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine ⟨c, eventually_map.2 (hc.bound.mono fun x hx => ?_)⟩
  rw [norm_div]
  exact div_le_of_le_mul₀ (norm_nonneg _) h₀ hx

/--
theorem `isBigO_iff_div_isBoundedUnder` / 定理 `isBigO_iff_div_isBoundedUnder`

English:
theorem isBigO_iff_div_isBoundedUnder
  statement: {α : Type*} {l : Filter α} {f g : α -> 𝕜}
  proof: by
  refine ⟨div_isBoundedUnder_of_isBigO, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine IsBigO.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => ?_)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff₀ (norm_pos_iff.2 hgx)).mp hx₂

中文:
定理 isBigO_iff_div_isBoundedUnder
  结论: {α : 类型} {l : 滤子 α} {f g : α -> 𝕜}
  证明: by
  refine ⟨div_isBoundedUnder_of_isBigO, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine IsBigO.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => ?_)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff₀ (norm_pos_iff.2 hgx)).mp hx₂

Depends on / 依赖: IsBigO, IsBigO.of_bound, div_isBoundedUnder_of_isBigO, eventually_map, hc.mp, hgf.mono, norm_div, norm_pos_iff, of_bound
-/
theorem isBigO_iff_div_isBoundedUnder {α : Type*} {l : Filter α} {f g : α -> 𝕜}
    (hgf : forallᶠ x in l, g x = 0 -> f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· <= ·) l fun x => ‖f x / g x‖ := by
  refine ⟨div_isBoundedUnder_of_isBigO, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine IsBigO.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => ?_)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff₀ (norm_pos_iff.2 hgx)).mp hx₂

/--
theorem `isBigO_of_div_tendsto_nhds` / 定理 `isBigO_of_div_tendsto_nhds`

English:
theorem isBigO_of_div_tendsto_nhds
  statement: {α : Type*} {l : Filter α} {f g : α -> 𝕜}
  proof: (isBigO_iff_div_isBoundedUnder hgf).2 H.norm.isBoundedUnder_le

中文:
定理 isBigO_of_div_tendsto_nhds
  结论: {α : 类型} {l : 滤子 α} {f g : α -> 𝕜}
  证明: (isBigO_iff_div_isBoundedUnder hgf).2 H.norm.isBoundedUnder_le

Depends on / 依赖: H.norm.isBoundedUnder_le, isBigO_iff_div_isBoundedUnder, isBoundedUnder_le
-/
theorem isBigO_of_div_tendsto_nhds {α : Type*} {l : Filter α} {f g : α -> 𝕜}
    (hgf : forallᶠ x in l, g x = 0 -> f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) :
    f =O[l] g :=
(isBigO_iff_div_isBoundedUnder hgf).2 H.norm.isBoundedUnder_le

/--
theorem `IsLittleO.tendsto_zero_of_tendsto` / 定理 `IsLittleO.tendsto_zero_of_tendsto`

English:
theorem IsLittleO.tendsto_zero_of_tendsto
  statement: {u : α -> E'} {v : α -> 𝕜} {l : Filter α} {y : 𝕜}
  proof: by
  suffices h : u =o[l] fun _x => (1 : 𝕜) by
    rwa [isLittleO_one_iff] at h
  exact huv.trans_isBigO (hv.isBigO_one 𝕜)

中文:
定理 IsLittleO.tendsto_zero_of_tendsto
  结论: {u : α -> E'} {v : α -> 𝕜} {l : 滤子 α} {y : 𝕜}
  证明: by
  suffices h : u =o[l] fun _x => (1 : 𝕜) by
    rwa [isLittleO_one_iff] at h
  exact huv.trans_isBigO (hv.isBigO_one 𝕜)

Depends on / 依赖: huv.trans_isBigO, hv.isBigO_one, isBigO_one, isLittleO_one_iff, trans_isBigO
-/
theorem IsLittleO.tendsto_zero_of_tendsto {u : α -> E'} {v : α -> 𝕜} {l : Filter α} {y : 𝕜}
    (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun _x => (1 : 𝕜) by
    rwa [isLittleO_one_iff] at h
  exact huv.trans_isBigO (hv.isBigO_one 𝕜)

/--
theorem `isBigOWith_of_div_tendsto_nhds` / 定理 `isBigOWith_of_div_tendsto_nhds`

English:
theorem isBigOWith_of_div_tendsto_nhds
  statement: {C : Real} {a : 𝕜} {f g : α -> 𝕜} {l : Filter α}
  proof: by
  simp only [IsBigOWith]
  apply (((continuous_norm.tendsto _).comp h).eventually_const_le ha).mono
  intro x hx
  simp only [Function.comp_apply, norm_div] at hx
  by_cases hf : f x = 0
  · simp [hf] at hx
    linarith
  rw [le_div_iff₀ (by positivity)] at hx
  field_simp at hx
  exact hx

中文:
定理 isBigOWith_of_div_tendsto_nhds
  结论: {C : 实数} {a : 𝕜} {f g : α -> 𝕜} {l : 滤子 α}
  证明: by
  simp only [IsBigOWith]
  apply (((continuous_norm.tendsto _).comp h).eventually_const_le ha).mono
  intro x hx
  simp only [Function.comp_apply, norm_div] at hx
  by_cases hf : f x = 0
  · simp [hf] at hx
    linarith
  rw [le_div_iff₀ (by positivity)] at hx
  field_simp at hx
  exact hx

Depends on / 依赖: Function, Function.comp_apply, IsBigOWith, comp_apply, continuous_norm, continuous_norm.tendsto, eventually_const_le, norm_div, tendsto
-/
theorem isBigOWith_of_div_tendsto_nhds {C : Real} {a : 𝕜} {f g : α -> 𝕜} {l : Filter α}
    (h : Tendsto (fun x => g x / f x) l (𝓝 a)) (hC : 0 < C) (ha : C⁻¹ < ‖a‖) :
    IsBigOWith C l f g := by
  simp only [IsBigOWith]
  apply (((continuous_norm.tendsto _).comp h).eventually_const_le ha).mono
  intro x hx
  simp only [Function.comp_apply, norm_div] at hx
  by_cases hf : f x = 0
  · simp [hf] at hx
    linarith
  rw [le_div_iff₀ (by positivity)] at hx
  field_simp at hx
  exact hx

/--
theorem `isBigO_of_div_tendsto_nhds_of_ne_zero` / 定理 `isBigO_of_div_tendsto_nhds_of_ne_zero`

English:
theorem isBigO_of_div_tendsto_nhds_of_ne_zero
  statement: {l : Filter α} {f g : α -> 𝕜}
  proof: by
  obtain ⟨C, hC, ha⟩ : exists C, 0 < C ∧ C⁻¹ < ‖a‖ := ⟨‖a‖⁻¹ + 1, by positivity, by field_simp; simpa⟩
  simp only [IsBigO]
  exact ⟨C, isBigOWith_of_div_tendsto_nhds h hC ha⟩

中文:
定理 isBigO_of_div_tendsto_nhds_of_ne_zero
  结论: {l : 滤子 α} {f g : α -> 𝕜}
  证明: by
  obtain ⟨C, hC, ha⟩ : exists C, 0 < C ∧ C⁻¹ < ‖a‖ := ⟨‖a‖⁻¹ + 1, by positivity, by field_simp; simpa⟩
  simp only [IsBigO]
  exact ⟨C, isBigOWith_of_div_tendsto_nhds h hC ha⟩

Depends on / 依赖: IsBigO, isBigOWith_of_div_tendsto_nhds
-/
theorem isBigO_of_div_tendsto_nhds_of_ne_zero {l : Filter α} {f g : α -> 𝕜}
    {a : 𝕜} (h : Tendsto (fun x => g x / f x) l (𝓝 a)) (ha : a != 0) :
    f =O[l] g := by
  obtain ⟨C, hC, ha⟩ : exists C, 0 < C ∧ C⁻¹ < ‖a‖ := ⟨‖a‖⁻¹ + 1, by positivity, by field_simp; simpa⟩
  simp only [IsBigO]
  exact ⟨C, isBigOWith_of_div_tendsto_nhds h hC ha⟩

/--
theorem `isLittleO_pow_pow` / 定理 `isLittleO_pow_pow`

English:
theorem isLittleO_pow_pow
  given: {m n : Nat} (h : m < n)
  statement: (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
  proof: by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact IsBigO.mul_isLittleO (isBigO_refl _ _)
    (IsLittleO.pow ((isLittleO_one_iff _).2 tendsto_id) hp0)

中文:
定理 isLittleO_pow_pow
  条件: {m n : 自然数} (h : m < n)
  结论: (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
  证明: by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact IsBigO.mul_isLittleO (isBigO_refl _ _)
    (IsLittleO.pow ((isLittleO_one_iff _).2 tendsto_id) hp0)

Depends on / 依赖: IsBigO, IsBigO.mul_isLittleO, IsLittleO, IsLittleO.pow, isBigO_refl, isLittleO_one_iff, lt_iff_exists_add, mul_isLittleO, mul_one, one_pow, pow_add, tendsto_id
-/
theorem isLittleO_pow_pow {m n : Nat} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m := by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact IsBigO.mul_isLittleO (isBigO_refl _ _)
    (IsLittleO.pow ((isLittleO_one_iff _).2 tendsto_id) hp0)

/--
theorem `isLittleO_norm_pow_norm_pow` / 定理 `isLittleO_norm_pow_norm_pow`

English:
theorem isLittleO_norm_pow_norm_pow
  given: {m n : Nat} (h : m < n)
  proof: (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero

中文:
定理 isLittleO_norm_pow_norm_pow
  条件: {m n : 自然数} (h : m < n)
  证明: (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero

Depends on / 依赖: comp_tendsto, isLittleO_pow_pow, tendsto_norm_zero
-/
theorem isLittleO_norm_pow_norm_pow {m n : Nat} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero

/--
theorem `isLittleO_pow_id` / 定理 `isLittleO_pow_id`

English:
theorem isLittleO_pow_id
  given: {n : Nat} (h : 1 < n)
  statement: (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x
  proof: by
  convert! isLittleO_pow_pow h (𝕜 := 𝕜)
  simp only [pow_one]

中文:
定理 isLittleO_pow_id
  条件: {n : 自然数} (h : 1 < n)
  结论: (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x
  证明: by
  convert! isLittleO_pow_pow h (𝕜 := 𝕜)
  simp only [pow_one]

Depends on / 依赖: convert, isLittleO_pow_pow, pow_one
-/
theorem isLittleO_pow_id {n : Nat} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert! isLittleO_pow_pow h (𝕜 := 𝕜)
  simp only [pow_one]

/--
theorem `isLittleO_norm_pow_id` / 定理 `isLittleO_norm_pow_id`

English:
theorem isLittleO_norm_pow_id
  given: {n : Nat} (h : 1 < n)
  proof: by
  have := @isLittleO_norm_pow_norm_pow E' _ _ _ h
  simp only [pow_one] at this
  exact isLittleO_norm_right.mp this

中文:
定理 isLittleO_norm_pow_id
  条件: {n : 自然数} (h : 1 < n)
  证明: by
  have := @isLittleO_norm_pow_norm_pow E' _ _ _ h
  simp only [pow_one] at this
  exact isLittleO_norm_right.mp this

Depends on / 依赖: isLittleO_norm_pow_norm_pow, isLittleO_norm_right, isLittleO_norm_right.mp, pow_one
-/
theorem isLittleO_norm_pow_id {n : Nat} (h : 1 < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  have := @isLittleO_norm_pow_norm_pow E' _ _ _ h
  simp only [pow_one] at this
  exact isLittleO_norm_right.mp this

/--
theorem `IsBigO.eq_zero_of_norm_pow_within` / 定理 `IsBigO.eq_zero_of_norm_pow_within`

English:
theorem IsBigO.eq_zero_of_norm_pow_within
  statement: {f : E'' -> F''} {s : Set E''} {x₀ : E''} {n : Nat}
  proof: mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp by simp_rw [sub_self, norm_zero, zero_pow hn]

中文:
定理 IsBigO.eq_zero_of_norm_pow_within
  结论: {f : E'' -> F''} {s : 集合 E''} {x₀ : E''} {n : 自然数}
  证明: mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp by simp_rw [sub_self, norm_zero, zero_pow hn]

Depends on / 依赖: eq_zero_imp, h.eq_zero_imp, mem_of_mem_nhdsWithin, norm_zero, simp_rw, sub_self, zero_pow
-/
theorem IsBigO.eq_zero_of_norm_pow_within {f : E'' -> F''} {s : Set E''} {x₀ : E''} {n : Nat}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ in s) (hn : n != 0) : f x₀ = 0 :=
mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp by simp_rw [sub_self, norm_zero, zero_pow hn]

/--
theorem `IsBigO.eq_zero_of_norm_pow` / 定理 `IsBigO.eq_zero_of_norm_pow`

English:
theorem IsBigO.eq_zero_of_norm_pow
  statement: {f : E'' -> F''} {x₀ : E''} {n : Nat}
  proof: by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn

中文:
定理 IsBigO.eq_zero_of_norm_pow
  结论: {f : E'' -> F''} {x₀ : E''} {n : 自然数}
  证明: by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn

Depends on / 依赖: eq_zero_of_norm_pow_within, h.eq_zero_of_norm_pow_within, mem_univ, nhdsWithin_univ
-/
theorem IsBigO.eq_zero_of_norm_pow {f : E'' -> F''} {x₀ : E''} {n : Nat}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : n != 0) : f x₀ = 0 := by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn

/--
theorem `isLittleO_pow_sub_pow_sub` / 定理 `isLittleO_pow_sub_pow_sub`

English:
theorem isLittleO_pow_sub_pow_sub
  given: (x₀ : E') {n m : Nat} (h : n < m)
  proof: (isLittleO_pow_pow h).comp_tendsto (tendsto_norm_sub_self x₀)

中文:
定理 isLittleO_pow_sub_pow_sub
  条件: (x₀ : E') {n m : 自然数} (h : n < m)
  证明: (isLittleO_pow_pow h).comp_tendsto (tendsto_norm_sub_self x₀)

Depends on / 依赖: comp_tendsto, isLittleO_pow_pow, tendsto_norm_sub_self
-/
theorem isLittleO_pow_sub_pow_sub (x₀ : E') {n m : Nat} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  (isLittleO_pow_pow h).comp_tendsto (tendsto_norm_sub_self x₀)

/--
theorem `isLittleO_pow_sub_sub` / 定理 `isLittleO_pow_sub_sub`

English:
theorem isLittleO_pow_sub_sub
  given: (x₀ : E') {m : Nat} (h : 1 < m)
  proof: by
  simpa only [isLittleO_norm_right, pow_one] using isLittleO_pow_sub_pow_sub x₀ h

中文:
定理 isLittleO_pow_sub_sub
  条件: (x₀ : E') {m : 自然数} (h : 1 < m)
  证明: by
  simpa only [isLittleO_norm_right, pow_one] using isLittleO_pow_sub_pow_sub x₀ h

Depends on / 依赖: isLittleO_norm_right, isLittleO_pow_sub_pow_sub, pow_one
-/
theorem isLittleO_pow_sub_sub (x₀ : E') {m : Nat} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [isLittleO_norm_right, pow_one] using isLittleO_pow_sub_pow_sub x₀ h

/--
theorem `IsBigOWith.right_le_sub_of_lt_one` / 定理 `IsBigOWith.right_le_sub_of_lt_one`

English:
theorem IsBigOWith.right_le_sub_of_lt_one
  given: {f₁ f₂ : α -> E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1)
  proof: IsBigOWith.of_bound
    mem_of_superset h.bound fun x hx => by
      simp only [mem_ofPred_eq] at hx ⊢
      rw [mul_comm]; rw [one_div]; rw [← div_eq_mul_inv]; rw [le_div_iff₀]; rw [mul_sub]; rw [mul_one]; rw [mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · ex

中文:
定理 IsBigOWith.right_le_sub_of_lt_one
  条件: {f₁ f₂ : α -> E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1)
  证明: IsBigOWith.of_bound
    mem_of_superset h.bound fun x hx => by
      simp only [mem_ofPred_eq] at hx ⊢
      rw [mul_comm]; rw [one_div]; rw [← div_eq_mul_inv]; rw [le_div_iff₀]; rw [mul_sub]; rw [mul_one]; rw [mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · ex

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, div_eq_mul_inv, h.bound, le_trans, mem_ofPred_eq, mem_of_superset, mul_comm, mul_one, mul_sub, norm_sub_norm_le, of_bound, one_div, sub_le_sub_left, sub_pos
-/
theorem IsBigOWith.right_le_sub_of_lt_one {f₁ f₂ : α -> E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
IsBigOWith.of_bound
    mem_of_superset h.bound fun x hx => by
      simp only [mem_ofPred_eq] at hx ⊢
      rw [mul_comm]; rw [one_div]; rw [← div_eq_mul_inv]; rw [le_div_iff₀]; rw [mul_sub]; rw [mul_one]; rw [mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc

/--
theorem `IsBigOWith.right_le_add_of_lt_one` / 定理 `IsBigOWith.right_le_add_of_lt_one`

English:
theorem IsBigOWith.right_le_add_of_lt_one
  given: {f₁ f₂ : α -> E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1)
  proof: (h.neg_right.right_le_sub_of_lt_one hc).neg_right.of_neg_left.congr rfl (fun _ => rfl) fun x => by
    rw [neg_sub]; rw [sub_neg_eq_add]

中文:
定理 IsBigOWith.right_le_add_of_lt_one
  条件: {f₁ f₂ : α -> E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1)
  证明: (h.neg_right.right_le_sub_of_lt_one hc).neg_right.of_neg_left.congr rfl (fun _ => rfl) fun x => by
    rw [neg_sub]; rw [sub_neg_eq_add]

Depends on / 依赖: h.neg_right.right_le_sub_of_lt_one, neg_right, neg_right.of_neg_left.congr, neg_sub, of_neg_left, right_le_sub_of_lt_one, sub_neg_eq_add
-/
theorem IsBigOWith.right_le_add_of_lt_one {f₁ f₂ : α -> E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_one hc).neg_right.of_neg_left.congr rfl (fun _ => rfl) fun x => by
    rw [neg_sub]; rw [sub_neg_eq_add]

/--
theorem `IsLittleO.right_isBigO_sub` / 定理 `IsLittleO.right_isBigO_sub`

English:
theorem IsLittleO.right_isBigO_sub
  given: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  proof: ((h.def' one_half_pos).right_le_sub_of_lt_one one_half_lt_one).isBigO

中文:
定理 IsLittleO.right_isBigO_sub
  条件: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  证明: ((h.def' one_half_pos).right_le_sub_of_lt_one one_half_lt_one).isBigO

Depends on / 依赖: h.def, isBigO, one_half_lt_one, one_half_pos, right_le_sub_of_lt_one
-/
theorem IsLittleO.right_isBigO_sub {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_one one_half_lt_one).isBigO

/--
theorem `IsLittleO.right_isBigO_add` / 定理 `IsLittleO.right_isBigO_add`

English:
theorem IsLittleO.right_isBigO_add
  given: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  proof: ((h.def' one_half_pos).right_le_add_of_lt_one one_half_lt_one).isBigO

中文:
定理 IsLittleO.right_isBigO_add
  条件: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  证明: ((h.def' one_half_pos).right_le_add_of_lt_one one_half_lt_one).isBigO

Depends on / 依赖: h.def, isBigO, one_half_lt_one, one_half_pos, right_le_add_of_lt_one
-/
theorem IsLittleO.right_isBigO_add {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_one one_half_lt_one).isBigO

/--
theorem `IsLittleO.right_isBigO_add'` / 定理 `IsLittleO.right_isBigO_add'`

English:
theorem IsLittleO.right_isBigO_add'
  given: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  proof: add_comm f₁ f₂ ▸ h.right_isBigO_add

中文:
定理 IsLittleO.right_isBigO_add'
  条件: {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂)
  证明: add_comm f₁ f₂ ▸ h.right_isBigO_add

Depends on / 依赖: add_comm, h.right_isBigO_add, right_isBigO_add
-/
theorem IsLittleO.right_isBigO_add' {f₁ f₂ : α -> E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] (f₂ + f₁) :=
  add_comm f₁ f₂ ▸ h.right_isBigO_add

/--
theorem `bound_of_isBigO_cofinite` / 定理 `bound_of_isBigO_cofinite`

English:
theorem bound_of_isBigO_cofinite
  given: (h : f =O[cofinite] g'')
  proof: by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [IsBigOWith_def]; rw [eventually_cofinite] at hC
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : forall x, C * ‖g'' x‖ < ‖f x‖ -> ‖f x‖ / ‖g'' x‖ <= C' := by simpa using hC'
  refine ⟨max C C', lt_max_iff.2 (Or.in

中文:
定理 bound_of_isBigO_cofinite
  条件: (h : f =O[cofinite] g'')
  证明: by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [IsBigOWith_def]; rw [eventually_cofinite] at hC
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : forall x, C * ‖g'' x‖ < ‖f x‖ -> ‖f x‖ / ‖g'' x‖ <= C' := by simpa using hC'
  refine ⟨max C C', lt_max_iff.2 (Or.in

Depends on / 依赖: IsBigOWith_def, Or.inl, eventually_cofinite, exists_le, exists_pos, h.exists_pos, hC.toFinset.image, le_max_iff, lt_max_iff, max_mul_of_nonneg, norm_nonneg, norm_pos_iff, not_le, or_iff_not_imp_left, toFinset
-/
theorem bound_of_isBigO_cofinite (h : f =O[cofinite] g'') :
    exists C > 0, forall ⦃x⦄, g'' x != 0 -> ‖f x‖ <= C * ‖g'' x‖ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [IsBigOWith_def]; rw [eventually_cofinite] at hC
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : forall x, C * ‖g'' x‖ < ‖f x‖ -> ‖f x‖ / ‖g'' x‖ <= C' := by simpa using hC'
  refine ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => ?_⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _)]; rw [le_max_iff]; rw [or_iff_not_imp_left]; rw [not_le]
  exact fun hx => (div_le_iff₀ (norm_pos_iff.2 h₀)).1 (this _ hx)

/--
theorem `isBigO_cofinite_iff` / 定理 `isBigO_cofinite_iff`

English:
theorem isBigO_cofinite_iff
  given: (h : forall x, g'' x = 0 -> f'' x = 0)
  proof: by
  classical
  exact ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩

中文:
定理 isBigO_cofinite_iff
  条件: (h : 对任意 x, g'' x = 0 -> f'' x = 0)
  证明: by
  classical
  exact ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩

Depends on / 依赖: bound_of_isBigO_cofinite, classical, isBigO_top, le_top
-/
theorem isBigO_cofinite_iff (h : forall x, g'' x = 0 -> f'' x = 0) :
    f'' =O[cofinite] g'' ↔ exists C, forall x, ‖f'' x‖ <= C * ‖g'' x‖ := by
  classical
  exact ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩

/--
theorem `bound_of_isBigO_nat_atTop` / 定理 `bound_of_isBigO_nat_atTop`

English:
theorem bound_of_isBigO_nat_atTop
  given: {f : Nat -> E} {g'' : Nat -> E''} (h : f =O[atTop] g'')
  proof: bound_of_isBigO_cofinite by rwa [Nat.cofinite_eq_atTop]

中文:
定理 bound_of_isBigO_nat_atTop
  条件: {f : 自然数 -> E} {g'' : 自然数 -> E''} (h : f =O[atTop] g'')
  证明: bound_of_isBigO_cofinite by rwa [Nat.cofinite_eq_atTop]

Depends on / 依赖: Nat.cofinite_eq_atTop, bound_of_isBigO_cofinite, cofinite_eq_atTop
-/
theorem bound_of_isBigO_nat_atTop {f : Nat -> E} {g'' : Nat -> E''} (h : f =O[atTop] g'') :
    exists C > 0, forall ⦃x⦄, g'' x != 0 -> ‖f x‖ <= C * ‖g'' x‖ :=
bound_of_isBigO_cofinite by rwa [Nat.cofinite_eq_atTop]

/--
theorem `isBigO_nat_atTop_iff` / 定理 `isBigO_nat_atTop_iff`

English:
theorem isBigO_nat_atTop_iff
  given: {f : Nat -> E''} {g : Nat -> F''} (h : forall x, g x = 0 -> f x = 0)
  proof: by
  rw [← Nat.cofinite_eq_atTop]; rw [isBigO_cofinite_iff h]

中文:
定理 isBigO_nat_atTop_iff
  条件: {f : 自然数 -> E''} {g : 自然数 -> F''} (h : 对任意 x, g x = 0 -> f x = 0)
  证明: by
  rw [← Nat.cofinite_eq_atTop]; rw [isBigO_cofinite_iff h]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, isBigO_cofinite_iff
-/
theorem isBigO_nat_atTop_iff {f : Nat -> E''} {g : Nat -> F''} (h : forall x, g x = 0 -> f x = 0) :
    f =O[atTop] g ↔ exists C, forall x, ‖f x‖ <= C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop]; rw [isBigO_cofinite_iff h]

/--
theorem `isBigO_one_nat_atTop_iff` / 定理 `isBigO_one_nat_atTop_iff`

English:
theorem isBigO_one_nat_atTop_iff
  given: {f : Nat -> E''}
  proof: Iff.trans (isBigO_nat_atTop_iff fun _ h => (one_ne_zero h).elim) by
    simp only [norm_one, mul_one]

中文:
定理 isBigO_one_nat_atTop_iff
  条件: {f : 自然数 -> E''}
  证明: Iff.trans (isBigO_nat_atTop_iff fun _ h => (one_ne_zero h).elim) by
    simp only [norm_one, mul_one]

Depends on / 依赖: Iff.trans, isBigO_nat_atTop_iff, mul_one, norm_one, one_ne_zero
-/
theorem isBigO_one_nat_atTop_iff {f : Nat -> E''} :
    f =O[atTop] (fun _n => 1 : Nat -> Real) ↔ exists C, forall n, ‖f n‖ <= C :=
Iff.trans (isBigO_nat_atTop_iff fun _ h => (one_ne_zero h).elim) by
    simp only [norm_one, mul_one]

/--
theorem `IsBigO.nat_of_atTop` / 定理 `IsBigO.nat_of_atTop`

English:
theorem IsBigO.nat_of_atTop
  statement: {f : Nat -> E''} {g : Nat -> F''} (hfg : f =O[atTop] g)
  proof: by
  obtain ⟨C, hC_pos, hC⟩ := bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  exact hC fun a => hf (h a)

中文:
定理 IsBigO.nat_of_atTop
  结论: {f : 自然数 -> E''} {g : 自然数 -> F''} (hfg : f =O[atTop] g)
  证明: by
  obtain ⟨C, hC_pos, hC⟩ := bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  exact hC fun a => hf (h a)

Depends on / 依赖: bound_of_isBigO_nat_atTop, filter_upwards, hC_pos, isBigO_iff, isBigO_iff.mpr
-/
theorem IsBigO.nat_of_atTop {f : Nat -> E''} {g : Nat -> F''} (hfg : f =O[atTop] g)
    {l : Filter Nat} (h : forallᶠ n in l, g n = 0 -> f n = 0) : f =O[l] g := by
  obtain ⟨C, hC_pos, hC⟩ := bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  exact hC fun a => hf (h a)

/--
theorem `isBigOWith_pi` / 定理 `isBigOWith_pi`

English:
theorem isBigOWith_pi
  statement: {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)]
  proof: by
  have this (x) : 0 <= C * ‖g' x‖ := by positivity
  simp only [isBigOWith_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]

@[simp]

中文:
定理 isBigOWith_pi
  结论: {ι : 类型} [有限类型 ι] {E' : ι -> 类型} [对任意 i, SeminormedAddComm群 (E' i)]
  证明: by
  have this (x) : 0 <= C * ‖g' x‖ := by positivity
  simp only [isBigOWith_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]

@[simp]

Depends on / 依赖: eventually_all, isBigOWith_iff, pi_norm_le_iff_of_nonneg
-/
theorem isBigOWith_pi {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)]
    {f : α -> forall i, E' i} {C : Real} (hC : 0 <= C) :
    IsBigOWith C l f g' ↔ forall i, IsBigOWith C l (fun x => f x i) g' := by
  have this (x) : 0 <= C * ‖g' x‖ := by positivity
  simp only [isBigOWith_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]

@[simp]
/--
theorem `isBigO_pi` / 定理 `isBigO_pi`

English:
theorem isBigO_pi
  statement: {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)]
  proof: by
  simp only [isBigO_iff_eventually_isBigOWith, ← eventually_all]
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => isBigOWith_pi⟩)

@[simp]

中文:
定理 isBigO_pi
  结论: {ι : 类型} [有限类型 ι] {E' : ι -> 类型} [对任意 i, SeminormedAddComm群 (E' i)]
  证明: by
  simp only [isBigO_iff_eventually_isBigOWith, ← eventually_all]
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => isBigOWith_pi⟩)

@[simp]

Depends on / 依赖: eventually_all, eventually_atTop, eventually_congr, isBigOWith_pi, isBigO_iff_eventually_isBigOWith
-/
theorem isBigO_pi {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)]
    {f : α -> forall i, E' i} : f =O[l] g' ↔ forall i, (fun x => f x i) =O[l] g' := by
  simp only [isBigO_iff_eventually_isBigOWith, ← eventually_all]
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => isBigOWith_pi⟩)

@[simp]
/--
theorem `isLittleO_pi` / 定理 `isLittleO_pi`

English:
theorem isLittleO_pi
  statement: {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)]
  proof: by
  simp +contextual only [IsLittleO_def, isBigOWith_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩

中文:
定理 isLittleO_pi
  结论: {ι : 类型} [有限类型 ι] {E' : ι -> 类型} [对任意 i, SeminormedAddComm群 (E' i)]
  证明: by
  simp +contextual only [IsLittleO_def, isBigOWith_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩

Depends on / 依赖: IsLittleO_def, contextual, isBigOWith_pi, le_of_lt
-/
theorem isLittleO_pi {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)]
    {f : α -> forall i, E' i} : f =o[l] g' ↔ forall i, (fun x => f x i) =o[l] g' := by
  simp +contextual only [IsLittleO_def, isBigOWith_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩

/--
theorem `IsBigO.natCast_atTop` / 定理 `IsBigO.natCast_atTop`

English:
theorem IsBigO.natCast_atTop
  statement: {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: IsBigO.comp_tendsto h tendsto_natCast_atTop_atTop

中文:
定理 IsBigO.natCast_atTop
  结论: {R : 类型} [半环 R] [偏序 R] [是StrictOrdered环 R]
  证明: IsBigO.comp_tendsto h tendsto_natCast_atTop_atTop

Depends on / 依赖: IsBigO, IsBigO.comp_tendsto, comp_tendsto, tendsto_natCast_atTop_atTop
-/
theorem IsBigO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R]
    {f : R -> E} {g : R -> F} (h : f =O[atTop] g) :
    (fun (n : Nat) => f n) =O[atTop] (fun n => g n) :=
  IsBigO.comp_tendsto h tendsto_natCast_atTop_atTop

/--
theorem `IsLittleO.natCast_atTop` / 定理 `IsLittleO.natCast_atTop`

English:
theorem IsLittleO.natCast_atTop
  statement: {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: IsLittleO.comp_tendsto h tendsto_natCast_atTop_atTop

中文:
定理 IsLittleO.natCast_atTop
  结论: {R : 类型} [半环 R] [偏序 R] [是StrictOrdered环 R]
  证明: IsLittleO.comp_tendsto h tendsto_natCast_atTop_atTop

Depends on / 依赖: IsLittleO, IsLittleO.comp_tendsto, comp_tendsto, tendsto_natCast_atTop_atTop
-/
theorem IsLittleO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R]
    {f : R -> E} {g : R -> F} (h : f =o[atTop] g) :
    (fun (n : Nat) => f n) =o[atTop] (fun n => g n) :=
  IsLittleO.comp_tendsto h tendsto_natCast_atTop_atTop

/--
theorem `isBigO_atTop_iff_eventually_exists` / 定理 `isBigO_atTop_iff_eventually_exists`

English:
theorem isBigO_atTop_iff_eventually_exists
  statement: {α : Type*} [SemilatticeSup α] [Nonempty α]
  proof: by
  rw [isBigO_iff]; rw [exists_eventually_atTop]

中文:
定理 isBigO_atTop_iff_eventually_存在
  结论: {α : 类型} [SemilatticeSup α] [非空 α]
  证明: by
  rw [isBigO_iff]; rw [exists_eventually_atTop]

Depends on / 依赖: exists_eventually_atTop, isBigO_iff
-/
theorem isBigO_atTop_iff_eventually_exists {α : Type*} [SemilatticeSup α] [Nonempty α]
    {f : α -> E} {g : α -> F} : f =O[atTop] g ↔ forallᶠ n₀ in atTop, exists c, forall n >= n₀, ‖f n‖ <= c * ‖g n‖ := by
  rw [isBigO_iff]; rw [exists_eventually_atTop]

/--
theorem `isBigO_atTop_iff_eventually_exists_pos` / 定理 `isBigO_atTop_iff_eventually_exists_pos`

English:
theorem isBigO_atTop_iff_eventually_exists_pos
  statement: {α : Type*}
  proof: by
  simp_rw [isBigO_iff'', ← exists_prop, Subtype.exists', exists_eventually_atTop]

中文:
定理 isBigO_atTop_iff_eventually_存在_pos
  结论: {α : 类型}
  证明: by
  simp_rw [isBigO_iff'', ← exists_prop, Subtype.exists', exists_eventually_atTop]

Depends on / 依赖: Subtype, Subtype.exists, exists_eventually_atTop, exists_prop, isBigO_iff, simp_rw
-/
theorem isBigO_atTop_iff_eventually_exists_pos {α : Type*}
    [SemilatticeSup α] [Nonempty α] {f : α -> G} {g : α -> G'} :
    f =O[atTop] g ↔ forallᶠ n₀ in atTop, exists c > 0, forall n >= n₀, c * ‖f n‖ <= ‖g n‖ := by
  simp_rw [isBigO_iff'', ← exists_prop, Subtype.exists', exists_eventually_atTop]

/--
lemma `isBigOWith_mul_iff_isBigOWith_div` / 引理 `isBigOWith_mul_iff_isBigOWith_div`

English:
lemma isBigOWith_mul_iff_isBigOWith_div
  given: {f g h : α -> 𝕜} {c : Real} (hf : forallᶠ x in l, f x != 0)
  proof: by
  rw [isBigOWith_iff]; rw [isBigOWith_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
· refine h.congr Eventually.mp hf Eventually.of_forall fun x hx => ?_
    rw [norm_mul]; rw [norm_div]; rw [← mul_div_assoc]; rw [le_div_iff₀' (norm_pos_iff.mpr hx)]

中文:
引理 isBigOWith_mul_iff_isBigOWith_div
  条件: {f g h : α -> 𝕜} {c : 实数} (hf : 对任意ᶠ x in l, f x != 0)
  证明: by
  rw [isBigOWith_iff]; rw [isBigOWith_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
· refine h.congr Eventually.mp hf Eventually.of_forall fun x hx => ?_
    rw [norm_mul]; rw [norm_div]; rw [← mul_div_assoc]; rw [le_div_iff₀' (norm_pos_iff.mpr hx)]

Depends on / 依赖: Eventually, Eventually.mp, Eventually.of_forall, h.congr, isBigOWith_iff, mul_div_assoc, norm_div, norm_mul, norm_pos_iff, norm_pos_iff.mpr, of_forall
-/
lemma isBigOWith_mul_iff_isBigOWith_div {f g h : α -> 𝕜} {c : Real} (hf : forallᶠ x in l, f x != 0) :
    IsBigOWith c l (fun x => f x * g x) h ↔ IsBigOWith c l g (fun x => h x / f x) := by
  rw [isBigOWith_iff]; rw [isBigOWith_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
· refine h.congr Eventually.mp hf Eventually.of_forall fun x hx => ?_
    rw [norm_mul]; rw [norm_div]; rw [← mul_div_assoc]; rw [le_div_iff₀' (norm_pos_iff.mpr hx)]

/--
lemma `isBigO_mul_iff_isBigO_div` / 引理 `isBigO_mul_iff_isBigO_div`

English:
lemma isBigO_mul_iff_isBigO_div
  given: {f g h : α -> 𝕜} (hf : forallᶠ x in l, f x != 0)
  proof: by
  rw [isBigO_iff_isBigOWith]; rw [isBigO_iff_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]

中文:
引理 isBigO_mul_iff_isBigO_div
  条件: {f g h : α -> 𝕜} (hf : 对任意ᶠ x in l, f x != 0)
  证明: by
  rw [isBigO_iff_isBigOWith]; rw [isBigO_iff_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]

Depends on / 依赖: isBigOWith_mul_iff_isBigOWith_div, isBigO_iff_isBigOWith
-/
lemma isBigO_mul_iff_isBigO_div {f g h : α -> 𝕜} (hf : forallᶠ x in l, f x != 0) :
    (fun x => f x * g x) =O[l] h ↔ g =O[l] (fun x => h x / f x) := by
  rw [isBigO_iff_isBigOWith]; rw [isBigO_iff_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]

/--
lemma `isLittleO_mul_iff_isLittleO_div` / 引理 `isLittleO_mul_iff_isLittleO_div`

English:
lemma isLittleO_mul_iff_isLittleO_div
  given: {f g h : α -> 𝕜} (hf : forallᶠ x in l, f x != 0)
  proof: by
  rw [isLittleO_iff_forall_isBigOWith]; rw [isLittleO_iff_forall_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]

中文:
引理 isLittleO_mul_iff_isLittleO_div
  条件: {f g h : α -> 𝕜} (hf : 对任意ᶠ x in l, f x != 0)
  证明: by
  rw [isLittleO_iff_forall_isBigOWith]; rw [isLittleO_iff_forall_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]

Depends on / 依赖: isBigOWith_mul_iff_isBigOWith_div, isLittleO_iff_forall_isBigOWith
-/
lemma isLittleO_mul_iff_isLittleO_div {f g h : α -> 𝕜} (hf : forallᶠ x in l, f x != 0) :
    (fun x => f x * g x) =o[l] h ↔ g =o[l] (fun x => h x / f x) := by
  rw [isLittleO_iff_forall_isBigOWith]; rw [isLittleO_iff_forall_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]

/--
lemma `isBigO_nat_atTop_induction` / 引理 `isBigO_nat_atTop_induction`

English:
lemma isBigO_nat_atTop_induction
  statement: {f : Nat -> E''} {g : Nat -> F''}
  proof: by
  rw [← eventually_forall_ge_atTop] at h
.exists obtain ⟨n₀, h, hrec⟩ := h.and hrec
  obtain ⟨C₀, hrec⟩ := hrec
  rw [isBigO_iff]
  rw [← eventually_forall_ge_atTop] at hrec
.exists obtain ⟨n₁, H₁, H₂⟩ := (eventually_ge_atTop n₀).and hrec
  let ubounds := {C | forall m in Finset.Icc n₀ n₁, ‖f m‖ 

中文:
引理 isBigO_nat_atTop_induction
  结论: {f : 自然数 -> E''} {g : 自然数 -> F''}
  证明: by
  rw [← eventually_forall_ge_atTop] at h
.exists obtain ⟨n₀, h, hrec⟩ := h.and hrec
  obtain ⟨C₀, hrec⟩ := hrec
  rw [isBigO_iff]
  rw [← eventually_forall_ge_atTop] at hrec
.exists obtain ⟨n₁, H₁, H₂⟩ := (eventually_ge_atTop n₀).and hrec
  let ubounds := {C | forall m in Finset.Icc n₀ n₁, ‖f m‖ 

Depends on / 依赖: Finset, Finset.Icc, Finset.nonempty_Icc.mpr, Set.mem_ofPred, eventually_forall_ge_atTop, eventually_ge_atTop, h.and, isBigO_iff, mem_ofPred, nonempty_Icc, ubounds
-/
lemma isBigO_nat_atTop_induction {f : Nat -> E''} {g : Nat -> F''}
    (h : forallᶠ n in atTop, g n = 0 -> f n = 0)
    (hrec : forallᶠ n₀ in atTop, exists C₀, forallᶠ n in atTop, forall C >= C₀,
      (forall m in Finset.Ico n₀ n, ‖f m‖ <= C * ‖g m‖) -> ‖f n‖ <= C * ‖g n‖) :
    f =O[atTop] g := by
  rw [← eventually_forall_ge_atTop] at h
.exists obtain ⟨n₀, h, hrec⟩ := h.and hrec
  obtain ⟨C₀, hrec⟩ := hrec
  rw [isBigO_iff]
  rw [← eventually_forall_ge_atTop] at hrec
.exists obtain ⟨n₁, H₁, H₂⟩ := (eventually_ge_atTop n₀).and hrec
  let ubounds := {C | forall m in Finset.Icc n₀ n₁, ‖f m‖ <= C * ‖g m‖}
  let C₁ := (Finset.Icc n₀ n₁).sup' (Finset.nonempty_Icc.mpr H₁) fun n => ‖f n‖ / ‖g n‖
  have C₁_mem : C₁ in ubounds := by
    rw [Set.mem_ofPred]
    intro m hm
    calc ‖f m‖ = (‖f m‖ / ‖g m‖) * ‖g m‖ := by by_cases hm' : g m = 0 <;> grind [norm_eq_zero]
      _ <= C₁ * ‖g m‖ := by
        gcongr
        exact Finset.le_sup' (fun x => ‖f x‖ / ‖g x‖) (Finset.mem_def.mpr hm)
  refine ⟨max C₀ C₁, ?_⟩
  filter_upwards [eventually_ge_atTop n₁] with n hn
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    refine H₂ _ (by grind) _ (by grind) fun m hm => ?_
    by_cases hbase : m < n₁
    · have hC₁ : C₁ <= max C₀ C₁ := by grind
      grw [← hC₁]
      grind
    · grind

/--
lemma `isBigO_nat_atTop_induction_of_eventually_pos` / 引理 `isBigO_nat_atTop_induction_of_eventually_pos`

English:
lemma isBigO_nat_atTop_induction_of_eventually_pos
  statement: {f g : Nat -> Real}
  proof: by
  refine isBigO_nat_atTop_induction ?hzero ?hrec
  case hzero => filter_upwards [hf, hg]; grind
  case hrec =>
    filter_upwards [eventually_forall_ge_atTop.mpr hg, eventually_forall_ge_atTop.mpr hf, hrec]
      with n₀ hn₀ hn₀' hnrec
    obtain ⟨C₀, hnrec⟩ := hnrec
    refine ⟨C₀, ?_⟩
    filte

中文:
引理 isBigO_nat_atTop_induction_of_eventually_pos
  结论: {f g : 自然数 -> 实数}
  证明: by
  refine isBigO_nat_atTop_induction ?hzero ?hrec
  case hzero => filter_upwards [hf, hg]; grind
  case hrec =>
    filter_upwards [eventually_forall_ge_atTop.mpr hg, eventually_forall_ge_atTop.mpr hf, hrec]
      with n₀ hn₀ hn₀' hnrec
    obtain ⟨C₀, hnrec⟩ := hnrec
    refine ⟨C₀, ?_⟩
    filte

Depends on / 依赖: Real.norm_eq_abs, eventually_forall_ge_atTop, eventually_forall_ge_atTop.mpr, eventually_ge_atTop, filter_upwards, isBigO_nat_atTop_induction, norm_eq_abs
-/
lemma isBigO_nat_atTop_induction_of_eventually_pos {f g : Nat -> Real}
    (hf : forallᶠ n in atTop, 0 <= f n) (hg : forallᶠ n in atTop, 0 < g n)
    (hrec : forallᶠ n₀ in atTop, exists C₀, forallᶠ n in atTop, forall C >= C₀,
      (forall m in Finset.Ico n₀ n, f m <= C * g m) -> f n <= C * g n) :
    f =O[atTop] g := by
  refine isBigO_nat_atTop_induction ?hzero ?hrec
  case hzero => filter_upwards [hf, hg]; grind
  case hrec =>
    filter_upwards [eventually_forall_ge_atTop.mpr hg, eventually_forall_ge_atTop.mpr hf, hrec]
      with n₀ hn₀ hn₀' hnrec
    obtain ⟨C₀, hnrec⟩ := hnrec
    refine ⟨C₀, ?_⟩
    filter_upwards [hnrec, eventually_ge_atTop n₀]
    grind [Real.norm_eq_abs]

end Asymptotics

open Asymptotics

/--
theorem `summable_of_isBigO` / 定理 `summable_of_isBigO`

English:
theorem summable_of_isBigO
  statement: {ι E} [SeminormedAddCommGroup E] [CompleteSpace E]
  proof: let ⟨_, hC⟩ := h.isBigOWith
  .of_norm_bounded_eventually (hg.abs.mul_left _) hC.bound

中文:
定理 summable_of_isBigO
  结论: {ι E} [SeminormedAddComm群 E] [完备空间 E]
  证明: let ⟨_, hC⟩ := h.isBigOWith
  .of_norm_bounded_eventually (hg.abs.mul_left _) hC.bound

Depends on / 依赖: h.isBigOWith, hC.bound, hg.abs.mul_left, isBigOWith, mul_left, of_norm_bounded_eventually
-/
theorem summable_of_isBigO {ι E} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨_, hC⟩ := h.isBigOWith
  .of_norm_bounded_eventually (hg.abs.mul_left _) hC.bound

/--
theorem `summable_of_isBigO_nat` / 定理 `summable_of_isBigO_nat`

English:
theorem summable_of_isBigO_nat
  statement: {E} [SeminormedAddCommGroup E] [CompleteSpace E]
  proof: summable_of_isBigO hg Nat.cofinite_eq_atTop.symm ▸ h

中文:
定理 summable_of_isBigO_nat
  结论: {E} [SeminormedAddComm群 E] [完备空间 E]
  证明: summable_of_isBigO hg Nat.cofinite_eq_atTop.symm ▸ h

Depends on / 依赖: Nat.cofinite_eq_atTop.symm, cofinite_eq_atTop, summable_of_isBigO
-/
theorem summable_of_isBigO_nat {E} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
summable_of_isBigO hg Nat.cofinite_eq_atTop.symm ▸ h

/--
lemma `Asymptotics.IsBigO.comp_summable_norm` / 引理 `Asymptotics.IsBigO.comp_summable_norm`

English:
lemma Asymptotics.IsBigO.comp_summable_norm
  statement: {ι E F : Type*}
  proof: summable_of_isBigO hg hf.norm_norm.comp_tendsto
    tendsto_zero_iff_norm_tendsto_zero.2 hg.tendsto_cofinite_zero

中文:
引理 Asymptotics.IsBigO.comp_summable_norm
  结论: {ι E F : 类型}
  证明: summable_of_isBigO hg hf.norm_norm.comp_tendsto
    tendsto_zero_iff_norm_tendsto_zero.2 hg.tendsto_cofinite_zero

Depends on / 依赖: comp_tendsto, hf.norm_norm.comp_tendsto, hg.tendsto_cofinite_zero, norm_norm, summable_of_isBigO, tendsto_cofinite_zero, tendsto_zero_iff_norm_tendsto_zero
-/
lemma Asymptotics.IsBigO.comp_summable_norm {ι E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {f : E -> F} {g : ι -> E}
    (hf : f =O[𝓝 0] id) (hg : Summable (‖g ·‖)) : Summable (‖f <| g ·‖) :=
summable_of_isBigO hg hf.norm_norm.comp_tendsto
    tendsto_zero_iff_norm_tendsto_zero.2 hg.tendsto_cofinite_zero

/--
lemma `Summable.mul_tendsto_const` / 引理 `Summable.mul_tendsto_const`

English:
lemma Summable.mul_tendsto_const
  statement: {F ι : Type*} [NormedRing F] [NormMulClass F] [NormOneClass F]
  proof: by
  apply summable_of_isBigO hf
  simpa using (isBigO_const_mul_self 1 f _).mul (hg.isBigO_one F)

中文:
引理 Summable.mul_tendsto_const
  结论: {F ι : 类型} [赋范环 F] [NormMul类 F] [NormOne类 F]
  证明: by
  apply summable_of_isBigO hf
  simpa using (isBigO_const_mul_self 1 f _).mul (hg.isBigO_one F)

Depends on / 依赖: hg.isBigO_one, isBigO_const_mul_self, isBigO_one, summable_of_isBigO
-/
lemma Summable.mul_tendsto_const {F ι : Type*} [NormedRing F] [NormMulClass F] [NormOneClass F]
    [CompleteSpace F] {f g : ι -> F} (hf : Summable fun n => ‖f n‖) {c : F}
    (hg : Tendsto g cofinite (𝓝 c)) : Summable fun n => f n * g n := by
  apply summable_of_isBigO hf
  simpa using (isBigO_const_mul_self 1 f _).mul (hg.isBigO_one F)

namespace OpenPartialHomeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {E : Type*} [Norm E] {F : Type*} [Norm F]

/--
theorem `isBigOWith_congr` / 定理 `isBigOWith_congr`

English:
theorem isBigOWith_congr
  statement: (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
  proof: ⟨fun h =>
h.comp_tendsto by
      have := e.continuousAt (e.map_target hb)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg f hx)
      ((e.eventually_right_inver

中文:
定理 isBigOWith_congr
  结论: (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
  证明: ⟨fun h =>
h.comp_tendsto by
      have := e.continuousAt (e.map_target hb)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg f hx)
      ((e.eventually_right_inver

Depends on / 依赖: ContinuousAt, comp_tendsto, congr_arg, continuousAt, continuousAt_symm, e.continuousAt, e.continuousAt_symm, e.eventually_right_inverse, e.map_target, e.rightInvOn, eventually_right_inverse, h.comp_tendsto, map_target, rightInvOn
-/
theorem isBigOWith_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
    {g : β -> F} {C : Real} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
h.comp_tendsto by
      have := e.continuousAt (e.map_target hb)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg g hx)⟩

/--
theorem `isBigO_congr` / 定理 `isBigO_congr`

English:
theorem isBigO_congr
  statement: (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr hb

中文:
定理 isBigO_congr
  结论: (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr hb

Depends on / 依赖: IsBigO_def, e.isBigOWith_congr, exists_congr, isBigOWith_congr
-/
theorem isBigO_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
    {g : β -> F} : f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr hb

/--
theorem `isLittleO_congr` / 定理 `isLittleO_congr`

English:
theorem isLittleO_congr
  statement: (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr hb

中文:
定理 isLittleO_congr
  结论: (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr hb

Depends on / 依赖: IsLittleO_def, e.isBigOWith_congr, isBigOWith_congr
-/
theorem isLittleO_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E}
    {g : β -> F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr hb

end OpenPartialHomeomorph

namespace Homeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {E : Type*} [Norm E] {F : Type*} [Norm F]

open Asymptotics

/--
theorem `isBigOWith_congr` / 定理 `isBigOWith_congr`

English:
theorem isBigOWith_congr
  given: (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} {C : Real}
  proof: e.toOpenPartialHomeomorph.isBigOWith_congr trivial

中文:
定理 isBigOWith_congr
  条件: (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} {C : 实数}
  证明: e.toOpenPartialHomeomorph.isBigOWith_congr trivial

Depends on / 依赖: e.toOpenPartialHomeomorph.isBigOWith_congr, isBigOWith_congr, toOpenPartialHomeomorph
-/
theorem isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} {C : Real} :
    IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toOpenPartialHomeomorph.isBigOWith_congr trivial

/--
theorem `isBigO_congr` / 定理 `isBigO_congr`

English:
theorem isBigO_congr
  given: (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F}
  proof: by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr

中文:
定理 isBigO_congr
  条件: (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F}
  证明: by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr

Depends on / 依赖: IsBigO_def, e.isBigOWith_congr, exists_congr, isBigOWith_congr
-/
theorem isBigO_congr (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr

/--
theorem `isLittleO_congr` / 定理 `isLittleO_congr`

English:
theorem isLittleO_congr
  given: (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F}
  proof: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr

中文:
定理 isLittleO_congr
  条件: (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F}
  证明: by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr

Depends on / 依赖: IsLittleO_def, e.isBigOWith_congr, isBigOWith_congr
-/
theorem isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr

end Homeomorph

namespace ContinuousOn

variable {α E F : Type*} [TopologicalSpace α] {s : Set α} {f : α -> E} {c : F}

section IsBigO

variable [SeminormedAddGroup E] [Norm F]

/--
theorem `isBigOWith_principal` / 定理 `isBigOWith_principal`

English:
theorem isBigOWith_principal
  proof: by
  rw [isBigOWith_principal]; rw [div_mul_cancel₀ _ hc]
.image continuous_norm exact fun x hx => hs.image_of_continuousOn hf
.isLUB_sSup (Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩)
.left Set.mem_image_of_mem _ Set.mem_image_of_mem _ hx

中文:
定理 isBigOWith_principal
  证明: by
  rw [isBigOWith_principal]; rw [div_mul_cancel₀ _ hc]
.image continuous_norm exact fun x hx => hs.image_of_continuousOn hf
.isLUB_sSup (Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩)
.left Set.mem_image_of_mem _ Set.mem_image_of_mem _ hx
-/
protected theorem isBigOWith_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hc : ‖c‖ != 0) :
    IsBigOWith (sSup (Norm.norm '' f '' s) / ‖c‖) (𝓟 s) f fun _ => c := by
  rw [isBigOWith_principal]; rw [div_mul_cancel₀ _ hc]
.image continuous_norm exact fun x hx => hs.image_of_continuousOn hf
.isLUB_sSup (Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩)
.left Set.mem_image_of_mem _ Set.mem_image_of_mem _ hx

/--
theorem `isBigO_principal` / 定理 `isBigO_principal`

English:
theorem isBigO_principal
  statement: (hf : ContinuousOn f s) (hs : IsCompact s)
  proof: (hf.isBigOWith_principal hs hc).isBigO

中文:
定理 isBigO_principal
  结论: (hf : ContinuousOn f s) (hs : 是紧集 s)
  证明: (hf.isBigOWith_principal hs hc).isBigO
-/
protected theorem isBigO_principal (hf : ContinuousOn f s) (hs : IsCompact s)
    (hc : ‖c‖ != 0) : f =O[𝓟 s] fun _ => c :=
  (hf.isBigOWith_principal hs hc).isBigO

end IsBigO

section IsBigORev

variable [NormedAddGroup E] [SeminormedAddGroup F]

/--
theorem `isBigOWith_rev_principal` / 定理 `isBigOWith_rev_principal`

English:
theorem isBigOWith_rev_principal
  proof: by
  refine isBigOWith_principal.mpr fun x hx => ?_
  rw [mul_comm_div]
.image continuous_norm replace hs := hs.image_of_continuousOn hf
have h_sInf := hs.isGLB_sInf Set.image_nonempty.mpr Set.image_nonempty.mpr ⟨x, hx⟩
refine le_mul_of_one_le_right (norm_nonneg c) (one_le_div ?_).mpr
h_sInf.1 Set.m

中文:
定理 isBigOWith_rev_principal
  证明: by
  refine isBigOWith_principal.mpr fun x hx => ?_
  rw [mul_comm_div]
.image continuous_norm replace hs := hs.image_of_continuousOn hf
have h_sInf := hs.isGLB_sInf Set.image_nonempty.mpr Set.image_nonempty.mpr ⟨x, hx⟩
refine le_mul_of_one_le_right (norm_nonneg c) (one_le_div ?_).mpr
h_sInf.1 Set.m
-/
protected theorem isBigOWith_rev_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hC : forall i in s, f i != 0) (c : F) :
    IsBigOWith (‖c‖ / sInf (Norm.norm '' f '' s)) (𝓟 s) (fun _ => c) f := by
  refine isBigOWith_principal.mpr fun x hx => ?_
  rw [mul_comm_div]
.image continuous_norm replace hs := hs.image_of_continuousOn hf
have h_sInf := hs.isGLB_sInf Set.image_nonempty.mpr Set.image_nonempty.mpr ⟨x, hx⟩
refine le_mul_of_one_le_right (norm_nonneg c) (one_le_div ?_).mpr
h_sInf.1 Set.mem_image_of_mem _ Set.mem_image_of_mem _ hx
  obtain ⟨_, ⟨x, hx, hCx⟩, hnormCx⟩ := hs.sInf_mem h_sInf.nonempty
  rw [← hnormCx]; rw [← hCx]
  exact (norm_ne_zero_iff.mpr (hC x hx)).symm.lt_of_le (norm_nonneg _)

/--
theorem `isBigO_rev_principal` / 定理 `isBigO_rev_principal`

English:
theorem isBigO_rev_principal
  statement: (hf : ContinuousOn f s)
  proof: (hf.isBigOWith_rev_principal hs hC c).isBigO

中文:
定理 isBigO_rev_principal
  结论: (hf : ContinuousOn f s)
  证明: (hf.isBigOWith_rev_principal hs hC c).isBigO
-/
protected theorem isBigO_rev_principal (hf : ContinuousOn f s)
    (hs : IsCompact s) (hC : forall i in s, f i != 0) (c : F) : (fun _ => c) =O[𝓟 s] f :=
  (hf.isBigOWith_rev_principal hs hC c).isBigO

end IsBigORev

end ContinuousOn

/--
lemma `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded` / 引理 `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded`

English:
lemma NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
  statement: {ι 𝕜 E : Type*}
  proof: by
  rw [← isLittleO_one_iff 𝕜] at hε ⊢
  simpa using! IsLittleO.smul_isBigO hε (hf.isBigO_const (one_ne_zero : (1 : 𝕜) != 0))

中文:
引理 赋范域.tendsto_zero_smul_of_tendsto_zero_of_bounded
  结论: {ι 𝕜 E : 类型}
  证明: by
  rw [← isLittleO_one_iff 𝕜] at hε ⊢
  simpa using! IsLittleO.smul_isBigO hε (hf.isBigO_const (one_ne_zero : (1 : 𝕜) != 0))

Depends on / 依赖: IsLittleO, IsLittleO.smul_isBigO, hf.isBigO_const, isBigO_const, isLittleO_one_iff, one_ne_zero, smul_isBigO
-/
lemma NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 E : Type*}
    [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {l : Filter ι} {ε : ι -> 𝕜} {f : ι -> E} (hε : Tendsto ε l (𝓝 0))
    (hf : IsBoundedUnder (· <= ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← isLittleO_one_iff 𝕜] at hε ⊢
  simpa using! IsLittleO.smul_isBigO hε (hf.isBigO_const (one_ne_zero : (1 : 𝕜) != 0))
