/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Seminorm
public import Mathlib.GroupTheory.GroupAction.Pointwise

/-!
# The Minkowski functional, normed field version

In this file we define `(egauge 𝕜 s ·)`
to be the Minkowski functional (gauge) of the set `s`
in a topological vector space `E` over a normed field `𝕜`,
as a function `E → ℝ≥0∞`.

It is defined as the infimum of the norms of `c : 𝕜` such that `x ∈ c • s`.
In particular, for `𝕜 = ℝ≥0` this definition gives an `ℝ≥0∞`-valued version of `gauge`
defined in `Mathlib/Analysis/Convex/Gauge.lean`.

This definition can be used to generalize the notion of Fréchet derivative
to maps between topological vector spaces without norms.

Currently, we can't reuse results about `egauge` for `gauge`,
because we lack a theory of normed semifields.
-/

@[expose] public section

open Function Set Filter Metric
open scoped Topology Pointwise ENNReal NNReal

section SMul

/--
Definition of `egauge` / `egauge` 的定义

English:
definition egauge
  signature: (𝕜 : Type*) [ENorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E)
  body: ⨅ (c : 𝕜) (_ : x in c • s), ‖c‖ₑ

中文:
定义 egauge
  签名: (𝕜 : 类型) [E范数 𝕜] {E : 类型} [标量乘法 𝕜 E] (s : 集合 E) (x : E)
  定义体: ⨅ (c : 𝕜) (_ : x in c • s), ‖c‖ₑ
-/
noncomputable def egauge (𝕜 : Type*) [ENorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E) : Real>=0∞ :=
  ⨅ (c : 𝕜) (_ : x in c • s), ‖c‖ₑ

variable (𝕜 : Type*) [NNNorm 𝕜] {E : Type*} [SMul 𝕜 E] {c : 𝕜} {s t : Set E} {x : E} {r : Real>=0∞}

/--
lemma `Set.MapsTo.egauge_le` / 引理 `Set.MapsTo.egauge_le`

English:
lemma Set.MapsTo.egauge_le
  statement: {E' F : Type*} [SMul 𝕜 E'] [FunLike F E E'] [MulActionHomClass F 𝕜 E E']
  proof: iInf_mono fun c => iInf_mono' fun hc => ⟨h.smul_set c hc, le_rfl⟩

@[mono, gcongr]

中文:
引理 集合.映射到.egauge_le
  结论: {E' F : 类型} [标量乘法 𝕜 E'] [函数状 F E E'] [MulActionHomClass F 𝕜 E E']
  证明: iInf_mono fun c => iInf_mono' fun hc => ⟨h.smul_set c hc, le_rfl⟩

@[mono, gcongr]

Depends on / 依赖: h.smul_set, iInf_mono, le_rfl, smul_set
-/
lemma Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [FunLike F E E'] [MulActionHomClass F 𝕜 E E']
    (f : F) {t : Set E'} (h : MapsTo f s t) (x : E) : egauge 𝕜 t (f x) <= egauge 𝕜 s x :=
  iInf_mono fun c => iInf_mono' fun hc => ⟨h.smul_set c hc, le_rfl⟩

@[mono, gcongr]
/--
lemma `egauge_anti` / 引理 `egauge_anti`

English:
lemma egauge_anti
  given: (h : s subseteq t) (x : E)
  statement: egauge 𝕜 t x <= egauge 𝕜 s x
  proof: MapsTo.egauge_le _ (MulActionHom.id ..) h _

中文:
引理 egauge_anti
  条件: (h : s subseteq t) (x : E)
  结论: egauge 𝕜 t x <= egauge 𝕜 s x
  证明: MapsTo.egauge_le _ (MulActionHom.id ..) h _

Depends on / 依赖: MapsTo, MapsTo.egauge_le, MulActionHom, MulActionHom.id, egauge_le
-/
lemma egauge_anti (h : s subseteq t) (x : E) : egauge 𝕜 t x <= egauge 𝕜 s x :=
  MapsTo.egauge_le _ (MulActionHom.id ..) h _

/--
lemma `egauge_empty` / 引理 `egauge_empty`

English:
lemma egauge_empty
  given: (x : E)
  statement: egauge 𝕜 ∅ x = ∞
  proof: by simp [egauge]

中文:
引理 egauge_empty
  条件: (x : E)
  结论: egauge 𝕜 ∅ x = ∞
  证明: by simp [egauge]
-/
@[simp] lemma egauge_empty (x : E) : egauge 𝕜 ∅ x = ∞ := by simp [egauge]

variable {𝕜}

/--
lemma `egauge_le_of_mem_smul` / 引理 `egauge_le_of_mem_smul`

English:
lemma egauge_le_of_mem_smul
  given: (h : x in c • s)
  statement: egauge 𝕜 s x <= ‖c‖ₑ
  proof: iInf₂_le c h

中文:
引理 egauge_le_of_mem_smul
  条件: (h : x in c • s)
  结论: egauge 𝕜 s x <= ‖c‖ₑ
  证明: iInf₂_le c h
-/
lemma egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜 s x <= ‖c‖ₑ := iInf₂_le c h

/--
lemma `le_egauge_iff` / 引理 `le_egauge_iff`

English:
lemma le_egauge_iff
  statement: r <= egauge 𝕜 s x ↔ forall c : 𝕜, x in c • s -> r <= ‖c‖ₑ
  proof: le_iInf₂_iff

中文:
引理 le_egauge_iff
  结论: r <= egauge 𝕜 s x ↔ 对任意 c : 𝕜, x in c • s -> r <= ‖c‖ₑ
  证明: le_iInf₂_iff
-/
lemma le_egauge_iff : r <= egauge 𝕜 s x ↔ forall c : 𝕜, x in c • s -> r <= ‖c‖ₑ := le_iInf₂_iff

/--
lemma `egauge_eq_top` / 引理 `egauge_eq_top`

English:
lemma egauge_eq_top
  statement: egauge 𝕜 s x = ∞ ↔ forall c : 𝕜, x ∉ c • s
  proof: by simp [egauge]

中文:
引理 egauge_eq_top
  结论: egauge 𝕜 s x = ∞ ↔ 对任意 c : 𝕜, x ∉ c • s
  证明: by simp [egauge]

Depends on / 依赖: egauge
-/
lemma egauge_eq_top : egauge 𝕜 s x = ∞ ↔ forall c : 𝕜, x ∉ c • s := by simp [egauge]

/--
lemma `egauge_lt_iff` / 引理 `egauge_lt_iff`

English:
lemma egauge_lt_iff
  statement: egauge 𝕜 s x < r ↔ exists c : 𝕜, x in c • s ∧ ‖c‖ₑ < r
  proof: by
  simp [egauge, iInf_lt_iff]

中文:
引理 egauge_lt_iff
  结论: egauge 𝕜 s x < r ↔ 存在 c : 𝕜, x in c • s ∧ ‖c‖ₑ < r
  证明: by
  simp [egauge, iInf_lt_iff]

Depends on / 依赖: egauge, iInf_lt_iff
-/
lemma egauge_lt_iff : egauge 𝕜 s x < r ↔ exists c : 𝕜, x in c • s ∧ ‖c‖ₑ < r := by
  simp [egauge, iInf_lt_iff]

/--
lemma `egauge_union` / 引理 `egauge_union`

English:
lemma egauge_union
  given: (s t : Set E) (x : E)
  statement: egauge 𝕜 (s union t) x = egauge 𝕜 s x ⊓ egauge 𝕜 t x
  proof: by
  unfold egauge
  simp [smul_set_union, iInf_or, iInf_inf_eq]

中文:
引理 egauge_union
  条件: (s t : 集合 E) (x : E)
  结论: egauge 𝕜 (s union t) x = egauge 𝕜 s x ⊓ egauge 𝕜 t x
  证明: by
  unfold egauge
  simp [smul_set_union, iInf_or, iInf_inf_eq]

Depends on / 依赖: egauge, iInf_inf_eq, iInf_or, smul_set_union
-/
lemma egauge_union (s t : Set E) (x : E) : egauge 𝕜 (s union t) x = egauge 𝕜 s x ⊓ egauge 𝕜 t x := by
  unfold egauge
  simp [smul_set_union, iInf_or, iInf_inf_eq]

/--
lemma `le_egauge_inter` / 引理 `le_egauge_inter`

English:
lemma le_egauge_inter
  given: (s t : Set E) (x : E)
  proof: max_le (egauge_anti _ inter_subset_left _) (egauge_anti _ inter_subset_right _)

中文:
引理 le_egauge_inter
  条件: (s t : 集合 E) (x : E)
  证明: max_le (egauge_anti _ inter_subset_left _) (egauge_anti _ inter_subset_right _)

Depends on / 依赖: egauge_anti, inter_subset_left, inter_subset_right, max_le
-/
lemma le_egauge_inter (s t : Set E) (x : E) :
    egauge 𝕜 s x ⊔ egauge 𝕜 t x <= egauge 𝕜 (s inter t) x :=
  max_le (egauge_anti _ inter_subset_left _) (egauge_anti _ inter_subset_right _)

/--
lemma `le_egauge_pi` / 引理 `le_egauge_pi`

English:
lemma le_egauge_pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, SMul 𝕜 (E i)] {I : Set ι} {i : ι}
  proof: MapsTo.egauge_le _ (Pi.evalMulActionHom i) (fun x hx => by exact hx i hi) _

中文:
引理 le_egauge_pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 标量乘法 𝕜 (E i)] {I : 集合 ι} {i : ι}
  证明: MapsTo.egauge_le _ (Pi.evalMulActionHom i) (fun x hx => by exact hx i hi) _

Depends on / 依赖: MapsTo, MapsTo.egauge_le, Pi.evalMulActionHom, egauge_le, evalMulActionHom
-/
lemma le_egauge_pi {ι : Type*} {E : ι -> Type*} [forall i, SMul 𝕜 (E i)] {I : Set ι} {i : ι}
    (hi : i in I) (s : forall i, Set (E i)) (x : forall i, E i) :
    egauge 𝕜 (s i) (x i) <= egauge 𝕜 (I.pi s) x :=
  MapsTo.egauge_le _ (Pi.evalMulActionHom i) (fun x hx => by exact hx i hi) _

variable {F : Type*} [SMul 𝕜 F]

/--
lemma `le_egauge_prod` / 引理 `le_egauge_prod`

English:
lemma le_egauge_prod
  given: (s : Set E) (t : Set F) (a : E) (b : F)
  proof: max_le (mapsTo_fst_prod.egauge_le 𝕜 (MulActionHom.fst 𝕜 E F) (a, b))
    (MapsTo.egauge_le 𝕜 (MulActionHom.snd 𝕜 E F) mapsTo_snd_prod (a, b))

中文:
引理 le_egauge_prod
  条件: (s : 集合 E) (t : 集合 F) (a : E) (b : F)
  证明: max_le (mapsTo_fst_prod.egauge_le 𝕜 (MulActionHom.fst 𝕜 E F) (a, b))
    (MapsTo.egauge_le 𝕜 (MulActionHom.snd 𝕜 E F) mapsTo_snd_prod (a, b))

Depends on / 依赖: MapsTo, MapsTo.egauge_le, MulActionHom, MulActionHom.fst, MulActionHom.snd, egauge_le, mapsTo_fst_prod, mapsTo_fst_prod.egauge_le, mapsTo_snd_prod, max_le
-/
lemma le_egauge_prod (s : Set E) (t : Set F) (a : E) (b : F) :
    max (egauge 𝕜 s a) (egauge 𝕜 t b) <= egauge 𝕜 (s ×ˢ t) (a, b) :=
  max_le (mapsTo_fst_prod.egauge_le 𝕜 (MulActionHom.fst 𝕜 E F) (a, b))
    (MapsTo.egauge_le 𝕜 (MulActionHom.snd 𝕜 E F) mapsTo_snd_prod (a, b))

end SMul

section SMulZero

variable (𝕜 : Type*) [NNNorm 𝕜] [Nonempty 𝕜] {E : Type*} [Zero E] [SMulZeroClass 𝕜 E] {x : E}

/--
lemma `egauge_zero_left_eq_top` / 引理 `egauge_zero_left_eq_top`

English:
lemma egauge_zero_left_eq_top
  statement: egauge 𝕜 0 x = ∞ ↔ x != 0
  proof: by
  simp [egauge_eq_top]

@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top

中文:
引理 egauge_zero_left_eq_top
  结论: egauge 𝕜 0 x = ∞ ↔ x != 0
  证明: by
  simp [egauge_eq_top]

@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top
-/
@[simp] lemma egauge_zero_left_eq_top : egauge 𝕜 0 x = ∞ ↔ x != 0 := by
  simp [egauge_eq_top]

@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top

end SMulZero

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {c : 𝕜} {s : Set E} {x : E}

/--
lemma `egauge_le_of_smul_mem_of_ne` / 引理 `egauge_le_of_smul_mem_of_ne`

English:
lemma egauge_le_of_smul_mem_of_ne
  given: (h : c • x in s) (hc : c != 0)
  statement: egauge 𝕜 s x <= (‖c‖₊⁻¹ : Real>=0)
  proof: by
  rw [← nnnorm_inv]
exact egauge_le_of_mem_smul (mem_inv_smul_set_iff₀ hc _ _).2 h

中文:
引理 egauge_le_of_smul_mem_of_ne
  条件: (h : c • x in s) (hc : c != 0)
  结论: egauge 𝕜 s x <= (‖c‖₊⁻¹ : 实数>=0)
  证明: by
  rw [← nnnorm_inv]
exact egauge_le_of_mem_smul (mem_inv_smul_set_iff₀ hc _ _).2 h

Depends on / 依赖: egauge_le_of_mem_smul, nnnorm_inv
-/
lemma egauge_le_of_smul_mem_of_ne (h : c • x in s) (hc : c != 0) : egauge 𝕜 s x <= (‖c‖₊⁻¹ : Real>=0) := by
  rw [← nnnorm_inv]
exact egauge_le_of_mem_smul (mem_inv_smul_set_iff₀ hc _ _).2 h

/--
lemma `egauge_le_of_smul_mem` / 引理 `egauge_le_of_smul_mem`

English:
lemma egauge_le_of_smul_mem
  given: (h : c • x in s)
  statement: egauge 𝕜 s x <= ‖c‖ₑ⁻¹
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le

中文:
引理 egauge_le_of_smul_mem
  条件: (h : c • x in s)
  结论: egauge 𝕜 s x <= ‖c‖ₑ⁻¹
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le

Depends on / 依赖: ENNReal, ENNReal.coe_inv_le, coe_inv_le, egauge_le_of_smul_mem_of_ne, eq_or_ne
-/
lemma egauge_le_of_smul_mem (h : c • x in s) : egauge 𝕜 s x <= ‖c‖ₑ⁻¹ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le

/--
lemma `mem_smul_of_egauge_lt` / 引理 `mem_smul_of_egauge_lt`

English:
lemma mem_smul_of_egauge_lt
  given: (hs : Balanced 𝕜 s) (hc : egauge 𝕜 s x < ‖c‖ₑ)
  statement: x in c • s
  proof: let ⟨a, hxa, ha⟩ := egauge_lt_iff.1 hc
  hs.smul_mono (by simpa [enorm] using! ha.le) hxa

中文:
引理 mem_smul_of_egauge_lt
  条件: (hs : Balanced 𝕜 s) (hc : egauge 𝕜 s x < ‖c‖ₑ)
  结论: x in c • s
  证明: let ⟨a, hxa, ha⟩ := egauge_lt_iff.1 hc
  hs.smul_mono (by simpa [enorm] using! ha.le) hxa

Depends on / 依赖: egauge_lt_iff, ha.le, hs.smul_mono, smul_mono
-/
lemma mem_smul_of_egauge_lt (hs : Balanced 𝕜 s) (hc : egauge 𝕜 s x < ‖c‖ₑ) : x in c • s :=
  let ⟨a, hxa, ha⟩ := egauge_lt_iff.1 hc
  hs.smul_mono (by simpa [enorm] using! ha.le) hxa

/--
lemma `mem_of_egauge_lt_one` / 引理 `mem_of_egauge_lt_one`

English:
lemma mem_of_egauge_lt_one
  given: (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1)
  statement: x in s
  proof: one_smul 𝕜 s ▸ mem_smul_of_egauge_lt hs (by simpa)

中文:
引理 mem_of_egauge_lt_one
  条件: (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1)
  结论: x in s
  证明: one_smul 𝕜 s ▸ mem_smul_of_egauge_lt hs (by simpa)

Depends on / 依赖: mem_smul_of_egauge_lt, one_smul
-/
lemma mem_of_egauge_lt_one (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1) : x in s :=
  one_smul 𝕜 s ▸ mem_smul_of_egauge_lt hs (by simpa)

/--
lemma `egauge_eq_zero_iff` / 引理 `egauge_eq_zero_iff`

English:
lemma egauge_eq_zero_iff
  statement: egauge 𝕜 s x = 0 ↔ existsᶠ c : 𝕜 in 𝓝 0, x in c • s
  proof: by
  refine (iInf₂_eq_bot _).trans ?_
  rw [(nhds_basis_uniformity uniformity_basis_edist).frequently_iff]
  simp [and_comm]

@[simp]

中文:
引理 egauge_eq_zero_iff
  结论: egauge 𝕜 s x = 0 ↔ 存在ᶠ c : 𝕜 in 𝓝 0, x in c • s
  证明: by
  refine (iInf₂_eq_bot _).trans ?_
  rw [(nhds_basis_uniformity uniformity_basis_edist).frequently_iff]
  simp [and_comm]

@[simp]

Depends on / 依赖: and_comm, frequently_iff, nhds_basis_uniformity, uniformity_basis_edist
-/
lemma egauge_eq_zero_iff : egauge 𝕜 s x = 0 ↔ existsᶠ c : 𝕜 in 𝓝 0, x in c • s := by
  refine (iInf₂_eq_bot _).trans ?_
  rw [(nhds_basis_uniformity uniformity_basis_edist).frequently_iff]
  simp [and_comm]

@[simp]
/--
lemma `egauge_univ` / 引理 `egauge_univ`

English:
lemma egauge_univ
  given: [(𝓝[!=] (0 : 𝕜)).NeBot]
  statement: egauge 𝕜 univ x = 0
  proof: by
  rw [egauge_eq_zero_iff]
  refine (frequently_iff_neBot.2 ‹_›).mono fun c hc => ?_
  simp_all [smul_set_univ₀]

中文:
引理 egauge_univ
  条件: [(𝓝[!=] (0 : 𝕜)).NeBot]
  结论: egauge 𝕜 univ x = 0
  证明: by
  rw [egauge_eq_zero_iff]
  refine (frequently_iff_neBot.2 ‹_›).mono fun c hc => ?_
  simp_all [smul_set_univ₀]

Depends on / 依赖: egauge_eq_zero_iff, frequently_iff_neBot
-/
lemma egauge_univ [(𝓝[!=] (0 : 𝕜)).NeBot] : egauge 𝕜 univ x = 0 := by
  rw [egauge_eq_zero_iff]
  refine (frequently_iff_neBot.2 ‹_›).mono fun c hc => ?_
  simp_all [smul_set_univ₀]

variable (𝕜)

@[simp]
/--
lemma `egauge_zero_right` / 引理 `egauge_zero_right`

English:
lemma egauge_zero_right
  given: (hs : s.Nonempty)
  statement: egauge 𝕜 s 0 = 0
  proof: by
  have : 0 in (0 : 𝕜) • s := by simp [zero_smul_set hs]
  simpa using egauge_le_of_mem_smul this

中文:
引理 egauge_zero_right
  条件: (hs : s.非空)
  结论: egauge 𝕜 s 0 = 0
  证明: by
  have : 0 in (0 : 𝕜) • s := by simp [zero_smul_set hs]
  simpa using egauge_le_of_mem_smul this

Depends on / 依赖: egauge_le_of_mem_smul, zero_smul_set
-/
lemma egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 0 := by
  have : 0 in (0 : 𝕜) • s := by simp [zero_smul_set hs]
  simpa using egauge_le_of_mem_smul this

/--
lemma `egauge_zero_zero` / 引理 `egauge_zero_zero`

English:
lemma egauge_zero_zero
  statement: egauge 𝕜 (0 : Set E) 0 = 0
  proof: by simp

中文:
引理 egauge_zero_zero
  结论: egauge 𝕜 (0 : 集合 E) 0 = 0
  证明: by simp
-/
lemma egauge_zero_zero : egauge 𝕜 (0 : Set E) 0 = 0 := by simp

/--
lemma `egauge_le_one` / 引理 `egauge_le_one`

English:
lemma egauge_le_one
  given: (h : x in s)
  statement: egauge 𝕜 s x <= 1
  proof: by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h

中文:
引理 egauge_le_one
  条件: (h : x in s)
  结论: egauge 𝕜 s x <= 1
  证明: by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h

Depends on / 依赖: egauge_le_of_mem_smul, one_smul
-/
lemma egauge_le_one (h : x in s) : egauge 𝕜 s x <= 1 := by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h

variable {𝕜}

/--
lemma `le_egauge_of_forall_ne_zero` / 引理 `le_egauge_of_forall_ne_zero`

English:
lemma le_egauge_of_forall_ne_zero
  statement: [(𝓝[!=] (0 : 𝕜)).NeBot] {r : Real>=0∞}
  proof: by
  rw [le_egauge_iff]
  intro c hc
  rcases ne_or_eq c 0 with hc₀ | rfl
  · exact h c hc₀ hc
  obtain rfl : x = 0 := by
    grw [zero_smul_set_subset, Set.mem_zero] at hc
    exact hc
  apply le_of_forall_gt
  intro b hb
rcases Filter.nonempty_of_mem
    inter_mem_nhdsWithin {(0 : 𝕜)}ᶜ (Metric.eba

中文:
引理 le_egauge_of_对任意_ne_zero
  结论: [(𝓝[!=] (0 : 𝕜)).NeBot] {r : 实数>=0∞}
  证明: by
  rw [le_egauge_iff]
  intro c hc
  rcases ne_or_eq c 0 with hc₀ | rfl
  · exact h c hc₀ hc
  obtain rfl : x = 0 := by
    grw [zero_smul_set_subset, Set.mem_zero] at hc
    exact hc
  apply le_of_forall_gt
  intro b hb
rcases Filter.nonempty_of_mem
    inter_mem_nhdsWithin {(0 : 𝕜)}ᶜ (Metric.eba

Depends on / 依赖: Filter, Filter.nonempty_of_mem, Metric, Metric.eball_mem_nhds, Set.mem_zero, eball_mem_nhds, inter_mem_nhdsWithin, le_egauge_iff, le_of_forall_gt, mem_zero, ne_or_eq, nonempty_of_mem, trans_lt, zero_smul_set_subset
-/
lemma le_egauge_of_forall_ne_zero [(𝓝[!=] (0 : 𝕜)).NeBot] {r : Real>=0∞}
    (hs₀ : 0 in s) (h : forall c : 𝕜, c != 0 -> x in c • s -> r <= ‖c‖ₑ) : r <= egauge 𝕜 s x := by
  rw [le_egauge_iff]
  intro c hc
  rcases ne_or_eq c 0 with hc₀ | rfl
  · exact h c hc₀ hc
  obtain rfl : x = 0 := by
    grw [zero_smul_set_subset, Set.mem_zero] at hc
    exact hc
  apply le_of_forall_gt
  intro b hb
rcases Filter.nonempty_of_mem
    inter_mem_nhdsWithin {(0 : 𝕜)}ᶜ (Metric.eball_mem_nhds 0 (by simpa using hb))
    with ⟨c, hc₀, hcb⟩
  exact (h c (by simpa using hc₀) ⟨_, hs₀, by simp⟩).trans_lt (by simpa using hcb)

/--
lemma `le_egauge_smul_left` / 引理 `le_egauge_smul_left`

English:
lemma le_egauge_smul_left
  given: (c : 𝕜) (s : Set E) (x : E)
  proof: by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← enorm_mul]
exact egauge_le_of_mem_smul smul_mem_smul_set hx

中文:
引理 le_egauge_smul_left
  条件: (c : 𝕜) (s : 集合 E) (x : E)
  证明: by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← enorm_mul]
exact egauge_le_of_mem_smul smul_mem_smul_set hx

Depends on / 依赖: ENNReal, ENNReal.div_le_of_le_mul, div_le_of_le_mul, egauge_le_of_mem_smul, enorm_mul, le_egauge_iff, simp_rw, smul_mem_smul_set, smul_smul
-/
lemma le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) :
    egauge 𝕜 s x / ‖c‖ₑ <= egauge 𝕜 (c • s) x := by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← enorm_mul]
exact egauge_le_of_mem_smul smul_mem_smul_set hx

/--
lemma `egauge_smul_left` / 引理 `egauge_smul_left`

English:
lemma egauge_smul_left
  given: (hc : c != 0) (s : Set E) (x : E)
  proof: by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  rw [ENNReal.le_div_iff_mul_le (by simp [*]) (by simp)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖ₑ = egauge 𝕜 (c • s) x / ‖c⁻¹‖ₑ := by
      rw [enorm_inv (by simpa)]; rw [div_eq_mul_inv]; rw [inv_inv]
    _ <= egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_s

中文:
引理 egauge_smul_left
  条件: (hc : c != 0) (s : 集合 E) (x : E)
  证明: by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  rw [ENNReal.le_div_iff_mul_le (by simp [*]) (by simp)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖ₑ = egauge 𝕜 (c • s) x / ‖c⁻¹‖ₑ := by
      rw [enorm_inv (by simpa)]; rw [div_eq_mul_inv]; rw [inv_inv]
    _ <= egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_s

Depends on / 依赖: ENNReal, ENNReal.le_div_iff_mul_le, div_eq_mul_inv, egauge, enorm_inv, inv_inv, le_antisymm, le_div_iff_mul_le, le_egauge_smul_left
-/
lemma egauge_smul_left (hc : c != 0) (s : Set E) (x : E) :
    egauge 𝕜 (c • s) x = egauge 𝕜 s x / ‖c‖ₑ := by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  rw [ENNReal.le_div_iff_mul_le (by simp [*]) (by simp)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖ₑ = egauge 𝕜 (c • s) x / ‖c⁻¹‖ₑ := by
      rw [enorm_inv (by simpa)]; rw [div_eq_mul_inv]; rw [inv_inv]
    _ <= egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_smul_left _ _ _
    _ = egauge 𝕜 s x := by rw [inv_smul_smul₀ hc]

/--
lemma `le_egauge_smul_right` / 引理 `le_egauge_smul_right`

English:
lemma le_egauge_smul_right
  given: (c : 𝕜) (s : Set E) (x : E)
  proof: by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
· refine ENNReal.mul_le_of_le_div' le_trans ?_ ENNReal.coe_div_le
    rw [div_eq_inv_mul]; rw [← nnnorm_inv]; rw [← nnnorm_mul]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [mul_smul, hxy, inv_

中文:
引理 le_egauge_smul_right
  条件: (c : 𝕜) (s : 集合 E) (x : E)
  证明: by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
· refine ENNReal.mul_le_of_le_div' le_trans ?_ ENNReal.coe_div_le
    rw [div_eq_inv_mul]; rw [← nnnorm_inv]; rw [← nnnorm_mul]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [mul_smul, hxy, inv_

Depends on / 依赖: ENNReal, ENNReal.coe_div_le, ENNReal.mul_le_of_le_div, coe_div_le, div_eq_inv_mul, egauge_le_of_mem_smul, eq_or_ne, le_egauge_iff, le_trans, mul_le_of_le_div, mul_smul, nnnorm_inv, nnnorm_mul
-/
lemma le_egauge_smul_right (c : 𝕜) (s : Set E) (x : E) :
    ‖c‖ₑ * egauge 𝕜 s x <= egauge 𝕜 s (c • x) := by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
· refine ENNReal.mul_le_of_le_div' le_trans ?_ ENNReal.coe_div_le
    rw [div_eq_inv_mul]; rw [← nnnorm_inv]; rw [← nnnorm_mul]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [mul_smul, hxy, inv_smul_smul₀ hc]

/--
lemma `egauge_smul_right` / 引理 `egauge_smul_right`

English:
lemma egauge_smul_right
  given: (h : c = 0 -> s.Nonempty) (x : E)
  proof: by
  refine le_antisymm ?_ (le_egauge_smul_right c s x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [egauge_zero_right _ (h rfl)]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl enorm_ne_top),
      ENNReal.div_eq_inv_mul, ← enorm_inv (by simpa)]
    refine (le_egauge_smul_ri

中文:
引理 egauge_smul_right
  条件: (h : c = 0 -> s.非空) (x : E)
  证明: by
  refine le_antisymm ?_ (le_egauge_smul_right c s x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [egauge_zero_right _ (h rfl)]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl enorm_ne_top),
      ENNReal.div_eq_inv_mul, ← enorm_inv (by simpa)]
    refine (le_egauge_smul_ri

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.div_le_iff_le_mul, div_eq_inv_mul, div_le_iff_le_mul, egauge_zero_right, enorm_inv, enorm_ne_top, eq_or_ne, le_antisymm, le_egauge_smul_right, mul_comm, trans_eq
-/
lemma egauge_smul_right (h : c = 0 -> s.Nonempty) (x : E) :
    egauge 𝕜 s (c • x) = ‖c‖ₑ * egauge 𝕜 s x := by
  refine le_antisymm ?_ (le_egauge_smul_right c s x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [egauge_zero_right _ (h rfl)]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl enorm_ne_top),
      ENNReal.div_eq_inv_mul, ← enorm_inv (by simpa)]
    refine (le_egauge_smul_right _ _ _).trans_eq ?_
    rw [inv_smul_smul₀ hc]

/--
theorem `egauge_prod_mk` / 定理 `egauge_prod_mk`

English:
theorem egauge_prod_mk
  statement: {F : Type*} [AddCommGroup F] [Module 𝕜 F] {U : Set E} {V : Set F}
  proof: by
  refine le_antisymm (le_of_forall_gt fun r hr => ?_) (le_egauge_prod _ _ _ _)
  simp only [max_lt_iff, egauge_lt_iff, smul_set_prod] at hr ⊢
  rcases hr with ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
  cases le_total ‖x‖ ‖y‖ with
  | inl hle => exact ⟨y, ⟨hU.smul_mono hle hx, hy⟩, hyr⟩
  | inr hle => exact ⟨

中文:
定理 egauge_prod_mk
  结论: {F : 类型} [加法交换群 F] [模 𝕜 F] {U : 集合 E} {V : 集合 F}
  证明: by
  refine le_antisymm (le_of_forall_gt fun r hr => ?_) (le_egauge_prod _ _ _ _)
  simp only [max_lt_iff, egauge_lt_iff, smul_set_prod] at hr ⊢
  rcases hr with ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
  cases le_total ‖x‖ ‖y‖ with
  | inl hle => exact ⟨y, ⟨hU.smul_mono hle hx, hy⟩, hyr⟩
  | inr hle => exact ⟨

Depends on / 依赖: egauge_lt_iff, hU.smul_mono, hV.smul_mono, le_antisymm, le_egauge_prod, le_of_forall_gt, le_total, max_lt_iff, smul_mono, smul_set_prod
-/
theorem egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F] {U : Set E} {V : Set F}
    (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F) :
    egauge 𝕜 (U ×ˢ V) (a, b) = max (egauge 𝕜 U a) (egauge 𝕜 V b) := by
  refine le_antisymm (le_of_forall_gt fun r hr => ?_) (le_egauge_prod _ _ _ _)
  simp only [max_lt_iff, egauge_lt_iff, smul_set_prod] at hr ⊢
  rcases hr with ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
  cases le_total ‖x‖ ‖y‖ with
  | inl hle => exact ⟨y, ⟨hU.smul_mono hle hx, hy⟩, hyr⟩
  | inr hle => exact ⟨x, ⟨hx, hV.smul_mono hle hy⟩, hxr⟩

/--
theorem `egauge_add_add_le` / 定理 `egauge_add_add_le`

English:
theorem egauge_add_add_le
  given: {U V : Set E} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a b : E)
  proof: by
  rw [← egauge_prod_mk hU hV a b]; rw [← add_image_prod]
  exact MapsTo.egauge_le 𝕜 (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E) (mapsTo_image _ _) (a, b)

中文:
定理 egauge_add_add_le
  条件: {U V : 集合 E} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a b : E)
  证明: by
  rw [← egauge_prod_mk hU hV a b]; rw [← add_image_prod]
  exact MapsTo.egauge_le 𝕜 (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E) (mapsTo_image _ _) (a, b)

Depends on / 依赖: LinearMap, LinearMap.fst, LinearMap.snd, MapsTo, MapsTo.egauge_le, add_image_prod, egauge_le, egauge_prod_mk, mapsTo_image
-/
theorem egauge_add_add_le {U V : Set E} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a b : E) :
    egauge 𝕜 (U + V) (a + b) <= max (egauge 𝕜 U a) (egauge 𝕜 V b) := by
  rw [← egauge_prod_mk hU hV a b]; rw [← add_image_prod]
  exact MapsTo.egauge_le 𝕜 (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E) (mapsTo_image _ _) (a, b)

end NormedDivisionRing

section Pi

variable {𝕜 : Type*} {ι : Type*} {E : ι -> Type*}
variable [NormedDivisionRing 𝕜] [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]

/--
theorem `egauge_pi'` / 定理 `egauge_pi'`

English:
theorem egauge_pi'
  statement: {I : Set ι} (hI : I.Finite)
  proof: by
  refine le_antisymm ?_ (iSup₂_le fun i hi => le_egauge_pi hi _ _)
  refine le_of_forall_gt fun r hr => ?_
  have : forall i in I, exists c : 𝕜, x i in c • U i ∧ ‖c‖ₑ < r := fun i hi =>
egauge_lt_iff.mp (le_iSup₂ i hi).trans_lt hr
  choose! c hc hcr using this
  obtain ⟨c₀, hc₀, hc₀I, hc₀r⟩ :
   

中文:
定理 egauge_pi'
  结论: {I : 集合 ι} (hI : I.有限)
  证明: by
  refine le_antisymm ?_ (iSup₂_le fun i hi => le_egauge_pi hi _ _)
  refine le_of_forall_gt fun r hr => ?_
  have : forall i in I, exists c : 𝕜, x i in c • U i ∧ ‖c‖ₑ < r := fun i hi =>
egauge_lt_iff.mp (le_iSup₂ i hi).trans_lt hr
  choose! c hc hcr using this
  obtain ⟨c₀, hc₀, hc₀I, hc₀r⟩ :
   

Depends on / 依赖: I.eq_empty_or_nonempty, IsEmpty, bot_lt, egauge_lt_iff, egauge_lt_iff.mp, eq_empty_or_nonempty, hr.bot_lt, le_antisymm, le_egauge_pi, le_of_forall_gt, trans_lt
-/
theorem egauge_pi' {I : Set ι} (hI : I.Finite)
    {U : forall i, Set (E i)} (hU : forall i in I, Balanced 𝕜 (U i))
    (x : forall i, E i) (hI₀ : I = univ ∨ (exists i in I, x i != 0) ∨ (𝓝[!=] (0 : 𝕜)).NeBot) :
    egauge 𝕜 (I.pi U) x = ⨆ i in I, egauge 𝕜 (U i) (x i) := by
  refine le_antisymm ?_ (iSup₂_le fun i hi => le_egauge_pi hi _ _)
  refine le_of_forall_gt fun r hr => ?_
  have : forall i in I, exists c : 𝕜, x i in c • U i ∧ ‖c‖ₑ < r := fun i hi =>
egauge_lt_iff.mp (le_iSup₂ i hi).trans_lt hr
  choose! c hc hcr using this
  obtain ⟨c₀, hc₀, hc₀I, hc₀r⟩ :
      exists c₀ : 𝕜, (c₀ != 0 ∨ I = univ) ∧ (forall i in I, ‖c i‖ <= ‖c₀‖) ∧ ‖c₀‖ₑ < r := by
    have hr₀ : 0 < r := hr.bot_lt
    rcases I.eq_empty_or_nonempty with rfl | hIne
    · obtain hι | hbot : IsEmpty ι ∨ (𝓝[!=] (0 : 𝕜)).NeBot := by simpa [@eq_comm _ ∅] using hI₀
      · use 0
        simp [@eq_comm _ ∅, hι, hr₀]
      · rcases exists_enorm_lt 𝕜 hr₀.ne' with ⟨c₀, hc₀, hc₀r⟩
        exact ⟨c₀, .inl hc₀, by simp, hc₀r⟩
    · obtain ⟨i₀, hi₀I, hc_max⟩ : exists i₀ in I, IsMaxOn (‖c ·‖ₑ) I i₀ :=
        exists_max_image _ (‖c ·‖ₑ) hI hIne
      by_cases! H : c i₀ != 0 ∨ I = univ
      · exact ⟨c i₀, H, fun i hi => by simpa [enorm] using! hc_max hi, hcr _ hi₀I⟩
      · have hc0 (i : ι) (hi : i in I) : c i = 0 := by simpa [H] using hc_max hi
        have heg0 (i : ι) (hi : i in I) : x i = 0 :=
          zero_smul_set_subset (α := 𝕜) (U i) (hc0 i hi ▸ hc i hi)
        have : (𝓝[!=] (0 : 𝕜)).NeBot := (hI₀.resolve_left H.2).resolve_left (by simpa)
        rcases exists_enorm_lt 𝕜 hr₀.ne' with ⟨c₁, hc₁, hc₁r⟩
        refine ⟨c₁, .inl hc₁, fun i hi => ?_, hc₁r⟩
        simp [hc0 i hi]
  refine egauge_lt_iff.2 ⟨c₀, ?_, hc₀r⟩
  rw [smul_set_pi₀' hc₀]
  intro i hi
  exact (hU i hi).smul_mono (hc₀I i hi) (hc i hi)

/--
theorem `egauge_univ_pi` / 定理 `egauge_univ_pi`

English:
theorem egauge_univ_pi
  given: [Finite ι] {U : forall i, Set (E i)} (hU : forall i, Balanced 𝕜 (U i)) (x : forall i, E i)
  proof: .trans by simp egauge_pi' finite_univ (fun i _ => hU i) x (.inl rfl)

中文:
定理 egauge_univ_pi
  条件: [有限 ι] {U : 对任意 i, 集合 (E i)} (hU : 对任意 i, Balanced 𝕜 (U i)) (x : 对任意 i, E i)
  证明: .trans by simp egauge_pi' finite_univ (fun i _ => hU i) x (.inl rfl)

Depends on / 依赖: egauge_pi, finite_univ
-/
theorem egauge_univ_pi [Finite ι] {U : forall i, Set (E i)} (hU : forall i, Balanced 𝕜 (U i)) (x : forall i, E i) :
    egauge 𝕜 (univ.pi U) x = ⨆ i, egauge 𝕜 (U i) (x i) :=
.trans by simp egauge_pi' finite_univ (fun i _ => hU i) x (.inl rfl)

/--
theorem `egauge_pi` / 定理 `egauge_pi`

English:
theorem egauge_pi
  statement: [(𝓝[!=] (0 : 𝕜)).NeBot] {I : Set ι} {U : forall i, Set (E i)}
  proof: egauge_pi' hI hU x .inr .inr inferInstance

中文:
定理 egauge_pi
  结论: [(𝓝[!=] (0 : 𝕜)).NeBot] {I : 集合 ι} {U : 对任意 i, 集合 (E i)}
  证明: egauge_pi' hI hU x .inr .inr inferInstance

Depends on / 依赖: egauge_pi
-/
theorem egauge_pi [(𝓝[!=] (0 : 𝕜)).NeBot] {I : Set ι} {U : forall i, Set (E i)}
    (hI : I.Finite) (hU : forall i in I, Balanced 𝕜 (U i)) (x : forall i, E i) :
    egauge 𝕜 (I.pi U) x = ⨆ i in I, egauge 𝕜 (U i) (x i) :=
egauge_pi' hI hU x .inr .inr inferInstance

end Pi

section SeminormedAddCommGroup

variable (𝕜 : Type*) [NormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
lemma `div_le_egauge_closedBall` / 引理 `div_le_egauge_closedBall`

English:
lemma div_le_egauge_closedBall
  given: (r : Real>=0) (x : E)
  statement: ‖x‖ₑ / r <= egauge 𝕜 (closedBall 0 r) x
  proof: by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe] at hy
  rw [enorm_smul]
  apply ENNReal.div_le_of_le_mul
  gcongr
  rwa [enorm_le_coe]

中文:
引理 div_le_egauge_closedBall
  条件: (r : 实数>=0) (x : E)
  结论: ‖x‖ₑ / r <= egauge 𝕜 (closedBall 0 r) x
  证明: by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe] at hy
  rw [enorm_smul]
  apply ENNReal.div_le_of_le_mul
  gcongr
  rwa [enorm_le_coe]

Depends on / 依赖: ENNReal, ENNReal.div_le_of_le_mul, NNReal, NNReal.coe_le_coe, coe_le_coe, coe_nnnorm, div_le_of_le_mul, enorm_le_coe, enorm_smul, le_egauge_iff, mem_closedBall_zero_iff
-/
lemma div_le_egauge_closedBall (r : Real>=0) (x : E) : ‖x‖ₑ / r <= egauge 𝕜 (closedBall 0 r) x := by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe] at hy
  rw [enorm_smul]
  apply ENNReal.div_le_of_le_mul
  gcongr
  rwa [enorm_le_coe]

/--
lemma `le_egauge_closedBall_one` / 引理 `le_egauge_closedBall_one`

English:
lemma le_egauge_closedBall_one
  given: (x : E)
  statement: ‖x‖ₑ <= egauge 𝕜 (closedBall 0 1) x
  proof: by
  simpa using div_le_egauge_closedBall 𝕜 1 x

中文:
引理 le_egauge_closedBall_one
  条件: (x : E)
  结论: ‖x‖ₑ <= egauge 𝕜 (closedBall 0 1) x
  证明: by
  simpa using div_le_egauge_closedBall 𝕜 1 x

Depends on / 依赖: div_le_egauge_closedBall
-/
lemma le_egauge_closedBall_one (x : E) : ‖x‖ₑ <= egauge 𝕜 (closedBall 0 1) x := by
  simpa using div_le_egauge_closedBall 𝕜 1 x

/--
lemma `div_le_egauge_ball` / 引理 `div_le_egauge_ball`

English:
lemma div_le_egauge_ball
  given: (r : Real>=0) (x : E)
  statement: ‖x‖ₑ / r <= egauge 𝕜 (ball 0 r) x
  proof: (div_le_egauge_closedBall 𝕜 r x).trans egauge_anti _ ball_subset_closedBall _

中文:
引理 div_le_egauge_ball
  条件: (r : 实数>=0) (x : E)
  结论: ‖x‖ₑ / r <= egauge 𝕜 (ball 0 r) x
  证明: (div_le_egauge_closedBall 𝕜 r x).trans egauge_anti _ ball_subset_closedBall _

Depends on / 依赖: ball_subset_closedBall, div_le_egauge_closedBall, egauge_anti
-/
lemma div_le_egauge_ball (r : Real>=0) (x : E) : ‖x‖ₑ / r <= egauge 𝕜 (ball 0 r) x :=
(div_le_egauge_closedBall 𝕜 r x).trans egauge_anti _ ball_subset_closedBall _

/--
lemma `le_egauge_ball_one` / 引理 `le_egauge_ball_one`

English:
lemma le_egauge_ball_one
  given: (x : E)
  statement: ‖x‖ₑ <= egauge 𝕜 (ball 0 1) x
  proof: by
  simpa using div_le_egauge_ball 𝕜 1 x

中文:
引理 le_egauge_ball_one
  条件: (x : E)
  结论: ‖x‖ₑ <= egauge 𝕜 (ball 0 1) x
  证明: by
  simpa using div_le_egauge_ball 𝕜 1 x

Depends on / 依赖: div_le_egauge_ball
-/
lemma le_egauge_ball_one (x : E) : ‖x‖ₑ <= egauge 𝕜 (ball 0 1) x := by
  simpa using div_le_egauge_ball 𝕜 1 x

variable {𝕜}
variable {c : 𝕜} {x : E} {r : Real>=0}

/--
lemma `egauge_ball_le_of_one_lt_norm` / 引理 `egauge_ball_le_of_one_lt_norm`

English:
lemma egauge_ball_le_of_one_lt_norm
  given: (hc : 1 < ‖c‖) (h₀ : r != 0 ∨ ‖x‖ != 0)
  proof: by
  let : NontriviallyNormedField 𝕜 := ⟨c, hc⟩
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa [enorm, ← NNReal.coe_eq_zero] using h₀
  · rcases eq_or_ne ‖x‖ 0 with hx | hx
    · 

中文:
引理 egauge_ball_le_of_one_lt_norm
  条件: (hc : 1 < ‖c‖) (h₀ : r != 0 ∨ ‖x‖ != 0)
  证明: by
  let : NontriviallyNormedField 𝕜 := ⟨c, hc⟩
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa [enorm, ← NNReal.coe_eq_zero] using h₀
  · rcases eq_or_ne ‖x‖ 0 with hx | hx
    · 

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.div_zero, ENNReal.zero_div, NNReal, NNReal.coe_eq_zero, NontriviallyNormedField, coe_eq_zero, coe_nnnorm, coe_zero, div_zero, egauge_eq_zero_iff, eq_or_ne, eq_zero_or_pos, frequently_iff_neBot, le_top, mul_ne_zero, mul_zero, nonpos_iff_eq_zero, one_pos
-/
lemma egauge_ball_le_of_one_lt_norm (hc : 1 < ‖c‖) (h₀ : r != 0 ∨ ‖x‖ != 0) :
    egauge 𝕜 (ball 0 r) x <= ‖c‖ₑ * ‖x‖ₑ / r := by
  let : NontriviallyNormedField 𝕜 := ⟨c, hc⟩
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa [enorm, ← NNReal.coe_eq_zero] using h₀
  · rcases eq_or_ne ‖x‖ 0 with hx | hx
    · have hx' : ‖x‖ₑ = 0 := by simpa [enorm, ← coe_nnnorm, NNReal.coe_eq_zero] using hx
      simp only [hx', mul_zero, ENNReal.zero_div, nonpos_iff_eq_zero, egauge_eq_zero_iff]
      refine (frequently_iff_neBot.2 (inferInstance : NeBot (𝓝[!=] (0 : 𝕜)))).mono fun c hc => ?_
      simp [mem_smul_set_iff_inv_smul_mem₀ hc, norm_smul, hx, hr]
    · rcases rescale_to_shell_semi_normed hc hr hx with ⟨a, ha₀, har, -, hainv⟩
      calc
        egauge 𝕜 (ball 0 r) x <= ↑(‖a‖₊⁻¹) :=
          egauge_le_of_smul_mem_of_ne (mem_ball_zero_iff.2 har) ha₀
        _ <= ↑(‖c‖₊ * ‖x‖₊ / r) := by rwa [ENNReal.coe_le_coe, div_eq_inv_mul, ← mul_assoc]
_ <= ‖c‖ₑ * ‖x‖ₑ / r := ENNReal.coe_div_le.trans by simp [ENNReal.coe_mul, enorm]

/--
lemma `egauge_ball_one_le_of_one_lt_norm` / 引理 `egauge_ball_one_le_of_one_lt_norm`

English:
lemma egauge_ball_one_le_of_one_lt_norm
  given: (hc : 1 < ‖c‖) (x : E)
  proof: by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)

中文:
引理 egauge_ball_one_le_of_one_lt_norm
  条件: (hc : 1 < ‖c‖) (x : E)
  证明: by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)

Depends on / 依赖: egauge_ball_le_of_one_lt_norm, one_ne_zero
-/
lemma egauge_ball_one_le_of_one_lt_norm (hc : 1 < ‖c‖) (x : E) :
    egauge 𝕜 (ball 0 1) x <= ‖c‖ₑ * ‖x‖ₑ := by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)

end SeminormedAddCommGroup
