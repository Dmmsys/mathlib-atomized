/-
Copyright (c) 2024 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous bundled maps on intervals

In this file we prove a few results about `ContinuousMap` when the domain is an interval.
-/

@[expose] public section

open Set ContinuousMap Filter Topology

namespace ContinuousMap

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable {a b c : α} [Fact (a <= b)] [Fact (b <= c)]
variable {E : Type*} [TopologicalSpace E]

/--
Definition of `IccInclusionLeft` / `IccInclusionLeft` 的定义

English:
definition IccInclusionLeft
  signature: : C(Icc a b, Icc a c)
  body: .inclusion Icc_subset_Icc le_rfl Fact.out

中文:
定义 IccInclusionLeft
  签名: : C(闭区间 a b, 闭区间 a c)
  定义体: .inclusion Icc_subset_Icc le_rfl Fact.out

Depends on / 依赖: Fact.out, Icc_subset_Icc, inclusion, le_rfl
-/
def IccInclusionLeft : C(Icc a b, Icc a c) :=
.inclusion Icc_subset_Icc le_rfl Fact.out

/--
Definition of `IccInclusionRight` / `IccInclusionRight` 的定义

English:
definition IccInclusionRight
  signature: : C(Icc b c, Icc a c)
  body: .inclusion Icc_subset_Icc Fact.out le_rfl

中文:
定义 IccInclusionRight
  签名: : C(闭区间 b c, 闭区间 a c)
  定义体: .inclusion Icc_subset_Icc Fact.out le_rfl

Depends on / 依赖: Fact.out, Icc_subset_Icc, inclusion, le_rfl
-/
def IccInclusionRight : C(Icc b c, Icc a c) :=
.inclusion Icc_subset_Icc Fact.out le_rfl

/--
Definition of `projIccCM` / `projIccCM` 的定义

English:
definition projIccCM
  signature: : C(α, Icc a b)
  body: ⟨projIcc a b Fact.out, continuous_projIcc⟩

中文:
定义 projIccCM
  签名: : C(α, 闭区间 a b)
  定义体: ⟨projIcc a b Fact.out, continuous_projIcc⟩

Depends on / 依赖: Fact.out, continuous_projIcc, projIcc
-/
def projIccCM : C(α, Icc a b) :=
  ⟨projIcc a b Fact.out, continuous_projIcc⟩

/--
Definition of `IccExtendCM` / `IccExtendCM` 的定义

English:
definition IccExtendCM
  signature: : C(C(Icc a b, E), C(α, E)) where
  body: f.comp projIccCM
  continuous_toFun := continuous_precomp projIccCM

@[simp]

中文:
定义 IccExtendCM
  签名: : C(C(闭区间 a b, E), C(α, E)) where
  定义体: f.comp projIccCM
  continuous_toFun := continuous_precomp projIccCM

@[simp]

Depends on / 依赖: f.comp, projIccCM
-/
def IccExtendCM : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp projIccCM
  continuous_toFun := continuous_precomp projIccCM

@[simp]
/--
theorem `IccExtendCM_of_mem` / 定理 `IccExtendCM_of_mem`

English:
theorem IccExtendCM_of_mem
  given: {f : C(Icc a b, E)} {x : α} (hx : x in Icc a b)
  proof: by
  simp [IccExtendCM, projIccCM, projIcc, hx.1, hx.2]

中文:
定理 IccExtendCM_of_mem
  条件: {f : C(闭区间 a b, E)} {x : α} (hx : x in 闭区间 a b)
  证明: by
  simp [IccExtendCM, projIccCM, projIcc, hx.1, hx.2]

Depends on / 依赖: IccExtendCM, projIcc, projIccCM
-/
theorem IccExtendCM_of_mem {f : C(Icc a b, E)} {x : α} (hx : x in Icc a b) :
    IccExtendCM f x = f ⟨x, hx⟩ := by
  simp [IccExtendCM, projIccCM, projIcc, hx.1, hx.2]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `concat` / `concat` 的定义

English:
definition concat
  signature: (f : C(Icc a b, E)) (g : C(Icc b c, E))
  body: by
  by_cases hb : f ⊤ = g ⊥
  · let h (t : α) : E := if t <= b then IccExtendCM f t else IccExtendCM g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl
    simpa [IccExtendCM, projIccCM]
  · exact .const _ (f ⊥) -- junk value

中文:
定义 concat
  签名: (f : C(闭区间 a b, E)) (g : C(闭区间 b c, E))
  定义体: by
  by_cases hb : f ⊤ = g ⊥
  · let h (t : α) : E := if t <= b then IccExtendCM f t else IccExtendCM g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl
    simpa [IccExtendCM, projIccCM]
  · exact .const _ (f ⊥) -- junk value

Depends on / 依赖: Continuous, Continuous.if_le, IccExtendCM, continuous_const, continuous_id, fun_prop, if_le, projIccCM
-/
noncomputable def concat (f : C(Icc a b, E)) (g : C(Icc b c, E)) :
    C(Icc a c, E) := by
  by_cases hb : f ⊤ = g ⊥
  · let h (t : α) : E := if t <= b then IccExtendCM f t else IccExtendCM g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl
    simpa [IccExtendCM, projIccCM]
  · exact .const _ (f ⊥) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}

/--
theorem `concat_comp_IccInclusionLeft` / 定理 `concat_comp_IccInclusionLeft`

English:
theorem concat_comp_IccInclusionLeft
  given: (hb : f ⊤ = g ⊥)
  proof: by
  ext x
  simp [concat, IccExtendCM, hb, IccInclusionLeft, projIccCM, inclusion, x.2.2]

中文:
定理 concat_comp_IccInclusionLeft
  条件: (hb : f ⊤ = g ⊥)
  证明: by
  ext x
  simp [concat, IccExtendCM, hb, IccInclusionLeft, projIccCM, inclusion, x.2.2]

Depends on / 依赖: IccExtendCM, IccInclusionLeft, concat, inclusion, projIccCM
-/
theorem concat_comp_IccInclusionLeft (hb : f ⊤ = g ⊥) :
    (concat f g).comp IccInclusionLeft = f := by
  ext x
  simp [concat, IccExtendCM, hb, IccInclusionLeft, projIccCM, inclusion, x.2.2]

/--
theorem `concat_comp_IccInclusionRight` / 定理 `concat_comp_IccInclusionRight`

English:
theorem concat_comp_IccInclusionRight
  given: (hb : f ⊤ = g ⊥)
  proof: by
  ext ⟨x, hx⟩
  obtain rfl | hxb := eq_or_ne x b
  · simpa [concat, IccInclusionRight, IccExtendCM, projIccCM, inclusion, hb]
.not_ge · have h : ¬ x <= b := lt_of_le_of_ne hx.1 (Ne.symm hxb)
    simp [concat, hb, IccInclusionRight, h, IccExtendCM, projIccCM, projIcc, inclusion, hx.2, hx.1]

@[simp]

中文:
定理 concat_comp_IccInclusionRight
  条件: (hb : f ⊤ = g ⊥)
  证明: by
  ext ⟨x, hx⟩
  obtain rfl | hxb := eq_or_ne x b
  · simpa [concat, IccInclusionRight, IccExtendCM, projIccCM, inclusion, hb]
.not_ge · have h : ¬ x <= b := lt_of_le_of_ne hx.1 (Ne.symm hxb)
    simp [concat, hb, IccInclusionRight, h, IccExtendCM, projIccCM, projIcc, inclusion, hx.2, hx.1]

@[simp]

Depends on / 依赖: IccExtendCM, IccInclusionRight, Ne.symm, concat, eq_or_ne, inclusion, lt_of_le_of_ne, not_ge, projIcc, projIccCM
-/
theorem concat_comp_IccInclusionRight (hb : f ⊤ = g ⊥) :
    (concat f g).comp IccInclusionRight = g := by
  ext ⟨x, hx⟩
  obtain rfl | hxb := eq_or_ne x b
  · simpa [concat, IccInclusionRight, IccExtendCM, projIccCM, inclusion, hb]
.not_ge · have h : ¬ x <= b := lt_of_le_of_ne hx.1 (Ne.symm hxb)
    simp [concat, hb, IccInclusionRight, h, IccExtendCM, projIccCM, projIcc, inclusion, hx.2, hx.1]

@[simp]
/--
theorem `concat_left` / 定理 `concat_left`

English:
theorem concat_left
  given: (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : t <= b)
  proof: by
  nth_rewrite 2 [← concat_comp_IccInclusionLeft hb]
  rfl

@[simp]

中文:
定理 concat_left
  条件: (hb : f ⊤ = g ⊥) {t : 闭区间 a c} (ht : t <= b)
  证明: by
  nth_rewrite 2 [← concat_comp_IccInclusionLeft hb]
  rfl

@[simp]

Depends on / 依赖: concat_comp_IccInclusionLeft, nth_rewrite
-/
theorem concat_left (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : t <= b) :
    concat f g t = f ⟨t, t.2.1, ht⟩ := by
  nth_rewrite 2 [← concat_comp_IccInclusionLeft hb]
  rfl

@[simp]
/--
theorem `concat_right` / 定理 `concat_right`

English:
theorem concat_right
  given: (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : b <= t)
  proof: by
  nth_rewrite 2 [← concat_comp_IccInclusionRight hb]
  rfl

中文:
定理 concat_right
  条件: (hb : f ⊤ = g ⊥) {t : 闭区间 a c} (ht : b <= t)
  证明: by
  nth_rewrite 2 [← concat_comp_IccInclusionRight hb]
  rfl

Depends on / 依赖: concat_comp_IccInclusionRight, nth_rewrite
-/
theorem concat_right (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : b <= t) :
    concat f g t = g ⟨t, ht, t.2.2⟩ := by
  nth_rewrite 2 [← concat_comp_IccInclusionRight hb]
  rfl

/--
theorem `tendsto_concat` / 定理 `tendsto_concat`

English:
theorem tendsto_concat
  statement: {ι : Type*} {p : Filter ι} {F : ι -> C(Icc a b, E)} {G : ι -> C(Icc b c, E)}
  proof: by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  have h : b in Icc a c := ⟨Fact.out, Fact.out⟩
  let K₁ : Set (Icc a b) := projIccCM '' Subtype.val '' (K inter Iic ⟨b, h⟩)
  let K₂ : Set (Icc b c) := projIccCM '' Subtype.val '' (K inter Ici ⟨b, h⟩)
  have hK₁ : IsCompact K₁ :=
.image projIccCM.continuous .image continuous_subtype_val hK.inter_right isClosed_Iic
  have hK₂ : IsCompact K₂ :=
.image projIccCM.continuous .image continuous_subtype_val hK.inter_right isClosed_Ici
  have hfU : MapsTo f K₁ U := by
    rw [← concat_comp_IccInclusionLeft hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : z <= b)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.1] using! h1
  have hgU : MapsTo g K₂ U := by
    rw [← concat_comp_IccInclusionRight hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : b <= z)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.2] using! h1
  filter_upwards [hf K₁ hK₁ U hU hfU, hg K₂ hK₂ U hU hgU, hfg] with i hf hg hfg x hx
  by_cases! hxb : x <= b
  · rw [concat_left hfg hxb]
    refine hf ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.1]
  · replace hxb : b <= x := hxb.le
    rw [concat_right hfg hxb]
    refine hg ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.2]

中文:
定理 tendsto_concat
  结论: {ι : 类型} {p : 滤子 ι} {F : ι -> C(闭区间 a b, E)} {G : ι -> C(闭区间 b c, E)}
  证明: by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  have h : b in Icc a c := ⟨Fact.out, Fact.out⟩
  let K₁ : Set (Icc a b) := projIccCM '' Subtype.val '' (K inter Iic ⟨b, h⟩)
  let K₂ : Set (Icc b c) := projIccCM '' Subtype.val '' (K inter Ici ⟨b, h⟩)
  have hK₁ : IsCompact K₁ :=
.image projIccCM.continuous .image continuous_subtype_val hK.inter_right isClosed_Iic
  have hK₂ : IsCompact K₂ :=
.image projIccCM.continuous .image continuous_subtype_val hK.inter_right isClosed_Ici
  have hfU : MapsTo f K₁ U := by
    rw [← concat_comp_IccInclusionLeft hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : z <= b)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.1] using! h1
  have hgU : MapsTo g K₂ U := by
    rw [← concat_comp_IccInclusionRight hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : b <= z)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.2] using! h1
  filter_upwards [hf K₁ hK₁ U hU hfU, hg K₂ hK₂ U hU hgU, hfg] with i hf hg hfg x hx
  by_cases! hxb : x <= b
  · rw [concat_left hfg hxb]
    refine hf ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.1]
  · replace hxb : b <= x := hxb.le
    rw [concat_right hfg hxb]
    refine hg ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.2]

Depends on / 依赖: Fact.out, IsCompact, Subtype, Subtype.val, continuous, continuous_subtype_val, hK.inter_right, inter_right, isClosed_Ici, isClosed_Iic, projIccCM, projIccCM.continuous, tendsto_nhds_compactOpen
-/
theorem tendsto_concat {ι : Type*} {p : Filter ι} {F : ι -> C(Icc a b, E)} {G : ι -> C(Icc b c, E)}
    (hfg : forallᶠ i in p, (F i) ⊤ = (G i) ⊥) (hfg' : f ⊤ = g ⊥)
    (hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) :
    Tendsto (fun i => concat (F i) (G i)) p (𝓝 (concat f g)) := by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  have h : b in Icc a c := ⟨Fact.out, Fact.out⟩
  let K₁ : Set (Icc a b) := projIccCM '' Subtype.val '' (K inter Iic ⟨b, h⟩)
  let K₂ : Set (Icc b c) := projIccCM '' Subtype.val '' (K inter Ici ⟨b, h⟩)
  have hK₁ : IsCompact K₁ :=
.image projIccCM.continuous .image continuous_subtype_val hK.inter_right isClosed_Iic
  have hK₂ : IsCompact K₂ :=
.image projIccCM.continuous .image continuous_subtype_val hK.inter_right isClosed_Ici
  have hfU : MapsTo f K₁ U := by
    rw [← concat_comp_IccInclusionLeft hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : z <= b)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.1] using! h1
  have hgU : MapsTo g K₂ U := by
    rw [← concat_comp_IccInclusionRight hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : b <= z)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.2] using! h1
  filter_upwards [hf K₁ hK₁ U hU hfU, hg K₂ hK₂ U hU hgU, hfg] with i hf hg hfg x hx
  by_cases! hxb : x <= b
  · rw [concat_left hfg hxb]
    refine hf ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.1]
  · replace hxb : b <= x := hxb.le
    rw [concat_right hfg hxb]
    refine hg ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.2]

/--
Definition of `concatCM` / `concatCM` 的定义

English:
definition concatCM
  signature: :
  body: concat fg.val.1 fg.val.2
  continuous_toFun := by
    let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {fg | fg.1 ⊤ = fg.2 ⊥}
    change Continuous (S.domRestrict concat.uncurry)
    refine continuousOn_iff_continuous_domRestrict.mp (fun fg hfg => ?_)
    refine tendsto_concat ?_ hfg ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun _ => id)
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[simp]

中文:
定义 concatCM
  签名: :
  定义体: concat fg.val.1 fg.val.2
  continuous_toFun := by
    let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {fg | fg.1 ⊤ = fg.2 ⊥}
    change Continuous (S.domRestrict concat.uncurry)
    refine continuousOn_iff_continuous_domRestrict.mp (fun fg hfg => ?_)
    refine tendsto_concat ?_ hfg ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun _ => id)
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[simp]

Depends on / 依赖: concat, fg.val
-/
noncomputable def concatCM :
    C({fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}, C(Icc a c, E)) where
  toFun fg := concat fg.val.1 fg.val.2
  continuous_toFun := by
    let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {fg | fg.1 ⊤ = fg.2 ⊥}
    change Continuous (S.domRestrict concat.uncurry)
    refine continuousOn_iff_continuous_domRestrict.mp (fun fg hfg => ?_)
    refine tendsto_concat ?_ hfg ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun _ => id)
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[simp]
/--
theorem `concatCM_left` / 定理 `concatCM_left`

English:
theorem concatCM_left
  statement: {x : Icc a c} (hx : x <= b)
  proof: by
  exact concat_left fg.2 hx

@[simp]

中文:
定理 concatCM_left
  结论: {x : 闭区间 a c} (hx : x <= b)
  证明: by
  exact concat_left fg.2 hx

@[simp]

Depends on / 依赖: concat_left
-/
theorem concatCM_left {x : Icc a c} (hx : x <= b)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}} :
    concatCM fg x = fg.1.1 ⟨x.1, x.2.1, hx⟩ := by
  exact concat_left fg.2 hx

@[simp]
/--
theorem `concatCM_right` / 定理 `concatCM_right`

English:
theorem concatCM_right
  statement: {x : Icc a c} (hx : b <= x)
  proof: concat_right fg.2 hx

中文:
定理 concatCM_right
  结论: {x : 闭区间 a c} (hx : b <= x)
  证明: concat_right fg.2 hx

Depends on / 依赖: concat_right
-/
theorem concatCM_right {x : Icc a c} (hx : b <= x)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}} :
    concatCM fg x = fg.1.2 ⟨x.1, hx, x.2.2⟩ :=
  concat_right fg.2 hx

end ContinuousMap
