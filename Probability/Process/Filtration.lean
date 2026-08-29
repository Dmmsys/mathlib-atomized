/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict

/-!
# Filtrations

This file defines filtrations of a measurable space and σ-finite filtrations.

## Main definitions

* `MeasureTheory.Filtration`: a filtration on a measurable space. That is, a monotone sequence of
  sub-σ-algebras.
* `MeasureTheory.SigmaFiniteFiltration`: a filtration `f` is σ-finite with respect to a measure
  `μ` if for all `i`, `μ.trim (f.le i)` is σ-finite.
* `MeasureTheory.Filtration.natural`: the smallest filtration that makes a process adapted. That
  notion `adapted` is not defined yet in this file. See `MeasureTheory.adapted`.
* `MeasureTheory.Filtration.rightCont`: the right-continuation of a filtration.
* `MeasureTheory.Filtration.IsRightContinuous`: a filtration is right-continuous if it is equal
  to its right-continuation.

## Main results

* `MeasureTheory.Filtration.instCompleteLattice`: filtrations are a complete lattice.

## Tags

filtration, stochastic process

-/

@[expose] public section


open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

/--
Definition of `Filtration` / `Filtration` 的定义

English:
structure Filtration
  parameters: {Ω : Type*} (ι : Type*) [Preorder ι] (m : MeasurableSpace Ω)
  axioms and operations (3):
    - seq : ι -> MeasurableSpace Ω
    - mono' : Monotone seq
    - le' : forall i : ι, seq i <= m

中文:
结构 滤子
  参数: {Ω : 类型} (ι : 类型) [预序 ι] (m : 可测空间 Ω)
  公理与运算 (3 个):
    - seq : ι -> 可测空间 Ω
    - mono' : 递增 seq
    - le' : 对任意 i : ι, seq i <= m
-/
structure Filtration {Ω : Type*} (ι : Type*) [Preorder ι] (m : MeasurableSpace Ω) where
  /-- The sequence of sub-σ-algebras of `m` -/
  seq : ι -> MeasurableSpace Ω
  mono' : Monotone seq
  le' : forall i : ι, seq i <= m

attribute [coe] Filtration.seq

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: ι] : CoeFun (Filtration ι m) fun _ => ι -> MeasurableSpace Ω
  body: ⟨fun f => f.seq⟩

中文:
实例 [预序
  签名: ι] : CoeFun (滤子 ι m) fun _ => ι -> 可测空间 Ω
  定义体: ⟨fun f => f.seq⟩

Depends on / 依赖: f.seq
-/
instance [Preorder ι] : CoeFun (Filtration ι m) fun _ => ι -> MeasurableSpace Ω :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorder ι]

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {i j : ι} (f : Filtration ι m) (hij : i <= j)
  statement: f i <= f j
  proof: f.mono' hij

中文:
定理 mono
  条件: {i j : ι} (f : 滤子 ι m) (hij : i <= j)
  结论: f i <= f j
  证明: f.mono' hij
-/
protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i <= j) : f i <= f j :=
  f.mono' hij

/--
theorem `le` / 定理 `le`

English:
theorem le
  given: (f : Filtration ι m) (i : ι)
  statement: f i <= m
  proof: f.le' i

@[ext]

中文:
定理 le
  条件: (f : 滤子 ι m) (i : ι)
  结论: f i <= m
  证明: f.le' i

@[ext]
-/
protected theorem le (f : Filtration ι m) (i : ι) : f i <= m :=
  f.le' i

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Filtration ι m} (h : (f : ι -> MeasurableSpace Ω) = g)
  statement: f = g
  proof: by
  cases f; cases g; congr

中文:
定理 ext
  条件: {f g : 滤子 ι m} (h : (f : ι -> 可测空间 Ω) = g)
  结论: f = g
  证明: by
  cases f; cases g; congr
-/
protected theorem ext {f g : Filtration ι m} (h : (f : ι -> MeasurableSpace Ω) = g) : f = g := by
  cases f; cases g; congr

variable (ι) in
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (m' : MeasurableSpace Ω) (hm' : m' <= m)
  body: ⟨fun _ => m', monotone_const, fun _ => hm'⟩

@[simp]

中文:
定义 const
  签名: (m' : 可测空间 Ω) (hm' : m' <= m)
  定义体: ⟨fun _ => m', monotone_const, fun _ => hm'⟩

@[simp]

Depends on / 依赖: monotone_const
-/
def const (m' : MeasurableSpace Ω) (hm' : m' <= m) : Filtration ι m :=
  ⟨fun _ => m', monotone_const, fun _ => hm'⟩

@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: {m' : MeasurableSpace Ω} {hm' : m' <= m} (i : ι)
  statement: const ι m' hm' i = m'
  proof: rfl

中文:
定理 const_apply
  条件: {m' : 可测空间 Ω} {hm' : m' <= m} (i : ι)
  结论: const ι m' hm' i = m'
  证明: rfl
-/
theorem const_apply {m' : MeasurableSpace Ω} {hm' : m' <= m} (i : ι) : const ι m' hm' i = m' :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Filtration ι m)
  body: ⟨const ι m le_rfl⟩

中文:
实例 :
  签名: 可居 (滤子 ι m)
  定义体: ⟨const ι m le_rfl⟩

Depends on / 依赖: le_rfl
-/
instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Filtration ι m)
  body: ⟨fun f g => forall i, f i <= g i⟩

中文:
实例 :
  签名: LE (滤子 ι m)
  定义体: ⟨fun f g => forall i, f i <= g i⟩
-/
instance : LE (Filtration ι m) :=
  ⟨fun f g => forall i, f i <= g i⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Filtration ι m)
  body: ⟨const ι ⊥ bot_le⟩

中文:
实例 :
  签名: 底元素 (滤子 ι m)
  定义体: ⟨const ι ⊥ bot_le⟩

Depends on / 依赖: bot_le
-/
instance : Bot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Filtration ι m)
  body: ⟨const ι m le_rfl⟩

中文:
实例 :
  签名: 顶元素 (滤子 ι m)
  定义体: ⟨const ι m le_rfl⟩

Depends on / 依赖: le_rfl
-/
instance : Top (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Filtration ι m)
  body: ⟨fun f g =>
    { seq := fun i => f i ⊔ g i
      mono' := fun _ _ hij =>
        sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right)
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]

中文:
实例 :
  签名: 最大值 (滤子 ι m)
  定义体: ⟨fun f g =>
    { seq := fun i => f i ⊔ g i
      mono' := fun _ _ hij =>
        sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right)
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]

Depends on / 依赖: f.le, f.mono, g.le, g.mono, le_sup_left, le_sup_right, sup_le
-/
instance : Max (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊔ g i
      mono' := fun _ _ hij =>
        sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right)
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
/--
theorem `coeFn_sup` / 定理 `coeFn_sup`

English:
theorem coeFn_sup
  given: {f g : Filtration ι m}
  statement: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  proof: rfl

中文:
定理 coeFn_sup
  条件: {f g : 滤子 ι m}
  结论: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  证明: rfl
-/
theorem coeFn_sup {f g : Filtration ι m} : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Filtration ι m)
  body: ⟨fun f g =>
    { seq := fun i => f i ⊓ g i
      mono' := fun _ _ hij =>
        le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij))
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]

中文:
实例 :
  签名: 最小值 (滤子 ι m)
  定义体: ⟨fun f g =>
    { seq := fun i => f i ⊓ g i
      mono' := fun _ _ hij =>
        le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij))
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]

Depends on / 依赖: f.le, f.mono, g.mono, inf_le_left, inf_le_left.trans, inf_le_right, inf_le_right.trans, le_inf
-/
instance : Min (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊓ g i
      mono' := fun _ _ hij =>
        le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij))
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
/--
theorem `coeFn_inf` / 定理 `coeFn_inf`

English:
theorem coeFn_inf
  given: {f g : Filtration ι m}
  statement: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  proof: rfl

中文:
定理 coeFn_inf
  条件: {f g : 滤子 ι m}
  结论: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  证明: rfl
-/
theorem coeFn_inf {f g : Filtration ι m} : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (Filtration ι m)
  body: ⟨fun s =>
    { seq := fun i => sSup ((fun f : Filtration ι m => f i) '' s)
      mono' := fun i j hij => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine (f.mono hij).trans ?_
        have hfj_mem

中文:
实例 :
  签名: 上确界集 (滤子 ι m)
  定义体: ⟨fun s =>
    { seq := fun i => sSup ((fun f : Filtration ι m => f i) '' s)
      mono' := fun i j hij => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine (f.mono hij).trans ?_
        have hfj_mem

Depends on / 依赖: Filtration, Set.mem_image, f.le, f.mono, hf_mem, hfj_mem, le_sSup, mem_image, sSup_le
-/
instance : SupSet (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => sSup ((fun f : Filtration ι m => f i) '' s)
      mono' := fun i j hij => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine (f.mono hij).trans ?_
        have hfj_mem : f j in (fun g : Filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_sSup hfj_mem
      le' := fun i => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, _, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩

/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: (s : Set (Filtration ι m)) (i : ι)
  proof: rfl

中文:
定理 sSup_def
  条件: (s : 集合 (滤子 ι m)) (i : ι)
  证明: rfl
-/
theorem sSup_def (s : Set (Filtration ι m)) (i : ι) :
    sSup s i = sSup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Filtration ι m)
  body: ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m
      mono' := fun i j hij => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true, le_sInf_iff, Set.m

中文:
实例 :
  签名: 下确界集 (滤子 ι m)
  定义体: ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m
      mono' := fun i j hij => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true, le_sInf_iff, Set.m

Depends on / 依赖: Filtration, Nonempty, Set.Nonempty, Set.mem_image, and_imp, f.mono, forall_exists_index, h_nonempty, hf_mem, hfi_mem, if_false, if_true, le_refl, le_sInf_iff, le_trans, mem_image, sInf_le
-/
noncomputable instance : InfSet (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m
      mono' := fun i j hij => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true, le_sInf_iff, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine fun f hf_mem => le_trans ?_ (f.mono hij)
        have hfi_mem : f i in (fun g : Filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact sInf_le hfi_mem
      le' := fun i => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_trans (sInf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

open scoped Classical in
/--
theorem `sInf_def` / 定理 `sInf_def`

English:
theorem sInf_def
  given: (s : Set (Filtration ι m)) (i : ι)
  proof: rfl

中文:
定理 sInf_def
  条件: (s : 集合 (滤子 ι m)) (i : ι)
  证明: rfl
-/
theorem sInf_def (s : Set (Filtration ι m)) (i : ι) :
    sInf s i = if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Filtration ι m) where
  body: le_rfl
  le_trans _ _ _ h_fg h_gh i := (h_fg i).trans (h_gh i)
le_antisymm _ _ h_fg h_gf := Filtration.ext funext fun i => (h_fg i).antisymm (h_gf i)

中文:
实例 instPartialOrder
  签名: : 偏序 (滤子 ι m) where
  定义体: le_rfl
  le_trans _ _ _ h_fg h_gh i := (h_fg i).trans (h_gh i)
le_antisymm _ _ h_fg h_gf := Filtration.ext funext fun i => (h_fg i).antisymm (h_gf i)

Depends on / 依赖: le_rfl
-/
noncomputable instance instPartialOrder : PartialOrder (Filtration ι m) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ h_fg h_gh i := (h_fg i).trans (h_gh i)
le_antisymm _ _ h_fg h_gf := Filtration.ext funext fun i => (h_fg i).antisymm (h_gf i)

set_option linter.style.longLine false in
/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (Filtration ι m) where
  body: (· ⊔ ·)
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h_fh h_gh i := sup_le (h_fh i) (h_gh _)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h_fg h_fh i := le_inf (h_fg i) (h_fh i)
  isLUB_sSup _ :=
   

中文:
实例 instCompleteLattice
  签名: : 完备格 (滤子 ι m) where
  定义体: (· ⊔ ·)
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h_fh h_gh i := sup_le (h_fh i) (h_gh _)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h_fg h_fh i := le_inf (h_fg i) (h_fh i)
  isLUB_sSup _ :=
   
-/
noncomputable instance instCompleteLattice : CompleteLattice (Filtration ι m) where
  sup := (· ⊔ ·)
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h_fh h_gh i := sup_le (h_fh i) (h_gh _)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h_fg h_fh i := le_inf (h_fg i) (h_fh i)
  isLUB_sSup _ :=
    .of_image (f := seq) .rfl (by simpa only [isLUB_pi, Set.image_image] using! fun _ => isLUB_sSup _)
  isGLB_sInf _ := by
    dsimp +instances [instInfSet]
    split_ifs with hn
    · refine .of_image (f := seq) .rfl ?_
      simpa only [isGLB_pi, Set.image_image] using! fun _ => isGLB_sInf _
    · rw [Set.not_nonempty_iff_eq_empty] at hn
      simpa [hn] using! Filtration.le
  le_top f i := f.le' i
  bot_le _ _ := bot_le

end Filtration

/--
theorem `measurableSet_of_filtration` / 定理 `measurableSet_of_filtration`

English:
theorem measurableSet_of_filtration
  statement: [Preorder ι] {f : Filtration ι m} {s : Set Ω} {i : ι}
  proof: f.le i s hs

中文:
定理 measurableSet_of_filtration
  结论: [预序 ι] {f : 滤子 ι m} {s : 集合 Ω} {i : ι}
  证明: f.le i s hs

Depends on / 依赖: f.le
-/
theorem measurableSet_of_filtration [Preorder ι] {f : Filtration ι m} {s : Set Ω} {i : ι}
    (hs : MeasurableSet[f i] s) : MeasurableSet[m] s :=
  f.le i s hs

/--
Definition of `SigmaFiniteFiltration` / `SigmaFiniteFiltration` 的定义

English:
class SigmaFiniteFiltration
  parameters: [Preorder ι] (μ : Measure Ω) (f : Filtration ι m)
  axioms and operations (1):
    - SigmaFinite : forall i : ι, SigmaFinite (μ.trim (f.le i))

中文:
类 σ有限滤子
  参数: [预序 ι] (μ : 测度 Ω) (f : 滤子 ι m)
  公理与运算 (1 个):
    - SigmaFinite : 对任意 i : ι, σ有限 (μ.trim (f.le i))
-/
class SigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m) : Prop where
  SigmaFinite : forall i : ι, SigmaFinite (μ.trim (f.le i))

/--
Instance `sigmaFinite_of_sigmaFiniteFiltration` / 实例 `sigmaFinite_of_sigmaFiniteFiltration`

English:
instance sigmaFinite_of_sigmaFiniteFiltration
  signature: [Preorder ι] (μ : Measure Ω) (f : Filtration ι m)
  body: hf.SigmaFinite _

中文:
实例 sigmaFinite_of_sigmaFiniteFiltration
  签名: [预序 ι] (μ : 测度 Ω) (f : 滤子 ι m)
  定义体: hf.SigmaFinite _

Depends on / 依赖: SigmaFinite, hf.SigmaFinite
-/
instance sigmaFinite_of_sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) :=
  hf.SigmaFinite _

instance (priority := 100) IsFiniteMeasure.sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω)
    (f : Filtration ι m) [IsFiniteMeasure μ] : SigmaFiniteFiltration μ f :=
  ⟨fun n => by infer_instance⟩

/--
theorem `Integrable.uniformIntegrable_condExp_filtration` / 定理 `Integrable.uniformIntegrable_condExp_filtration`

English:
theorem Integrable.uniformIntegrable_condExp_filtration
  statement: [Preorder ι] {μ : Measure Ω}
  proof: hg.uniformIntegrable_condExp f.le

中文:
定理 可积.uniform整数egrable_condExp_filtration
  结论: [预序 ι] {μ : 测度 Ω}
  证明: hg.uniformIntegrable_condExp f.le

Depends on / 依赖: f.le, hg.uniformIntegrable_condExp, uniformIntegrable_condExp
-/
theorem Integrable.uniformIntegrable_condExp_filtration [Preorder ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Filtration ι m} {g : Ω -> Real} (hg : Integrable g μ) :
    UniformIntegrable (fun i => μ[g | f i]) 1 μ :=
  hg.uniformIntegrable_condExp f.le

/--
theorem `Filtration.condExp_condExp` / 定理 `Filtration.condExp_condExp`

English:
theorem Filtration.condExp_condExp
  statement: [Preorder ι] {E : Type*} [NormedAddCommGroup E]
  proof: condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)

中文:
定理 滤子.condExp_condExp
  结论: [预序 ι] {E : 类型} [赋范交换加群 E]
  证明: condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)

Depends on / 依赖: condExp_condExp_of_le
-/
theorem Filtration.condExp_condExp [Preorder ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] (f : Ω -> E) {μ : Measure Ω} (ℱ : Filtration ι m)
    {i j : ι} (hij : i <= j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f | ℱ j] | ℱ i] =ᵐ[μ] μ[f | ℱ i] := condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)

section OfSet

variable [Preorder ι]

/--
Definition of `filtrationOfSet` / `filtrationOfSet` 的定义

English:
definition filtrationOfSet
  signature: {s : ι -> Set Ω} (hsm : forall i, MeasurableSet (s i))
  body: MeasurableSpace.generateFrom {t | exists j <= i, s j = t}
  mono' _ _ hnm := MeasurableSpace.generateFrom_mono fun _ ⟨k, hk₁, hk₂⟩ => ⟨k, hk₁.trans hnm, hk₂⟩
  le' _ := MeasurableSpace.generateFrom_le fun _ ⟨k, _, hk₂⟩ => hk₂ ▸ hsm k

中文:
定义 filtrationOfSet
  签名: {s : ι -> 集合 Ω} (hsm : 对任意 i, 可测集 (s i))
  定义体: MeasurableSpace.generateFrom {t | exists j <= i, s j = t}
  mono' _ _ hnm := MeasurableSpace.generateFrom_mono fun _ ⟨k, hk₁, hk₂⟩ => ⟨k, hk₁.trans hnm, hk₂⟩
  le' _ := MeasurableSpace.generateFrom_le fun _ ⟨k, _, hk₂⟩ => hk₂ ▸ hsm k

Depends on / 依赖: MeasurableSpace, MeasurableSpace.generateFrom, generateFrom
-/
def filtrationOfSet {s : ι -> Set Ω} (hsm : forall i, MeasurableSet (s i)) : Filtration ι m where
  seq i := MeasurableSpace.generateFrom {t | exists j <= i, s j = t}
  mono' _ _ hnm := MeasurableSpace.generateFrom_mono fun _ ⟨k, hk₁, hk₂⟩ => ⟨k, hk₁.trans hnm, hk₂⟩
  le' _ := MeasurableSpace.generateFrom_le fun _ ⟨k, _, hk₂⟩ => hk₂ ▸ hsm k

/--
theorem `measurableSet_filtrationOfSet` / 定理 `measurableSet_filtrationOfSet`

English:
theorem measurableSet_filtrationOfSet
  statement: {s : ι -> Set Ω} (hsm : forall i, MeasurableSet[m] (s i)) (i : ι)
  proof: MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩

中文:
定理 measurableSet_filtrationOfSet
  结论: {s : ι -> 集合 Ω} (hsm : 对任意 i, 可测集[m] (s i)) (i : ι)
  证明: MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩

Depends on / 依赖: MeasurableSpace, MeasurableSpace.measurableSet_generateFrom, measurableSet_generateFrom
-/
theorem measurableSet_filtrationOfSet {s : ι -> Set Ω} (hsm : forall i, MeasurableSet[m] (s i)) (i : ι)
    {j : ι} (hj : j <= i) : MeasurableSet[filtrationOfSet hsm i] (s j) :=
  MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩

/--
theorem `measurableSet_filtrationOfSet'` / 定理 `measurableSet_filtrationOfSet'`

English:
theorem measurableSet_filtrationOfSet'
  statement: {s : ι -> Set Ω} (hsm : forall n, MeasurableSet[m] (s n))
  proof: measurableSet_filtrationOfSet hsm i le_rfl

中文:
定理 measurableSet_filtrationOfSet'
  结论: {s : ι -> 集合 Ω} (hsm : 对任意 n, 可测集[m] (s n))
  证明: measurableSet_filtrationOfSet hsm i le_rfl

Depends on / 依赖: le_rfl, measurableSet_filtrationOfSet
-/
theorem measurableSet_filtrationOfSet' {s : ι -> Set Ω} (hsm : forall n, MeasurableSet[m] (s n))
    (i : ι) : MeasurableSet[filtrationOfSet hsm i] (s i) :=
  measurableSet_filtrationOfSet hsm i le_rfl

end OfSet

namespace Filtration

section IsRightContinuous

open scoped Classical in
/-- Given a filtration `𝓕`, its **right continuation** is the filtration `𝓕₊` defined as follows:
- If `i` is isolated on the right, then `𝓕₊ i := 𝓕 i`;
- Otherwise, `𝓕₊ i := ⨅ j > i, 𝓕 j`.

It is sometimes simply defined as `𝓕₊ i := ⨅ j > i, 𝓕 j` when the index type is `ℝ`. In the
general case this is not ideal however. If `i` is maximal for instance, then `𝓕₊ i = ⊤`, which
is inconvenient because `𝓕₊` is not a `Filtration ι m` anymore. If the index type
is discrete (such as `ℕ`), then we would have `𝓕 = 𝓕₊` (i.e. `𝓕` is right-continuous) only if
`𝓕` is constant.

To avoid requiring a `TopologicalSpace` instance on `ι` in the definition, we endow `ι` with
the order topology `Preorder.topology` inside the definition. Say you write a statement about
`𝓕₊` which does not require a `TopologicalSpace` structure on `ι`,
but you wish to use a statement which requires a topology (such as `rightCont_apply`).
Then you can endow `ι` with the order topology by writing
```lean
  letI := Preorder.topology ι
  haveI : OrderTopology ι := ⟨rfl⟩
``` -/
noncomputable irreducible_def rightCont [PartialOrder ι] (𝓕 : Filtration ι m) : Filtration ι m :=
  letI : TopologicalSpace ι := Preorder.topology ι
  { seq i := if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i
    mono' i j hij := by
      simp only [gt_iff_lt]
      split_ifs with hi hj hj
      · exact le_iInf₂ fun k hkj => iInf₂_le k (hij.trans_lt hkj)
      · obtain rfl | hj := eq_or_ne j i
        · contradiction
        · exact iInf₂_le j (lt_of_le_of_ne hij hj.symm)
      · exact le_iInf₂ fun k hk => 𝓕.mono (hij.trans hk.le)
      · exact 𝓕.mono hij
    le' i := by
      split_ifs with hi
      · obtain ⟨j, hj⟩ := (frequently_gt_nhds i).exists
        exact iInf₂_le_of_le j hj (𝓕.le j)
      · exact 𝓕.le i }

@[inherit_doc] scoped postfix:max "₊" => rightCont

open scoped Classical in
/--
lemma `rightCont_apply` / 引理 `rightCont_apply`

English:
lemma rightCont_apply
  statement: [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  simp +instances only [rightCont, OrderTopology.topology_eq_generate_intervals]

中文:
引理 rightCont_apply
  结论: [偏序 ι] [拓扑空间 ι] [Order拓扑 ι]
  证明: by
  simp +instances only [rightCont, OrderTopology.topology_eq_generate_intervals]

Depends on / 依赖: OrderTopology, OrderTopology.topology_eq_generate_intervals, instances, rightCont, topology_eq_generate_intervals
-/
lemma rightCont_apply [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i := by
  simp +instances only [rightCont, OrderTopology.topology_eq_generate_intervals]

/--
lemma `rightCont_eq_of_nhdsGT_eq_bot` / 引理 `rightCont_eq_of_nhdsGT_eq_bot`

English:
lemma rightCont_eq_of_nhdsGT_eq_bot
  statement: [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  rw [rightCont_apply]; rw [hi]; rw [neBot_iff]; rw [ne_self_iff_false]; rw [if_false]

中文:
引理 rightCont_eq_of_nhdsGT_eq_bot
  结论: [偏序 ι] [拓扑空间 ι] [Order拓扑 ι]
  证明: by
  rw [rightCont_apply]; rw [hi]; rw [neBot_iff]; rw [ne_self_iff_false]; rw [if_false]

Depends on / 依赖: if_false, neBot_iff, ne_self_iff_false, rightCont_apply
-/
lemma rightCont_eq_of_nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : 𝓝[>] i = ⊥) :
    𝓕₊ i = 𝓕 i := by
  rw [rightCont_apply]; rw [hi]; rw [neBot_iff]; rw [ne_self_iff_false]; rw [if_false]

/--
lemma `rightCont_eq_self` / 引理 `rightCont_eq_self`

English:
lemma rightCont_eq_self
  given: [LinearOrder ι] [SuccOrder ι] (𝓕 : Filtration ι m)
  proof: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  ext _
  rw [rightCont_eq_of_nhdsGT_eq_bot _ SuccOrder.nhdsGT]

中文:
引理 rightCont_eq_self
  条件: [线性序 ι] [Succ序 ι] (𝓕 : 滤子 ι m)
  证明: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  ext _
  rw [rightCont_eq_of_nhdsGT_eq_bot _ SuccOrder.nhdsGT]
-/
@[simp] lemma rightCont_eq_self [LinearOrder ι] [SuccOrder ι] (𝓕 : Filtration ι m) :
    𝓕₊ = 𝓕 := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  ext _
  rw [rightCont_eq_of_nhdsGT_eq_bot _ SuccOrder.nhdsGT]

/--
lemma `rightCont_eq_of_isMax` / 引理 `rightCont_eq_of_isMax`

English:
lemma rightCont_eq_of_isMax
  given: [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i)
  proof: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ (hi.Ioi_eq ▸ nhdsWithin_empty i)

中文:
引理 rightCont_eq_of_isMax
  条件: [偏序 ι] (𝓕 : 滤子 ι m) {i : ι} (hi : IsMax i)
  证明: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ (hi.Ioi_eq ▸ nhdsWithin_empty i)

Depends on / 依赖: Ioi_eq, OrderTopology, Preorder, Preorder.topology, hi.Ioi_eq, nhdsWithin_empty, rightCont_eq_of_nhdsGT_eq_bot, topology
-/
lemma rightCont_eq_of_isMax [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i) :
    𝓕₊ i = 𝓕 i := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ (hi.Ioi_eq ▸ nhdsWithin_empty i)

/--
lemma `rightCont_eq_of_exists_gt` / 引理 `rightCont_eq_of_exists_gt`

English:
lemma rightCont_eq_of_exists_gt
  statement: [LinearOrder ι] (𝓕 : Filtration ι m) {i : ι}
  proof: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  obtain ⟨j, hij, hIoo⟩ := hi
  have hcov : i ⋖ j := covBy_iff_Ioo_eq.mpr ⟨hij, hIoo⟩
exact rightCont_eq_of_nhdsGT_eq_bot _ CovBy.nhdsGT hcov

中文:
引理 rightCont_eq_of_存在_gt
  结论: [线性序 ι] (𝓕 : 滤子 ι m) {i : ι}
  证明: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  obtain ⟨j, hij, hIoo⟩ := hi
  have hcov : i ⋖ j := covBy_iff_Ioo_eq.mpr ⟨hij, hIoo⟩
exact rightCont_eq_of_nhdsGT_eq_bot _ CovBy.nhdsGT hcov

Depends on / 依赖: CovBy.nhdsGT, OrderTopology, Preorder, Preorder.topology, covBy_iff_Ioo_eq, covBy_iff_Ioo_eq.mpr, nhdsGT, rightCont_eq_of_nhdsGT_eq_bot, topology
-/
lemma rightCont_eq_of_exists_gt [LinearOrder ι] (𝓕 : Filtration ι m) {i : ι}
    (hi : exists j > i, Set.Ioo i j = ∅) :
    𝓕₊ i = 𝓕 i := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  obtain ⟨j, hij, hIoo⟩ := hi
  have hcov : i ⋖ j := covBy_iff_Ioo_eq.mpr ⟨hij, hIoo⟩
exact rightCont_eq_of_nhdsGT_eq_bot _ CovBy.nhdsGT hcov

/--
lemma `rightCont_eq_of_neBot_nhdsGT` / 引理 `rightCont_eq_of_neBot_nhdsGT`

English:
lemma rightCont_eq_of_neBot_nhdsGT
  statement: [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  rw [rightCont_apply]; rw [if_pos ‹(𝓝[>] i).NeBot›]

中文:
引理 rightCont_eq_of_neBot_nhdsGT
  结论: [偏序 ι] [拓扑空间 ι] [Order拓扑 ι]
  证明: by
  rw [rightCont_apply]; rw [if_pos ‹(𝓝[>] i).NeBot›]

Depends on / 依赖: if_pos, rightCont_apply
-/
lemma rightCont_eq_of_neBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) [(𝓝[>] i).NeBot] :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  rw [rightCont_apply]; rw [if_pos ‹(𝓝[>] i).NeBot›]

/--
lemma `rightCont_eq_of_not_isMax` / 引理 `rightCont_eq_of_not_isMax`

English:
lemma rightCont_eq_of_not_isMax
  statement: [LinearOrder ι] [DenselyOrdered ι]
  proof: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  have : (𝓝[>] i).NeBot := nhdsGT_neBot_of_exists_gt (not_isMax_iff.mp hi)
  exact rightCont_eq_of_neBot_nhdsGT _ _

中文:
引理 rightCont_eq_of_not_isMax
  结论: [线性序 ι] [稠密序 ι]
  证明: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  have : (𝓝[>] i).NeBot := nhdsGT_neBot_of_exists_gt (not_isMax_iff.mp hi)
  exact rightCont_eq_of_neBot_nhdsGT _ _

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, nhdsGT_neBot_of_exists_gt, not_isMax_iff, not_isMax_iff.mp, rightCont_eq_of_neBot_nhdsGT, topology
-/
lemma rightCont_eq_of_not_isMax [LinearOrder ι] [DenselyOrdered ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsMax i) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  have : (𝓝[>] i).NeBot := nhdsGT_neBot_of_exists_gt (not_isMax_iff.mp hi)
  exact rightCont_eq_of_neBot_nhdsGT _ _

/--
lemma `rightCont_eq` / 引理 `rightCont_eq`

English:
lemma rightCont_eq
  statement: [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
  proof: 𝓕.rightCont_eq_of_not_isMax (not_isMax i)

中文:
引理 rightCont_eq
  结论: [线性序 ι] [稠密序 ι] [NoMax序 ι]
  证明: 𝓕.rightCont_eq_of_not_isMax (not_isMax i)

Depends on / 依赖: not_isMax, rightCont_eq_of_not_isMax
-/
lemma rightCont_eq [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := 𝓕.rightCont_eq_of_not_isMax (not_isMax i)

variable [PartialOrder ι]

/--
lemma `le_rightCont` / 引理 `le_rightCont`

English:
lemma le_rightCont
  given: (𝓕 : Filtration ι m)
  statement: 𝓕 <= 𝓕₊
  proof: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · rw [rightCont_eq_of_neBot_nhdsGT]
    exact le_iInf₂ fun _ he => 𝓕.mono he.le
  · rw [rightCont_apply, if_neg hne]

中文:
引理 le_rightCont
  条件: (𝓕 : 滤子 ι m)
  结论: 𝓕 <= 𝓕₊
  证明: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · rw [rightCont_eq_of_neBot_nhdsGT]
    exact le_iInf₂ fun _ he => 𝓕.mono he.le
  · rw [rightCont_apply, if_neg hne]

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, he.le, if_neg, rightCont_apply, rightCont_eq_of_neBot_nhdsGT, topology
-/
lemma le_rightCont (𝓕 : Filtration ι m) : 𝓕 <= 𝓕₊ := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · rw [rightCont_eq_of_neBot_nhdsGT]
    exact le_iInf₂ fun _ he => 𝓕.mono he.le
  · rw [rightCont_apply, if_neg hne]

/--
lemma `rightCont_self` / 引理 `rightCont_self`

English:
lemma rightCont_self
  given: (𝓕 : Filtration ι m)
  statement: 𝓕₊₊ = 𝓕₊
  proof: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  apply le_antisymm _ 𝓕₊.le_rightCont
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · have hineq : (⨅ j > i, 𝓕₊ j) <= ⨅ j > i, 𝓕 j := by
      apply le_iInf₂ fun u hu => ?_
      have hiou : Set.Ioo i u in 𝓝[>] i := by
        rw [mem_nh

中文:
引理 rightCont_self
  条件: (𝓕 : 滤子 ι m)
  结论: 𝓕₊₊ = 𝓕₊
  证明: by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  apply le_antisymm _ 𝓕₊.le_rightCont
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · have hineq : (⨅ j > i, 𝓕₊ j) <= ⨅ j > i, 𝓕 j := by
      apply le_iInf₂ fun u hu => ?_
      have hiou : Set.Ioo i u in 𝓝[>] i := by
        rw [mem_nh
-/
@[simp] lemma rightCont_self (𝓕 : Filtration ι m) : 𝓕₊₊ = 𝓕₊ := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  apply le_antisymm _ 𝓕₊.le_rightCont
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · have hineq : (⨅ j > i, 𝓕₊ j) <= ⨅ j > i, 𝓕 j := by
      apply le_iInf₂ fun u hu => ?_
      have hiou : Set.Ioo i u in 𝓝[>] i := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Set.Iio u, (isOpen_Iio' u).mem_nhds hu, fun _ hx => ⟨hx.2, hx.1⟩⟩
      obtain ⟨v, hv⟩ := hne.nonempty_of_mem hiou
      have hle₁ : (⨅ j > i, 𝓕₊ j) <= 𝓕₊ v := iInf₂_le_of_le v hv.1 le_rfl
      have hle₂ : 𝓕₊ v <= 𝓕 u := by
        by_cases hnv : (𝓝[>] v).NeBot
        · simpa [rightCont_eq_of_neBot_nhdsGT] using iInf₂_le_of_le u hv.2 le_rfl
        · simpa [rightCont_apply, hnv] using 𝓕.mono hv.2.le
      exact hle₁.trans hle₂
    simpa [rightCont_eq_of_neBot_nhdsGT] using hineq
  · rw [rightCont_apply, if_neg hne]

/--
Definition of `IsRightContinuous` / `IsRightContinuous` 的定义

English:
class IsRightContinuous
  parameters: (𝓕 : Filtration ι m)
  axioms and operations (1):
    - RC : 𝓕₊ <= 𝓕

中文:
类 是RightContinuous
  参数: (𝓕 : 滤子 ι m)
  公理与运算 (1 个):
    - RC : 𝓕₊ <= 𝓕
-/
class IsRightContinuous (𝓕 : Filtration ι m) where
  /-- The right continuity property. -/
  RC : 𝓕₊ <= 𝓕

/--
lemma `IsRightContinuous.eq` / 引理 `IsRightContinuous.eq`

English:
lemma IsRightContinuous.eq
  given: {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕]
  proof: (le_antisymm 𝓕.le_rightCont h.RC).symm

中文:
引理 是RightContinuous.eq
  条件: {𝓕 : 滤子 ι m} [h : 是RightContinuous 𝓕]
  证明: (le_antisymm 𝓕.le_rightCont h.RC).symm

Depends on / 依赖: h.RC, le_antisymm, le_rightCont
-/
lemma IsRightContinuous.eq {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕] :
    𝓕₊ = 𝓕 := (le_antisymm 𝓕.le_rightCont h.RC).symm

instance {𝓕 : Filtration ι m} : 𝓕₊.IsRightContinuous := ⟨(rightCont_self 𝓕).le⟩

/--
lemma `IsRightContinuous.measurableSet` / 引理 `IsRightContinuous.measurableSet`

English:
lemma IsRightContinuous.measurableSet
  statement: {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
  proof: IsRightContinuous.eq (𝓕 := 𝓕) ▸ hs

中文:
引理 是RightContinuous.measurableSet
  结论: {𝓕 : 滤子 ι m} [是RightContinuous 𝓕] {i : ι}
  证明: IsRightContinuous.eq (𝓕 := 𝓕) ▸ hs

Depends on / 依赖: IsRightContinuous, IsRightContinuous.eq
-/
lemma IsRightContinuous.measurableSet {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[𝓕₊ i] s) :
    MeasurableSet[𝓕 i] s := IsRightContinuous.eq (𝓕 := 𝓕) ▸ hs

end IsRightContinuous

variable {β : ι -> Type*} [forall i, TopologicalSpace (β i)] [forall i, MetrizableSpace (β i)]
  [mβ : forall i, MeasurableSpace (β i)] [forall i, BorelSpace (β i)]
  [Preorder ι]

/--
Definition of `natural` / `natural` 的定义

English:
definition natural
  signature: (u : (i : ι) -> Ω -> β i) (hum : forall i, StronglyMeasurable (u i))
  body: ⨆ j <= i, MeasurableSpace.comap (u j) (mβ j)
  mono' _ _ hij := biSup_mono fun _ => ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j _ s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht

中文:
定义 natural
  签名: (u : (i : ι) -> Ω -> β i) (hum : 对任意 i, StronglyMeasurable (u i))
  定义体: ⨆ j <= i, MeasurableSpace.comap (u j) (mβ j)
  mono' _ _ hij := biSup_mono fun _ => ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j _ s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap
-/
def natural (u : (i : ι) -> Ω -> β i) (hum : forall i, StronglyMeasurable (u i)) : Filtration ι m where
  seq i := ⨆ j <= i, MeasurableSpace.comap (u j) (mβ j)
  mono' _ _ hij := biSup_mono fun _ => ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j _ s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht

/--
lemma `natural_eq_comap` / 引理 `natural_eq_comap`

English:
lemma natural_eq_comap
  given: (u : (i : ι) -> Ω -> β i) (hum : forall (i : ι), StronglyMeasurable (u i)) (i : ι)
  proof: by
  simp_rw [natural, MeasurableSpace.comap_process_pi, iSup_subtype']
  rfl

中文:
引理 natural_eq_comap
  条件: (u : (i : ι) -> Ω -> β i) (hum : 对任意 (i : ι), StronglyMeasurable (u i)) (i : ι)
  证明: by
  simp_rw [natural, MeasurableSpace.comap_process_pi, iSup_subtype']
  rfl

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap_process_pi, comap_process_pi, iSup_subtype, natural, simp_rw
-/
lemma natural_eq_comap (u : (i : ι) -> Ω -> β i) (hum : forall (i : ι), StronglyMeasurable (u i)) (i : ι) :
    natural u hum i = .comap (fun ω (j : Set.Iic i) => u j ω) inferInstance := by
  simp_rw [natural, MeasurableSpace.comap_process_pi, iSup_subtype']
  rfl

section

open MeasurableSpace

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `filtrationOfSet_eq_natural` / 定理 `filtrationOfSet_eq_natural`

English:
theorem filtrationOfSet_eq_natural
  statement: [forall i, MulZeroOneClass (β i)] [forall i, Nontrivial (β i)]
  proof: by
  simp only [filtrationOfSet, natural, measurableSpace_iSup_eq, exists_prop, mk.injEq]
  ext1 i
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_)
  · rintro _ ⟨j, hij, rfl⟩
    refine measurableSet_generateFrom ⟨j, measurableSet_generateFrom ⟨hij, ?_⟩⟩
    rw [comap_eq_generateFrom]


中文:
定理 filtrationOfSet_eq_natural
  结论: [对任意 i, 乘零幺类 (β i)] [对任意 i, 非平凡 (β i)]
  证明: by
  simp only [filtrationOfSet, natural, measurableSpace_iSup_eq, exists_prop, mk.injEq]
  ext1 i
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_)
  · rintro _ ⟨j, hij, rfl⟩
    refine measurableSet_generateFrom ⟨j, measurableSet_generateFrom ⟨hij, ?_⟩⟩
    rw [comap_eq_generateFrom]


Depends on / 依赖: MeasurableSet, MeasurableSpace, MeasurableSpace.comap, MeasurableSpace.generateFrom, comap_eq_generateFrom, exists_prop, filtrationOfSet, generateFrom, generateFrom_le, indicator, le_antisymm, measurableSet_generateFrom, measurableSet_singleton, measurableSpace_iSup_eq, mk.injEq, natural
-/
theorem filtrationOfSet_eq_natural [forall i, MulZeroOneClass (β i)] [forall i, Nontrivial (β i)]
    {s : ι -> Set Ω} (hsm : forall i, MeasurableSet[m] (s i)) :
    filtrationOfSet hsm = natural (fun i => (s i).indicator (fun _ => 1 : Ω -> β i)) fun i =>
      stronglyMeasurable_one.indicator (hsm i) := by
  simp only [filtrationOfSet, natural, measurableSpace_iSup_eq, exists_prop, mk.injEq]
  ext1 i
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_)
  · rintro _ ⟨j, hij, rfl⟩
    refine measurableSet_generateFrom ⟨j, measurableSet_generateFrom ⟨hij, ?_⟩⟩
    rw [comap_eq_generateFrom]
    refine measurableSet_generateFrom ⟨{1}, measurableSet_singleton 1, ?_⟩
    ext x
    simp
  · rintro t ⟨n, ht⟩
    suffices MeasurableSpace.generateFrom {t | n <= i ∧
      MeasurableSet[MeasurableSpace.comap ((s n).indicator (fun _ => 1 : Ω -> β n)) (mβ n)] t} <=
        MeasurableSpace.generateFrom {t | exists (j : ι), j <= i ∧ s j = t} by
      exact this _ ht
    refine generateFrom_le ?_
    rintro t ⟨hn, u, _, hu'⟩
    obtain heq | heq | heq | heq := Set.indicator_const_preimage (s n) u (1 : β n)
    on_goal 4 => rw [Set.mem_singleton_iff] at heq
    all_goals rw [heq] at hu'; rw [← hu']
    exacts [MeasurableSet.univ, measurableSet_generateFrom ⟨n, hn, rfl⟩,
      MeasurableSet.compl (measurableSet_generateFrom ⟨n, hn, rfl⟩), measurableSet_empty _]

end

section Limit

variable {E : Type*} [Zero E] [TopologicalSpace E] {ℱ : Filtration ι m} {f : ι -> Ω -> E}
  {μ : Measure Ω}

open scoped Classical in
/--
Definition of `limitProcess` / `limitProcess` 的定义

English:
definition limitProcess
  signature: (f : ι -> Ω -> E) (ℱ : Filtration ι m)
  body: if h : exists g : Ω -> E,
    StronglyMeasurable[⨆ n, ℱ n] g ∧ forallᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0

中文:
定义 limitProcess
  签名: (f : ι -> Ω -> E) (ℱ : 滤子 ι m)
  定义体: if h : exists g : Ω -> E,
    StronglyMeasurable[⨆ n, ℱ n] g ∧ forallᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0

Depends on / 依赖: Classical, Classical.choose, StronglyMeasurable, Tendsto
-/
noncomputable def limitProcess (f : ι -> Ω -> E) (ℱ : Filtration ι m)
    (μ : Measure Ω) :=
  if h : exists g : Ω -> E,
    StronglyMeasurable[⨆ n, ℱ n] g ∧ forallᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0

/--
theorem `stronglyMeasurable_limitProcess` / 定理 `stronglyMeasurable_limitProcess`

English:
theorem stronglyMeasurable_limitProcess
  statement: StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ)
  proof: by
  rw [limitProcess]
  split_ifs with h
  exacts [(Classical.choose_spec h).1, stronglyMeasurable_zero]

中文:
定理 stronglyMeasurable_limitProcess
  结论: StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ)
  证明: by
  rw [limitProcess]
  split_ifs with h
  exacts [(Classical.choose_spec h).1, stronglyMeasurable_zero]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exacts, limitProcess, split_ifs, stronglyMeasurable_zero
-/
theorem stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ) := by
  rw [limitProcess]
  split_ifs with h
  exacts [(Classical.choose_spec h).1, stronglyMeasurable_zero]

/--
theorem `stronglyMeasurable_limit_process'` / 定理 `stronglyMeasurable_limit_process'`

English:
theorem stronglyMeasurable_limit_process'
  statement: StronglyMeasurable[m] (limitProcess f ℱ μ)
  proof: stronglyMeasurable_limitProcess.mono (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _)

中文:
定理 stronglyMeasurable_limit_process'
  结论: StronglyMeasurable[m] (limitProcess f ℱ μ)
  证明: stronglyMeasurable_limitProcess.mono (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _)

Depends on / 依赖: sSup_le, stronglyMeasurable_limitProcess, stronglyMeasurable_limitProcess.mono
-/
theorem stronglyMeasurable_limit_process' : StronglyMeasurable[m] (limitProcess f ℱ μ) :=
  stronglyMeasurable_limitProcess.mono (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _)

/--
theorem `memLp_limitProcess_of_eLpNorm_bdd` / 定理 `memLp_limitProcess_of_eLpNorm_bdd`

English:
theorem memLp_limitProcess_of_eLpNorm_bdd
  statement: {R : Real>=0} {p : Real>=0∞} {F : Type*} [NormedAddCommGroup F]
  proof: by
  rw [limitProcess]
  split_ifs with h
  · refine ⟨StronglyMeasurable.aestronglyMeasurable
      ((Classical.choose_spec h).1.mono (sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)),
      lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ (Classical.choose_spec h).2)
        (lt_of_le_of_lt ?_ (ENNReal

中文:
定理 memLp_limitProcess_of_eLpNorm_bdd
  结论: {R : 实数>=0} {p : 实数>=0∞} {F : 类型} [赋范交换加群 F]
  证明: by
  rw [limitProcess]
  split_ifs with h
  · refine ⟨StronglyMeasurable.aestronglyMeasurable
      ((Classical.choose_spec h).1.mono (sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)),
      lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ (Classical.choose_spec h).2)
        (lt_of_le_of_lt ?_ (ENNReal

Depends on / 依赖: Classical, Classical.choose_spec, ENNReal, ENNReal.coe_lt_top, Lp.eLpNorm_lim_le_liminf_eLpNorm, MemLp.zero, StronglyMeasurable, StronglyMeasurable.aestronglyMeasurable, aestronglyMeasurable, choose_spec, coe_lt_top, eLpNorm_lim_le_liminf_eLpNorm, eventually_atTop, le_rfl, liminf_eq, limitProcess, lt_of_le_of_lt, sSup_le, simp_rw, split_ifs
-/
theorem memLp_limitProcess_of_eLpNorm_bdd {R : Real>=0} {p : Real>=0∞} {F : Type*} [NormedAddCommGroup F]
    {ℱ : Filtration Nat m} {f : Nat -> Ω -> F} (hfm : forall n, AEStronglyMeasurable (f n) μ)
    (hbdd : forall n, eLpNorm (f n) p μ <= R) : MemLp (limitProcess f ℱ μ) p μ := by
  rw [limitProcess]
  split_ifs with h
  · refine ⟨StronglyMeasurable.aestronglyMeasurable
      ((Classical.choose_spec h).1.mono (sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)),
      lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ (Classical.choose_spec h).2)
        (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top : ↑R < ∞))⟩
    simp_rw [liminf_eq, eventually_atTop]
    exact sSup_le fun b ⟨a, ha⟩ => (ha a le_rfl).trans (hbdd _)
  · exact MemLp.zero

end Limit

section piLE

/-! ### Filtration of the first events -/

open MeasurableSpace Preorder

variable {X : ι -> Type*} [forall i, MeasurableSpace (X i)]

/--
Definition of `piLE` / `piLE` 的定义

English:
definition piLE
  signature: : @Filtration (Π i, X i) ι _ pi where
  body: pi.comap (restrictLe i)
  mono' i j hij := by
    simp only
    rw [← restrictLe₂_comp_restrictLe hij]; rw [← comap_comp]
    exact comap_mono (measurable_restrictLe₂ _).comap_le
  le' i := (measurable_restrictLe i).comap_le

中文:
定义 piLE
  签名: : @滤子 (Π i, X i) ι _ pi where
  定义体: pi.comap (restrictLe i)
  mono' i j hij := by
    simp only
    rw [← restrictLe₂_comp_restrictLe hij]; rw [← comap_comp]
    exact comap_mono (measurable_restrictLe₂ _).comap_le
  le' i := (measurable_restrictLe i).comap_le

Depends on / 依赖: pi.comap, restrictLe
-/
def piLE : @Filtration (Π i, X i) ι _ pi where
  seq i := pi.comap (restrictLe i)
  mono' i j hij := by
    simp only
    rw [← restrictLe₂_comp_restrictLe hij]; rw [← comap_comp]
    exact comap_mono (measurable_restrictLe₂ _).comap_le
  le' i := (measurable_restrictLe i).comap_le

variable [LocallyFiniteOrderBot ι]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `piLE_eq_comap_frestrictLe` / 引理 `piLE_eq_comap_frestrictLe`

English:
lemma piLE_eq_comap_frestrictLe
  given: (i : ι)
  statement: piLE (X := X) i = pi.comap (frestrictLe i)
  proof: by
  apply le_antisymm
  · simp_rw [piLE, ← piCongrLeft_comp_frestrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
exact MeasurableSpace.comap_mono Measurable.comap_le (by fun_prop)
  · rw [← piCongrLeft_comp_restrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
exact MeasurableSpace.

中文:
引理 piLE_eq_comap_frestrictLe
  条件: (i : ι)
  结论: piLE (X := X) i = pi.comap (frestrictLe i)
  证明: by
  apply le_antisymm
  · simp_rw [piLE, ← piCongrLeft_comp_frestrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
exact MeasurableSpace.comap_mono Measurable.comap_le (by fun_prop)
  · rw [← piCongrLeft_comp_restrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
exact MeasurableSpace.

Depends on / 依赖: Measurable, Measurable.comap_le, MeasurableEquiv, MeasurableEquiv.coe_piCongrLeft, MeasurableSpace, MeasurableSpace.comap_mono, coe_piCongrLeft, comap_comp, comap_le, comap_mono, frestrictLe, fun_prop, le_antisymm, pi.comap, piCongrLeft_comp_frestrictLe, piCongrLeft_comp_restrictLe, simp_rw
-/
lemma piLE_eq_comap_frestrictLe (i : ι) : piLE (X := X) i = pi.comap (frestrictLe i) := by
  apply le_antisymm
  · simp_rw [piLE, ← piCongrLeft_comp_frestrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
exact MeasurableSpace.comap_mono Measurable.comap_le (by fun_prop)
  · rw [← piCongrLeft_comp_restrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
exact MeasurableSpace.comap_mono Measurable.comap_le (by fun_prop)

end piLE

section piFinset

open MeasurableSpace Finset

variable {ι : Type*} {X : ι -> Type*} [forall i, MeasurableSpace (X i)]

/--
Definition of `piFinset` / `piFinset` 的定义

English:
definition piFinset
  signature: : @Filtration (Π i, X i) (Finset ι) _ pi where
  body: pi.comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst]; rw [← comap_comp]
    exact comap_mono (measurable_restrict₂ hst).comap_le
  le' s := s.measurable_restrict.comap_le

中文:
定义 piFinset
  签名: : @滤子 (Π i, X i) (有限集 ι) _ pi where
  定义体: pi.comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst]; rw [← comap_comp]
    exact comap_mono (measurable_restrict₂ hst).comap_le
  le' s := s.measurable_restrict.comap_le

Depends on / 依赖: pi.comap, restrict, s.restrict
-/
def piFinset : @Filtration (Π i, X i) (Finset ι) _ pi where
  seq s := pi.comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst]; rw [← comap_comp]
    exact comap_mono (measurable_restrict₂ hst).comap_le
  le' s := s.measurable_restrict.comap_le

/--
lemma `piFinset_eq_comap_restrict` / 引理 `piFinset_eq_comap_restrict`

English:
lemma piFinset_eq_comap_restrict
  given: (s : Finset ι)
  proof: rfl

中文:
引理 piFinset_eq_comap_restrict
  条件: (s : 有限集 ι)
  证明: rfl

Depends on / 依赖: domRestrict, pi.comap
-/
lemma piFinset_eq_comap_restrict (s : Finset ι) :
    piFinset (X := X) s = pi.comap (s : Set ι).domRestrict := rfl

end piFinset

variable {α : Type*}

/--
Definition of `cylinderEventsCompl` / `cylinderEventsCompl` 的定义

English:
definition cylinderEventsCompl
  signature: : Filtration (Finset α)ᵒᵈ (.pi (X := fun _ : α => Ω)) where
  body: cylinderEvents (↑(OrderDual.ofDual Λ))ᶜ
mono' _ _ h := cylinderEvents_mono Set.compl_subset_compl_of_subset h
  le' _ := cylinderEvents_le_pi

中文:
定义 cylinderEventsCompl
  签名: : 滤子 (有限集 α)ᵒᵈ (.pi (X := fun _ : α => Ω)) where
  定义体: cylinderEvents (↑(OrderDual.ofDual Λ))ᶜ
mono' _ _ h := cylinderEvents_mono Set.compl_subset_compl_of_subset h
  le' _ := cylinderEvents_le_pi
-/
def cylinderEventsCompl : Filtration (Finset α)ᵒᵈ (.pi (X := fun _ : α => Ω)) where
  seq Λ := cylinderEvents (↑(OrderDual.ofDual Λ))ᶜ
mono' _ _ h := cylinderEvents_mono Set.compl_subset_compl_of_subset h
  le' _ := cylinderEvents_le_pi

end Filtration

end MeasureTheory
