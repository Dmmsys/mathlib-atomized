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

/-- A `Filtration` on a measurable space `Ω` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
/-
**MeasureTheory.Filtration** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{Ω : Type u_1} → (ι : Type u_2) → [Preorder ι] → MeasurableSpace Ω → Type 
(max u_1 u_2)
参数：ι : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Filtration` on a measurable space `Ω` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`.
-/
structure Filtration {Ω : Type*} (ι : Type*) [Preorder ι] (m : MeasurableSpace Ω) where
  /-- The sequence of sub-σ-algebras of `m` -/
  seq : ι → MeasurableSpace Ω
  mono' : Monotone seq
  le' : ∀ i : ι, seq i ≤ m

attribute [coe] Filtration.seq

variable {Ω ι : Type*} {m : MeasurableSpace Ω}
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder ι] : CoeFun (Filtration ι m) fun _ => ι → MeasurableSpace Ω :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorder ι]

/-
**MeasureTheory.Filtration.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Filtrat
ion`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {i j : ι}   (f : MeasureTheory.Filtration ι m), i ≤ j → ↑f i ≤ ↑f j
参数：f : MeasureTheory.Filtration ι m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.mono'`：∀ {Ω : Type u_1} {ι : Type u_2} [inst : 
Preorder ι] {m : MeasurableSpace Ω} (self : MeasureTheory.Filtration ι m),   Mon
otone ↑self
-/
protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij
/-
**MeasureTheory.Filtration.le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Filtratio
n`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑f i ≤ m
参数：f : MeasureTheory.Filtration ι m；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.le'`：∀ {Ω : Type u_1} {ι : Type u_2} [inst : Pr
eorder ι] {m : MeasurableSpace Ω} (self : MeasureTheory.Filtration ι m)   (i : ι
), ↑self i ≤ m
-/
protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i

@[ext]
/-
**MeasureTheory.Filtration.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Filtrati
on`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f g : MeasureTheory.Filtration ι m},   ↑f = ↑g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace Ω) = g) : f = g := by
  cases f; cases g; congr

variable (ι) in
/-- The constant filtration which is equal to `m` for all `i : ι`. -/
/-
**MeasureTheory.Filtration.const** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Filtra
tion`。
形式化陈述：const (m' : MeasurableSpace Ω) (hm' : m' <= m) : Filtration ι m
参数：m' : MeasurableSpace Ω；hm' : m' <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant filtration which is equal to `m` for all `i : ι`.
-/
def const (m' : MeasurableSpace Ω) (hm' : m' ≤ m) : Filtration ι m :=
  ⟨fun _ => m', monotone_const, fun _ => hm'⟩

@[simp]
/-
**MeasureTheory.Filtration.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Filtration`。
形式化陈述：const_apply {m' : MeasurableSpace Ω} {hm' : m' <= m} (i : ι) : const ι m' 
hm' i = m'
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply {m' : MeasurableSpace Ω} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' :=
  rfl
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rfl⟩
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Filtration ι m) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (Filtration ι m) :=
  ⟨const ι m le_rfl⟩
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊔ g i
      mono' := fun _ _ hij =>
        sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right)
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
/-
**MeasureTheory.Filtration.coeFn_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fi
ltration`。
形式化陈述：coeFn_sup {f g : Filtration ι m} : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_sup {f g : Filtration ι m} : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊓ g i
      mono' := fun _ _ hij =>
        le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij))
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
/-
**MeasureTheory.Filtration.coeFn_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fi
ltration`。
形式化陈述：coeFn_inf {f g : Filtration ι m} : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_inf {f g : Filtration ι m} : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
        have hfj_mem : f j ∈ (fun g : Filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_sSup hfj_mem
      le' := fun i => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, _, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩
/-
**MeasureTheory.Filtration.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fil
tration`。
形式化陈述：sSup_def (s : Set (Filtration ι m)) (i : ι) : sSup s i = sSup ((fun f : Fi
ltration ι m => f i) '' s)
参数：s : Set (Filtration ι m)；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_def (s : Set (Filtration ι m)) (i : ι) :
    sSup s i = sSup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

open scoped Classical in
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
        have hfi_mem : f i ∈ (fun g : Filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact sInf_le hfi_mem
      le' := fun i => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_trans (sInf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

open scoped Classical in
/-
**MeasureTheory.Filtration.sInf_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Fil
tration`。
形式化陈述：sInf_def (s : Set (Filtration ι m)) (i : ι) : sInf s i = if Set.Nonempty s
 then sInf ((fun f : Filtration ι m => f i) '' s) else m
参数：s : Set (Filtration ι m)；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_def (s : Set (Filtration ι m)) (i : ι) :
    sInf s i = if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl
/-
**MeasureTheory.Filtration.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Filtration`。
形式化陈述：instPartialOrder : PartialOrder (Filtration ι m) where le_refl _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instPartialOrder : PartialOrder (Filtration ι m) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ h_fg h_gh i := (h_fg i).trans (h_gh i)
  le_antisymm _ _ h_fg h_gf := Filtration.ext <| funext fun i => (h_fg i).antisymm (h_gf i)

set_option linter.style.longLine false in
/-
**MeasureTheory.Filtration.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.Filtration`。
形式化陈述：instCompleteLattice : CompleteLattice (Filtration ι m) where sup
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.le'`：∀ {Ω : Type u_1} {ι : Type u_2} [inst : Pr
eorder ι] {m : MeasurableSpace Ω} (self : MeasureTheory.Filtration ι m)   (i : ι
), ↑self i ≤ m
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
    .of_image (f := seq) .rfl (by simpa only [isLUB_pi, Set.image_image] using! fun _ ↦ isLUB_sSup _)
  isGLB_sInf _ := by
    dsimp +instances [instInfSet]
    split_ifs with hn
    · refine .of_image (f := seq) .rfl ?_
      simpa only [isGLB_pi, Set.image_image] using! fun _ ↦ isGLB_sInf _
    · rw [Set.not_nonempty_iff_eq_empty] at hn
      simpa [hn] using! Filtration.le
  le_top f i := f.le' i
  bot_le _ _ := bot_le

end Filtration

/-
**MeasureTheory.measurableSet_of_filtration** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measurableSet_of_filtration [Preorder ι] {f : Filtration ι m} {s : Set Ω} 
{i : ι} (hs : MeasurableSet[f i] s) : MeasurableSet[m] s
参数：hs : MeasurableSet[f i] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem measurableSet_of_filtration [Preorder ι] {f : Filtration ι m} {s : Set Ω} {i : ι}
    (hs : MeasurableSet[f i] s) : MeasurableSet[m] s :=
  f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
/-
**MeasureTheory.SigmaFiniteFiltration** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory
`。
形式化陈述：{Ω : Type u_1} →   {ι : Type u_2} →     {m : MeasurableSpace Ω} → [inst : 
Preorder ι] → MeasureTheory.Measure Ω → MeasureTheory.Filtration ι m → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration.
-/
class SigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m) : Prop where
  SigmaFinite : ∀ i : ι, SigmaFinite (μ.trim (f.le i))
/-
**MeasureTheory.sigmaFinite_of_sigmaFiniteFiltration** 是 Mathlib 中的一个实例，位于命名空间 `
MeasureTheory`。
形式化陈述：sigmaFinite_of_sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Fil
tration ι m) [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.l
e i))
参数：μ : Measure Ω；f : Filtration ι m；i : ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFiniteFiltration.SigmaFinite`：∀ {Ω : Type u_1} {ι : T
ype u_2} {m : MeasurableSpace Ω} {inst : Preorder ι} {μ : MeasureTheory.Measure 
Ω}   {f : MeasureTheory.Filtration ι …
-/
instance sigmaFinite_of_sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) :=
  hf.SigmaFinite _
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsFiniteMeasure.sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω)
    (f : Filtration ι m) [IsFiniteMeasure μ] : SigmaFiniteFiltration μ f :=
  ⟨fun n => by infer_instance⟩

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to a
filtration is uniformly integrable. -/
/-
**MeasureTheory.Integrable.uniformIntegrable_condExp_filtration** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {μ : MeasureTheory.Measure Ω}   [MeasureTheory.IsFiniteMeasure μ] {f : Measure
Theory.Filtration ι m} {g : Ω → ℝ},   MeasureTheory.Integrable g μ → MeasureTheo
ry.UniformIntegrable (fun i => μ[g | ↑f i]) 1 μ
参数：fun i => μ[g | ↑f i]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.uniformIntegrable_condExp`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ι : Type u_2} [MeasureTheor
y.IsFiniteMeasure μ]   {g : α → ℝ},   Me…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m

--- 原说明 ---
Given an integrable function `g`, the conditional expectations of `g` with respe
ct to a
filtration is uniformly integrable.
-/
theorem Integrable.uniformIntegrable_condExp_filtration [Preorder ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Filtration ι m} {g : Ω → ℝ} (hg : Integrable g μ) :
    UniformIntegrable (fun i => μ[g | f i]) 1 μ :=
  hg.uniformIntegrable_condExp f.le
/-
**MeasureTheory.Filtration.condExp_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Filtration`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {E : Type u_3}   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E] [C
ompleteSpace E] (f : Ω → E) {μ : MeasureTheory.Measure Ω}   (ℱ : MeasureTheory.F
iltration ι m) {i j : ι},   i ≤ j → ∀ [MeasureTheory.SigmaFinite (μ.trim ⋯)], μ[
μ[f | ↑ℱ j] | ↑ℱ i] =ᵐ[μ] μ[f | ↑ℱ i]
参数：f : Ω → E；ℱ : MeasureTheory.Filtration ι m；μ.trim ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.condExp_condExp_of_le`：condExp_condExp_of_le {m₁ m₂ m₀ : M
easurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂) (hm₂ : m₂ <= m₀) [SigmaFinit
e (μ.trim hm₂)] : μ[μ[f |…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
-/
theorem Filtration.condExp_condExp [Preorder ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : Ω → E) {μ : Measure Ω} (ℱ : Filtration ι m)
    {i j : ι} (hij : i ≤ j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f | ℱ j] | ℱ i] =ᵐ[μ] μ[f | ℱ i] := condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)

section OfSet

variable [Preorder ι]

/-- Given a sequence of measurable sets `(sₙ)`, `filtrationOfSet` is the smallest filtration
such that `sₙ` is measurable with respect to the `n`-th sub-σ-algebra in `filtrationOfSet`. -/
/-
**MeasureTheory.filtrationOfSet** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：filtrationOfSet {s : ι -> Set Ω} (hsm : forall i, MeasurableSet (s i)) : F
iltration ι m where seq i
参数：hsm : forall i, MeasurableSet (s i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence of measurable sets `(sₙ)`, `filtrationOfSet` is the smallest fi
ltration
such that `sₙ` is measurable with respect to the `n`-th sub-σ-algebra in `filtra
tionOfSet`.
-/
def filtrationOfSet {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet (s i)) : Filtration ι m where
  seq i := MeasurableSpace.generateFrom {t | ∃ j ≤ i, s j = t}
  mono' _ _ hnm := MeasurableSpace.generateFrom_mono fun _ ⟨k, hk₁, hk₂⟩ => ⟨k, hk₁.trans hnm, hk₂⟩
  le' _ := MeasurableSpace.generateFrom_le fun _ ⟨k, _, hk₂⟩ => hk₂ ▸ hsm k
/-
**MeasureTheory.measurableSet_filtrationOfSet** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measurableSet_filtrationOfSet {s : ι -> Set Ω} (hsm : forall i, Measurable
Set[m] (s i)) (i : ι) {j : ι} (hj : j <= i) : MeasurableSet[filtrationOfSet hsm 
i] (s j)
参数：hsm : forall i, MeasurableSet[m] (s i)；i : ι；hj : j <= i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
-/
theorem measurableSet_filtrationOfSet {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[m] (s i)) (i : ι)
    {j : ι} (hj : j ≤ i) : MeasurableSet[filtrationOfSet hsm i] (s j) :=
  MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩
/-
**MeasureTheory.measurableSet_filtrationOfSet'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measurableSet_filtrationOfSet' {s : ι -> Set Ω} (hsm : forall n, Measurabl
eSet[m] (s n)) (i : ι) : MeasurableSet[filtrationOfSet hsm i] (s i)
参数：hsm : forall n, MeasurableSet[m] (s n)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_filtrationOfSet`：measurableSet_filtrationOfS
et {s : ι -> Set Ω} (hsm : forall i, MeasurableSet[m] (s i)) (i : ι) {j : ι} (hj
 : j <= i) : MeasurableSet[filtra…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem measurableSet_filtrationOfSet' {s : ι → Set Ω} (hsm : ∀ n, MeasurableSet[m] (s n))
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
      · exact le_iInf₂ fun k hkj ↦ iInf₂_le k (hij.trans_lt hkj)
      · obtain rfl | hj := eq_or_ne j i
        · contradiction
        · exact iInf₂_le j (lt_of_le_of_ne hij hj.symm)
      · exact le_iInf₂ fun k hk ↦ 𝓕.mono (hij.trans hk.le)
      · exact 𝓕.mono hij
    le' i := by
      split_ifs with hi
      · obtain ⟨j, hj⟩ := (frequently_gt_nhds i).exists
        exact iInf₂_le_of_le j hj (𝓕.le j)
      · exact 𝓕.le i }

@[inherit_doc] scoped postfix:max "₊" => rightCont

open scoped Classical in
/-
**MeasureTheory.Filtration.rightCont_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Filtration`。
形式化陈述：rightCont_apply [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕
 : Filtration ι m) (i : ι) : 𝓕₊ i = if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i
参数：𝓕 : Filtration ι m；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Filtration.rightCont_def`：∀ {Ω : Type u_3} {ι : Type u_4} 
{m : MeasurableSpace Ω} [inst : PartialOrder ι] (𝓕 : MeasureTheory.Filtration ι 
m),   𝓕.rightCont =     { se…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `OrderTopology.topology_eq_generate_intervals`：∀ {α : Type u_1} {t : Topo
logicalSpace α} {inst : Preorder α} [self : OrderTopology α], t = Preorder.topol
ogy α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightCont_apply [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i := by
  simp +instances only [rightCont, OrderTopology.topology_eq_generate_intervals]
/-
**MeasureTheory.Filtration.rightCont_eq_of_nhdsGT_eq_bot** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Filtration`。
形式化陈述：rightCont_eq_of_nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [Order
Topology ι] (𝓕 : Filtration ι m) {i : ι} (hi : 𝓝[>] i = ⊥) : 𝓕₊ i = 𝓕 i
参数：𝓕 : Filtration ι m；hi : 𝓝[>] i = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Filtration.rightCont_apply`：rightCont_apply [PartialOrder 
ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtration ι m) (i : ι) : 𝓕₊ i = 
if (𝓝[>] i).NeBot then ⨅ j > i…
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `ne_self_iff_false`：∀ {α : Sort u_1} (a : α), a ≠ a ↔ False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
-/
lemma rightCont_eq_of_nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : 𝓝[>] i = ⊥) :
    𝓕₊ i = 𝓕 i := by
  rw [rightCont_apply, hi, neBot_iff, ne_self_iff_false, if_false]

/-- If the index type is a `SuccOrder`, then `𝓕₊ = 𝓕`. -/
/-
**MeasureTheory.Filtration.rightCont_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Filtration`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : LinearOrde
r ι] [SuccOrder ι]   (𝓕 : MeasureTheory.Filtration ι m), 𝓕.rightCont = 𝓕
参数：𝓕 : MeasureTheory.Filtration ι m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.ext`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measu
rableSpace Ω} [inst : Preorder ι] {f g : MeasureTheory.Filtration ι m},   ↑f = ↑
g → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_nhdsGT_eq_bot`：rightCont_eq_of_
nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtr
ation ι m) {i : ι} (hi : 𝓝[>] i = ⊥) : 𝓕₊ i …
· 使用定理 `SuccOrder.nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : L
inearOrder α] [ClosedIciTopology α] {a : α} [SuccOrder α],   nhdsWithin a (Set.I
oi a) …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the index type is a `SuccOrder`, then `𝓕₊ = 𝓕`.
-/
@[simp] lemma rightCont_eq_self [LinearOrder ι] [SuccOrder ι] (𝓕 : Filtration ι m) :
    𝓕₊ = 𝓕 := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  ext _
  rw [rightCont_eq_of_nhdsGT_eq_bot _ SuccOrder.nhdsGT]
/-
**MeasureTheory.Filtration.rightCont_eq_of_isMax** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Filtration`。
形式化陈述：rightCont_eq_of_isMax [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : 
IsMax i) : 𝓕₊ i = 𝓕 i
参数：𝓕 : Filtration ι m；hi : IsMax i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_nhdsGT_eq_bot`：rightCont_eq_of_
nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtr
ation ι m) {i : ι} (hi : 𝓝[>] i = ⊥) : 𝓕₊ i …
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMax.Ioi_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMax a → Se
t.Ioi a = ∅
-/
lemma rightCont_eq_of_isMax [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i) :
    𝓕₊ i = 𝓕 i := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ (hi.Ioi_eq ▸ nhdsWithin_empty i)
/-
**MeasureTheory.Filtration.rightCont_eq_of_exists_gt** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Filtration`。
形式化陈述：rightCont_eq_of_exists_gt [LinearOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi
 : exists j > i, Set.Ioo i j = ∅) : 𝓕₊ i = 𝓕 i
参数：𝓕 : Filtration ι m；hi : exists j > i, Set.Ioo i j = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `covBy_iff_Ioo_eq`：covBy_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_nhdsGT_eq_bot`：rightCont_eq_of_
nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtr
ation ι m) {i : ι} (hi : 𝓝[>] i = ⊥) : 𝓕₊ i …
· 使用定理 `CovBy.nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b ⋖ a → nhdsWithin b (Set.Ioi b) = 
⊥
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
lemma rightCont_eq_of_exists_gt [LinearOrder ι] (𝓕 : Filtration ι m) {i : ι}
    (hi : ∃ j > i, Set.Ioo i j = ∅) :
    𝓕₊ i = 𝓕 i := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  obtain ⟨j, hij, hIoo⟩ := hi
  have hcov : i ⋖ j := covBy_iff_Ioo_eq.mpr ⟨hij, hIoo⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ <| CovBy.nhdsGT hcov

/-- If `i` is not isolated on the right, then `𝓕₊ i = ⨅ j > i, 𝓕 j`. This is for instance the case
when `ι` is a densely ordered linear order with no maximal elements and equipped with the order
topology, see `rightCont_eq`. -/
/-
**MeasureTheory.Filtration.rightCont_eq_of_neBot_nhdsGT** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Filtration`。
形式化陈述：rightCont_eq_of_neBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderT
opology ι] (𝓕 : Filtration ι m) (i : ι) [(𝓝[>] i).NeBot] : 𝓕₊ i = ⨅ j > i, 𝓕 j
参数：𝓕 : Filtration ι m；i : ι；𝓝[>] i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Filtration.rightCont_apply`：rightCont_apply [PartialOrder 
ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtration ι m) (i : ι) : 𝓕₊ i = 
if (𝓝[>] i).NeBot then ⨅ j > i…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
If `i` is not isolated on the right, then `𝓕₊ i = ⨅ j > i, 𝓕 j`. This is for ins
tance the case
when `ι` is a densely ordered linear order with no maximal elements and equipped
 with the order
topology, see `rightCont_eq`.
-/
lemma rightCont_eq_of_neBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) [(𝓝[>] i).NeBot] :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  rw [rightCont_apply, if_pos ‹(𝓝[>] i).NeBot›]
/-
**MeasureTheory.Filtration.rightCont_eq_of_not_isMax** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Filtration`。
形式化陈述：rightCont_eq_of_not_isMax [LinearOrder ι] [DenselyOrdered ι] (𝓕 : Filtrati
on ι m) {i : ι} (hi : ¬IsMax i) : 𝓕₊ i = ⨅ j > i, 𝓕 j
参数：𝓕 : Filtration ι m；hi : ¬IsMax i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsGT_neBot_of_exists_gt`：nhdsGT_neBot_of_exists_gt {a : α} (H : exists
 b, a < b) : NeBot (𝓝[>] a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_neBot_nhdsGT`：rightCont_eq_of_n
eBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtrat
ion ι m) (i : ι) [(𝓝[>] i).NeBot] : 𝓕₊ i = …
-/
lemma rightCont_eq_of_not_isMax [LinearOrder ι] [DenselyOrdered ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsMax i) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  have : (𝓝[>] i).NeBot := nhdsGT_neBot_of_exists_gt (not_isMax_iff.mp hi)
  exact rightCont_eq_of_neBot_nhdsGT _ _

/-- If `ι` is a densely ordered linear order with no maximal element, then no point is isolated
on the right, so that `𝓕₊ i = ⨅ j > i, 𝓕 j` holds for all `i`. This is in particular the
case when `ι := ℝ≥0`. -/
/-
**MeasureTheory.Filtration.rightCont_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Filtration`。
形式化陈述：rightCont_eq [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι] (𝓕 : Filtra
tion ι m) (i : ι) : 𝓕₊ i = ⨅ j > i, 𝓕 j
参数：𝓕 : Filtration ι m；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_not_isMax`：rightCont_eq_of_not_
isMax [LinearOrder ι] [DenselyOrdered ι] (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsM
ax i) : 𝓕₊ i = ⨅ j > i, 𝓕 j
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a

--- 原说明 ---
If `ι` is a densely ordered linear order with no maximal element, then no point 
is isolated
on the right, so that `𝓕₊ i = ⨅ j > i, 𝓕 j` holds for all `i`. This is in partic
ular the
case when `ι := ℝ≥0`.
-/
lemma rightCont_eq [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := 𝓕.rightCont_eq_of_not_isMax (not_isMax i)

variable [PartialOrder ι]
/-
**MeasureTheory.Filtration.le_rightCont** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Filtration`。
形式化陈述：le_rightCont (𝓕 : Filtration ι m) : 𝓕 <= 𝓕₊
参数：𝓕 : Filtration ι m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_neBot_nhdsGT`：rightCont_eq_of_n
eBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtrat
ion ι m) (i : ι) [(𝓝[>] i).NeBot] : 𝓕₊ i = …
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `MeasureTheory.Filtration.rightCont_apply`：rightCont_apply [PartialOrder 
ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtration ι m) (i : ι) : 𝓕₊ i = 
if (𝓝[>] i).NeBot then ⨅ j > i…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_rightCont (𝓕 : Filtration ι m) : 𝓕 ≤ 𝓕₊ := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · rw [rightCont_eq_of_neBot_nhdsGT]
    exact le_iInf₂ fun _ he => 𝓕.mono he.le
  · rw [rightCont_apply, if_neg hne]
/-
**MeasureTheory.Filtration.rightCont_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Filtration`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] (𝓕 : MeasureTheory.Filtration ι m),   𝓕.rightCont.rightCont = 𝓕.rightCont
参数：𝓕 : MeasureTheory.Filtration ι m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Iio'`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] (a : α), IsOpen (Set.Iio a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Filtration.rightCont_eq_of_neBot_nhdsGT`：rightCont_eq_of_n
eBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtrat
ion ι m) (i : ι) [(𝓝[>] i).NeBot] : 𝓕₊ i = …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `MeasureTheory.Filtration.rightCont_apply`：rightCont_apply [PartialOrder 
ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtration ι m) (i : ι) : 𝓕₊ i = 
if (𝓝[>] i).NeBot then ⨅ j > i…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.Filtration.le_rightCont`：le_rightCont (𝓕 : Filtration ι m)
 : 𝓕 <= 𝓕₊
-/
@[simp] lemma rightCont_self (𝓕 : Filtration ι m) : 𝓕₊₊ = 𝓕₊ := by
  let := Preorder.topology ι; have : OrderTopology ι := ⟨rfl⟩
  apply le_antisymm _ 𝓕₊.le_rightCont
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · have hineq : (⨅ j > i, 𝓕₊ j) ≤ ⨅ j > i, 𝓕 j := by
      apply le_iInf₂ fun u hu => ?_
      have hiou : Set.Ioo i u ∈ 𝓝[>] i := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Set.Iio u, (isOpen_Iio' u).mem_nhds hu, fun _ hx ↦ ⟨hx.2, hx.1⟩⟩
      obtain ⟨v, hv⟩ := hne.nonempty_of_mem hiou
      have hle₁ : (⨅ j > i, 𝓕₊ j) ≤ 𝓕₊ v := iInf₂_le_of_le v hv.1 le_rfl
      have hle₂ : 𝓕₊ v ≤ 𝓕 u := by
        by_cases hnv : (𝓝[>] v).NeBot
        · simpa [rightCont_eq_of_neBot_nhdsGT] using iInf₂_le_of_le u hv.2 le_rfl
        · simpa [rightCont_apply, hnv] using 𝓕.mono hv.2.le
      exact hle₁.trans hle₂
    simpa [rightCont_eq_of_neBot_nhdsGT] using hineq
  · rw [rightCont_apply, if_neg hne]

/-- A filtration `𝓕` is right continuous if it is equal to its right continuation `𝓕₊`. -/
/-
**MeasureTheory.Filtration.IsRightContinuous** 是 Mathlib 中的一个归纳类型，位于命名空间 `Measur
eTheory.Filtration`。
形式化陈述：{Ω : Type u_1} →   {ι : Type u_2} → {m : MeasurableSpace Ω} → [inst : Part
ialOrder ι] → MeasureTheory.Filtration ι m → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filtration `𝓕` is right continuous if it is equal to its right continuation `𝓕
₊`.
-/
class IsRightContinuous (𝓕 : Filtration ι m) where
  /-- The right continuity property. -/
  RC : 𝓕₊ ≤ 𝓕
/-
**MeasureTheory.Filtration.IsRightContinuous.eq** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Filtration.IsRightContinuous`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] {𝓕 : MeasureTheory.Filtration ι m}   [h : 𝓕.IsRightContinuous], 𝓕.rightCon
t = 𝓕
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.Filtration.le_rightCont`：le_rightCont (𝓕 : Filtration ι m)
 : 𝓕 <= 𝓕₊
· 使用定理 `MeasureTheory.Filtration.IsRightContinuous.RC`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {m : MeasurableSpace Ω} {inst : PartialOrder ι} {𝓕 : MeasureTheory.Filtra
tion ι m}   [self : 𝓕.IsRightContin…
-/
lemma IsRightContinuous.eq {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕] :
    𝓕₊ = 𝓕 := (le_antisymm 𝓕.le_rightCont h.RC).symm
/-
**MeasureTheory.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Filtration`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝓕 : Filtration ι m} : 𝓕₊.IsRightContinuous := ⟨(rightCont_self 𝓕).le⟩
/-
**MeasureTheory.Filtration.IsRightContinuous.measurableSet** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Filtration.IsRightContinuous`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : PartialOrd
er ι] {𝓕 : MeasureTheory.Filtration ι m}   [𝓕.IsRightContinuous] {i : ι} {s : Se
t Ω}, MeasurableSet s → MeasurableSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.IsRightContinuous.eq`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {m : MeasurableSpace Ω} [inst : PartialOrder ι] {𝓕 : MeasureTheory.Filtra
tion ι m}   [h : 𝓕.IsRightContinuou…
-/
lemma IsRightContinuous.measurableSet {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[𝓕₊ i] s) :
    MeasurableSet[𝓕 i] s := IsRightContinuous.eq (𝓕 := 𝓕) ▸ hs

end IsRightContinuous

variable {β : ι → Type*} [∀ i, TopologicalSpace (β i)] [∀ i, MetrizableSpace (β i)]
  [mβ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
  [Preorder ι]

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that the sequence of functions is measurable with respect to
the filtration. -/
/-
**MeasureTheory.Filtration.natural** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Filt
ration`。
形式化陈述：natural (u : (i : ι) -> Ω -> β i) (hum : forall i, StronglyMeasurable (u i
)) : Filtration ι m where seq i
参数：u : (i : ι) -> Ω -> β i；hum : forall i, StronglyMeasurable (u i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that the sequence of functions is measurable with respect to
the filtration.
-/
def natural (u : (i : ι) → Ω → β i) (hum : ∀ i, StronglyMeasurable (u i)) : Filtration ι m where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap (u j) (mβ j)
  mono' _ _ hij := biSup_mono fun _ => ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j _ s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht
/-
**MeasureTheory.Filtration.natural_eq_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Filtration`。
形式化陈述：natural_eq_comap (u : (i : ι) -> Ω -> β i) (hum : forall (i : ι), Strongly
Measurable (u i)) (i : ι) : natural u hum i = .comap (fun ω (j : Set.Iic i) => u
 j ω) inferInstance
参数：u : (i : ι) -> Ω -> β i；hum : forall (i : ι), StronglyMeasurable (u i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableSpace.comap_process_pi`：MeasurableSpace.comap_process_pi (X : 
(a : δ) -> β -> X a) : MeasurableSpace.comap (fun b a => X a b) inferInstance = 
⨆ a, MeasurableSpace.c…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
-/
lemma natural_eq_comap (u : (i : ι) → Ω → β i) (hum : ∀ (i : ι), StronglyMeasurable (u i)) (i : ι) :
    natural u hum i = .comap (fun ω (j : Set.Iic i) ↦ u j ω) inferInstance := by
  simp_rw [natural, MeasurableSpace.comap_process_pi, iSup_subtype']
  rfl

section

open MeasurableSpace

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.Filtration.filtrationOfSet_eq_natural** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Filtration`。
形式化陈述：filtrationOfSet_eq_natural [forall i, MulZeroOneClass (β i)] [forall i, No
ntrivial (β i)] {s : ι -> Set Ω} (hsm : forall i, MeasurableSet[m] (s i)) : filt
rationOfSet hsm = natural (fun i => (s i).indicator (fun _ => 1 : Ω -> β i)) fun
 i => stronglyMeasurable_one.indicator (hsm i)
参数：β i；β i；hsm : forall i, MeasurableSet[m] (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_one`：stronglyMeasurable_one [One β] : S
tronglyMeasurable (1 : α -> β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSpace.measurableSpace_iSup_eq`：measurableSpace_iSup_eq (m : ι 
-> MeasurableSpace α) : ⨆ n, m n = generateFrom { s | exists n, MeasurableSet[m 
n] s }
· 使用定理 `MeasureTheory.Filtration.mk.congr_simp`：∀ {Ω : Type u_1} {ι : Type u_2} 
[inst : Preorder ι] {m : MeasurableSpace Ω} (seq seq_1 : ι → MeasurableSpace Ω) 
  (e_seq : seq = seq_1) (mon…
· 使用定理 `MeasureTheory.Filtration.mk.injEq`：∀ {Ω : Type u_1} {ι : Type u_2} [inst
 : Preorder ι] {m : MeasurableSpace Ω} (seq : ι → MeasurableSpace Ω)   (mono' : 
Monotone seq) (le' : ∀ …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasurableSpace.comap_eq_generateFrom`：comap_eq_generateFrom (m : Measur
ableSpace β) (f : α -> β) : m.comap f = generateFrom { t | exists s, MeasurableS
et s ∧ f ⁻¹' s = t }
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.indicator_const_preimage`：∀ {α : Type u_1} {M : Type u_3} [inst : Ze
ro M] (U : Set α) (s : Set M) (a : M),   (U.indicator fun x => a) ⁻¹' s ∈ {Set.u
niv, U, Uᶜ, ∅}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
（共 31 条，此处仅展示前 30 条）
-/
theorem filtrationOfSet_eq_natural [∀ i, MulZeroOneClass (β i)] [∀ i, Nontrivial (β i)]
    {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[m] (s i)) :
    filtrationOfSet hsm = natural (fun i => (s i).indicator (fun _ => 1 : Ω → β i)) fun i =>
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
    suffices MeasurableSpace.generateFrom {t | n ≤ i ∧
      MeasurableSet[MeasurableSpace.comap ((s n).indicator (fun _ => 1 : Ω → β n)) (mβ n)] t} ≤
        MeasurableSpace.generateFrom {t | ∃ (j : ι), j ≤ i ∧ s j = t} by
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

variable {E : Type*} [Zero E] [TopologicalSpace E] {ℱ : Filtration ι m} {f : ι → Ω → E}
  {μ : Measure Ω}

open scoped Classical in
/-- Given a process `f` and a filtration `ℱ`, if `f` converges to some `g` almost everywhere and
`g` is `⨆ n, ℱ n`-measurable, then `limitProcess f ℱ μ` chooses said `g`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `f` adapted to `ℱ`
converges to `limitProcess f ℱ μ` `μ`-almost everywhere. -/
/-
**MeasureTheory.Filtration.limitProcess** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.Filtration`。
形式化陈述：limitProcess (f : ι -> Ω -> E) (ℱ : Filtration ι m) (μ : Measure Ω)
参数：f : ι -> Ω -> E；ℱ : Filtration ι m；μ : Measure Ω。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Given a process `f` and a filtration `ℱ`, if `f` converges to some `g` almost ev
erywhere and
`g` is `⨆ n, ℱ n`-measurable, then `limitProcess f ℱ μ` chooses said `g`, else i
t returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `f` ad
apted to `ℱ`
converges to `limitProcess f ℱ μ` `μ`-almost everywhere.
-/
noncomputable def limitProcess (f : ι → Ω → E) (ℱ : Filtration ι m)
    (μ : Measure Ω) :=
  if h : ∃ g : Ω → E,
    StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0
/-
**MeasureTheory.Filtration.stronglyMeasurable_limitProcess** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Filtration`。
形式化陈述：stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ n, ℱ n] (limitProce
ss f ℱ μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Filtration.limitProcess.eq_1`：∀ {Ω : Type u_1} {ι : Type u
_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {E : Type u_4} [inst_1 : Zero E]
   [inst_2 : TopologicalSpace E]…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
-/
theorem stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ) := by
  rw [limitProcess]
  split_ifs with h
  exacts [(Classical.choose_spec h).1, stronglyMeasurable_zero]
/-
**MeasureTheory.Filtration.stronglyMeasurable_limit_process'** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Filtration`。
形式化陈述：stronglyMeasurable_limit_process' : StronglyMeasurable[m] (limitProcess f 
ℱ μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.stronglyMeasurable_limitProcess`：stronglyMeasur
able_limitProcess : StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ)
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem stronglyMeasurable_limit_process' : StronglyMeasurable[m] (limitProcess f ℱ μ) :=
  stronglyMeasurable_limitProcess.mono (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _)
/-
**MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Filtration`。
形式化陈述：memLp_limitProcess_of_eLpNorm_bdd {R : Real>=0} {p : Real>=0∞} {F : Type*}
 [NormedAddCommGroup F] {ℱ : Filtration Nat m} {f : Nat -> Ω -> F} (hfm : forall
 n, AEStronglyMeasurable (f n) μ) (hbdd : forall n, eLpNorm (f n) p μ <= R) : Me
mLp (limitProcess f ℱ μ) p μ
参数：hfm : forall n, AEStronglyMeasurable (f n) μ；hbdd : forall n, eLpNorm (f n) p
 μ <= R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Filtration.limitProcess.eq_1`：∀ {Ω : Type u_1} {ι : Type u
_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {E : Type u_4} [inst_1 : Zero E]
   [inst_2 : TopologicalSpace E]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`：eLpNorm_lim_le_liminf_eL
pNorm {f : Nat -> α -> E} (hf : forall n, AEStronglyMeasurable (f n) μ) (f_lim :
 α -> E) (h_lim : forallᵐ x : α ∂μ, …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
-/
theorem memLp_limitProcess_of_eLpNorm_bdd {R : ℝ≥0} {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F]
    {ℱ : Filtration ℕ m} {f : ℕ → Ω → F} (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : MemLp (limitProcess f ℱ μ) p μ := by
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

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The canonical filtration on the product space `Π i, X i`, where `piLE i`
consists of measurable sets depending only on coordinates `≤ i`. -/
/-
**MeasureTheory.Filtration.piLE** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Filtrat
ion`。
形式化陈述：piLE : @Filtration (Π i, X i) ι _ pi where seq i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical filtration on the product space `Π i, X i`, where `piLE i`
consists of measurable sets depending only on coordinates `≤ i`.
-/
def piLE : @Filtration (Π i, X i) ι _ pi where
  seq i := pi.comap (restrictLe i)
  mono' i j hij := by
    simp only
    rw [← restrictLe₂_comp_restrictLe hij, ← comap_comp]
    exact comap_mono (measurable_restrictLe₂ _).comap_le
  le' i := (measurable_restrictLe i).comap_le

variable [LocallyFiniteOrderBot ι]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.Filtration.piLE_eq_comap_frestrictLe** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Filtration`。
形式化陈述：piLE_eq_comap_frestrictLe (i : ι) : piLE (X
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.comap_mono`：comap_mono (h : m₁ <= m₂) : m₁.comap g <= m₂
.comap g
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Preorder.piCongrLeft_comp_restrictLe`：piCongrLeft_comp_restrictLe {a : α
} : ((Equiv.IicFinsetSet a).symm.piCongrLeft (fun i : Iic a => π i)) ∘ (restrict
Le a) = frestrictLe a
· 使用定理 `MeasurableEquiv.coe_piCongrLeft`：coe_piCongrLeft (f : δ ≃ δ') : ⇑(Measur
ableEquiv.piCongrLeft π f) = f.piCongrLeft π
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
-/
lemma piLE_eq_comap_frestrictLe (i : ι) : piLE (X := X) i = pi.comap (frestrictLe i) := by
  apply le_antisymm
  · simp_rw [piLE, ← piCongrLeft_comp_frestrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
    exact MeasurableSpace.comap_mono <| Measurable.comap_le (by fun_prop)
  · rw [← piCongrLeft_comp_restrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
    exact MeasurableSpace.comap_mono <| Measurable.comap_le (by fun_prop)

end piLE

section piFinset

open MeasurableSpace Finset

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The filtration of events which only depends on finitely many coordinates
on the product space `Π i, X i`, `piFinset s` consists of measurable sets depending only on
coordinates in `s`, where `s : Finset ι`. -/
/-
**MeasureTheory.Filtration.piFinset** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Fil
tration`。
形式化陈述：piFinset : @Filtration (Π i, X i) (Finset ι) _ pi where seq s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filtration of events which only depends on finitely many coordinates
on the product space `Π i, X i`, `piFinset s` consists of measurable sets depend
ing only on
coordinates in `s`, where `s : Finset ι`.
-/
def piFinset : @Filtration (Π i, X i) (Finset ι) _ pi where
  seq s := pi.comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst, ← comap_comp]
    exact comap_mono (measurable_restrict₂ hst).comap_le
  le' s := s.measurable_restrict.comap_le
/-
**MeasureTheory.Filtration.piFinset_eq_comap_restrict** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Filtration`。
形式化陈述：piFinset_eq_comap_restrict (s : Finset ι) : piFinset (X
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piFinset_eq_comap_restrict (s : Finset ι) :
    piFinset (X := X) s = pi.comap (s : Set ι).domRestrict := rfl

end piFinset

variable {α : Type*}

/-- The exterior σ-algebras of finite sets of `α` form a cofiltration indexed by `Finset α`. -/
/-
**MeasureTheory.Filtration.cylinderEventsCompl** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.Filtration`。
形式化陈述：cylinderEventsCompl : Filtration (Finset α)ᵒᵈ (.pi (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exterior σ-algebras of finite sets of `α` form a cofiltration indexed by `Fi
nset α`.
-/
def cylinderEventsCompl : Filtration (Finset α)ᵒᵈ (.pi (X := fun _ : α ↦ Ω)) where
  seq Λ := cylinderEvents (↑(OrderDual.ofDual Λ))ᶜ
  mono' _ _ h := cylinderEvents_mono <| Set.compl_subset_compl_of_subset h
  le' _ := cylinderEvents_le_pi

end Filtration

end MeasureTheory

