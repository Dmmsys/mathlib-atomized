/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Filter.AtTopBot.CompleteLattice
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Tactic.FinCases

/-!
# Measurably generated filters

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `Filter.Eventually`.
-/

public section

open Set Filter

universe uι

variable {α β γ δ : Type*} {ι : Sort uι}

namespace MeasurableSpace

/--
theorem `generateFrom_singleton` / 定理 `generateFrom_singleton`

English:
theorem generateFrom_singleton
  given: (s : Set α)
  proof: by
  let : MeasurableSpace α := generateFrom {s}
  refine le_antisymm (generateFrom_le fun t ht => ⟨{True}, trivial, by simp [ht.symm]⟩) ?_
  rintro _ ⟨u, -, rfl⟩
  exact (show MeasurableSet s from GenerateMeasurable.basic _ <| mem_singleton s).mem trivial

中文:
定理 generateFrom_singleton
  条件: (s : 集合 α)
  证明: by
  let : MeasurableSpace α := generateFrom {s}
  refine le_antisymm (generateFrom_le fun t ht => ⟨{True}, trivial, by simp [ht.symm]⟩) ?_
  rintro _ ⟨u, -, rfl⟩
  exact (show MeasurableSet s from GenerateMeasurable.basic _ <| mem_singleton s).mem trivial
-/
@[simp] theorem generateFrom_singleton (s : Set α) :
    generateFrom {s} = MeasurableSpace.comap (· in s) ⊤ := by
  let : MeasurableSpace α := generateFrom {s}
  refine le_antisymm (generateFrom_le fun t ht => ⟨{True}, trivial, by simp [ht.symm]⟩) ?_
  rintro _ ⟨u, -, rfl⟩
  exact (show MeasurableSet s from GenerateMeasurable.basic _ <| mem_singleton s).mem trivial

/--
lemma `generateFrom_singleton_le` / 引理 `generateFrom_singleton_le`

English:
lemma generateFrom_singleton_le
  given: {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
  proof: generateFrom_le (fun _ ht => mem_singleton_iff.1 ht ▸ hs)

中文:
引理 generateFrom_singleton_le
  条件: {m : 可测空间 α} {s : 集合 α} (hs : 可测集 s)
  证明: generateFrom_le (fun _ ht => mem_singleton_iff.1 ht ▸ hs)

Depends on / 依赖: generateFrom_le, mem_singleton_iff
-/
lemma generateFrom_singleton_le {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) :
    MeasurableSpace.generateFrom {s} <= m :=
  generateFrom_le (fun _ ht => mem_singleton_iff.1 ht ▸ hs)

/--
lemma `comap_indicator_const_le_generateFrom_singleton` / 引理 `comap_indicator_const_le_generateFrom_singleton`

English:
lemma comap_indicator_const_le_generateFrom_singleton
  statement: {M : Type*} [Zero M] [MeasurableSpace M]
  proof: (measurable_const.indicator (measurableSet_generateFrom (by simp))).comap_le

中文:
引理 comap_indicator_const_le_generateFrom_singleton
  结论: {M : 类型} [零 M] [可测空间 M]
  证明: (measurable_const.indicator (measurableSet_generateFrom (by simp))).comap_le

Depends on / 依赖: comap_le, indicator, measurableSet_generateFrom, measurable_const, measurable_const.indicator
-/
lemma comap_indicator_const_le_generateFrom_singleton {M : Type*} [Zero M] [MeasurableSpace M]
    (s : Set α) (c : M) :
    MeasurableSpace.comap (s.indicator (fun _ => c)) inferInstance <=
      MeasurableSpace.generateFrom {s} :=
  (measurable_const.indicator (measurableSet_generateFrom (by simp))).comap_le

end MeasurableSpace

namespace MeasureTheory

/--
theorem `measurableSet_generateFrom_singleton_iff` / 定理 `measurableSet_generateFrom_singleton_iff`

English:
theorem measurableSet_generateFrom_singleton_iff
  given: {s t : Set α}
  proof: by
  simp_rw +instances [MeasurableSpace.generateFrom_singleton]
  unfold MeasurableSet MeasurableSpace.MeasurableSet' MeasurableSpace.comap
  simp_rw [MeasurableSpace.measurableSet_top, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hT : True in x
    · by_cases hF : False in x
      · su

中文:
定理 measurableSet_generateFrom_singleton_iff
  条件: {s t : 集合 α}
  证明: by
  simp_rw +instances [MeasurableSpace.generateFrom_singleton]
  unfold MeasurableSet MeasurableSpace.MeasurableSet' MeasurableSpace.comap
  simp_rw [MeasurableSpace.measurableSet_top, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hT : True in x
    · by_cases hF : False in x
      · su

Depends on / 依赖: MeasurableSet, MeasurableSpace, MeasurableSpace.MeasurableSet, MeasurableSpace.comap, MeasurableSpace.generateFrom_singleton, MeasurableSpace.measurableSet_top, fin_cases, generateFrom_singleton, instances, measurableSet_top, on_goal, simp_rw, subseteq, true_and, univ_eq_true_false
-/
theorem measurableSet_generateFrom_singleton_iff {s t : Set α} :
    MeasurableSet[MeasurableSpace.generateFrom {s}] t ↔ t = ∅ ∨ t = s ∨ t = sᶜ ∨ t = univ := by
  simp_rw +instances [MeasurableSpace.generateFrom_singleton]
  unfold MeasurableSet MeasurableSpace.MeasurableSet' MeasurableSpace.comap
  simp_rw [MeasurableSpace.measurableSet_top, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hT : True in x
    · by_cases hF : False in x
      · suffices x = univ by grind
        grind [univ_eq_true_false]
      · grind
    · by_cases hF : False in x
      · grind
      · suffices x subseteq ∅ by grind
        intro p hp
        fin_cases p <;> contradiction
  · rintro (rfl | rfl | rfl | rfl)
    on_goal 1 => use ∅
    on_goal 2 => use {True}
    on_goal 3 => use {False}
    on_goal 4 => use Set.univ
    all_goals
      simp [compl_def]

end MeasureTheory

namespace Filter

variable [MeasurableSpace α]

/--
Definition of `IsMeasurablyGenerated` / `IsMeasurablyGenerated` 的定义

English:
class IsMeasurablyGenerated
  parameters: (f : Filter α)
  axioms and operations (1):
    - exists_measurable_subset : forall ⦃s⦄, s in f -> exists t in f, MeasurableSet t ∧ t subseteq s

中文:
类 是MeasurablyGenerated
  参数: (f : 滤子 α)
  公理与运算 (1 个):
    - exists_measurable_subset : 对任意 ⦃s⦄, s in f -> 存在 t in f, 可测集 t ∧ t subseteq s
-/
class IsMeasurablyGenerated (f : Filter α) : Prop where
  exists_measurable_subset : forall ⦃s⦄, s in f -> exists t in f, MeasurableSet t ∧ t subseteq s

/--
Instance `isMeasurablyGenerated_bot` / 实例 `isMeasurablyGenerated_bot`

English:
instance isMeasurablyGenerated_bot
  signature: : IsMeasurablyGenerated (⊥ : Filter α)
  body: ⟨fun _ _ => ⟨∅, mem_bot, MeasurableSet.empty, empty_subset _⟩⟩

中文:
实例 isMeasurablyGenerated_bot
  签名: : 是MeasurablyGenerated (⊥ : 滤子 α)
  定义体: ⟨fun _ _ => ⟨∅, mem_bot, MeasurableSet.empty, empty_subset _⟩⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, empty_subset, mem_bot
-/
instance isMeasurablyGenerated_bot : IsMeasurablyGenerated (⊥ : Filter α) :=
  ⟨fun _ _ => ⟨∅, mem_bot, MeasurableSet.empty, empty_subset _⟩⟩

/--
Instance `isMeasurablyGenerated_top` / 实例 `isMeasurablyGenerated_top`

English:
instance isMeasurablyGenerated_top
  signature: : IsMeasurablyGenerated (⊤ : Filter α)
  body: ⟨fun _s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩

中文:
实例 isMeasurablyGenerated_top
  签名: : 是MeasurablyGenerated (⊤ : 滤子 α)
  定义体: ⟨fun _s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, univ_mem
-/
instance isMeasurablyGenerated_top : IsMeasurablyGenerated (⊤ : Filter α) :=
  ⟨fun _s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩

/--
theorem `Eventually.exists_measurable_mem` / 定理 `Eventually.exists_measurable_mem`

English:
theorem Eventually.exists_measurable_mem
  statement: {f : Filter α} [IsMeasurablyGenerated f] {p : α -> Prop}
  proof: IsMeasurablyGenerated.exists_measurable_subset h

中文:
定理 Eventually.存在_measurable_mem
  结论: {f : 滤子 α} [是MeasurablyGenerated f] {p : α -> 命题}
  证明: IsMeasurablyGenerated.exists_measurable_subset h

Depends on / 依赖: IsMeasurablyGenerated, IsMeasurablyGenerated.exists_measurable_subset, exists_measurable_subset
-/
theorem Eventually.exists_measurable_mem {f : Filter α} [IsMeasurablyGenerated f] {p : α -> Prop}
    (h : forallᶠ x in f, p x) : exists s in f, MeasurableSet s ∧ forall x in s, p x :=
  IsMeasurablyGenerated.exists_measurable_subset h

/--
theorem `Eventually.exists_measurable_mem_of_smallSets` / 定理 `Eventually.exists_measurable_mem_of_smallSets`

English:
theorem Eventually.exists_measurable_mem_of_smallSets
  statement: {f : Filter α} [IsMeasurablyGenerated f]
  proof: let ⟨_s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩

中文:
定理 Eventually.存在_measurable_mem_of_smallSets
  结论: {f : 滤子 α} [是MeasurablyGenerated f]
  证明: let ⟨_s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩

Depends on / 依赖: IsMeasurablyGenerated, IsMeasurablyGenerated.exists_measurable_subset, eventually_smallSets, exists_measurable_subset
-/
theorem Eventually.exists_measurable_mem_of_smallSets {f : Filter α} [IsMeasurablyGenerated f]
    {p : Set α -> Prop} (h : forallᶠ s in f.smallSets, p s) : exists s in f, MeasurableSet s ∧ p s :=
  let ⟨_s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩

/--
Instance `inf_isMeasurablyGenerated` / 实例 `inf_isMeasurablyGenerated`

English:
instance inf_isMeasurablyGenerated
  signature: (f g : Filter α) [IsMeasurablyGenerated f]
  body: by
  constructor
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine ⟨s'f inter s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, ?_⟩
 

中文:
实例 inf_isMeasurablyGenerated
  签名: (f g : 滤子 α) [是MeasurablyGenerated f]
  定义体: by
  constructor
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine ⟨s'f inter s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, ?_⟩
 

Depends on / 依赖: IsMeasurablyGenerated, IsMeasurablyGenerated.exists_measurable_subset, exists_measurable_subset, hmf.inter, inter_mem_inf, inter_subset_inter
-/
instance inf_isMeasurablyGenerated (f g : Filter α) [IsMeasurablyGenerated f]
    [IsMeasurablyGenerated g] : IsMeasurablyGenerated (f ⊓ g) := by
  constructor
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine ⟨s'f inter s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, ?_⟩
  exact inter_subset_inter hs'sf hs'sg

/--
theorem `principal_isMeasurablyGenerated_iff` / 定理 `principal_isMeasurablyGenerated_iff`

English:
theorem principal_isMeasurablyGenerated_iff
  given: {s : Set α}
  proof: by
  refine ⟨?_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := hts.antisymm ht
  rwa [← this]

alias ⟨_, _root_.MeasurableSet.principal_isMeasurablyGenerated⟩ :=
  principal_isMeasurablyGenerated_i

中文:
定理 principal_isMeasurablyGenerated_iff
  条件: {s : 集合 α}
  证明: by
  refine ⟨?_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := hts.antisymm ht
  rwa [← this]

alias ⟨_, _root_.MeasurableSet.principal_isMeasurablyGenerated⟩ :=
  principal_isMeasurablyGenerated_i

Depends on / 依赖: antisymm, hts.antisymm, mem_principal_self
-/
theorem principal_isMeasurablyGenerated_iff {s : Set α} :
    IsMeasurablyGenerated (𝓟 s) ↔ MeasurableSet s := by
  refine ⟨?_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := hts.antisymm ht
  rwa [← this]

alias ⟨_, _root_.MeasurableSet.principal_isMeasurablyGenerated⟩ :=
  principal_isMeasurablyGenerated_iff

/--
Instance `iInf_isMeasurablyGenerated` / 实例 `iInf_isMeasurablyGenerated`

English:
instance iInf_isMeasurablyGenerated
  signature: {f : ι -> Filter α} [forall i, IsMeasurablyGenerated (f i)]
  body: by
  refine ⟨fun s hs => ?_⟩
  rw [← Equiv.plift.surjective.iInf_comp]; rw [mem_iInf] at hs
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩
  choose U hUf hU using fun i => IsMeasurablyGenerated.exists_measurable_subset (hVf i)
  refine ⟨⋂ i : t, U i, ?_, ?_, ?_⟩
  · rw [← Equiv.plift.surjective.iInf_comp, 

中文:
实例 iInf_isMeasurablyGenerated
  签名: {f : ι -> 滤子 α} [对任意 i, 是MeasurablyGenerated (f i)]
  定义体: by
  refine ⟨fun s hs => ?_⟩
  rw [← Equiv.plift.surjective.iInf_comp]; rw [mem_iInf] at hs
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩
  choose U hUf hU using fun i => IsMeasurablyGenerated.exists_measurable_subset (hVf i)
  refine ⟨⋂ i : t, U i, ?_, ?_, ?_⟩
  · rw [← Equiv.plift.surjective.iInf_comp, 

Depends on / 依赖: Equiv.plift.surjective.iInf_comp, IsMeasurablyGenerated, IsMeasurablyGenerated.exists_measurable_subset, MeasurableSet, MeasurableSet.iInter, countable, exists_measurable_subset, ht.countable.toEncodable.countable, iInf_comp, iInter, iInter_mono, mem_iInf, surjective, toEncodable
-/
instance iInf_isMeasurablyGenerated {f : ι -> Filter α} [forall i, IsMeasurablyGenerated (f i)] :
    IsMeasurablyGenerated (⨅ i, f i) := by
  refine ⟨fun s hs => ?_⟩
  rw [← Equiv.plift.surjective.iInf_comp]; rw [mem_iInf] at hs
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩
  choose U hUf hU using fun i => IsMeasurablyGenerated.exists_measurable_subset (hVf i)
  refine ⟨⋂ i : t, U i, ?_, ?_, ?_⟩
  · rw [← Equiv.plift.surjective.iInf_comp, mem_iInf]
    exact ⟨t, ht, U, hUf, rfl⟩
  · have := ht.countable.toEncodable.countable
    exact MeasurableSet.iInter fun i => (hU i).1
  · exact iInter_mono fun i => (hU i).2

end Filter

/-- The set of points for which a sequence of measurable functions converges to a given value
is measurable. -/
@[measurability]
/--
lemma `measurableSet_tendsto` / 引理 `measurableSet_tendsto`

English:
lemma measurableSet_tendsto
  statement: {_ : MeasurableSpace β} [MeasurableSpace γ]
  proof: by
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  rcases (Filter.hasBasis_self.mpr hl'.exists_measurable_subset).exists_antitone_subbasis with
    ⟨v, v_meas, hv⟩
  simp only [hu.tendsto_iff hv.toHasBasis, true_imp_iff, true_and, ofPred_forall, ofPred_exists]
  exact .iInter fun n => .iUnion fun _ 

中文:
引理 measurableSet_tendsto
  结论: {_ : 可测空间 β} [可测空间 γ]
  证明: by
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  rcases (Filter.hasBasis_self.mpr hl'.exists_measurable_subset).exists_antitone_subbasis with
    ⟨v, v_meas, hv⟩
  simp only [hu.tendsto_iff hv.toHasBasis, true_imp_iff, true_and, ofPred_forall, ofPred_exists]
  exact .iInter fun n => .iUnion fun _ 

Depends on / 依赖: Filter, Filter.hasBasis_self.mpr, biInter, exists_antitone_basis, exists_antitone_subbasis, exists_measurable_subset, hasBasis_self, hu.tendsto_iff, hv.toHasBasis, iInter, iUnion, l.exists_antitone_basis, ofPred_exists, ofPred_forall, preimage, tendsto_iff, toHasBasis, to_countable, true_and, true_imp_iff
-/
lemma measurableSet_tendsto {_ : MeasurableSpace β} [MeasurableSpace γ]
    [Countable δ] {l : Filter δ} [l.IsCountablyGenerated]
    (l' : Filter γ) [l'.IsCountablyGenerated] [hl' : l'.IsMeasurablyGenerated]
    {f : δ -> β -> γ} (hf : forall i, Measurable (f i)) :
    MeasurableSet { x | Tendsto (fun n => f n x) l l' } := by
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  rcases (Filter.hasBasis_self.mpr hl'.exists_measurable_subset).exists_antitone_subbasis with
    ⟨v, v_meas, hv⟩
  simp only [hu.tendsto_iff hv.toHasBasis, true_imp_iff, true_and, ofPred_forall, ofPred_exists]
  exact .iInter fun n => .iUnion fun _ => .biInter (to_countable _) fun i _ =>
    (v_meas n).2.preimage (hf i)

namespace MeasurableSet

variable [MeasurableSpace α]

/--
theorem `iUnion_of_monotone_of_frequently` / 定理 `iUnion_of_monotone_of_frequently`

English:
theorem iUnion_of_monotone_of_frequently
  proof: by
  rcases exists_seq_forall_of_frequently hs with ⟨x, hx, hxm⟩
  rw [← hsm.iUnion_comp_tendsto_atTop hx]
  exact .iUnion hxm

中文:
定理 iUnion_of_monotone_of_frequently
  证明: by
  rcases exists_seq_forall_of_frequently hs with ⟨x, hx, hxm⟩
  rw [← hsm.iUnion_comp_tendsto_atTop hx]
  exact .iUnion hxm
-/
protected theorem iUnion_of_monotone_of_frequently
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α}
    (hsm : Monotone s) (hs : existsᶠ i in atTop, MeasurableSet (s i)) : MeasurableSet (⋃ i, s i) := by
  rcases exists_seq_forall_of_frequently hs with ⟨x, hx, hxm⟩
  rw [← hsm.iUnion_comp_tendsto_atTop hx]
  exact .iUnion hxm

/--
theorem `iInter_of_antitone_of_frequently` / 定理 `iInter_of_antitone_of_frequently`

English:
theorem iInter_of_antitone_of_frequently
  proof: by
  rw [← compl_iff]; rw [compl_iInter]
exact .iUnion_of_monotone_of_frequently (compl_anti.comp hsm) hs.mono fun _ => .compl

中文:
定理 i整数er_of_antitone_of_frequently
  证明: by
  rw [← compl_iff]; rw [compl_iInter]
exact .iUnion_of_monotone_of_frequently (compl_anti.comp hsm) hs.mono fun _ => .compl
-/
protected theorem iInter_of_antitone_of_frequently
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α}
    (hsm : Antitone s) (hs : existsᶠ i in atTop, MeasurableSet (s i)) : MeasurableSet (⋂ i, s i) := by
  rw [← compl_iff]; rw [compl_iInter]
exact .iUnion_of_monotone_of_frequently (compl_anti.comp hsm) hs.mono fun _ => .compl

/--
theorem `iUnion_of_monotone` / 定理 `iUnion_of_monotone`

English:
theorem iUnion_of_monotone
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  proof: by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
| inr _ => exact .iUnion_of_monotone_of_frequently hsm .of_forall hs

中文:
定理 iUnion_of_monotone
  结论: {ι : 类型} [预序 ι] [IsDirectedOrder ι]
  证明: by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
| inr _ => exact .iUnion_of_monotone_of_frequently hsm .of_forall hs
-/
protected theorem iUnion_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α}
    (hsm : Monotone s) (hs : forall i, MeasurableSet (s i)) : MeasurableSet (⋃ i, s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
| inr _ => exact .iUnion_of_monotone_of_frequently hsm .of_forall hs

/--
theorem `iInter_of_antitone` / 定理 `iInter_of_antitone`

English:
theorem iInter_of_antitone
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  proof: by
  rw [← compl_iff]; rw [compl_iInter]
  exact .iUnion_of_monotone (compl_anti.comp hsm) fun i => (hs i).compl

中文:
定理 i整数er_of_antitone
  结论: {ι : 类型} [预序 ι] [IsDirectedOrder ι]
  证明: by
  rw [← compl_iff]; rw [compl_iInter]
  exact .iUnion_of_monotone (compl_anti.comp hsm) fun i => (hs i).compl
-/
protected theorem iInter_of_antitone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α}
    (hsm : Antitone s) (hs : forall i, MeasurableSet (s i)) : MeasurableSet (⋂ i, s i) := by
  rw [← compl_iff]; rw [compl_iInter]
  exact .iUnion_of_monotone (compl_anti.comp hsm) fun i => (hs i).compl


/--
Instance `Subtype.instMembership` / 实例 `Subtype.instMembership`

English:
instance Subtype.instMembership
  signature: : Membership α (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun s a => a in (s : Set α)⟩

@[simp]

中文:
实例 子类型.instMembership
  签名: : Membership α (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun s a => a in (s : Set α)⟩

@[simp]
-/
instance Subtype.instMembership : Membership α (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun s a => a in (s : Set α)⟩

@[simp]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: (a : α) (s : Subtype (MeasurableSet : Set α -> Prop))
  statement: a in (s : Set α) ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_coe
  条件: (a : α) (s : 子类型 (可测集 : 集合 α -> 命题))
  结论: a in (s : 集合 α) ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe (a : α) (s : Subtype (MeasurableSet : Set α -> Prop)) : a in (s : Set α) ↔ a in s :=
  Iff.rfl

/--
Instance `Subtype.instEmptyCollection` / 实例 `Subtype.instEmptyCollection`

English:
instance Subtype.instEmptyCollection
  signature: : EmptyCollection (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨⟨∅, MeasurableSet.empty⟩⟩

@[simp]

中文:
实例 子类型.instEmptyCollection
  签名: : EmptyCollection (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨⟨∅, MeasurableSet.empty⟩⟩

@[simp]

Depends on / 依赖: LawfulBEq, MeasurableSet, MeasurableSet.empty
-/
instance Subtype.instEmptyCollection : EmptyCollection (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩

@[simp]
/--
theorem `coe_empty` / 定理 `coe_empty`

English:
theorem coe_empty
  statement: ↑(∅ : Subtype (MeasurableSet : Set α -> Prop)) = (∅ : Set α)
  proof: rfl

中文:
定理 coe_empty
  结论: ↑(∅ : 子类型 (可测集 : 集合 α -> 命题)) = (∅ : 集合 α)
  证明: rfl

Depends on / 依赖: DecidableEq
-/
theorem coe_empty : ↑(∅ : Subtype (MeasurableSet : Set α -> Prop)) = (∅ : Set α) :=
  rfl

/--
Instance `Subtype.instInsert` / 实例 `Subtype.instInsert`

English:
instance Subtype.instInsert
  signature: [MeasurableSingletonClass α]
  body: ⟨fun a s => ⟨insert a (s : Set α), s.prop.insert a⟩⟩

@[simp]

中文:
实例 子类型.instInsert
  签名: [MeasurableSingleton类 α]
  定义体: ⟨fun a s => ⟨insert a (s : Set α), s.prop.insert a⟩⟩

@[simp]

Depends on / 依赖: Inhabited, insert, s.prop.insert
-/
instance Subtype.instInsert [MeasurableSingletonClass α] :
    Insert α (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun a s => ⟨insert a (s : Set α), s.prop.insert a⟩⟩

@[simp]
/--
theorem `coe_insert` / 定理 `coe_insert`

English:
theorem coe_insert
  statement: [MeasurableSingletonClass α] (a : α)
  proof: rfl

中文:
定理 coe_insert
  结论: [MeasurableSingleton类 α] (a : α)
  证明: rfl

Depends on / 依赖: Nonempty
-/
theorem coe_insert [MeasurableSingletonClass α] (a : α)
    (s : Subtype (MeasurableSet : Set α -> Prop)) :
    ↑(Insert.insert a s) = (Insert.insert a s : Set α) :=
  rfl

/--
Instance `Subtype.instSingleton` / 实例 `Subtype.instSingleton`

English:
instance Subtype.instSingleton
  signature: [MeasurableSingletonClass α]
  body: ⟨fun a => ⟨{a}, .singleton _⟩⟩

中文:
实例 子类型.instSingleton
  签名: [MeasurableSingleton类 α]
  定义体: ⟨fun a => ⟨{a}, .singleton _⟩⟩

Depends on / 依赖: Nontrivial, singleton
-/
instance Subtype.instSingleton [MeasurableSingletonClass α] :
    Singleton α (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun a => ⟨{a}, .singleton _⟩⟩

/--
theorem `coe_singleton` / 定理 `coe_singleton`

English:
theorem coe_singleton
  given: [MeasurableSingletonClass α] (a : α)
  proof: rfl

中文:
定理 coe_singleton
  条件: [MeasurableSingleton类 α] (a : α)
  证明: rfl

Depends on / 依赖: Unique
-/
@[simp] theorem coe_singleton [MeasurableSingletonClass α] (a : α) :
    ↑({a} : Subtype (MeasurableSet : Set α -> Prop)) = ({a} : Set α) :=
  rfl

/--
Instance `Subtype.instLawfulSingleton` / 实例 `Subtype.instLawfulSingleton`

English:
instance Subtype.instLawfulSingleton
  signature: [MeasurableSingletonClass α]
  body: ⟨fun _ => Subtype.ext insert_empty_eq _⟩

中文:
实例 子类型.instLawfulSingleton
  签名: [MeasurableSingleton类 α]
  定义体: ⟨fun _ => Subtype.ext insert_empty_eq _⟩

Depends on / 依赖: H.coe, Subtype, Subtype.ext, insert_empty_eq
-/
instance Subtype.instLawfulSingleton [MeasurableSingletonClass α] :
    LawfulSingleton α (Subtype (MeasurableSet : Set α -> Prop)) :=
⟨fun _ => Subtype.ext insert_empty_eq _⟩

/--
Instance `Subtype.instCompl` / 实例 `Subtype.instCompl`

English:
instance Subtype.instCompl
  signature: : Compl (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun x => ⟨xᶜ, x.prop.compl⟩⟩

@[simp]

中文:
实例 子类型.instCompl
  签名: : 补集 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun x => ⟨xᶜ, x.prop.compl⟩⟩

@[simp]
-/
instance Subtype.instCompl : Compl (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun x => ⟨xᶜ, x.prop.compl⟩⟩

@[simp]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: (s : Subtype (MeasurableSet : Set α -> Prop))
  statement: ↑sᶜ = (sᶜ : Set α)
  proof: rfl

中文:
定理 coe_compl
  条件: (s : 子类型 (可测集 : 集合 α -> 命题))
  结论: ↑sᶜ = (sᶜ : 集合 α)
  证明: rfl
-/
theorem coe_compl (s : Subtype (MeasurableSet : Set α -> Prop)) : ↑sᶜ = (sᶜ : Set α) :=
  rfl

/--
Instance `Subtype.instUnion` / 实例 `Subtype.instUnion`

English:
instance Subtype.instUnion
  signature: : Union (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun x y => ⟨(x : Set α) union y, x.prop.union y.prop⟩⟩

@[simp]

中文:
实例 子类型.instUnion
  签名: : 并集 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun x y => ⟨(x : Set α) union y, x.prop.union y.prop⟩⟩

@[simp]

Depends on / 依赖: x.prop.union, y.prop
-/
instance Subtype.instUnion : Union (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun x y => ⟨(x : Set α) union y, x.prop.union y.prop⟩⟩

@[simp]
/--
theorem `coe_union` / 定理 `coe_union`

English:
theorem coe_union
  given: (s t : Subtype (MeasurableSet : Set α -> Prop))
  statement: ↑(s union t) = (s union t : Set α)
  proof: rfl

中文:
定理 coe_union
  条件: (s t : 子类型 (可测集 : 集合 α -> 命题))
  结论: ↑(s union t) = (s union t : 集合 α)
  证明: rfl
-/
theorem coe_union (s t : Subtype (MeasurableSet : Set α -> Prop)) : ↑(s union t) = (s union t : Set α) :=
  rfl

/--
Instance `Subtype.instSup` / 实例 `Subtype.instSup`

English:
instance Subtype.instSup
  signature: : Max (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun x y => x union y⟩

@[simp]

中文:
实例 子类型.instSup
  签名: : 最大值 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun x y => x union y⟩

@[simp]
-/
instance Subtype.instSup : Max (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun x y => x union y⟩

@[simp]
/--
theorem `sup_eq_union` / 定理 `sup_eq_union`

English:
theorem sup_eq_union
  given: (s t : {s : Set α // MeasurableSet s})
  statement: s ⊔ t = s union t
  proof: rfl

中文:
定理 sup_eq_union
  条件: (s t : {s : 集合 α // 可测集 s})
  结论: s ⊔ t = s union t
  证明: rfl
-/
protected theorem sup_eq_union (s t : {s : Set α // MeasurableSet s}) : s ⊔ t = s union t := rfl

/--
Instance `Subtype.instInter` / 实例 `Subtype.instInter`

English:
instance Subtype.instInter
  signature: : Inter (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun x y => ⟨x inter y, x.prop.inter y.prop⟩⟩

@[simp]

中文:
实例 子类型.inst整数er
  签名: : 交集 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun x y => ⟨x inter y, x.prop.inter y.prop⟩⟩

@[simp]

Depends on / 依赖: x.prop.inter, y.prop
-/
instance Subtype.instInter : Inter (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun x y => ⟨x inter y, x.prop.inter y.prop⟩⟩

@[simp]
/--
theorem `coe_inter` / 定理 `coe_inter`

English:
theorem coe_inter
  given: (s t : Subtype (MeasurableSet : Set α -> Prop))
  statement: ↑(s inter t) = (s inter t : Set α)
  proof: rfl

中文:
定理 coe_inter
  条件: (s t : 子类型 (可测集 : 集合 α -> 命题))
  结论: ↑(s inter t) = (s inter t : 集合 α)
  证明: rfl
-/
theorem coe_inter (s t : Subtype (MeasurableSet : Set α -> Prop)) : ↑(s inter t) = (s inter t : Set α) :=
  rfl

/--
Instance `Subtype.instInf` / 实例 `Subtype.instInf`

English:
instance Subtype.instInf
  signature: : Min (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun x y => x inter y⟩

@[simp]

中文:
实例 子类型.instInf
  签名: : 最小值 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun x y => x inter y⟩

@[simp]
-/
instance Subtype.instInf : Min (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun x y => x inter y⟩

@[simp]
/--
theorem `inf_eq_inter` / 定理 `inf_eq_inter`

English:
theorem inf_eq_inter
  given: (s t : {s : Set α // MeasurableSet s})
  statement: s ⊓ t = s inter t
  proof: rfl

中文:
定理 inf_eq_inter
  条件: (s t : {s : 集合 α // 可测集 s})
  结论: s ⊓ t = s inter t
  证明: rfl

Depends on / 依赖: ofColex
-/
protected theorem inf_eq_inter (s t : {s : Set α // MeasurableSet s}) : s ⊓ t = s inter t := rfl

/--
Instance `Subtype.instSDiff` / 实例 `Subtype.instSDiff`

English:
instance Subtype.instSDiff
  signature: : SDiff (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨fun x y => ⟨x \ y, x.prop.diff y.prop⟩⟩

中文:
实例 子类型.instSDiff
  签名: : 对称差 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨fun x y => ⟨x \ y, x.prop.diff y.prop⟩⟩

Depends on / 依赖: LawfulBEq, x.prop.diff, y.prop
-/
instance Subtype.instSDiff : SDiff (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨fun x y => ⟨x \ y, x.prop.diff y.prop⟩⟩

-- TODO: Why does it complain that `x ⇨ y` is noncomputable?
/--
Instance `Subtype.instHImp` / 实例 `Subtype.instHImp`

English:
instance Subtype.instHImp
  signature: : HImp (Subtype (MeasurableSet : Set α -> Prop)) where
  body: ⟨x ⇨ y, x.prop.himp y.prop⟩

@[simp]

中文:
实例 子类型.instHImp
  签名: : HImp (子类型 (可测集 : 集合 α -> 命题)) where
  定义体: ⟨x ⇨ y, x.prop.himp y.prop⟩

@[simp]

Depends on / 依赖: DecidableEq, x.prop.himp, y.prop
-/
noncomputable instance Subtype.instHImp : HImp (Subtype (MeasurableSet : Set α -> Prop)) where
  himp x y := ⟨x ⇨ y, x.prop.himp y.prop⟩

@[simp]
/--
theorem `coe_sdiff` / 定理 `coe_sdiff`

English:
theorem coe_sdiff
  given: (s t : Subtype (MeasurableSet : Set α -> Prop))
  statement: ↑(s \ t) = (s : Set α) \ t
  proof: rfl

@[simp]

中文:
定理 coe_sdiff
  条件: (s t : 子类型 (可测集 : 集合 α -> 命题))
  结论: ↑(s \ t) = (s : 集合 α) \ t
  证明: rfl

@[simp]

Depends on / 依赖: Inhabited
-/
theorem coe_sdiff (s t : Subtype (MeasurableSet : Set α -> Prop)) : ↑(s \ t) = (s : Set α) \ t :=
  rfl

@[simp]
/--
lemma `coe_himp` / 引理 `coe_himp`

English:
lemma coe_himp
  given: (s t : Subtype (MeasurableSet : Set α -> Prop))
  statement: ↑(s ⇨ t) = (s ⇨ t : Set α)
  proof: rfl

中文:
引理 coe_himp
  条件: (s t : 子类型 (可测集 : 集合 α -> 命题))
  结论: ↑(s ⇨ t) = (s ⇨ t : 集合 α)
  证明: rfl

Depends on / 依赖: Nonempty
-/
lemma coe_himp (s t : Subtype (MeasurableSet : Set α -> Prop)) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl

/--
Instance `Subtype.instBot` / 实例 `Subtype.instBot`

English:
instance Subtype.instBot
  signature: : Bot (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨∅⟩

@[simp]

中文:
实例 子类型.instBot
  签名: : 底元素 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨∅⟩

@[simp]

Depends on / 依赖: Nontrivial
-/
instance Subtype.instBot : Bot (Subtype (MeasurableSet : Set α -> Prop)) := ⟨∅⟩

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ↑(⊥ : Subtype (MeasurableSet : Set α -> Prop)) = (⊥ : Set α)
  proof: rfl

@[simp]

中文:
定理 coe_bot
  结论: ↑(⊥ : 子类型 (可测集 : 集合 α -> 命题)) = (⊥ : 集合 α)
  证明: rfl

@[simp]

Depends on / 依赖: Unique
-/
theorem coe_bot : ↑(⊥ : Subtype (MeasurableSet : Set α -> Prop)) = (⊥ : Set α) :=
  rfl

@[simp]
/--
theorem `subtype_bot_eq` / 定理 `subtype_bot_eq`

English:
theorem subtype_bot_eq
  statement: (⟨∅, .empty⟩ : Subtype (MeasurableSet : Set α -> Prop)) = ⊥
  proof: rfl

中文:
定理 subtype_bot_eq
  结论: (⟨∅, .empty⟩ : 子类型 (可测集 : 集合 α -> 命题)) = ⊥
  证明: rfl

Depends on / 依赖: H.coe, ofColex
-/
theorem subtype_bot_eq : (⟨∅, .empty⟩ : Subtype (MeasurableSet : Set α -> Prop)) = ⊥ :=
  rfl

/--
Instance `Subtype.instTop` / 实例 `Subtype.instTop`

English:
instance Subtype.instTop
  signature: : Top (Subtype (MeasurableSet : Set α -> Prop))
  body: ⟨⟨Set.univ, MeasurableSet.univ⟩⟩

@[simp]

中文:
实例 子类型.instTop
  签名: : 顶元素 (子类型 (可测集 : 集合 α -> 命题))
  定义体: ⟨⟨Set.univ, MeasurableSet.univ⟩⟩

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.univ
-/
instance Subtype.instTop : Top (Subtype (MeasurableSet : Set α -> Prop)) :=
  ⟨⟨Set.univ, MeasurableSet.univ⟩⟩

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ↑(⊤ : Subtype (MeasurableSet : Set α -> Prop)) = (⊤ : Set α)
  proof: rfl

中文:
定理 coe_top
  结论: ↑(⊤ : 子类型 (可测集 : 集合 α -> 命题)) = (⊤ : 集合 α)
  证明: rfl
-/
theorem coe_top : ↑(⊤ : Subtype (MeasurableSet : Set α -> Prop)) = (⊤ : Set α) :=
  rfl

/--
Instance `Subtype.instBooleanAlgebra` / 实例 `Subtype.instBooleanAlgebra`

English:
instance Subtype.instBooleanAlgebra
  signature: :
  body: Subtype.coe_injective.booleanAlgebra _ .rfl .rfl coe_union coe_inter coe_top coe_bot coe_compl
    coe_sdiff coe_himp

@[measurability]

中文:
实例 子类型.inst布尔eanAlgebra
  签名: :
  定义体: Subtype.coe_injective.booleanAlgebra _ .rfl .rfl coe_union coe_inter coe_top coe_bot coe_compl
    coe_sdiff coe_himp

@[measurability]

Depends on / 依赖: Subtype, Subtype.coe_injective.booleanAlgebra, booleanAlgebra, coe_bot, coe_compl, coe_himp, coe_injective, coe_inter, coe_sdiff, coe_top, coe_union
-/
noncomputable instance Subtype.instBooleanAlgebra :
    BooleanAlgebra (Subtype (MeasurableSet : Set α -> Prop)) :=
  Subtype.coe_injective.booleanAlgebra _ .rfl .rfl coe_union coe_inter coe_top coe_bot coe_compl
    coe_sdiff coe_himp

@[measurability]
/--
theorem `measurableSet_blimsup` / 定理 `measurableSet_blimsup`

English:
theorem measurableSet_blimsup
  given: {s : Nat -> Set α} {p : Nat -> Prop} (h : forall n, p n -> MeasurableSet (s n))
  proof: by
  simp only [blimsup_eq_iInf_biSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter]
  exact .iInter fun _ => .iUnion fun m => .iUnion fun hm => h m hm.1

@[measurability]

中文:
定理 measurableSet_blimsup
  条件: {s : 自然数 -> 集合 α} {p : 自然数 -> 命题} (h : 对任意 n, p n -> 可测集 (s n))
  证明: by
  simp only [blimsup_eq_iInf_biSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter]
  exact .iInter fun _ => .iUnion fun m => .iUnion fun hm => h m hm.1

@[measurability]

Depends on / 依赖: blimsup_eq_iInf_biSup_of_nat, iInf_eq_iInter, iInter, iSup_eq_iUnion, iUnion
-/
theorem measurableSet_blimsup {s : Nat -> Set α} {p : Nat -> Prop} (h : forall n, p n -> MeasurableSet (s n)) :
MeasurableSet blimsup s atTop p := by
  simp only [blimsup_eq_iInf_biSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter]
  exact .iInter fun _ => .iUnion fun m => .iUnion fun hm => h m hm.1

@[measurability]
/--
theorem `measurableSet_bliminf` / 定理 `measurableSet_bliminf`

English:
theorem measurableSet_bliminf
  given: {s : Nat -> Set α} {p : Nat -> Prop} (h : forall n, p n -> MeasurableSet (s n))
  proof: by
  simp only [Filter.bliminf_eq_iSup_biInf_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
  exact .iUnion fun n => .iInter fun m => .iInter fun hm => h m hm.1

@[measurability]

中文:
定理 measurableSet_bliminf
  条件: {s : 自然数 -> 集合 α} {p : 自然数 -> 命题} (h : 对任意 n, p n -> 可测集 (s n))
  证明: by
  simp only [Filter.bliminf_eq_iSup_biInf_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
  exact .iUnion fun n => .iInter fun m => .iInter fun hm => h m hm.1

@[measurability]

Depends on / 依赖: Filter, Filter.bliminf_eq_iSup_biInf_of_nat, bliminf_eq_iSup_biInf_of_nat, iInf_eq_iInter, iInter, iSup_eq_iUnion, iUnion
-/
theorem measurableSet_bliminf {s : Nat -> Set α} {p : Nat -> Prop} (h : forall n, p n -> MeasurableSet (s n)) :
MeasurableSet Filter.bliminf s Filter.atTop p := by
  simp only [Filter.bliminf_eq_iSup_biInf_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
  exact .iUnion fun n => .iInter fun m => .iInter fun hm => h m hm.1

@[measurability]
/--
theorem `measurableSet_limsup` / 定理 `measurableSet_limsup`

English:
theorem measurableSet_limsup
  given: {s : Nat -> Set α} (hs : forall n, MeasurableSet <| s n)
  proof: by
  simpa only [← blimsup_true] using measurableSet_blimsup fun n _ => hs n

@[measurability]

中文:
定理 measurableSet_limsup
  条件: {s : 自然数 -> 集合 α} (hs : 对任意 n, 可测集 <| s n)
  证明: by
  simpa only [← blimsup_true] using measurableSet_blimsup fun n _ => hs n

@[measurability]

Depends on / 依赖: blimsup_true, measurableSet_blimsup
-/
theorem measurableSet_limsup {s : Nat -> Set α} (hs : forall n, MeasurableSet <| s n) :
MeasurableSet Filter.limsup s Filter.atTop := by
  simpa only [← blimsup_true] using measurableSet_blimsup fun n _ => hs n

@[measurability]
/--
theorem `measurableSet_liminf` / 定理 `measurableSet_liminf`

English:
theorem measurableSet_liminf
  given: {s : Nat -> Set α} (hs : forall n, MeasurableSet <| s n)
  proof: by
  simpa only [← bliminf_true] using measurableSet_bliminf fun n _ => hs n

中文:
定理 measurableSet_liminf
  条件: {s : 自然数 -> 集合 α} (hs : 对任意 n, 可测集 <| s n)
  证明: by
  simpa only [← bliminf_true] using measurableSet_bliminf fun n _ => hs n

Depends on / 依赖: bliminf_true, measurableSet_bliminf
-/
theorem measurableSet_liminf {s : Nat -> Set α} (hs : forall n, MeasurableSet <| s n) :
MeasurableSet Filter.liminf s Filter.atTop := by
  simpa only [← bliminf_true] using measurableSet_bliminf fun n _ => hs n

end MeasurableSet
