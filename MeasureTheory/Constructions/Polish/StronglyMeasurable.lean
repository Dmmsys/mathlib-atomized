/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Results about strongly measurable functions

In measure theory it is often assumed that some space is a `PolishSpace`, i.e. a separable and
completely metrizable topological space, because it ensures a nice interaction between the topology
and the measurable space structure. Moreover a strongly measurable function whose codomain is a
metric space is measurable and has a separable range
(see `stronglyMeasurable_iff_measurable_separable`). Therefore if the codomain is also complete,
by corestricting the function to the closure of its range, some results about measurable functions
can be extended to strongly measurable functions without assuming separability on the codomain.
The purpose of this file is to collect those results.
-/

public section

open Filter MeasureTheory Set TopologicalSpace

open scoped Topology

variable {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [Countable ι] {l : Filter ι}
  [l.IsCountablyGenerated] {f : ι → X → E}

namespace MeasureTheory.StronglyMeasurable

/-
**MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：measurableSet_exists_tendsto [IsCompletelyPseudoMetrizableSpace E] (hf : f
orall i, StronglyMeasurable (f i)) : MeasurableSet {x | exists c, Tendsto (f · x
) l (𝓝 c)}
参数：hf : forall i, StronglyMeasurable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsCountablyGeneratedProdElemUniformity`：∀ {α : Type ua} [inst : Unif
ormSpace α] [(uniformity α).IsCountablyGenerated] (s : Set α),   (uniformity ↑s)
.IsCountablyGenerated
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.IsSeparable.separableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X},   Topo
logicalSpace.IsSeparable s → Topo…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用定理 `TopologicalSpace.IsSeparable.iUnion`：∀ {α : Type u} [t : TopologicalSpac
e α] {ι : Sort u_2} [Countable ι] {s : ι → Set α},   (∀ (i : ι), TopologicalSpac
e.IsSeparable (s i)) → To…
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用定理 `IsClosed.isCompletelyPseudoMetrizableSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X] {s : Set
 X},   IsClosed s → TopologicalS…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measurableSet_exists_tendsto`：MeasureTheory.measurableSet_
exists_tendsto [TopologicalSpace γ] [IsCompletelyPseudoMetrizableSpace γ] [Secon
dCountableTopology γ] [Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem measurableSet_exists_tendsto [IsCompletelyPseudoMetrizableSpace E]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    MeasurableSet {x | ∃ c, Tendsto (f · x) l (𝓝 c)} := by
  obtain rfl | hl := eq_or_neBot l
  · simp_all
  borelize E
  let := upgradeIsCompletelyPseudoMetrizable E
  let s := closure (⋃ i, range (f i))
  have : SecondCountableTopology s := @UniformSpace.secondCountable_of_separable s _ _
    (IsSeparable.iUnion (fun i ↦ (hf i).isSeparable_range)).closure.separableSpace
  have : IsCompletelyPseudoMetrizableSpace s := isClosed_closure.isCompletelyPseudoMetrizableSpace
  let g i x : s := ⟨f i x, subset_closure <| mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩⟩
  have mg i : Measurable (g i) := (hf i).measurable.subtype_mk
  convert! MeasureTheory.measurableSet_exists_tendsto (l := l) mg with x
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨⟨c, ?_⟩, tendsto_subtype_rng.2 hc⟩,
    fun ⟨c, hc⟩ ↦ ⟨c, tendsto_subtype_rng.1 hc⟩⟩
  exact mem_closure_of_tendsto hc (Eventually.of_forall fun i ↦ mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)
/-
**MeasureTheory.StronglyMeasurable.limUnder** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.StronglyMeasurable`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} {E : Type u_3} [inst : MeasurableSpace X] 
[inst_1 : TopologicalSpace E] [Countable ι]   {l : Filter ι} [l.IsCountablyGener
ated] {f : ι → X → E} [hE : Nonempty E]   [TopologicalSpace.IsCompletelyMetrizab
leSpace E],   (∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)) →     MeasureT
heory.StronglyMeasurable fun x => l.limUnder fun x_1 => f x_1 x
参数：∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.lim.congr_simp`：∀ {X : Type u_1} [inst : TopologicalSpace X] [ins
t_1 : Nonempty X] (f f_1 : Filter X), f = f_1 → f.lim = f_1.lim
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto`：measurabl
eSet_exists_tendsto [IsCompletelyPseudoMetrizableSpace E] (hf : forall i, Strong
lyMeasurable (f i)) : MeasurableSet {x | exists c, …
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.MetrizableSpace`：∀ {X : Typ
e u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace
 X],   TopologicalSpace.MetrizableSpace X
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Function.extend_val_apply`：∀ {β : Sort u_2} {γ : Sort u_3} {p : β → Prop
} {g : { x // p x } → γ} {j : β → γ} {b : β} (hb : p b),   Function.extend Subty
pe.val g j b = …
· 使用定理 `Function.extend_val_apply'`：∀ {β : Sort u_2} {γ : Sort u_3} {p : β → Pro
p} {g : { x // p x } → γ} {j : β → γ} {b : β},   ¬p b → Function.extend Subtype.
val g j b = j b
· 使用定理 `limUnder_of_not_tendsto`：limUnder_of_not_tendsto [hX : Nonempty X] {f : 
Filter α} {g : α -> X} (h : ¬ exists x, Tendsto g f (𝓝 x)) : limUnder f g = Clas
sical.choice …
· 使用定理 `MeasurableEmbedding.stronglyMeasurable_extend`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {f : α → β} {g : α → γ} {g' : γ → β} {mα : MeasurableSpace
 α}   {mγ : MeasurableSpace γ} [ins…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
-/
protected theorem limUnder [hE : Nonempty E] [IsCompletelyMetrizableSpace E]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simpa [limUnder, Filter.map_bot] using stronglyMeasurable_const
  let e := Classical.choice hE
  let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
  have hconv : StronglyMeasurable (fun x : conv ↦ limUnder l (f · x)) := by
    refine stronglyMeasurable_of_tendsto l
      (fun i ↦ (hf i).comp_measurable measurable_subtype_coe) ?_
    refine tendsto_pi_nhds.2 fun x ↦ ?_
    obtain ⟨c, hc⟩ := x.2
    rwa [hc.limUnder_eq]
  have : (fun x ↦ limUnder l (f · x)) = ((↑) : conv → X).extend
      (fun x ↦ limUnder l (f · x)) (fun _ ↦ e) := by
    ext x
    by_cases hx : x ∈ conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  exact (MeasurableEmbedding.subtype_coe mconv).stronglyMeasurable_extend hconv
    stronglyMeasurable_const

end MeasureTheory.StronglyMeasurable

namespace MeasureTheory

variable {X E ι : Type*} [MeasurableSpace X] [CommMonoid E] [TopologicalSpace E]

section

variable [ContinuousMul E] {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The infinite product of strongly measurable functions is measurable, `HasProd` version. -/
@[to_additive (attr := fun_prop)
/-- The infinite sum of strongly measurable functions is measurable, `HasSum` version. -/]
/-
**MeasureTheory.StronglyMeasurable.hasProd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.StronglyMeasurable`。
形式化陈述：∀ {X : Type u_4} {E : Type u_5} {ι : Type u_6} [inst : MeasurableSpace X] 
[inst_1 : CommMonoid E]   [inst_2 : TopologicalSpace E] [ContinuousMul E] {L : S
ummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]   [TopologicalSpace.
PseudoMetrizableSpace E] {f : ι → X → E} {g : X → E},   (∀ (i : ι), MeasureTheor
y.StronglyMeasurable (f i)) →     (∀ (x : X), HasProd (fun i => f i x) (g x) L) 
→ MeasureTheory.StronglyMeasurable g
参数：∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；∀ (x : X), HasProd (fun i =
> f i x) (g x) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Finset.stronglyMeasurable_fun_prod`：∀ {α : Type u_1} {M : Type u_5} [ins
t : CommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousMul M]   {m : Measura
bleSpace α} {ι : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
-/
theorem StronglyMeasurable.hasProd [PseudoMetrizableSpace E] {f : ι → X → E} {g : X → E}
    (h : ∀ i : ι, StronglyMeasurable (f i)) (h' : ∀ x, HasProd (fun i ↦ f i x) (g x) L) :
    StronglyMeasurable g := by
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr h')
  fun_prop

variable [IsCompletelyPseudoMetrizableSpace E] [Countable ι]

/-- The infinite product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The infinite sum of strongly measurable functions is measurable. -/]
/-
**MeasureTheory.StronglyMeasurable.tprod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.StronglyMeasurable`。
形式化陈述：∀ {X : Type u_4} {E : Type u_5} {ι : Type u_6} [inst : MeasurableSpace X] 
[inst_1 : CommMonoid E]   [inst_2 : TopologicalSpace E] [ContinuousMul E] {L : S
ummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]   [TopologicalSpace.
IsCompletelyPseudoMetrizableSpace E] [Countable ι] {f : ι → X → E},   (∀ (i : ι)
, MeasureTheory.StronglyMeasurable (f i)) → MeasureTheory.StronglyMeasurable fun
 x => ∏'[L] (i : ι), f i x
参数：∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto`：measurabl
eSet_exists_tendsto [IsCompletelyPseudoMetrizableSpace E] (hf : forall i, Strong
lyMeasurable (f i)) : MeasurableSet {x | exists c, …
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `Finset.stronglyMeasurable_fun_prod`：∀ {α : Type u_1} {M : Type u_5} [ins
t : CommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousMul M]   {m : Measura
bleSpace α} {ι : Type u_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `stronglyMeasurable_of_restrict_of_restrict_compl`：∀ {α : Type u_1} {β : 
Type u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] {f : α → β} {s : S
et α},   MeasurableSet s →     Measure…
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.subtype_coe`：Measurable.subtype_coe {p : β -> Prop} {f : α ->
 Subtype p} (hf : Measurable f) : Measurable fun a : α => (f a : β)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem StronglyMeasurable.tprod {f : ι → X → E} (h : ∀ i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x => ∏'[L] i : ι, f i x) := by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := StronglyMeasurable.measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine stronglyMeasurable_of_restrict_of_restrict_compl hE ?_ (h0 ▸ stronglyMeasurable_const)
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr fun e => e.2.hasProd)
  fun_prop

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
/-
**MeasureTheory.AEStronglyMeasurable.tprod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEStronglyMeasurable`。
形式化陈述：∀ {X : Type u_4} {E : Type u_5} {ι : Type u_6} [inst : MeasurableSpace X] 
[inst_1 : CommMonoid E]   [inst_2 : TopologicalSpace E] [ContinuousMul E] {L : S
ummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]   [TopologicalSpace.
IsCompletelyPseudoMetrizableSpace E] [Countable ι] {μ : MeasureTheory.Measure X}
 {f : ι → X → E},   (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ) →   
  MeasureTheory.AEStronglyMeasurable (fun x => ∏'[L] (i : ι), f i x) μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ；fun x => ∏'[L] (i : ι),
 f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.tprod`：∀ {X : Type u_4} {E : Type u_5} 
{ι : Type u_6} [inst : MeasurableSpace X] [inst_1 : CommMonoid E]   [inst_2 : To
pologicalSpace E] [Continuou…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tprod_congr`：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'
[L] b, f b = ∏'[L] b, g b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem AEStronglyMeasurable.tprod {μ : MeasureTheory.Measure X} {f : ι → X → E}
    (h : ∀ i : ι, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∏'[L] i : ι, f i x) μ := by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), StronglyMeasurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

end

section

variable [PseudoMetrizableSpace E] [ContinuousMul E]
  {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of strongly measurable functions is measurable. -/]
/-
**MeasureTheory.StronglyMeasurable.tprod'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.StronglyMeasurable`。
形式化陈述：∀ {X : Type u_4} {E : Type u_5} {ι : Type u_6} [inst : MeasurableSpace X] 
[inst_1 : CommMonoid E]   [inst_2 : TopologicalSpace E] [TopologicalSpace.Pseudo
MetrizableSpace E] [ContinuousMul E] {L : SummationFilter ι}   [L.NeBot] [L.filt
er.IsCountablyGenerated] {f : ι → X → E},   (∀ (i : ι), MeasureTheory.StronglyMe
asurable (f i)) → MeasureTheory.StronglyMeasurable (∏'[L] (i : ι), f i)
参数：∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；∏'[L] (i : ι), f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.stronglyMeasurable_prod`：∀ {α : Type u_1} {M : Type u_5} [inst : 
CommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousMul M]   {m : MeasurableS
pace α} {ι : Type u_…
· 使用定理 `Set.mulIndicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : One M] (s
 : Set α) (f : α → M) (x : α),   s.mulIndicator f x = if x ∈ s then f x else 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.stronglyMeasurable_one`：stronglyMeasurable_one [One β] : S
tronglyMeasurable (1 : α -> β)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem StronglyMeasurable.tprod' {f : ι → X → E} (h : ∀ i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (∏'[L] i : ι, f i) := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact stronglyMeasurable_one
  · refine Finset.stronglyMeasurable_prod _ (fun _ _ ↦ ?_)
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (by fun_prop) hm.choose_spec

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
/-
**MeasureTheory.AEStronglyMeasurable.tprod'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEStronglyMeasurable`。
形式化陈述：∀ {X : Type u_4} {E : Type u_5} {ι : Type u_6} [inst : MeasurableSpace X] 
[inst_1 : CommMonoid E]   [inst_2 : TopologicalSpace E] [TopologicalSpace.Pseudo
MetrizableSpace E] [ContinuousMul E] {L : SummationFilter ι}   [L.NeBot] [L.filt
er.IsCountablyGenerated] {μ : MeasureTheory.Measure X} {f : ι → X → E},   (∀ (i 
: ι), MeasureTheory.AEStronglyMeasurable (f i) μ) → MeasureTheory.AEStronglyMeas
urable (∏'[L] (i : ι), f i) μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ；∏'[L] (i : ι), f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.aestronglyMeasurable_prod`：∀ {α : Type u_1} {m₀ : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {M : Type u_5} [inst : CommMonoid M]   [inst_1
 : TopologicalSpace M]…
· 使用定理 `Set.mulIndicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : One M] (s
 : Set α) (f : α → M) (x : α),   s.mulIndicator f x = if x ∈ s then f x else 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.aestronglyMeasurable_one`：aestronglyMeasurable_one [One β]
 : AEStronglyMeasurable[m] (1 : α -> β) μ
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem AEStronglyMeasurable.tprod' {μ : MeasureTheory.Measure X} {f : ι → X → E}
    (h : ∀ i : ι, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏'[L] i : ι, f i) μ := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact aestronglyMeasurable_one
  · refine Finset.aestronglyMeasurable_prod _ (fun _ _ ↦ ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aestronglyMeasurable_of_tendsto_ae L.filter (f := fun s => ∏ i ∈ s, f i) (by fun_prop)
    exact .of_forall fun x ↦ hm.choose_spec.apply_nhds x

end

end MeasureTheory

