/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `Topology.UniformSpace.Completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/

@[expose] public section

open Set Filter UniformSpace Metric

open Filter Topology Uniformity

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [PseudoMetricSpace α]

namespace UniformSpace.Completion

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance on the completion is obtained by extending the distance on the orig
inal space,
by uniform continuity.
-/
instance : Dist (Completion α) :=
  ⟨Completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
/-
**UniformSpace.Completion.uniformContinuous_dist** 是 Mathlib 中的一个定理，位于命名空间 `Unif
ormSpace.Completion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α], UniformContinuous fun p => di
st p.1 p.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.uniformContinuous_extension₂`：uniformContinuous_
extension₂ : UniformContinuous₂ (Completion.extension₂ f)

--- 原说明 ---
The new distance is uniformly continuous.
-/
protected theorem uniformContinuous_dist :
    UniformContinuous fun p : Completion α × Completion α ↦ dist p.1 p.2 :=
  uniformContinuous_extension₂ dist

/-- The new distance is continuous. -/
/-
**UniformSpace.Completion.continuous_dist** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpac
e.Completion`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [inst_1 : Topolog
icalSpace β]   {f g : β → UniformSpace.Completion α}, Continuous f → Continuous 
g → Continuous fun x => dist (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformSpace.Completion.uniformContinuous_dist`：∀ {α : Type u} [inst : P
seudoMetricSpace α], UniformContinuous fun p => dist p.1 p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)

--- 原说明 ---
The new distance is continuous.
-/
protected theorem continuous_dist [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ dist (f x) (g x) :=
  Completion.uniformContinuous_dist.continuous.comp (hf.prodMk hg :)

/-- The new distance is an extension of the original distance. -/
@[simp]
/-
**UniformSpace.Completion.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (x y : α), dist ↑x ↑y = dist x
 y
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.extension₂_coe_coe`：extension₂_coe_coe (hf : Uni
formContinuous₂ f) (a : α) (b : β) : Completion.extension₂ f a b = f a b
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `uniformContinuous_dist`：uniformContinuous_dist : UniformContinuous fun p
 : α × α => dist p.1 p.2

--- 原说明 ---
The new distance is an extension of the original distance.
-/
protected theorem dist_eq (x y : α) : dist (x : Completion α) y = dist x y :=
  Completion.extension₂_coe_coe uniformContinuous_dist _ _

/-! Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `Completion α` by continuity. -/

/-
**UniformSpace.Completion.dist_self** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comp
letion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : UniformSpace.Completion α
), dist x x = 0
参数：x : UniformSpace.Completion α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `UniformSpace.Completion.continuous_dist`：∀ {α : Type u} {β : Type v} [in
st : PseudoMetricSpace α] [inst_1 : TopologicalSpace β]   {f g : β → UniformSpac
e.Completion α}, Continuous f…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0

--- 原说明 ---
Let us check that the new distance satisfies the axioms of a distance, by starti
ng from the
properties on α and extending them to `Completion α` by continuity.
-/
protected theorem dist_self (x : Completion α) : dist x x = 0 := by
  refine induction_on x ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    exact Completion.continuous_dist continuous_id continuous_id
  · intro a
    rw [Completion.dist_eq, dist_self]
/-
**UniformSpace.Completion.dist_comm** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comp
letion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (x y : UniformSpace.Completion
 α), dist x y = dist y x
参数：x y : UniformSpace.Completion α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.induction_on₂`：induction_on₂ {p : Completion α -
> Completion β -> Prop} (a : Completion α) (b : Completion β) (hp : IsClosed { x
 : Completion α × Completio…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `UniformSpace.Completion.continuous_dist`：∀ {α : Type u} {β : Type v} [in
st : PseudoMetricSpace α] [inst_1 : TopologicalSpace β]   {f g : β → UniformSpac
e.Completion α}, Continuous f…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
protected theorem dist_comm (x y : Completion α) : dist x y = dist y x := by
  refine induction_on₂ x y ?_ ?_
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    rw [Completion.dist_eq, Completion.dist_eq, dist_comm]
/-
**UniformSpace.Completion.dist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.
Completion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (x y z : UniformSpace.Completi
on α), dist x z ≤ dist x y + dist y z
参数：x y z : UniformSpace.Completion α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.induction_on₃`：induction_on₃ {p : Completion α -
> Completion β -> Completion γ -> Prop} (a : Completion α) (b : Completion β) (c
 : Completion γ) (hp : IsCl…
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.Completion.continuous_dist`：∀ {α : Type u} {β : Type v} [in
st : PseudoMetricSpace α] [inst_1 : TopologicalSpace β]   {f g : β → UniformSpac
e.Completion α}, Continuous f…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
-/
protected theorem dist_triangle (x y z : Completion α) : dist x z ≤ dist x y + dist y z := by
  refine induction_on₃ x y z ?_ ?_
  · refine isClosed_le ?_ (Continuous.add ?_ ?_) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
  · intro a b c
    rw [Completion.dist_eq, Completion.dist_eq, Completion.dist_eq]
    exact dist_triangle a b c

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
/-
**UniformSpace.Completion.mem_uniformity_dist** 是 Mathlib 中的一个定理，位于命名空间 `Uniform
Space.Completion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set (UniformSpace.Complet
ion α × UniformSpace.Completion α)),   s ∈ uniformity (UniformSpace.Completion α
) ↔ ∃ ε > 0, ∀ {a b : UniformSpace.Completion α}, dist a b < ε → (a, b) ∈ s
参数：s : Set (UniformSpace.Completion α × UniformSpace.Completion α)；UniformSpace.
Completion α；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_uniformity_isClosed`：mem_uniformity_isClosed {s : SetRel α α} (h : s
 in 𝓤 α) : exists t in 𝓤 α, IsClosed t ∧ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_def`：uniformContinuous_def {f : α -> β} : UniformConti
nuous f ↔ forall r in 𝓤 β, { x : α × α | (f x.1, f x.2) in r } in 𝓤 α
· 使用定理 `UniformSpace.Completion.uniformContinuous_coe`：uniformContinuous_coe : U
niformContinuous ((↑) : α -> Completion α)
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s
· 使用定理 `UniformSpace.Completion.induction_on₂`：induction_on₂ {p : Completion α -
> Completion β -> Prop} (a : Completion α) (b : Completion β) (hp : IsClosed { x
 : Completion α × Completio…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformSpace.Completion.uniformContinuous_dist`：∀ {α : Type u} [inst : P
seudoMetricSpace α], UniformContinuous fun p => dist p.1 p.2
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `uniformity_prod_eq_prod`：uniformity_prod_eq_prod [UniformSpace α] [Unifo
rmSpace β] : 𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2
, p.2.2))) (𝓤…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Elements of the uniformity (defined generally for completions) can be characteri
zed in terms
of the distance.
-/
protected theorem mem_uniformity_dist (s : Set (Completion α × Completion α)) :
    s ∈ 𝓤 (Completion α) ↔ ∃ ε > 0, ∀ {a b}, dist a b < ε → (a, b) ∈ s := by
  constructor
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
      entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
      in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `Completion α`, as
      closed properties pass to the completion. -/
    intro hs
    rcases mem_uniformity_isClosed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩
    have A : { x : α × α | (↑x.1, ↑x.2) ∈ t } ∈ uniformity α :=
      uniformContinuous_def.1 (uniformContinuous_coe α) t ht
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩
    refine ⟨ε, εpos, @fun x y hxy ↦ ?_⟩
    have : ε ≤ dist x y ∨ (x, y) ∈ t := by
      refine induction_on₂ x y ?_ ?_
      · have : { x : Completion α × Completion α | ε ≤ dist x.fst x.snd ∨ (x.fst, x.snd) ∈ t } =
               { p : Completion α × Completion α | ε ≤ dist p.1 p.2 } ∪ t := by ext; simp
        rw [this]
        apply IsClosed.union _ tclosed
        exact isClosed_le continuous_const Completion.uniformContinuous_dist.continuous
      · intro x y
        rw [Completion.dist_eq]
        by_cases! h : ε ≤ dist x y
        · exact Or.inl h
        · have Z := hε h
          simp only [Set.mem_ofPred_eq] at Z
          exact Or.inr Z
    simp only [not_le.mpr hxy, false_or] at this
    exact ts this
  · /- Start from a set `s` containing an ε-neighborhood of the diagonal in `Completion α`. To show
        that it is an entourage, we use the fact that `dist` is uniformly continuous on
        `Completion α × Completion α` (this is a general property of the extension of uniformly
        continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
        is an entourage in `Completion α × Completion α`. Massaging this property, it follows that
        the ε-neighborhood of the diagonal is an entourage in `Completion α`, and therefore this is
        also the case of `s`. -/
    rintro ⟨ε, εpos, hε⟩
    let r : Set (ℝ × ℝ) := { p | dist p.1 p.2 < ε }
    have : r ∈ uniformity ℝ := Metric.dist_mem_uniformity εpos
    have T := uniformContinuous_def.1 (@Completion.uniformContinuous_dist α _) r this
    simp only [uniformity_prod_eq_prod, mem_prod_iff, Filter.mem_map] at T
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩
    refine mem_of_superset ht1 ?_
    have A : ∀ a b : Completion α, (a, b) ∈ t1 → dist a b < ε := by
      intro a b hab
      have : ((a, b), (a, a)) ∈ t1 ×ˢ t2 := ⟨hab, refl_mem_uniformity ht2⟩
      exact lt_of_le_of_lt (le_abs_self _)
        (by simpa [r, Completion.dist_self, Real.dist_eq, Completion.dist_comm] using ht this)
    grind

/-- Reformulate `Completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
/-
**UniformSpace.Completion.uniformity_dist'** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpa
ce.Completion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α],   uniformity (UniformSpace.Co
mpletion α) = ⨅ ε, Filter.principal {p | dist p.1 p.2 < ↑ε}
参数：UniformSpace.Completion α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `nonempty_gt`：∀ {α : Type u_1} [inst : LT α] [NoMaxOrder α] (a : α), None
mpty { x // a < x }
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Reformulate `Completion.mem_uniformity_dist` in terms that are suitable for the 
definition
of the metric space structure.
-/
protected theorem uniformity_dist' :
    𝓤 (Completion α) = ⨅ ε : { ε : ℝ // 0 < ε }, 𝓟 { p | dist p.1 p.2 < ε.val } := by
  ext s; rw [mem_iInf_of_directed]
  · simp [Completion.mem_uniformity_dist, subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_min hr hp⟩
    simp +contextual
/-
**UniformSpace.Completion.uniformity_dist** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpac
e.Completion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α],   uniformity (UniformSpace.Co
mpletion α) = ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | dist p.1 p.2 < ε}
参数：UniformSpace.Completion α；_ : ε > 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `UniformSpace.Completion.uniformity_dist'`：∀ {α : Type u} [inst : PseudoM
etricSpace α],   uniformity (UniformSpace.Completion α) = ⨅ ε, Filter.principal 
{p | dist p.1 p.2 < ↑ε}
-/
protected theorem uniformity_dist : 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε } := by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _

/-- Metric space structure on the completion of a `PseudoMetric` space. -/
/-
**UniformSpace.Completion.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpac
e.Completion`。
形式化陈述：instMetricSpace : MetricSpace (Completion α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.dist_self`：∀ {α : Type u} [inst : PseudoMetricSp
ace α] (x : UniformSpace.Completion α), dist x x = 0
· 使用定理 `UniformSpace.Completion.dist_comm`：∀ {α : Type u} [inst : PseudoMetricSp
ace α] (x y : UniformSpace.Completion α), dist x y = dist y x
· 使用定理 `UniformSpace.Completion.dist_triangle`：∀ {α : Type u} [inst : PseudoMetr
icSpace α] (x y z : UniformSpace.Completion α), dist x z ≤ dist x y + dist y z
· 使用定理 `UniformSpace.Completion.uniformity_dist`：∀ {α : Type u} [inst : PseudoMe
tricSpace α],   uniformity (UniformSpace.Completion α) = ⨅ ε, ⨅ (_ : ε > 0), Fil
ter.principal {p | dist p.1 p…

--- 原说明 ---
Metric space structure on the completion of a `PseudoMetric` space.
-/
instance instMetricSpace : MetricSpace (Completion α) :=
  @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _

/-- The embedding of a metric space in its completion is an isometry. -/
/-
**UniformSpace.Completion.coe_isometry** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.C
ompletion`。
形式化陈述：coe_isometry : Isometry ((↑) : α -> Completion α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y

--- 原说明 ---
The embedding of a metric space in its completion is an isometry.
-/
theorem coe_isometry : Isometry ((↑) : α → Completion α) :=
  Isometry.of_dist_eq Completion.dist_eq

@[simp]
/-
**UniformSpace.Completion.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (x y : α), edist ↑x ↑y = edist
 x y
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.coe_isometry`：coe_isometry : Isometry ((↑) : α -
> Completion α)
-/
protected theorem edist_eq (x y : α) : edist (x : Completion α) y = edist x y :=
  coe_isometry x y
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M} [Zero M] [Zero α] [SMul M α] [PseudoMetricSpace M] [IsBoundedSMul M α] :
    IsBoundedSMul M (Completion α) where
  dist_smul_pair' c x₁ x₂ := by
    induction x₁, x₂ using induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x₁ x₂ =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq, Completion.dist_eq]
      exact dist_smul_pair c x₁ x₂
  dist_pair_smul' c₁ c₂ x := by
    induction x using induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq, ← coe_zero, Completion.dist_eq]
      exact dist_pair_smul c₁ c₂ x

end UniformSpace.Completion

open UniformSpace Completion NNReal

/-
**LipschitzWith.completion_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.completion_extension [MetricSpace β] [CompleteSpace β] {f : 
α -> β} {K : Real>=0} (h : LipschitzWith K f) : LipschitzWith K (Completion.exte
nsion f)
参数：h : LipschitzWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `UniformSpace.Completion.induction_on₂`：induction_on₂ {p : Completion α -
> Completion β -> Prop} (a : Completion α) (b : Completion β) (hp : IsClosed { x
 : Completion α × Completio…
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `UniformSpace.Completion.continuous_extension`：continuous_extension : Con
tinuous (Completion.extension f)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `MetricSpace.instT0Space`：∀ {γ : Type w} [inst : MetricSpace γ], T0Space 
γ
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
-/
theorem LipschitzWith.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    {K : ℝ≥0} (h : LipschitzWith K f) : LipschitzWith K (Completion.extension f) :=
  LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
    (isClosed_le (by fun_prop) (by fun_prop)) <| by
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul
/-
**LipschitzWith.completion_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.completion_map [PseudoMetricSpace β] {f : α -> β} {K : Real>
=0} (h : LipschitzWith K f) : LipschitzWith K (Completion.map f)
参数：h : LipschitzWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.completion_extension`：LipschitzWith.completion_extension [
MetricSpace β] [CompleteSpace β] {f : α -> β} {K : Real>=0} (h : LipschitzWith K
 f) : LipschitzWith K (C…
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `UniformSpace.Completion.coe_isometry`：coe_isometry : Isometry ((↑) : α -
> Completion α)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem LipschitzWith.completion_map [PseudoMetricSpace β] {f : α → β} {K : ℝ≥0}
    (h : LipschitzWith K f) : LipschitzWith K (Completion.map f) :=
  one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension
/-
**Isometry.completion_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.completion_extension [PseudoMetricSpace β] [CompleteSpace β] [T0S
pace β] {f : α -> β} (h : Isometry f) : Isometry (Completion.extension f)
参数：h : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `UniformSpace.Completion.induction_on₂`：induction_on₂ {p : Completion α -
> Completion β -> Prop} (a : Completion α) (b : Completion β) (hp : IsClosed { x
 : Completion α × Completio…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `UniformSpace.Completion.continuous_extension`：continuous_extension : Con
tinuous (Completion.extension f)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `Isometry.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEM
etricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Unifor
mContinuous f
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Isometry.completion_extension [PseudoMetricSpace β] [CompleteSpace β] [T0Space β]
    {f : α → β} (h : Isometry f) : Isometry (Completion.extension f) :=
  Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ ↦ by
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]
/-
**Isometry.completion_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.completion_map [PseudoMetricSpace β] {f : α -> β} (h : Isometry f
) : Isometry (Completion.map f)
参数：h : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.completion_extension`：Isometry.completion_extension [PseudoMetr
icSpace β] [CompleteSpace β] [T0Space β] {f : α -> β} (h : Isometry f) : Isometr
y (Completion.exten…
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `UniformSpace.Completion.coe_isometry`：coe_isometry : Isometry ((↑) : α -
> Completion α)
-/
theorem Isometry.completion_map [PseudoMetricSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.map f) :=
  (coe_isometry.comp h).completion_extension

section extension_maps

variable [Ring α] [IsTopologicalRing α] [IsUniformAddGroup α] [Ring β]
    [PseudoMetricSpace β] [IsUniformAddGroup β] [IsTopologicalRing β]

/-- The extension of an isometry to the completion of the domain. -/
/-
**Isometry.extensionHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Isometry.extensionHom [CompleteSpace β] [T0Space β] {f : α ->+* β} (h : Is
ometry f) : Completion α ->+* β
参数：h : Isometry f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of an isometry to the completion of the domain.
-/
def Isometry.extensionHom [CompleteSpace β] [T0Space β] {f : α →+* β} (h : Isometry f) :
    Completion α →+* β := Completion.extensionHom f h.continuous

@[simp]
/-
**Isometry.extensionHom_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.extensionHom_coe [CompleteSpace β] [T0Space β] {f : α ->+* β} (h 
: Isometry f) (x : α) : h.extensionHom x = f x
参数：h : Isometry f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.extensionHom_coe`：extensionHom_coe [CompleteSpac
e β] [T0Space β] (a : α) : Completion.extensionHom f hf a = f a
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
-/
theorem Isometry.extensionHom_coe [CompleteSpace β] [T0Space β] {f : α →+* β} (h : Isometry f)
    (x : α) : h.extensionHom x = f x := Completion.extensionHom_coe f h.continuous _

/-- The lift of an isometry to completions. -/
/-
**Isometry.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Isometry.mapRingHom {f : α ->+* β} (h : Isometry f) : Completion α ->+* Co
mpletion β
参数：h : Isometry f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of an isometry to completions.
-/
def Isometry.mapRingHom {f : α →+* β} (h : Isometry f) : Completion α →+* Completion β :=
  Completion.mapRingHom f h.continuous
/-
**Isometry.mapRingHom_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.mapRingHom_coe {f : α ->+* β} (h : Isometry f) (x : α) : h.mapRin
gHom x = f x
参数：h : Isometry f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.mapRingHom_coe`：mapRingHom_coe (hf : Continuous 
f) (a : α) : mapRingHom f hf a = f a
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Isometry.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEM
etricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Unifor
mContinuous f
-/
theorem Isometry.mapRingHom_coe {f : α →+* β} (h : Isometry f) (x : α) : h.mapRingHom x = f x :=
  Completion.mapRingHom_coe h.uniformContinuous.continuous _
/-
**Isometry.isometry_mapRingHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.isometry_mapRingHom {f : α ->+* β} (h : Isometry f) : Isometry h.
mapRingHom
参数：h : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `UniformSpace.Completion.induction_on₂`：induction_on₂ {p : Completion α -
> Completion β -> Prop} (a : Completion α) (b : Completion β) (hp : IsClosed { x
 : Completion α × Completio…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformSpace.Completion.continuous_map`：continuous_map : Continuous (Com
pletion.map f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Isometry.mapRingHom_coe`：Isometry.mapRingHom_coe {f : α ->+* β} (h : Iso
metry f) (x : α) : h.mapRingHom x = f x
· 使用定理 `UniformSpace.Completion.dist_eq`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] (x y : α), dist ↑x ↑y = dist x y
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Isometry.isometry_mapRingHom {f : α →+* β} (h : Isometry f) : Isometry h.mapRingHom :=
  Isometry.of_dist_eq fun x y => by
    induction x, y using induction_on₂ with
    | hp => exact isClosed_eq (continuous_dist.comp₂ (continuous_map.comp continuous_fst)
        (continuous_map.comp continuous_snd)) (by fun_prop)
    | ih x y => simp only [Completion.dist_eq, mapRingHom_coe, h.dist_eq]

end extension_maps

