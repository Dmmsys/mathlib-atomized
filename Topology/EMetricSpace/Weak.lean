/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.WithTop

/-!
# Lemmas around weak (pseudo) extended metric spaces.

In this file we show that whenever `some : α → Option α` is an open embedding and `α` is a
`WeakPseudoEMetricSpace`, then `Option α` is as well in a natural manner. We then use this to prove
`ℝ≥0` and `EReal` are weak extended metric spaces.

## Main statements

* `Option.weakPseudoEMetricSpace_of_isOpenEmbedding`: states that under a weak condition, if `α` is
  a weak pseudo extended space, so is `Option α`.
* `instWeakPseudoEMetricSpaceOnePoint`: The one point compactification of a weak pseudo extended
  metric space is a weak pseudo extended metric space.
* `instWeakEMetricSpaceENNReal`: `ℝ≥0∞` is a weak extended metric space.
* `instWeakEMetricSpaceEReal`: `EReal` is a weak extended metric space.

TODO: Some lemmas around order topologies can likely be generalised from linear orders to pre-
or partial orders.

-/

@[expose] public section

open Set Filter Topology WithTop WithBot

open scoped Uniformity Topology NNReal ENNReal Pointwise

universe u

variable {α : Type u} [t : TopologicalSpace α]

section

namespace Option

/-- Given some (extended) distance function on `α`, it can be extended to a distance function on
`Option α` by defining `edist none a = 0` if `a = none` and `∞` otherwise. -/
/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given some (extended) distance function on `α`, it can be extended to a distance
 function on
`Option α` by defining `edist none a = 0` if `a = none` and `∞` otherwise.
-/
instance (priority := low) toEDist {α : Type u} [EDist α] : EDist (Option α) where
  edist
  | none, (x : α) => ∞
  | none, none => 0
  | (x : α), none => ∞
  | (x : α), (y : α) => edist x y

variable [m : WeakPseudoEMetricSpace α]

@[simp]
/-
**Option.edist_none_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：edist_none_none : edist (self
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_none_none : edist (self := Option.toEDist (α := α))
    none none = 0 := rfl

@[simp]
/-
**Option.edist_none_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：edist_none_some {a : α} : edist (self
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_none_some {a : α} :
    edist (self := Option.toEDist (α := α)) none a = ⊤ := rfl

@[simp]
/-
**Option.edist_some_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：edist_some_none {a : α} : edist (self
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_some_none {a : α} :
    edist (self := Option.toEDist (α := α)) a none = ⊤ := rfl

@[simp]
/-
**Option.edist_some_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：edist_some_some {a b : α} : edist (self
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_some_some {a b : α} :
    edist (self := Option.toEDist (α := α)) a b = edist a b := rfl
/-
**Option.some_eball** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：some_eball (a : α) (r : ENNReal) : Option.some '' Metric.eball a r = Metri
c.eball (α
参数：a : α；r : ENNReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem some_eball (a : α) (r : ENNReal) :
    Option.some '' Metric.eball a r = Metric.eball (α := Option α) a r := by
  ext x
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | none => simp at h
  | (y : α) =>
    exact ⟨y, h, rfl⟩
/-
**Option.edist_self'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] (m : WeakPseudoEMetricSpace α) 
(x : Option α), edist x x = 0
参数：m : WeakPseudoEMetricSpace α；x : Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeakPseudoEMetricSpace.edist_self`：∀ {α : Type u} {τ : TopologicalSpace 
α} [self : WeakPseudoEMetricSpace α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_self' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x : Option α, edist x x = 0
  | (_ : α) => by simp [m.edist_self]
  | none => rfl
/-
**Option.edist_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] (m : WeakPseudoEMetricSpace α) 
(x y : Option α), edist x y = edist y x
参数：m : WeakPseudoEMetricSpace α；x y : Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeakPseudoEMetricSpace.edist_comm`：∀ {α : Type u} {τ : TopologicalSpace 
α} [self : WeakPseudoEMetricSpace α] (x y : α), edist x y = edist y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_comm' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y : Option α, edist x y = edist y x
  | (_ : α), (_ : α) => by simp [m.edist_comm]
  | (_ : α), none => by simp
  | none, (_ : α) => by simp
  | none, none => by simp
/-
**Option.edist_triangle'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] (m : WeakPseudoEMetricSpace α) 
(x y z : Option α),   edist x z ≤ edist x y + edist y z
参数：m : WeakPseudoEMetricSpace α；x y z : Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `WeakPseudoEMetricSpace.edist_triangle`：∀ {α : Type u} {τ : TopologicalSp
ace α} [self : WeakPseudoEMetricSpace α] (x y z : α), edist x z ≤ edist x y + ed
ist y z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma edist_triangle' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y z : Option α, edist x z ≤ edist x y + edist y z
  | (_ : α), (_ : α), (_ : α) => by simp [m.edist_triangle]
  | none, (_ : α), (_ : α) => by simp
  | (_ : α), none, (_ : α) => by simp
  | none, none, (_ : α) => by simp
  | (_ : α), (_ : α), none => by simp
  | none, (_ : α), none => by simp
  | (_ : α), none, none => by simp
  | none, none, none => by simp
/-
**Option.ball_infty_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：ball_infty_of_pos {r : ENNReal} (hr : 0 < r) : Metric.eball (none : Option
 α) r = {none}
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem ball_infty_of_pos {r : ENNReal} (hr : 0 < r) :
    Metric.eball (none : Option α) r = {none} := by
  refine eq_singleton_iff_unique_mem.mpr ⟨Metric.mem_eball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | none => tauto

/-- If `some : α → Option α` is an open embedding and `α` is has a weak pseudo extended metric
structure, the structure extends naturally to `Option α`. -/
/-
**Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Opt
ion.WeakPseudoEMetricSpace`。
形式化陈述：{α : Type u} →   [t : TopologicalSpace α] →     [inst : TopologicalSpace (
Option α)] →       [m : WeakPseudoEMetricSpace α] →         [inst_1 : EDist (Opt
ion α)] →           inst_1 = Option.toEDist → Topology.IsOpenEmbedding some → We
akPseudoEMetricSpace (Option α)
参数：Option α；Option α；Option α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `some : α → Option α` is an open embedding and `α` is has a weak pseudo exten
ded metric
structure, the structure extends naturally to `Option α`.
-/
abbrev WeakPseudoEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakPseudoEMetricSpace α] [inst : EDist (Option α)]
    (h_edist : inst = Option.toEDist) (h : IsOpenEmbedding (some (α := α))) :
    WeakPseudoEMetricSpace (Option α) where
  edist := edist
  edist_self := h_edist ▸ edist_self' m
  edist_comm := h_edist ▸ edist_comm' m
  edist_triangle := h_edist ▸ edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (Option α) (PseudoEMetricSpace.ofEDist edist
      (h_edist ▸ edist_self' m) (h_edist ▸ edist_comm' m) (h_edist ▸ edist_triangle' m))).mpr
    intro x xs
    suffices ∃ ε > 0, @Metric.eball (Option α) Option.toEDist x ε ⊆ s by rwa [← h_edist] at this
    match x with
    | none =>
      exact ⟨1, by norm_num, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, some_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    rw [h_edist]
    match x with
    | (x : α) =>
      obtain ⟨s', s'o, s's⟩ := m.topology_eq_on_restrict x r
      refine ⟨some '' s', ?_, ?_⟩
      · exact (IsOpenEmbedding.isOpen_iff_image_isOpen h).mp s'o
      ext ⟨y, yh⟩
      match y with
      | none => contradiction
      | (z : α) =>
        apply Set.ext_iff.mp at s's
        simp only [mem_preimage, Subtype.forall, Metric.mem_eball, mem_image] at s's ⊢ yh
        specialize s's z yh
        refine ⟨fun ⟨r, rh, rh'⟩ ↦ ?_, fun _ ↦ ⟨z, by tauto⟩⟩
        exact s's.1 <| h.injective rh' ▸ rh
    | none =>
      apply discreteTopology_iff_forall_isOpen.mp
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

/-- If `some : α → Option α` is an open embedding and `α` is has a weak pseudo extended metric
structure, the structure extends naturally to `Option α`. -/
/-
**Option.WeakEMetricSpace.OfIsOpenEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Option.We
akEMetricSpace`。
形式化陈述：{α : Type u} →   [t : TopologicalSpace α] →     [inst : TopologicalSpace (
Option α)] →       [m : WeakEMetricSpace α] →         [inst_1 : EDist (Option α)
] →           inst_1 = Option.toEDist → Topology.IsOpenEmbedding some → WeakEMet
ricSpace (Option α)
参数：Option α；Option α；Option α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `some : α → Option α` is an open embedding and `α` is has a weak pseudo exten
ded metric
structure, the structure extends naturally to `Option α`.
-/
abbrev WeakEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakEMetricSpace α] [inst : EDist (Option α)]
    (h_edist : inst = Option.toEDist) (h : IsOpenEmbedding (some (α := α))) :
    WeakEMetricSpace (Option α) :=
  { toWeakPseudoEMetricSpace := WeakPseudoEMetricSpace.OfIsOpenEmbedding h_edist h,
    eq_of_edist_eq_zero {x y} xy := by
      rw [congr(@edist _ $h_edist x y)] at xy
      cases x <;> cases y
      · rfl
      · simp at xy
      · simp at xy
      rw [m.eq_of_edist_eq_zero xy]
    }

end Option

variable [LinearOrder α] [OrderTopology α]

/-- If `α` has a linear order topology, `some : α → WithTop α` is an open embedding with respect to
the order topologies. -/
@[to_dual]
/-
**WithTop.isOpenEmbedding_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithTop.isOpenEmbedding_some : IsOpenEmbedding (some (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isEmbedding_of_ordConnected`：StrictMono.isEmbedding_of_ordCon
nected {α β : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace α] [h : O
rderTopology α] [Topological…
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `WithTop.coe_strictMono`：∀ {α : Type u_1} [inst : Preorder α], StrictMono
 fun a => ↑a
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
· 使用定理 `isOpen_Iio'`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] (a : α), IsOpen (Set.Iio a)

--- 原说明 ---
If `α` has a linear order topology, `some : α → WithTop α` is an open embedding 
with respect to
the order topologies.
-/
theorem WithTop.isOpenEmbedding_some : IsOpenEmbedding (some (α := α)) :=
  ⟨WithTop.coe_strictMono.isEmbedding_of_ordConnected (range_coe (α := α) ▸ ordConnected_Iio),
   range_coe (α := α) ▸ isOpen_Iio' ⊤⟩

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EDist α] : EDist (WithTop α) where
  edist
  | ⊤, (x : α) => ∞
  | ⊤, ⊤ => 0
  | (x : α), ⊤ => ∞
  | (x : α), (y : α) => edist x y

/-- If `α` has a topology induced by a linear order and is a weak pseudo extended metric space,
so is `WithTop α` -/
@[to_dual]
/-
**instWeakPseudoEMetricSpaceWithTop** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakPseudoEMetricSpaceWithTop [m : WeakPseudoEMetricSpace α] : WeakPse
udoEMetricSpace (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a topology induced by a linear order and is a weak pseudo extended me
tric space,
so is `WithTop α`
-/
instance instWeakPseudoEMetricSpaceWithTop [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (WithTop α) :=
  letI : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  letI : WeakPseudoEMetricSpace (Option α) :=
    Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding (inst := instEDistWithTop) rfl
    WithTop.isOpenEmbedding_some
  inferInstanceAs <| WeakPseudoEMetricSpace (Option α)

/-- If `α` has a topology induced by a linear order and is a weak extended metric space,
so is `WithTop α` -/
@[to_dual]
/-
**instWeakEMetricSpaceWithTop** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakEMetricSpaceWithTop [m : WeakEMetricSpace α] : WeakEMetricSpace (W
ithTop α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.isOpenEmbedding_some`：WithTop.isOpenEmbedding_some : IsOpenEmbed
ding (some (α

--- 原说明 ---
If `α` has a topology induced by a linear order and is a weak extended metric sp
ace,
so is `WithTop α`
-/
instance instWeakEMetricSpaceWithTop [m : WeakEMetricSpace α] : WeakEMetricSpace (WithTop α) :=
  let : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistWithTop) rfl WithTop.isOpenEmbedding_some
  inferInstanceAs <| WeakEMetricSpace (Option α)

open scoped OnePoint in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EDist α] : EDist (OnePoint α) where
  edist
  | ∞, (x : α) => none
  | ∞, ∞ => 0
  | (x : α), ∞ => none
  | (x : α), (y : α) => edist x y

/-- The one point compactification of a weak pseudo extended metric space is again a weak pseudo
extended metric space. -/
/-
**instWeakPseudoEMetricSpaceOnePoint** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakPseudoEMetricSpaceOnePoint [m : WeakPseudoEMetricSpace α] : WeakPs
eudoEMetricSpace (OnePoint α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)

--- 原说明 ---
The one point compactification of a weak pseudo extended metric space is again a
 weak pseudo
extended metric space.
-/
instance instWeakPseudoEMetricSpaceOnePoint [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakPseudoEMetricSpace (Option α) := Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
  inferInstanceAs <| WeakPseudoEMetricSpace (Option α)

/-- The one point compactification of a weak extended metric space is again a weak extended metric
space. -/
/-
**instWeakEMetricSpaceOnePoint** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakEMetricSpaceOnePoint [m : WeakEMetricSpace α] : WeakEMetricSpace (
OnePoint α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)

--- 原说明 ---
The one point compactification of a weak extended metric space is again a weak e
xtended metric
space.
-/
instance instWeakEMetricSpaceOnePoint [m : WeakEMetricSpace α] :
    WeakEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
  inferInstanceAs <| WeakEMetricSpace (Option α)

/-- `ℝ≥0∞` is a weak extended metric space with its usual distance function. -/
/-
**instWeakEMetricSpaceENNReal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakEMetricSpaceENNReal : WeakEMetricSpace Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℝ≥0∞` is a weak extended metric space with its usual distance function.
-/
noncomputable instance instWeakEMetricSpaceENNReal : WeakEMetricSpace ℝ≥0∞ :=
  inferInstanceAs <| WeakEMetricSpace (WithTop ℝ≥0)

/-- `EReal` is a weak extended metric space with its usual distance function. -/
/-
**instWeakEMetricSpaceEReal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakEMetricSpaceEReal : WeakEMetricSpace EReal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EReal` is a weak extended metric space with its usual distance function.
-/
noncomputable instance instWeakEMetricSpaceEReal : WeakEMetricSpace EReal :=
  inferInstanceAs <| WeakEMetricSpace (WithBot (WithTop ℝ))

/-- `ℕ∞` is a weak extended metric space with its usual distance function. -/
/-
**instWeakEMetricSpaceENat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instWeakEMetricSpaceENat : WeakEMetricSpace Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℕ∞` is a weak extended metric space with its usual distance function.
-/
noncomputable instance instWeakEMetricSpaceENat : WeakEMetricSpace ℕ∞ :=
  inferInstanceAs <| WeakEMetricSpace (WithTop ℕ)
/-
**ENNReal.edist_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.edist_eq_top_iff (a b : Real>=0∞) : edist a b = ∞ ↔ a != b ∧ (a = 
∞ ∨ b = ∞)
参数：a b : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
-/
theorem ENNReal.edist_eq_top_iff (a b : ℝ≥0∞) : edist a b = ∞ ↔ a ≠ b ∧ (a = ∞ ∨ b = ∞) := by
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, or_self, and_true, iff_false,
    top_ne_coe, not_false_eq_true, coe_ne_top, or_false, and_self, or_true, and_self, iff_true,
    coe_inj, and_false, iff_false]
  · exact zero_ne_top
  · rfl
  · rfl
  · exact edist_ne_top _ _

--TODO: Many more lemmas around `edist` on `ℝ≥0∞` etc. to add
