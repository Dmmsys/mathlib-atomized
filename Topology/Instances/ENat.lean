/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Order.Interval.Set.WithBotTop
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Topology on extended natural numbers
-/

public section

open Filter Set Topology

namespace ENat

/--
Topology on `ℕ∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, but all neighborhoods of `∞` in `ℕ∞` contain infinite intervals.
-/
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology on `ℕ∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` top
ology has
`IsOpen {∞}`, but all neighborhoods of `∞` in `ℕ∞` contain infinite intervals.
-/
instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology ℕ∞ := ⟨rfl⟩
/-
**ENat.range_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：Set.range Nat.cast = Set.Iio ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
-/
@[simp] theorem range_natCast : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe
/-
**ENat.isEmbedding_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：isEmbedding_natCast : IsEmbedding ((↑) : Nat -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isEmbedding_of_ordConnected`：StrictMono.isEmbedding_of_ordCon
nected {α β : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace α] [h : O
rderTopology α] [Topological…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `ENat.instOrderTopology`：OrderTopology ℕ∞
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.range_natCast`：Set.range Nat.cast = Set.Iio ⊤
-/
theorem isEmbedding_natCast : IsEmbedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.isEmbedding_of_ordConnected <| range_natCast ▸ ordConnected_Iio
/-
**ENat.isOpenEmbedding_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：isOpenEmbedding_natCast : IsOpenEmbedding ((↑) : Nat -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.isEmbedding_natCast`：isEmbedding_natCast : IsEmbedding ((↑) : Nat -
> Nat∞)
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENat.instOrderTopology`：OrderTopology ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.range_natCast`：Set.range Nat.cast = Set.Iio ⊤
-/
theorem isOpenEmbedding_natCast : IsOpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨isEmbedding_natCast, range_natCast ▸ isOpen_Iio⟩
/-
**ENat.nhds_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：nhds_natCast (n : Nat) : 𝓝 (n : Nat∞) = pure (n : Nat∞)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `ENat.isOpenEmbedding_natCast`：isOpenEmbedding_natCast : IsOpenEmbedding 
((↑) : Nat -> Nat∞)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_natCast (n : ℕ) : 𝓝 (n : ℕ∞) = pure (n : ℕ∞) := by
  simp [← isOpenEmbedding_natCast.map_nhds_eq]

@[simp]
/-
**ENat.nhds_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, n ≠ ⊤ → nhds n = pure n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.nhds_natCast`：nhds_natCast (n : Nat) : 𝓝 (n : Nat∞) = pure (n : Nat
∞)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem nhds_eq_pure {n : ℕ∞} (h : n ≠ ⊤) : 𝓝 n = pure n := by
  lift n to ℕ using h
  simp [nhds_natCast]
/-
**ENat.isOpen_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：isOpen_singleton {x : Nat∞} (hx : x != ⊤) : IsOpen {x}
参数：hx : x != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_singleton_iff_nhds_eq_pure`：isOpen_singleton_iff_nhds_eq_pure (x 
: X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
· 使用定理 `ENat.nhds_eq_pure`：∀ {n : ℕ∞}, n ≠ ⊤ → nhds n = pure n
-/
theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  rw [isOpen_singleton_iff_nhds_eq_pure, ENat.nhds_eq_pure hx]
/-
**ENat.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：mem_nhds_iff {x : Nat∞} {s : Set Nat∞} (hx : x != ⊤) : s in 𝓝 x ↔ x in s
参数：hx : x != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.nhds_eq_pure`：∀ {n : ℕ∞}, n ≠ ⊤ → nhds n = pure n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  simp [hx]
/-
**ENat.mem_nhds_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：mem_nhds_natCast_iff (n : Nat) {s : Set Nat∞} : s in 𝓝 (n : Nat∞) ↔ (n : N
at∞) in s
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.mem_nhds_iff`：mem_nhds_iff {x : Nat∞} {s : Set Nat∞} (hx : x != ⊤) 
: s in 𝓝 x ↔ x in s
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
-/
theorem mem_nhds_natCast_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (natCast_ne_top _)
/-
**ENat.tendsto_nhds_top_iff_natCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：tendsto_nhds_top_iff_natCast_lt {α : Type*} {l : Filter α} {f : α -> Nat∞}
 : Tendsto f l (𝓝 ⊤) ↔ forall n : Nat, forallᶠ a in l, n < f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_top_order`：nhds_top_order [TopologicalSpace α] [Preorder α] [OrderT
op α] [OrderTopology α] : 𝓝 (⊤ : α) = ⨅ (l) (_ : l < ⊤), 𝓟 (Ioi l)
· 使用定理 `ENat.instOrderTopology`：OrderTopology ℕ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_top_iff_natCast_lt {α : Type*} {l : Filter α} {f : α → ℕ∞} :
    Tendsto f l (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ a in l, n < f a := by
  simp_rw [nhds_top_order, lt_top_iff_ne_top, tendsto_iInf, tendsto_principal, ENat.forall_ne_top,
    mem_Ioi]
/-
**ENat.tendsto_natCast_nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：tendsto_natCast_nhds_top : Tendsto Nat.cast atTop (𝓝 (⊤ : Nat∞))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.tendsto_nhds_top_iff_natCast_lt`：tendsto_nhds_top_iff_natCast_lt {α
 : Type*} {l : Filter α} {f : α -> Nat∞} : Tendsto f l (𝓝 ⊤) ↔ forall n : Nat, f
orallᶠ a in l, n < f a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem tendsto_natCast_nhds_top : Tendsto Nat.cast atTop (𝓝 (⊤ : ℕ∞)) := by
  rw [tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [eventually_ge_atTop (n + 1)] with a ha using by simpa
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.mpr fun (a, b) ↦ ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  | (a : ℕ), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  | (a : ℕ), (b : ℕ) => simp [ContinuousAt, nhds_prod_eq]
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMul ℕ∞ where
  continuous_mul :=
    have key (a : ℕ∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases eq_zero_or_pos a with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [continuousAt_fst (lt_mem_nhds ha)] with (x, y) (hx : 0 < x)
        exact le_mul_of_one_le_left' (Order.one_le_iff_pos.2 hx)
    continuous_iff_continuousAt.2 <| Prod.forall.2 fun
      | (a : ℕ∞), ⊤ => key a
      | ⊤, (b : ℕ∞) =>
        ((key b).comp_of_eq (continuous_swap.tendsto (⊤, b)) rfl).congr <|
          .of_forall fun _ ↦ mul_comm ..
      | (a : ℕ), (b : ℕ) => by
        simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalSemiring ℕ∞ where
  toContinuousAdd := inferInstance
  toContinuousMul := inferInstance
/-
**ENat.continuousAt_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b : ℕ∞}, a ≠ ⊤ ∨ b ≠ ⊤ → ContinuousAt (Function.uncurry fun x1 x2 => 
x1 - x2) (a, b)
参数：Function.uncurry fun x1 x2 => x1 - x2；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `ENat.nhds_eq_pure`：∀ {n : ℕ∞}, n ≠ ⊤ → nhds n = pure n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `le_mem_nhds`：le_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a <= x
· 使用定理 `ENat.instOrderTopology`：OrderTopology ℕ∞
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.pure_prod`：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (
Prod.mk a) f
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem continuousAt_sub {a b : ℕ∞} (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    ContinuousAt (· - ·).uncurry (a, b) := by
  match a, b, h with
  | (a : ℕ), (b : ℕ), _ => simp [ContinuousAt, nhds_prod_eq]
  | (a : ℕ), ⊤, _ =>
    suffices ∀ᶠ b in 𝓝 ⊤, (a - b : ℕ∞) = 0 by
      simpa [ContinuousAt, nhds_prod_eq, tsub_eq_zero_of_le]
    filter_upwards [le_mem_nhds (WithTop.coe_lt_top a)] with b using tsub_eq_zero_of_le
  | ⊤, (b : ℕ), _ =>
    suffices ∀ n : ℕ, ∀ᶠ a : ℕ∞ in 𝓝 ⊤, b + n < a by
      simpa [ContinuousAt, nhds_prod_eq, (· ∘ ·), lt_tsub_iff_left, tendsto_nhds_top_iff_natCast_lt]
    exact fun n ↦ lt_mem_nhds <| WithTop.coe_lt_top (b + n)

end ENat

/-
**Filter.Tendsto.enatSub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.enatSub {α : Type*} {l : Filter α} {f g : α -> Nat∞} {a b :
 Nat∞} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : a != ⊤ ∨ b != ⊤) :
 Tendsto (fun x => f x - g x) l (𝓝 (a - b))
参数：hf : Tendsto f l (𝓝 a)；hg : Tendsto g l (𝓝 b)；h : a != ⊤ ∨ b != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENat.continuousAt_sub`：∀ {a b : ℕ∞}, a ≠ ⊤ ∨ b ≠ ⊤ → ContinuousAt (Funct
ion.uncurry fun x1 x2 => x1 - x2) (a, b)
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.enatSub {α : Type*} {l : Filter α} {f g : α → ℕ∞} {a b : ℕ∞}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    Tendsto (fun x ↦ f x - g x) l (𝓝 (a - b)) :=
  (ENat.continuousAt_sub h).tendsto.comp (hf.prodMk_nhds hg)

variable {X : Type*} [TopologicalSpace X] {f g : X → ℕ∞} {s : Set X} {x : X}

nonrec theorem ContinuousWithinAt.enatSub
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) (h : f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousWithinAt (fun x ↦ f x - g x) s x :=
  hf.enatSub hg h

nonrec theorem ContinuousAt.enatSub
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousAt (fun x ↦ f x - g x) x :=
  hf.enatSub hg h

nonrec theorem ContinuousOn.enatSub
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h : ∀ x ∈ s, f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousOn (fun x ↦ f x - g x) s := fun x hx ↦
  (hf x hx).enatSub (hg x hx) (h x hx)

nonrec theorem Continuous.enatSub
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ ⊤ ∨ g x ≠ ⊤) :
    Continuous (fun x ↦ f x - g x) :=
  continuous_iff_continuousAt.2 fun x ↦ hf.continuousAt.enatSub hg.continuousAt (h x)
