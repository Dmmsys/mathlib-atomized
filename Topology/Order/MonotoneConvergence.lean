/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `IsLUB`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `Prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

public section

open Filter Set Function
open scoped Topology

variable {α β : Type*}

/--
Definition of `SupConvergenceClass` / `SupConvergenceClass` 的定义

English:
class SupConvergenceClass
  parameters: (α : Type*) [Preorder α] [TopologicalSpace α]
  axioms and operations (1):
    - tendsto_coe_atTop_isLUB : forall (a : α) (s : Set α), IsLUB s a -> Tendsto ((↑) : s -> α) atTop (𝓝 a)

中文:
类 SupConvergenceClass
  参数: (α : 类型) [Preorder α] [TopologicalSpace α]
  公理与运算 (1 个):
    - tendsto_coe_atTop_isLUB : 对任意 (a : α) (s : Set α), IsLUB s a -> Tendsto ((↑) : s -> α) atTop (𝓝 a)
-/
class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    forall (a : α) (s : Set α), IsLUB s a -> Tendsto ((↑) : s -> α) atTop (𝓝 a)

/--
Definition of `InfConvergenceClass` / `InfConvergenceClass` 的定义

English:
class InfConvergenceClass
  parameters: (α : Type*) [Preorder α] [TopologicalSpace α]
  axioms and operations (1):
    - tendsto_coe_atBot_isGLB : forall (a : α) (s : Set α), IsGLB s a -> Tendsto ((↑) : s -> α) atBot (𝓝 a)

中文:
类 InfConvergenceClass
  参数: (α : 类型) [Preorder α] [TopologicalSpace α]
  公理与运算 (1 个):
    - tendsto_coe_atBot_isGLB : 对任意 (a : α) (s : Set α), IsGLB s a -> Tendsto ((↑) : s -> α) atBot (𝓝 a)
-/
class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞` -/
  tendsto_coe_atBot_isGLB :
    forall (a : α) (s : Set α), IsGLB s a -> Tendsto ((↑) : s -> α) atBot (𝓝 a)

/--
Instance `OrderDual.supConvergenceClass` / 实例 `OrderDual.supConvergenceClass`

English:
instance OrderDual.supConvergenceClass
  signature: [Preorder α] [TopologicalSpace α] [InfConvergenceClass α]
  body: ⟨‹InfConvergenceClass α›.1⟩

中文:
实例 OrderDual.supConvergenceClass
  签名: [Preorder α] [TopologicalSpace α] [InfConvergenceClass α]
  定义体: ⟨‹InfConvergenceClass α›.1⟩

Depends on / 依赖: InfConvergenceClass
-/
instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ :=
  ⟨‹InfConvergenceClass α›.1⟩

/--
Instance `OrderDual.infConvergenceClass` / 实例 `OrderDual.infConvergenceClass`

English:
instance OrderDual.infConvergenceClass
  signature: [Preorder α] [TopologicalSpace α] [SupConvergenceClass α]
  body: ⟨‹SupConvergenceClass α›.1⟩

中文:
实例 OrderDual.infConvergenceClass
  签名: [Preorder α] [TopologicalSpace α] [SupConvergenceClass α]
  定义体: ⟨‹SupConvergenceClass α›.1⟩

Depends on / 依赖: SupConvergenceClass
-/
instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ :=
  ⟨‹SupConvergenceClass α›.1⟩

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    exact (eventually_ge_atTop c).mono fun x hx => bc.trans_le hx
  · exact Eventually.of_forall fun x => (ha.1 x.2).trans_lt hb

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α :=
  show InfConvergenceClass αᵒᵈᵒᵈ from OrderDual.infConvergenceClass

section

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι -> α} {a : α}

/--
theorem `tendsto_atTop_isLUB` / 定理 `tendsto_atTop_isLUB`

English:
theorem tendsto_atTop_isLUB
  given: (h_mono : Monotone f) (ha : IsLUB (Set.range f) a)
  proof: by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

中文:
定理 tendsto_atTop_isLUB
  条件: (h_mono : Monotone f) (ha : IsLUB (Set.range f) a)
  证明: by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

Depends on / 依赖: SupConvergenceClass, SupConvergenceClass.tendsto_coe_atTop_isLUB, Tendsto, h_mono, h_mono.rangeFactorization.tendsto_atTop_atTop, ha.ge, rangeFactorization, tendsto_atTop_atTop, tendsto_coe_atTop_isLUB
-/
theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

/--
theorem `tendsto_atBot_isLUB` / 定理 `tendsto_atBot_isLUB`

English:
theorem tendsto_atBot_isLUB
  given: (h_anti : Antitone f) (ha : IsLUB (Set.range f) a)
  proof: by convert! tendsto_atTop_isLUB h_anti.dual_left ha using 1

中文:
定理 tendsto_atBot_isLUB
  条件: (h_anti : Antitone f) (ha : IsLUB (Set.range f) a)
  证明: by convert! tendsto_atTop_isLUB h_anti.dual_left ha using 1

Depends on / 依赖: convert, dual_left, h_anti, h_anti.dual_left, tendsto_atTop_isLUB
-/
theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert! tendsto_atTop_isLUB h_anti.dual_left ha using 1

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι -> α} {a : α}

/--
theorem `tendsto_atBot_isGLB` / 定理 `tendsto_atBot_isGLB`

English:
theorem tendsto_atBot_isGLB
  given: (h_mono : Monotone f) (ha : IsGLB (Set.range f) a)
  proof: by convert! tendsto_atTop_isLUB h_mono.dual ha.dual using 1

中文:
定理 tendsto_atBot_isGLB
  条件: (h_mono : Monotone f) (ha : IsGLB (Set.range f) a)
  证明: by convert! tendsto_atTop_isLUB h_mono.dual ha.dual using 1

Depends on / 依赖: convert, h_mono, h_mono.dual, ha.dual, tendsto_atTop_isLUB
-/
theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert! tendsto_atTop_isLUB h_mono.dual ha.dual using 1

/--
theorem `tendsto_atTop_isGLB` / 定理 `tendsto_atTop_isGLB`

English:
theorem tendsto_atTop_isGLB
  given: (h_anti : Antitone f) (ha : IsGLB (Set.range f) a)
  proof: by convert! tendsto_atBot_isLUB h_anti.dual ha.dual using 1

中文:
定理 tendsto_atTop_isGLB
  条件: (h_anti : Antitone f) (ha : IsGLB (Set.range f) a)
  证明: by convert! tendsto_atBot_isLUB h_anti.dual ha.dual using 1

Depends on / 依赖: convert, h_anti, h_anti.dual, ha.dual, tendsto_atBot_isLUB
-/
theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by convert! tendsto_atBot_isLUB h_anti.dual ha.dual using 1

end IsGLB

section CiSup

variable [ConditionallyCompletePartialOrderSup α] [SupConvergenceClass α] {f : ι -> α}

/--
theorem `tendsto_atTop_ciSup` / 定理 `tendsto_atTop_ciSup`

English:
theorem tendsto_atTop_ciSup
  given: (h_mono : Monotone f) (hbdd : BddAbove <| range f)
  proof: by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
exact tendsto_atTop_isLUB h_mono
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

中文:
定理 tendsto_atTop_ciSup
  条件: (h_mono : Monotone f) (hbdd : BddAbove <| range f)
  证明: by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
exact tendsto_atTop_isLUB h_mono
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

Depends on / 依赖: Filter, Filter.atTop_neBot_iff.mp, Set.range_nonempty, atTop_neBot_iff, directedOn_range, directed_le, eq_or_ne, h_mono, h_mono.directed_le.directedOn_range.isLUB_csSup, isLUB_csSup, range_nonempty, tendsto_atTop_isLUB
-/
theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
exact tendsto_atTop_isLUB h_mono
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

/--
theorem `tendsto_atBot_ciSup` / 定理 `tendsto_atBot_ciSup`

English:
theorem tendsto_atBot_ciSup
  given: (h_anti : Antitone f) (hbdd : BddAbove <| range f)
  proof: by convert! tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1

中文:
定理 tendsto_atBot_ciSup
  条件: (h_anti : Antitone f) (hbdd : BddAbove <| range f)
  证明: by convert! tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1

Depends on / 依赖: convert, h_anti, h_anti.dual, hbdd.dual, tendsto_atTop_ciSup
-/
theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by convert! tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1

end CiSup

section CiInf

variable [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {f : ι -> α}

/--
theorem `tendsto_atBot_ciInf` / 定理 `tendsto_atBot_ciInf`

English:
theorem tendsto_atBot_ciInf
  given: (h_mono : Monotone f) (hbdd : BddBelow <| range f)
  proof: by convert! tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1

中文:
定理 tendsto_atBot_ciInf
  条件: (h_mono : Monotone f) (hbdd : BddBelow <| range f)
  证明: by convert! tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1

Depends on / 依赖: convert, h_mono, h_mono.dual, hbdd.dual, tendsto_atTop_ciSup
-/
theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by convert! tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1

/--
theorem `tendsto_atTop_ciInf` / 定理 `tendsto_atTop_ciInf`

English:
theorem tendsto_atTop_ciInf
  given: (h_anti : Antitone f) (hbdd : BddBelow <| range f)
  proof: by convert! tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1

中文:
定理 tendsto_atTop_ciInf
  条件: (h_anti : Antitone f) (hbdd : BddBelow <| range f)
  证明: by convert! tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1

Depends on / 依赖: convert, h_anti, h_anti.dual, hbdd.dual, tendsto_atBot_ciSup
-/
theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by convert! tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι -> α}

/--
theorem `tendsto_atTop_iSup` / 定理 `tendsto_atTop_iSup`

English:
theorem tendsto_atTop_iSup
  given: (h_mono : Monotone f)
  statement: Tendsto f atTop (𝓝 (⨆ i, f i))
  proof: tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

中文:
定理 tendsto_atTop_iSup
  条件: (h_mono : Monotone f)
  结论: Tendsto f atTop (𝓝 (⨆ i, f i))
  证明: tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, h_mono, tendsto_atTop_ciSup
-/
theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

/--
theorem `tendsto_atBot_iSup` / 定理 `tendsto_atBot_iSup`

English:
theorem tendsto_atBot_iSup
  given: (h_anti : Antitone f)
  statement: Tendsto f atBot (𝓝 (⨆ i, f i))
  proof: tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

中文:
定理 tendsto_atBot_iSup
  条件: (h_anti : Antitone f)
  结论: Tendsto f atBot (𝓝 (⨆ i, f i))
  证明: tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, h_anti, tendsto_atBot_ciSup
-/
theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι -> α}

/--
theorem `tendsto_atBot_iInf` / 定理 `tendsto_atBot_iInf`

English:
theorem tendsto_atBot_iInf
  given: (h_mono : Monotone f)
  statement: Tendsto f atBot (𝓝 (⨅ i, f i))
  proof: tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

中文:
定理 tendsto_atBot_iInf
  条件: (h_mono : Monotone f)
  结论: Tendsto f atBot (𝓝 (⨅ i, f i))
  证明: tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, h_mono, tendsto_atBot_ciInf
-/
theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

/--
theorem `tendsto_atTop_iInf` / 定理 `tendsto_atTop_iInf`

English:
theorem tendsto_atTop_iInf
  given: (h_anti : Antitone f)
  statement: Tendsto f atTop (𝓝 (⨅ i, f i))
  proof: tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

中文:
定理 tendsto_atTop_iInf
  条件: (h_anti : Antitone f)
  结论: Tendsto f atTop (𝓝 (⨅ i, f i))
  证明: tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, h_anti, tendsto_atTop_ciInf
-/
theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

end iInf

end

/--
Instance `Prod.supConvergenceClass` / 实例 `Prod.supConvergenceClass`

English:
instance Prod.supConvergenceClass
  body: by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod]; rw [← range_domRestrict]; rw [← range_domRestrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.domRestrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    t

中文:
实例 Prod.supConvergenceClass
  定义体: by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod]; rw [← range_domRestrict]; rw [← range_domRestrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.domRestrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    t

Depends on / 依赖: A.prodMk_nhds, Tendsto, domRestrict, isLUB_prod, monotone_fst, monotone_fst.domRestrict, monotone_snd, monotone_snd.domRestrict, prodMk_nhds, range_domRestrict, tendsto_atTop_isLUB
-/
instance Prod.supConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [SupConvergenceClass α] [SupConvergenceClass β] : SupConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod]; rw [← range_domRestrict]; rw [← range_domRestrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.domRestrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.domRestrict s) h.2
  exact A.prodMk_nhds B

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
  body: show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

中文:
实例 [Preorder
  签名: α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
  定义体: show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

Depends on / 依赖: InfConvergenceClass, OrderDual, OrderDual.infConvergenceClass, infConvergenceClass
-/
instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) :=
  show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

/--
Instance `Pi.supConvergenceClass` / 实例 `Pi.supConvergenceClass`

English:
instance Pi.supConvergenceClass
  body: by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_domRestrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).domRestrict _) (h i)

中文:
实例 Pi.supConvergenceClass
  定义体: by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_domRestrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).domRestrict _) (h i)

Depends on / 依赖: domRestrict, isLUB_pi, monotone_eval, range_domRestrict, tendsto_atTop_isLUB, tendsto_pi_nhds
-/
instance Pi.supConvergenceClass
    {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] [forall i, TopologicalSpace (α i)]
    [forall i, SupConvergenceClass (α i)] : SupConvergenceClass (forall i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_domRestrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).domRestrict _) (h i)

/--
Instance `Pi.infConvergenceClass` / 实例 `Pi.infConvergenceClass`

English:
instance Pi.infConvergenceClass
  body: show InfConvergenceClass (forall i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

中文:
实例 Pi.infConvergenceClass
  定义体: show InfConvergenceClass (forall i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

Depends on / 依赖: InfConvergenceClass, OrderDual, OrderDual.infConvergenceClass, infConvergenceClass
-/
instance Pi.infConvergenceClass
    {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] [forall i, TopologicalSpace (α i)]
    [forall i, InfConvergenceClass (α i)] : InfConvergenceClass (forall i, α i) :=
  show InfConvergenceClass (forall i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

/--
Instance `Pi.supConvergenceClass'` / 实例 `Pi.supConvergenceClass'`

English:
instance Pi.supConvergenceClass'
  signature: {ι : Type*} [Preorder α] [TopologicalSpace α]
  body: supConvergenceClass

中文:
实例 Pi.supConvergenceClass'
  签名: {ι : 类型} [Preorder α] [TopologicalSpace α]
  定义体: supConvergenceClass

Depends on / 依赖: supConvergenceClass
-/
instance Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι -> α) :=
  supConvergenceClass

/--
Instance `Pi.infConvergenceClass'` / 实例 `Pi.infConvergenceClass'`

English:
instance Pi.infConvergenceClass'
  signature: {ι : Type*} [Preorder α] [TopologicalSpace α]
  body: Pi.infConvergenceClass

中文:
实例 Pi.infConvergenceClass'
  签名: {ι : 类型} [Preorder α] [TopologicalSpace α]
  定义体: Pi.infConvergenceClass

Depends on / 依赖: Pi.infConvergenceClass, infConvergenceClass
-/
instance Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι -> α) :=
  Pi.infConvergenceClass

/--
theorem `tendsto_atTop_of_monotone` / 定理 `tendsto_atTop_of_monotone`

English:
theorem tendsto_atTop_of_monotone
  statement: {ι α : Type*} [Preorder ι] [TopologicalSpace α]
  proof: by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
else Or.inl tendsto_atTop_atTop_of_monotone' h_mono H

@[deprecated (since := "2026-01-22")] alias tendsto_of_monotone := tendsto_atTop_of_monotone

中文:
定理 tendsto_atTop_of_monotone
  结论: {ι α : 类型} [Preorder ι] [TopologicalSpace α]
  证明: by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
else Or.inl tendsto_atTop_atTop_of_monotone' h_mono H

@[deprecated (since := "2026-01-22")] alias tendsto_of_monotone := tendsto_atTop_of_monotone

Depends on / 依赖: BddAbove, Or.inl, Or.inr, classical, h_mono, tendsto_atTop_atTop_of_monotone, tendsto_atTop_ciSup
-/
theorem tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ exists l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
else Or.inl tendsto_atTop_atTop_of_monotone' h_mono H

@[deprecated (since := "2026-01-22")] alias tendsto_of_monotone := tendsto_atTop_of_monotone

/--
theorem `tendsto_atTop_of_antitone` / 定理 `tendsto_atTop_of_antitone`

English:
theorem tendsto_atTop_of_antitone
  statement: {ι α : Type*} [Preorder ι] [TopologicalSpace α]
  proof: tendsto_atTop_of_monotone (α := αᵒᵈ) h_mono

@[deprecated (since := "2026-01-22")] alias tendsto_of_antitone := tendsto_atTop_of_antitone

中文:
定理 tendsto_atTop_of_antitone
  结论: {ι α : 类型} [Preorder ι] [TopologicalSpace α]
  证明: tendsto_atTop_of_monotone (α := αᵒᵈ) h_mono

@[deprecated (since := "2026-01-22")] alias tendsto_of_antitone := tendsto_atTop_of_antitone

Depends on / 依赖: h_mono, tendsto_atTop_of_monotone
-/
theorem tendsto_atTop_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : Antitone f) :
    Tendsto f atTop atBot ∨ exists l, Tendsto f atTop (𝓝 l) :=
  tendsto_atTop_of_monotone (α := αᵒᵈ) h_mono

@[deprecated (since := "2026-01-22")] alias tendsto_of_antitone := tendsto_atTop_of_antitone

/--
theorem `tendsto_atBot_of_monotone` / 定理 `tendsto_atBot_of_monotone`

English:
theorem tendsto_atBot_of_monotone
  statement: {ι α : Type*} [Preorder ι] [TopologicalSpace α]
  proof: tendsto_atTop_of_monotone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

中文:
定理 tendsto_atBot_of_monotone
  结论: {ι α : 类型} [Preorder ι] [TopologicalSpace α]
  证明: tendsto_atTop_of_monotone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

Depends on / 依赖: h_mono, h_mono.dual, tendsto_atTop_of_monotone
-/
theorem tendsto_atBot_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : Monotone f) :
    Tendsto f atBot atBot ∨ exists l, Tendsto f atBot (𝓝 l) :=
  tendsto_atTop_of_monotone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

/--
theorem `tendsto_atBot_of_antitone` / 定理 `tendsto_atBot_of_antitone`

English:
theorem tendsto_atBot_of_antitone
  statement: {ι α : Type*} [Preorder ι] [TopologicalSpace α]
  proof: tendsto_atTop_of_antitone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

中文:
定理 tendsto_atBot_of_antitone
  结论: {ι α : 类型} [Preorder ι] [TopologicalSpace α]
  证明: tendsto_atTop_of_antitone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

Depends on / 依赖: h_mono, h_mono.dual, tendsto_atTop_of_antitone
-/
theorem tendsto_atBot_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : Antitone f) :
    Tendsto f atBot atTop ∨ exists l, Tendsto f atBot (𝓝 l) :=
  tendsto_atTop_of_antitone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

/--
theorem `tendsto_iff_tendsto_subseq_of_monotone` / 定理 `tendsto_iff_tendsto_subseq_of_monotone`

English:
theorem tendsto_iff_tendsto_subseq_of_monotone
  statement: {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
  proof: by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

中文:
定理 tendsto_iff_tendsto_subseq_of_monotone
  结论: {ι₁ ι₂ α : 类型} [SemilatticeSup ι₁] [Preorder ι₂]
  证明: by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

Depends on / 依赖: h.comp, not_tendsto_atTop_of_tendsto_nhds, tendsto_atTop_of_monotone, tendsto_nhds_unique
-/
theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ -> α} {φ : ι₁ -> ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

/--
theorem `tendsto_iff_tendsto_subseq_of_antitone` / 定理 `tendsto_iff_tendsto_subseq_of_antitone`

English:
theorem tendsto_iff_tendsto_subseq_of_antitone
  statement: {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
  proof: tendsto_iff_tendsto_subseq_of_monotone (α := αᵒᵈ) hf hg

中文:
定理 tendsto_iff_tendsto_subseq_of_antitone
  结论: {ι₁ ι₂ α : 类型} [SemilatticeSup ι₁] [Preorder ι₂]
  证明: tendsto_iff_tendsto_subseq_of_monotone (α := αᵒᵈ) hf hg

Depends on / 依赖: tendsto_iff_tendsto_subseq_of_monotone
-/
theorem tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMinOrder α] {f : ι₂ -> α} {φ : ι₁ -> ι₂} {l : α} (hf : Antitone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) :=
  tendsto_iff_tendsto_subseq_of_monotone (α := αᵒᵈ) hf hg


/--
theorem `Monotone.ge_of_tendsto` / 定理 `Monotone.ge_of_tendsto`

English:
theorem Monotone.ge_of_tendsto
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

中文:
定理 Monotone.ge_of_tendsto
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

Depends on / 依赖: Nonempty, Nonempty.intro, _root_, _root_.ge_of_tendsto, eventually_ge_atTop, ge_of_tendsto
-/
theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β -> α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b <= a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

/--
theorem `Monotone.le_of_tendsto` / 定理 `Monotone.le_of_tendsto`

English:
theorem Monotone.le_of_tendsto
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: hf.dual.ge_of_tendsto ha b

中文:
定理 Monotone.le_of_tendsto
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: hf.dual.ge_of_tendsto ha b

Depends on / 依赖: ge_of_tendsto, hf.dual.ge_of_tendsto
-/
theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β -> α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a <= f b :=
  hf.dual.ge_of_tendsto ha b

/--
theorem `Antitone.le_of_tendsto` / 定理 `Antitone.le_of_tendsto`

English:
theorem Antitone.le_of_tendsto
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: hf.dual_right.ge_of_tendsto ha b

中文:
定理 Antitone.le_of_tendsto
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: hf.dual_right.ge_of_tendsto ha b

Depends on / 依赖: dual_right, ge_of_tendsto, hf.dual_right.ge_of_tendsto
-/
theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β -> α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a <= f b :=
  hf.dual_right.ge_of_tendsto ha b

/--
theorem `Antitone.ge_of_tendsto` / 定理 `Antitone.ge_of_tendsto`

English:
theorem Antitone.ge_of_tendsto
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: hf.dual_right.le_of_tendsto ha b

中文:
定理 Antitone.ge_of_tendsto
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: hf.dual_right.le_of_tendsto ha b

Depends on / 依赖: dual_right, hf.dual_right.le_of_tendsto, le_of_tendsto
-/
theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β -> α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b <= a :=
  hf.dual_right.le_of_tendsto ha b

/--
theorem `isLUB_of_tendsto_atTop` / 定理 `isLUB_of_tendsto_atTop`

English:
theorem isLUB_of_tendsto_atTop
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

中文:
定理 isLUB_of_tendsto_atTop
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

Depends on / 依赖: Set.mem_range_self, ge_of_tendsto, hf.ge_of_tendsto, le_of_tendsto, mem_range_self
-/
theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

/--
theorem `isGLB_of_tendsto_atBot` / 定理 `isGLB_of_tendsto_atBot`

English:
theorem isGLB_of_tendsto_atBot
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: isLUB_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) hf.dual ha

中文:
定理 isGLB_of_tendsto_atBot
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: isLUB_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) hf.dual ha

Depends on / 依赖: hf.dual, isLUB_of_tendsto_atTop
-/
theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a :=
  isLUB_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) hf.dual ha

/--
theorem `isLUB_of_tendsto_atBot` / 定理 `isLUB_of_tendsto_atBot`

English:
theorem isLUB_of_tendsto_atBot
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: isLUB_of_tendsto_atTop (α := α) (β := βᵒᵈ) hf.dual_left ha

中文:
定理 isLUB_of_tendsto_atBot
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: isLUB_of_tendsto_atTop (α := α) (β := βᵒᵈ) hf.dual_left ha

Depends on / 依赖: dual_left, hf.dual_left, isLUB_of_tendsto_atTop
-/
theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a :=
  isLUB_of_tendsto_atTop (α := α) (β := βᵒᵈ) hf.dual_left ha

/--
theorem `isGLB_of_tendsto_atTop` / 定理 `isGLB_of_tendsto_atTop`

English:
theorem isGLB_of_tendsto_atTop
  statement: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  proof: isGLB_of_tendsto_atBot (α := α) (β := βᵒᵈ) hf.dual_left ha

中文:
定理 isGLB_of_tendsto_atTop
  结论: [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
  证明: isGLB_of_tendsto_atBot (α := α) (β := βᵒᵈ) hf.dual_left ha

Depends on / 依赖: dual_left, hf.dual_left, isGLB_of_tendsto_atBot
-/
theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a :=
  isGLB_of_tendsto_atBot (α := α) (β := βᵒᵈ) hf.dual_left ha

/--
theorem `iSup_eq_of_tendsto` / 定理 `iSup_eq_of_tendsto`

English:
theorem iSup_eq_of_tendsto
  statement: {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
  proof: tendsto_nhds_unique (tendsto_atTop_iSup hf)

中文:
定理 iSup_eq_of_tendsto
  结论: {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
  证明: tendsto_nhds_unique (tendsto_atTop_iSup hf)

Depends on / 依赖: tendsto_atTop_iSup, tendsto_nhds_unique
-/
theorem iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β -> α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) -> iSup f = a :=
  tendsto_nhds_unique (tendsto_atTop_iSup hf)

/--
theorem `iInf_eq_of_tendsto` / 定理 `iInf_eq_of_tendsto`

English:
theorem iInf_eq_of_tendsto
  statement: {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
  proof: tendsto_nhds_unique (tendsto_atTop_iInf hf)

中文:
定理 iInf_eq_of_tendsto
  结论: {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
  证明: tendsto_nhds_unique (tendsto_atTop_iInf hf)

Depends on / 依赖: tendsto_atTop_iInf, tendsto_nhds_unique
-/
theorem iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β -> α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) -> iInf f = a :=
  tendsto_nhds_unique (tendsto_atTop_iInf hf)

/--
theorem `iSup_eq_iSup_subseq_of_monotone` / 定理 `iSup_eq_iSup_subseq_of_monotone`

English:
theorem iSup_eq_iSup_subseq_of_monotone
  statement: {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
  proof: le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i <= φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

中文:
定理 iSup_eq_iSup_subseq_of_monotone
  结论: {ι₁ ι₂ α : 类型} [Preorder ι₂] [CompleteLattice α]
  证明: le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i <= φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

Depends on / 依赖: Exists, Exists.imp, eventually, eventually_ge_atTop, iSup_mono, le_antisymm, le_rfl
-/
theorem iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i <= φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

/--
theorem `iSup_eq_iSup_subseq_of_antitone` / 定理 `iSup_eq_iSup_subseq_of_antitone`

English:
theorem iSup_eq_iSup_subseq_of_antitone
  statement: {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
  proof: le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j <= i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

中文:
定理 iSup_eq_iSup_subseq_of_antitone
  结论: {ι₁ ι₂ α : 类型} [Preorder ι₂] [CompleteLattice α]
  证明: le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j <= i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

Depends on / 依赖: Exists, Exists.imp, eventually, eventually_le_atBot, iSup_mono, le_antisymm, le_rfl
-/
theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j <= i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

/--
theorem `iInf_eq_iInf_subseq_of_monotone` / 定理 `iInf_eq_iInf_subseq_of_monotone`

English:
theorem iInf_eq_iInf_subseq_of_monotone
  statement: {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
  proof: iSup_eq_iSup_subseq_of_monotone hf.dual hφ

中文:
定理 iInf_eq_iInf_subseq_of_monotone
  结论: {ι₁ ι₂ α : 类型} [Preorder ι₂] [CompleteLattice α]
  证明: iSup_eq_iSup_subseq_of_monotone hf.dual hφ

Depends on / 依赖: hf.dual, iSup_eq_iSup_subseq_of_monotone
-/
theorem iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_monotone hf.dual hφ

/--
theorem `iInf_eq_iInf_subseq_of_antitone` / 定理 `iInf_eq_iInf_subseq_of_antitone`

English:
theorem iInf_eq_iInf_subseq_of_antitone
  statement: {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
  proof: iSup_eq_iSup_subseq_of_antitone hf.dual hφ

中文:
定理 iInf_eq_iInf_subseq_of_antitone
  结论: {ι₁ ι₂ α : 类型} [Preorder ι₂] [CompleteLattice α]
  证明: iSup_eq_iSup_subseq_of_antitone hf.dual hφ

Depends on / 依赖: hf.dual, iSup_eq_iSup_subseq_of_antitone
-/
theorem iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_antitone hf.dual hφ
