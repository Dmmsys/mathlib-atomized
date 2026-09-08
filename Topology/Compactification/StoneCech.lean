/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

For any topological space `α`, we build a compact Hausdorff space `StoneCech α` and a continuous
map `stoneCechUnit : α → StoneCech α` which is minimal in the sense of the following universal
property: for any compact Hausdorff space `β` and every map `f : α → β` such that
`hf : Continuous f`, there is a unique map `stoneCechExtend hf : StoneCech α → β` such that
`stoneCechExtend_extends : stoneCechExtend hf ∘ stoneCechUnit = f`.
Continuity of this extension is asserted by `continuous_stoneCechExtend` and uniqueness by
`stoneCech_hom_ext`.

Beware that the terminology “extend” is slightly misleading since `stoneCechUnit` is not always
injective, so one cannot always think of `α` as being “inside” its compactification `StoneCech α`.

## Implementation notes

Parts of the formalization are based on “Ultrafilters and Topology”
by Marius Stekelenburg, particularly section 5. However the construction in the general
case is different because the equivalence relation on spaces of ultrafilters described
by Stekelenburg causes issues with universes since it involves a condition
on all compact Hausdorff spaces. We replace it by a two steps construction.
The first step called `PreStoneCech` guarantees the expected universal property but
not the Hausdorff condition. We then define `StoneCech α` as `T2Quotient (PreStoneCech α)`.
-/

@[expose] public section


noncomputable section

open Filter Set

open Topology

universe u v

section Ultrafilter

/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/
/-- Basis for the topology on `Ultrafilter α`. -/
/-
**ultrafilterBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ultrafilterBasis (α : Type u) : Set (Set (Ultrafilter α))
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basis for the topology on `Ultrafilter α`.
-/
def ultrafilterBasis (α : Type u) : Set (Set (Ultrafilter α)) :=
  range fun s : Set α ↦ { u | s ∈ u }

variable {α : Type u}
/-
**Ultrafilter.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ultrafilter.topologicalSpace : TopologicalSpace (Ultrafilter α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Ultrafilter.topologicalSpace : TopologicalSpace (Ultrafilter α) :=
  TopologicalSpace.generateFrom (ultrafilterBasis α)
/-
**ultrafilterBasis_is_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ultrafilterBasis_is_basis : TopologicalSpace.IsTopologicalBasis (ultrafilt
erBasis α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.eq_univ_of_univ_subset`：∀ {α : Type u} {s : Set α}, Set.univ ⊆ s → s
 = Set.univ
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem ultrafilterBasis_is_basis : TopologicalSpace.IsTopologicalBasis (ultrafilterBasis α) :=
  ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine ⟨_, ⟨a ∩ b, rfl⟩, inter_mem ua ub, fun v hv ↦ ⟨?_, ?_⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right],
    eq_univ_of_univ_subset <| subset_sUnion_of_mem <| ⟨univ, eq_univ_of_forall fun _ ↦ univ_mem⟩,
    rfl⟩

/-- The basic open sets for the topology on ultrafilters are open. -/
/-
**ultrafilter_isOpen_basic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ultrafilter_isOpen_basic (s : Set α) : IsOpen { u : Ultrafilter α | s in u
 }
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `ultrafilterBasis_is_basis`：ultrafilterBasis_is_basis : TopologicalSpace.
IsTopologicalBasis (ultrafilterBasis α)

--- 原说明 ---
The basic open sets for the topology on ultrafilters are open.
-/
theorem ultrafilter_isOpen_basic (s : Set α) : IsOpen { u : Ultrafilter α | s ∈ u } :=
  ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩

/-- The basic open sets for the topology on ultrafilters are also closed. -/
/-
**ultrafilter_isClosed_basic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ultrafilter_isClosed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s 
in u }
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
· 使用定理 `ultrafilter_isOpen_basic`：ultrafilter_isOpen_basic (s : Set α) : IsOpen 
{ u : Ultrafilter α | s in u }

--- 原说明 ---
The basic open sets for the topology on ultrafilters are also closed.
-/
theorem ultrafilter_isClosed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s ∈ u } := by
  rw [← isOpen_compl_iff]
  convert! ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_notMem.symm

/-- Every ultrafilter `u` on `Ultrafilter α` converges to a unique
  point of `Ultrafilter α`, namely `joinM u`. -/
/-
**ultrafilter_converges_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilt
er α} : ↑u <= 𝓝 x ↔ x = joinM u
参数：Ultrafilter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ultrafilter.coe_le_coe`：coe_le_coe {f g : Ultrafilter α} : (f : Filter α
) <= g ↔ f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Every ultrafilter `u` on `Ultrafilter α` converges to a unique
  point of `Ultrafilter α`, namely `joinM u`.
-/
theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} :
    ↑u ≤ 𝓝 x ↔ x = joinM u := by
  rw [eq_comm, ← Ultrafilter.coe_le_coe]
  change ↑u ≤ 𝓝 x ↔ ∀ s ∈ x, { v : Ultrafilter α | s ∈ v } ∈ u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_ofPred_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · rintro h a ⟨xi, a, rfl⟩
    exact h _ xi
/-
**ultrafilter_compact** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ultrafilter_compact : CompactSpace (Ultrafilter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_ultrafilter_le_nhds`：isCompact_iff_ultrafilter_le_nhds : I
sCompact s ↔ forall f : Ultrafilter X, ↑f <= 𝓟 s -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `trivial`：True
· 使用定理 `ultrafilter_converges_iff`：ultrafilter_converges_iff {u : Ultrafilter (U
ltrafilter α)} {x : Ultrafilter α} : ↑u <= 𝓝 x ↔ x = joinM u
-/
instance ultrafilter_compact : CompactSpace (Ultrafilter α) :=
  ⟨isCompact_iff_ultrafilter_le_nhds.mpr fun f _ ↦
      ⟨joinM f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩
/-
**Ultrafilter.t2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ultrafilter.t2Space : T2Space (Ultrafilter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t2_iff_ultrafilter`：t2_iff_ultrafilter : T2Space X ↔ forall {x y : X} (f
 : Ultrafilter X), ↑f <= 𝓝 x -> ↑f <= 𝓝 y -> x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ultrafilter_converges_iff`：ultrafilter_converges_iff {u : Ultrafilter (U
ltrafilter α)} {x : Ultrafilter α} : ↑u <= 𝓝 x ↔ x = joinM u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance Ultrafilter.t2Space : T2Space (Ultrafilter α) :=
  t2_iff_ultrafilter.mpr fun {x y} f fx fy ↦
    have hx : x = joinM f := ultrafilter_converges_iff.mp fx
    have hy : y = joinM f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TotallyDisconnectedSpace (Ultrafilter α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connectedComponent, true_and]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter] at hB
  let Z := { F : Ultrafilter α | s ∈ F }
  have hZ : IsClopen Z := ⟨ultrafilter_isClosed_basic s, ultrafilter_isOpen_basic s⟩
  exact hB ⟨Z, hZ, hs⟩
/-
**Ultrafilter.tendsto_pure_self** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：∀ {α : Type u} (b : Ultrafilter α), Filter.Tendsto pure (↑b) (nhds b)
参数：b : Ultrafilter α；↑b；nhds b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ultrafilter.coe_map`：coe_map (m : α -> β) (f : Ultrafilter α) : (map m f
 : Filter β) = Filter.map m ↑f
· 使用定理 `ultrafilter_converges_iff`：ultrafilter_converges_iff {u : Ultrafilter (U
ltrafilter α)} {x : Ultrafilter α} : ↑u <= 𝓝 x ↔ x = joinM u
· 使用定理 `Ultrafilter.ext`：ext ⦃f g : Ultrafilter α⦄ (h : forall s, s in f ↔ s in 
g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem Ultrafilter.tendsto_pure_self (b : Ultrafilter α) : Tendsto pure b (𝓝 b) := by
  rw [Tendsto, ← coe_map, ultrafilter_converges_iff]
  ext s
  change s ∈ b ↔ {t | s ∈ t} ∈ map pure b
  simp_rw [mem_map, preimage_ofPred_eq, mem_pure, ofPred_mem_eq]
/-
**ultrafilter_comap_pure_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ultrafilter_comap_pure_nhds (b : Ultrafilter α) : comap pure (𝓝 b) <= b
参数：b : Ultrafilter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem ultrafilter_comap_pure_nhds (b : Ultrafilter α) : comap pure (𝓝 b) ≤ b := by
  rw [TopologicalSpace.nhds_generateFrom]
  simp only [comap_iInf, comap_principal]
  intro s hs
  rw [← le_principal_iff]
  refine iInf_le_of_le { u | s ∈ u } ?_
  refine iInf_le_of_le ⟨hs, ⟨s, rfl⟩⟩ ?_
  exact principal_mono.2 fun _ ↦ id

section Embedding

open TopologicalSpace

/-- The range of `pure : α → Ultrafilter α` is dense in `Ultrafilter α`. -/
/-
**denseRange_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_pure : DenseRange (pure : α -> Ultrafilter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_ultrafilter`：mem_closure_iff_ultrafilter : x in closure 
s ↔ exists u : Ultrafilter X, s in u ∧ ↑u <= 𝓝 x
· 使用定理 `Filter.range_mem_map`：range_mem_map : range m in map m f
· 使用定理 `ultrafilter_converges_iff`：ultrafilter_converges_iff {u : Ultrafilter (U
ltrafilter α)} {x : Ultrafilter α} : ↑u <= 𝓝 x ↔ x = joinM u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x

--- 原说明 ---
The range of `pure : α → Ultrafilter α` is dense in `Ultrafilter α`.
-/
theorem denseRange_pure : DenseRange (pure : α → Ultrafilter α) :=
  fun x ↦ mem_closure_iff_ultrafilter.mpr
    ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩

/-- The map `pure : α → Ultrafilter α` induces on `α` the discrete topology. -/
/-
**induced_topology_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_topology_pure : TopologicalSpace.induced (pure : α -> Ultrafilter 
α) Ultrafilter.topologicalSpace = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_of_singletons_open`：eq_bot_of_singletons_open {t : TopologicalSpa
ce α} (h : forall x, IsOpen[t] {x}) : t = ⊥
· 使用定理 `ultrafilter_isOpen_basic`：ultrafilter_isOpen_basic (s : Set α) : IsOpen 
{ u : Ultrafilter α | s in u }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The map `pure : α → Ultrafilter α` induces on `α` the discrete topology.
-/
theorem induced_topology_pure :
    TopologicalSpace.induced (pure : α → Ultrafilter α) Ultrafilter.topologicalSpace = ⊥ := by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} ∈ u }, ultrafilter_isOpen_basic _
  simp

/-- `pure : α → Ultrafilter α` defines a dense inducing of `α` in `Ultrafilter α`. -/
/-
**isDenseInducing_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (pure : α -> Ultrafilter α
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `induced_topology_pure`：induced_topology_pure : TopologicalSpace.induced 
(pure : α -> Ultrafilter α) Ultrafilter.topologicalSpace = ⊥
· 使用定理 `denseRange_pure`：denseRange_pure : DenseRange (pure : α -> Ultrafilter α
)

--- 原说明 ---
`pure : α → Ultrafilter α` defines a dense inducing of `α` in `Ultrafilter α`.
-/
theorem isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (pure : α → Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  ⟨⟨induced_topology_pure.symm⟩, denseRange_pure⟩

-- The following refined version will never be used
/-- `pure : α → Ultrafilter α` defines a dense embedding of `α` in `Ultrafilter α`. -/
/-
**isDenseEmbedding_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDenseEmbedding_pure : @IsDenseEmbedding _ _ ⊥ _ (pure : α -> Ultrafilter
 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isDenseInducing_pure`：isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (p
ure : α -> Ultrafilter α)
· 使用定理 `Ultrafilter.pure_injective`：pure_injective : Injective (pure : α -> Ultr
afilter α)

--- 原说明 ---
`pure : α → Ultrafilter α` defines a dense embedding of `α` in `Ultrafilter α`.
-/
theorem isDenseEmbedding_pure : @IsDenseEmbedding _ _ ⊥ _ (pure : α → Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  { isDenseInducing_pure with injective := Ultrafilter.pure_injective }

end Embedding

section Extension

/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `Ultrafilter α → γ`. We
  already know it must be unique because `α → Ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `IsDenseInducing.continuous_extend`. -/
variable {γ : Type*} [TopologicalSpace γ]

/-- The extension of a function `α → γ` to a function `Ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
/-
**Ultrafilter.extend** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ultrafilter.extend (f : α -> γ) : Ultrafilter α -> γ
参数：f : α -> γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isDenseInducing_pure`：isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (p
ure : α -> Ultrafilter α)

--- 原说明 ---
The extension of a function `α → γ` to a function `Ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous.
-/
def Ultrafilter.extend (f : α → γ) : Ultrafilter α → γ :=
  letI : TopologicalSpace α := ⊥
  isDenseInducing_pure.extend f

variable [T2Space γ]

@[simp]
/-
**ultrafilter_extend_extends** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ultrafilter_extend_extends (f : α -> γ) : Ultrafilter.extend f ∘ pure = f
参数：f : α -> γ。
该定理/引理给出了一组等式。
继承自：(f : α -> γ) : Ultrafilter.extend f ∘ pure = f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsDenseInducing.extend_eq`：extend_eq [T2Space γ] (di : IsDenseInducing i
) {f : α -> γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a
· 使用定理 `isDenseInducing_pure`：isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (p
ure : α -> Ultrafilter α)
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
-/
lemma ultrafilter_extend_extends (f : α → γ) : Ultrafilter.extend f ∘ pure = f := by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  exact funext (isDenseInducing_pure.extend_eq continuous_of_discreteTopology)

@[simp]
/-
**ultrafilter_extend_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ultrafilter_extend_pure (f : α -> γ) (a : α) : Ultrafilter.extend f (pure 
a) = f a
参数：f : α -> γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `ultrafilter_extend_extends`：ultrafilter_extend_extends (f : α -> γ) : Ul
trafilter.extend f ∘ pure = f
-/
lemma ultrafilter_extend_pure (f : α → γ) (a : α) : Ultrafilter.extend f (pure a) = f a :=
  congr_fun (ultrafilter_extend_extends f) a

variable [CompactSpace γ]
/-
**continuous_ultrafilter_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_ultrafilter_extend (f : α -> γ) : Continuous (Ultrafilter.exten
d f)
参数：f : α -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.ultrafilter_le_nhds`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), ↑f ≤ Filter.principal s → 
∃ x ∈ s, ↑f ≤ nhds …
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `ultrafilter_comap_pure_nhds`：ultrafilter_comap_pure_nhds (b : Ultrafilte
r α) : comap pure (𝓝 b) <= b
· 使用定理 `IsDenseInducing.continuous_extend`：continuous_extend [T3Space γ] {f : α 
-> γ} (di : IsDenseInducing i) (hf : forall b, exists c, Tendsto f (comap i (𝓝 b
)) (𝓝 c)) : Continuous …
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `isDenseInducing_pure`：isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (p
ure : α -> Ultrafilter α)
-/
theorem continuous_ultrafilter_extend (f : α → γ) : Continuous (Ultrafilter.extend f) := by
  have h (b : Ultrafilter α) : ∃ c, Tendsto f (comap pure (𝓝 b)) (𝓝 c) :=
    -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
    let ⟨c, _, h'⟩ :=
      isCompact_univ.ultrafilter_le_nhds (b.map f) (by rw [le_principal_iff]; exact univ_mem)
    ⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h'⟩
  let _ : TopologicalSpace α := ⊥
  exact isDenseInducing_pure.continuous_extend h

/-- The value of `Ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
/-
**ultrafilter_extend_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ultrafilter_extend_eq_iff {f : α -> γ} {b : Ultrafilter α} {c : γ} : Ultra
filter.extend f b = c ↔ ↑(b.map f) <= 𝓝 c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ultrafilter_converges_iff`：ultrafilter_converges_iff {u : Ultrafilter (U
ltrafilter α)} {x : Ultrafilter α} : ↑u <= 𝓝 x ↔ x = joinM u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_ultrafilter_extend`：continuous_ultrafilter_extend (f : α -> γ
) : Continuous (Ultrafilter.extend f)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `ultrafilter_extend_extends`：ultrafilter_extend_extends (f : α -> γ) : Ul
trafilter.extend f ∘ pure = f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `IsDenseInducing.extend_eq_of_tendsto`：extend_eq_of_tendsto [T2Space γ] (
di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ} (hf : Tendsto f (comap i (𝓝
 b)) (𝓝 c)) : di.extend f …
· 使用定理 `isDenseInducing_pure`：isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (p
ure : α -> Ultrafilter α)
· 使用定理 `ultrafilter_comap_pure_nhds`：ultrafilter_comap_pure_nhds (b : Ultrafilte
r α) : comap pure (𝓝 b) <= b

--- 原说明 ---
The value of `Ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`.
-/
theorem ultrafilter_extend_eq_iff {f : α → γ} {b : Ultrafilter α} {c : γ} :
    Ultrafilter.extend f b = c ↔ ↑(b.map f) ≤ 𝓝 c :=
  ⟨fun h ↦ by
     -- Write b as an ultrafilter limit of pure ultrafilters, and use
     -- the facts that ultrafilter.extend is a continuous extension of f.
     let b' : Ultrafilter (Ultrafilter α) := b.map pure
     have t : ↑b' ≤ 𝓝 b := ultrafilter_converges_iff.mpr (bind_pure _).symm
     rw [← h]
     have := (continuous_ultrafilter_extend f).tendsto b
     refine le_trans ?_ (le_trans (map_mono t) this)
     change _ ≤ map (Ultrafilter.extend f ∘ pure) ↑b
     rw [ultrafilter_extend_extends]
     exact le_rfl,
   fun h ↦
    let _ : TopologicalSpace α := ⊥
    isDenseInducing_pure.extend_eq_of_tendsto
      (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩

end Extension

end Ultrafilter

section PreStoneCech

variable (α : Type u) [TopologicalSpace α]

/-- Auxiliary construction towards the Stone-Čech compactification of a topological space.
It should not be used after the Stone-Čech compactification is constructed. -/
/-
**PreStoneCech** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PreStoneCech : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction towards the Stone-Čech compactification of a topological 
space.
It should not be used after the Stone-Čech compactification is constructed.
-/
def PreStoneCech : Type u :=
  Quot fun F G : Ultrafilter α ↦ ∃ x, (F : Filter α) ≤ 𝓝 x ∧ (G : Filter α) ≤ 𝓝 x

variable {α}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (PreStoneCech α) :=
  inferInstanceAs (TopologicalSpace <| Quot _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactSpace (PreStoneCech α) :=
  Quot.compactSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (PreStoneCech α) :=
  inferInstanceAs (Inhabited <| Quot _)

/-- The natural map from α to its pre-Stone-Čech compactification. -/
/-
**preStoneCechUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preStoneCechUnit (x : α) : PreStoneCech α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from α to its pre-Stone-Čech compactification.
-/
def preStoneCechUnit (x : α) : PreStoneCech α :=
  Quot.mk _ (pure x : Ultrafilter α)

set_option backward.isDefEq.respectTransparency false in
/-
**continuous_preStoneCechUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_preStoneCechUnit : Continuous (preStoneCechUnit : α -> PreStone
Cech α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_ultrafilter`：continuous_iff_ultrafilter : Continuous f ↔ 
forall (x) (g : Ultrafilter X), ↑g <= 𝓝 x -> Tendsto f g (𝓝 (f x))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ultrafilter_converges_iff`：ultrafilter_converges_iff {u : Ultrafilter (U
ltrafilter α)} {x : Ultrafilter α} : ↑u <= 𝓝 x ↔ x = joinM u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem continuous_preStoneCechUnit : Continuous (preStoneCechUnit : α → PreStoneCech α) :=
  continuous_iff_ultrafilter.mpr fun x g gx ↦ by
    have : (g.map pure).toFilter ≤ 𝓝 g := by
      rw [ultrafilter_converges_iff, ← bind_pure g]
      rfl
    have : (map preStoneCechUnit g : Filter (PreStoneCech α)) ≤ 𝓝 (Quot.mk _ g) :=
      (map_mono this).trans (continuous_quot_mk.tendsto _)
    convert! this
    exact Quot.sound ⟨x, pure_le_nhds x, gx⟩
/-
**denseRange_preStoneCechUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_preStoneCechUnit : DenseRange (preStoneCechUnit : α -> PreStone
Cech α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `denseRange_pure`：denseRange_pure : DenseRange (pure : α -> Ultrafilter α
)
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
theorem denseRange_preStoneCechUnit : DenseRange (preStoneCechUnit : α → PreStoneCech α) :=
  Quot.mk_surjective.denseRange.comp denseRange_pure continuous_coinduced_rng


section Extension
variable {β : Type v} [TopologicalSpace β] [T2Space β]

/-
**preStoneCech_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preStoneCech_hom_ext {g₁ g₂ : PreStoneCech α -> β} (h₁ : Continuous g₁) (h
₂ : Continuous g₂) (h : g₁ ∘ preStoneCechUnit = g₂ ∘ preStoneCechUnit) : g₁ = g₂
参数：h₁ : Continuous g₁；h₂ : Continuous g₂；h : g₁ ∘ preStoneCechUnit = g₂ ∘ preSto
neCechUnit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.ext_on`：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense
 s) {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f 
= g
· 使用定理 `denseRange_preStoneCechUnit`：denseRange_preStoneCechUnit : DenseRange (p
reStoneCechUnit : α -> PreStoneCech α)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem preStoneCech_hom_ext {g₁ g₂ : PreStoneCech α → β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ preStoneCechUnit = g₂ ∘ preStoneCechUnit) : g₁ = g₂ := by
  apply Continuous.ext_on denseRange_preStoneCechUnit h₁ h₂
  rintro x ⟨x, rfl⟩
  apply congr_fun h x

variable [CompactSpace β]
variable {g : α → β} (hg : Continuous g)
include hg
/-
**preStoneCechCompat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preStoneCechCompat {F G : Ultrafilter α} {x : α} (hF : ↑F <= 𝓝 x) (hG : ↑G
 <= 𝓝 x) : Ultrafilter.extend g F = Ultrafilter.extend g G
参数：hF : ↑F <= 𝓝 x；hG : ↑G <= 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ultrafilter_extend_eq_iff`：ultrafilter_extend_eq_iff {f : α -> γ} {b : U
ltrafilter α} {c : γ} : Ultrafilter.extend f b = c ↔ ↑(b.map f) <= 𝓝 c
· 使用定理 `Ultrafilter.coe_map`：coe_map (m : α -> β) (f : Ultrafilter α) : (map m f
 : Filter β) = Filter.map m ↑f
-/
lemma preStoneCechCompat {F G : Ultrafilter α} {x : α} (hF : ↑F ≤ 𝓝 x) (hG : ↑G ≤ 𝓝 x) :
    Ultrafilter.extend g F = Ultrafilter.extend g G := by
  replace hF := (map_mono hF).trans hg.continuousAt
  replace hG := (map_mono hG).trans hg.continuousAt
  rwa [show Ultrafilter.extend g G = g x by rwa [ultrafilter_extend_eq_iff, G.coe_map],
       ultrafilter_extend_eq_iff, F.coe_map]

/-- The extension of a continuous function from `α` to a compact
  Hausdorff space `β` to the pre-Stone-Čech compactification of `α`. -/
/-
**preStoneCechExtend** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preStoneCechExtend : PreStoneCech α -> β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of a continuous function from `α` to a compact
  Hausdorff space `β` to the pre-Stone-Čech compactification of `α`.
-/
def preStoneCechExtend : PreStoneCech α → β :=
  Quot.lift (Ultrafilter.extend g) fun _ _ ⟨_, hF, hG⟩ ↦ preStoneCechCompat hg hF hG

@[simp]
/-
**preStoneCechExtend_extends** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preStoneCechExtend_extends : preStoneCechExtend hg ∘ preStoneCechUnit = g
该定理/引理给出了一组等式。
继承自：: preStoneCechExtend hg ∘ preStoneCechUnit = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ultrafilter_extend_extends`：ultrafilter_extend_extends (f : α -> γ) : Ul
trafilter.extend f ∘ pure = f
-/
lemma preStoneCechExtend_extends : preStoneCechExtend hg ∘ preStoneCechUnit = g :=
  ultrafilter_extend_extends g

@[simp]
/-
**preStoneCechExtend_preStoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preStoneCechExtend_preStoneCechUnit (a : α) : preStoneCechExtend hg (preSt
oneCechUnit a) = g a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `preStoneCechExtend_extends`：preStoneCechExtend_extends : preStoneCechExt
end hg ∘ preStoneCechUnit = g
-/
lemma preStoneCechExtend_preStoneCechUnit (a : α) :
    preStoneCechExtend hg (preStoneCechUnit a) = g a :=
  congr_fun (preStoneCechExtend_extends hg) a

set_option backward.isDefEq.respectTransparency false in
/-
**eq_if_preStoneCechUnit_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_if_preStoneCechUnit_eq {a b : α} (h : preStoneCechUnit a = preStoneCech
Unit b) : g a = g b
参数：h : preStoneCechUnit a = preStoneCechUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ultrafilter_extend_extends`：ultrafilter_extend_extends (f : α -> γ) : Ul
trafilter.extend f ∘ pure = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `preStoneCechCompat`：preStoneCechCompat {F G : Ultrafilter α} {x : α} (hF
 : ↑F <= 𝓝 x) (hG : ↑G <= 𝓝 x) : Ultrafilter.extend g F = Ultrafilter.extend g G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
· 使用定理 `preStoneCechUnit.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (x : α
),   preStoneCechUnit x = Quot.mk (fun F G => ∃ x, ↑F ≤ nhds x ∧ ↑G ≤ nhds x) (p
ure x)
-/
lemma eq_if_preStoneCechUnit_eq {a b : α} (h : preStoneCechUnit a = preStoneCechUnit b) :
    g a = g b := by
  have e := ultrafilter_extend_extends g
  rw [← congrFun e a, ← congrFun e b, Function.comp_apply, Function.comp_apply]
  rw [preStoneCechUnit, preStoneCechUnit, Quot.eq] at h
  generalize (pure a : Ultrafilter α) = F at h
  generalize (pure b : Ultrafilter α) = G at h
  induction h with
  | rel x y a => exact let ⟨a, hx, hy⟩ := a; preStoneCechCompat hg hx hy
  | refl x => rfl
  | symm x y _ h => rw [h]
  | trans x y z _ _ h h' => exact h.trans h'
/-
**continuous_preStoneCechExtend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_preStoneCechExtend : Continuous (preStoneCechExtend hg)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quot_lift`：continuous_quot_lift {f : X -> Y} (hr : forall a b
, r a b -> f a = f b) (h : Continuous f) : Continuous (Quot.lift f hr : Quot r -
> Y)
· 使用定理 `continuous_ultrafilter_extend`：continuous_ultrafilter_extend (f : α -> γ
) : Continuous (Ultrafilter.extend f)
-/
theorem continuous_preStoneCechExtend : Continuous (preStoneCechExtend hg) :=
  continuous_quot_lift _ (continuous_ultrafilter_extend g)

end Extension

end PreStoneCech

section StoneCech

variable (α : Type u) [TopologicalSpace α]

/-- The Stone-Čech compactification of a topological space. -/
/-
**StoneCech** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StoneCech : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Stone-Čech compactification of a topological space.
-/
def StoneCech : Type u :=
  T2Quotient (PreStoneCech α)

variable {α}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (StoneCech α) :=
  inferInstanceAs <| TopologicalSpace <| T2Quotient _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T2Space (StoneCech α) :=
  inferInstanceAs <| T2Space <| T2Quotient _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactSpace (StoneCech α) :=
  Quot.compactSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (StoneCech α) :=
  inferInstanceAs <| Inhabited <| Quotient _

/-- The natural map from α to its Stone-Čech compactification. -/
/-
**stoneCechUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stoneCechUnit (x : α) : StoneCech α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from α to its Stone-Čech compactification.
-/
def stoneCechUnit (x : α) : StoneCech α :=
  T2Quotient.mk (preStoneCechUnit x)
/-
**continuous_stoneCechUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_stoneCechUnit : Continuous (stoneCechUnit : α -> StoneCech α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `T2Quotient.continuous_mk`：continuous_mk : Continuous (mk : X -> T2Quotie
nt X)
· 使用定理 `continuous_preStoneCechUnit`：continuous_preStoneCechUnit : Continuous (p
reStoneCechUnit : α -> PreStoneCech α)
-/
theorem continuous_stoneCechUnit : Continuous (stoneCechUnit : α → StoneCech α) :=
  (T2Quotient.continuous_mk _).comp continuous_preStoneCechUnit

/-- The image of `stoneCechUnit` is dense. (But `stoneCechUnit` need
  not be an embedding, for example if the original space is not Hausdorff.) -/
/-
**denseRange_stoneCechUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_stoneCechUnit : DenseRange (stoneCechUnit : α -> StoneCech α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `denseRange_preStoneCechUnit`：denseRange_preStoneCechUnit : DenseRange (p
reStoneCechUnit : α -> PreStoneCech α)
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f

--- 原说明 ---
The image of `stoneCechUnit` is dense. (But `stoneCechUnit` need
  not be an embedding, for example if the original space is not Hausdorff.)
-/
theorem denseRange_stoneCechUnit : DenseRange (stoneCechUnit : α → StoneCech α) := by
  unfold stoneCechUnit T2Quotient.mk
  have : Function.Surjective (T2Quotient.mk : PreStoneCech α → StoneCech α) := by
    exact Quot.mk_surjective
  exact this.denseRange.comp denseRange_preStoneCechUnit continuous_coinduced_rng

section Extension

variable {β : Type v} [TopologicalSpace β] [T2Space β]
variable {g : α → β} (hg : Continuous g)

/-
**stoneCech_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stoneCech_hom_ext {g₁ g₂ : StoneCech α -> β} (h₁ : Continuous g₁) (h₂ : Co
ntinuous g₂) (h : g₁ ∘ stoneCechUnit = g₂ ∘ stoneCechUnit) : g₁ = g₂
参数：h₁ : Continuous g₁；h₂ : Continuous g₂；h : g₁ ∘ stoneCechUnit = g₂ ∘ stoneCech
Unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.ext_on`：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense
 s) {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f 
= g
· 使用定理 `denseRange_stoneCechUnit`：denseRange_stoneCechUnit : DenseRange (stoneCe
chUnit : α -> StoneCech α)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem stoneCech_hom_ext {g₁ g₂ : StoneCech α → β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ stoneCechUnit = g₂ ∘ stoneCechUnit) : g₁ = g₂ := by
  apply h₁.ext_on denseRange_stoneCechUnit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

variable [CompactSpace β]

/-- The extension of a continuous function from `α` to a compact
  Hausdorff space `β` to the Stone-Čech compactification of `α`.
  This extension implements the universal property of this compactification. -/
/-
**stoneCechExtend** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stoneCechExtend : StoneCech α -> β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_preStoneCechExtend`：continuous_preStoneCechExtend : Continuou
s (preStoneCechExtend hg)

--- 原说明 ---
The extension of a continuous function from `α` to a compact
  Hausdorff space `β` to the Stone-Čech compactification of `α`.
  This extension implements the universal property of this compactification.
-/
def stoneCechExtend : StoneCech α → β :=
  T2Quotient.lift (continuous_preStoneCechExtend hg)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**stoneCechExtend_extends** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stoneCechExtend_extends : stoneCechExtend hg ∘ stoneCechUnit = g
该定理/引理给出了一组等式。
继承自：: stoneCechExtend hg ∘ stoneCechUnit = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `continuous_preStoneCechExtend`：continuous_preStoneCechExtend : Continuou
s (preStoneCechExtend hg)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `stoneCechExtend.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] {β : Ty
pe v} [inst_1 : TopologicalSpace β] [inst_2 : T2Space β] {g : α → β}   (hg : Con
tinuous g)…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `stoneCechUnit.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (x : α), 
stoneCechUnit x = T2Quotient.mk (preStoneCechUnit x)
· 使用引理 `T2Quotient.lift_mk`：lift_mk {X Y : Type*} [TopologicalSpace X] [Topologi
calSpace Y] [T2Space Y] {f : X -> Y} (hf : Continuous f) (x : X) : lift hf (mk x
) = f x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `preStoneCechExtend_extends`：preStoneCechExtend_extends : preStoneCechExt
end hg ∘ preStoneCechUnit = g
-/
lemma stoneCechExtend_extends : stoneCechExtend hg ∘ stoneCechUnit = g := by
  ext x
  rw [stoneCechExtend, Function.comp_apply, stoneCechUnit, T2Quotient.lift_mk]
  apply congrFun (preStoneCechExtend_extends hg)

@[simp]
/-
**stoneCechExtend_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stoneCechExtend_stoneCechUnit (a : α) : stoneCechExtend hg (stoneCechUnit 
a) = g a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `stoneCechExtend_extends`：stoneCechExtend_extends : stoneCechExtend hg ∘ 
stoneCechUnit = g
-/
lemma stoneCechExtend_stoneCechUnit (a : α) : stoneCechExtend hg (stoneCechUnit a) = g a :=
  congr_fun (stoneCechExtend_extends hg) a
/-
**continuous_stoneCechExtend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_stoneCechExtend : Continuous (stoneCechExtend hg)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `continuous_preStoneCechExtend`：continuous_preStoneCechExtend : Continuou
s (preStoneCechExtend hg)
-/
theorem continuous_stoneCechExtend : Continuous (stoneCechExtend hg) :=
  continuous_coinduced_dom.mpr (continuous_preStoneCechExtend hg)
/-
**eq_if_stoneCechUnit_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_if_stoneCechUnit_eq {a b : α} {f : α -> β} (hcf : Continuous f) (h : st
oneCechUnit a = stoneCechUnit b) : f a = f b
参数：hcf : Continuous f；h : stoneCechUnit a = stoneCechUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `stoneCechExtend_extends`：stoneCechExtend_extends : stoneCechExtend hg ∘ 
stoneCechUnit = g
-/
lemma eq_if_stoneCechUnit_eq {a b : α} {f : α → β} (hcf : Continuous f)
    (h : stoneCechUnit a = stoneCechUnit b) : f a = f b := by
  rw [← congrFun (stoneCechExtend_extends hcf), ← congrFun (stoneCechExtend_extends hcf)]
  exact congrArg (stoneCechExtend hcf) h

end Extension

end StoneCech

