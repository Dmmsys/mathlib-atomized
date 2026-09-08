/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Discreteness of subgroups in archimedean ordered groups

This file contains some supplements to the results in
`Mathlib/Topology/Algebra/Order/Archimedean.lean`, involving discreteness of subgroups, which
require heavier imports.
-/

public section

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [TopologicalSpace G] [OrderTopology G]

/-- In a linearly ordered group with the order topology, the powers of a single element form a
discrete subgroup. -/
@[to_additive /-- In a linearly ordered additive group with the order topology, the multiples of a
single element form a discrete subgroup. -/]
/-
**Subgroup.instDiscreteTopologyZMultiples** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instDiscreteTopologyZMultiples (g : G) : DiscreteTopology (zpowers g)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.zpowers_one_eq_bot`：zpowers_one_eq_bot : Subgroup.zpowers (1 : 
G) = ⊥
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `discreteTopology_iff_isOpen_singleton_one`：discreteTopology_iff_isOpen_s
ingleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Subgroup.instIsTopologicalGroupSubtypeMem`：∀ {G : Type w} [inst : Topolo
gicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S : Subgroup G),   IsTo
pologicalGroup ↥S
· 使用定理 `LinearOrderedCommGroup.toIsTopologicalGroup`：∀ {G : Type u_1} [inst : To
pologicalSpace G] [inst_1 : CommGroup G] [inst_2 : LinearOrder G] [IsOrderedMono
id G]   [OrderTopology G], IsTopo…
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `zpow_lt_zpow_iff_right`：zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a 
^ n ↔ m < n
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
（共 37 条，此处仅展示前 30 条）
-/
instance instDiscreteTopologyZMultiples (g : G) : DiscreteTopology (zpowers g) := by
  wlog ha : 1 ≤ g
  · specialize this g⁻¹ (one_le_inv'.mpr (le_of_not_ge ha))
    rwa [zpowers_inv] at this
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [zpowers_one_eq_bot]
    exact Subsingleton.discreteTopology
  rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff]
  refine ⟨Set.Ioo (g ^ (-1 : ℤ)) (g ^ (1 : ℤ)), isOpen_Ioo, ?_⟩
  ext ⟨_, ⟨n, rfl⟩⟩
  constructor
  · simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
    intro hn hn'
    rw [zpow_lt_zpow_iff_right ha] at hn hn'
    simp only [Subtype.ext_iff, show n = 0 by lia, zpow_zero, coe_one]
  · simp_all

variable [MulArchimedean G]

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology G] : IsCyclic G := by
  nontriviality G
  exact LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr fun h ↦
    have := h.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G

/-- In an Archimedean linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
@[to_additive /-- In an Archimedean linearly ordered additive group (with the order topology), a
subgroup is discrete iff it is cyclic. -/]
/-
**Subgroup.discrete_iff_cyclic** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：discrete_iff_cyclic {H : Subgroup G} : IsCyclic H ↔ DiscreteTopology H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Subgroup.isCyclic_iff_exists_zpowers_eq_top`：∀ {α : Type u_1} [inst : Gr
oup α] (H : Subgroup α), IsCyclic ↥H ↔ ∃ g, Subgroup.zpowers g = H
· 使用定理 `Subgroup.dense_or_cyclic`：dense_or_cyclic (S : Subgroup G) : Dense (S : 
Set G) ∨ exists a : G, S = closure {a}
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.discreteTopology_iff`：discreteTopology_iff (h : X ≃ₜ Y) : Dis
creteTopology X ↔ DiscreteTopology Y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCyclic_iff_exists_zpowers_eq_top`：isCyclic_iff_exists_zpowers_eq_top [
Group α] : IsCyclic α ↔ exists g : α, zpowers g = ⊤
· 使用定理 `Subgroup.instIsCyclicOfDiscreteTopology`：∀ {G : Type u_1} [inst : CommGr
oup G] [inst_1 : LinearOrder G] [IsOrderedMonoid G] [inst_3 : TopologicalSpace G
]   [OrderTopology G] [MulArc…
· 使用定理 `Subgroup.coe_eq_univ`：coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.u
niv ↔ H = ⊤
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `LinearOrderedCommGroup.toIsTopologicalGroup`：∀ {G : Type u_1} [inst : To
pologicalSpace G] [inst_1 : CommGroup G] [inst_2 : LinearOrder G] [IsOrderedMono
id G]   [OrderTopology G], IsTopo…
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
lemma discrete_iff_cyclic {H : Subgroup G} : IsCyclic H ↔ DiscreteTopology H := by
  nontriviality G using isCyclic_of_subsingleton, Subsingleton.discreteTopology
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← Subgroup.zpowers_eq_closure, Eq.comm (a := H)] at this
    refine fun hA ↦ this.elim (fun h ↦ ?_) id
    -- remains to show a contradiction assuming `H` is both dense and discrete
    obtain rfl : H = ⊤ := by
      rw [← coe_eq_univ, ← (dense_iff_closure_eq.mp h), H.isClosed_of_discrete.closure_eq]
    have : DiscreteTopology G := by rwa [← (Homeomorph.Set.univ G).discreteTopology_iff]
    exact isCyclic_iff_exists_zpowers_eq_top.mp inferInstance

end Subgroup

