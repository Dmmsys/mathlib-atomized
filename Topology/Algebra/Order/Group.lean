/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Topology on a linear ordered commutative group

In this file we prove that a linear ordered commutative group with order topology
is a topological group.
We also prove continuity of `abs : G → G` and provide convenience lemmas like `ContinuousAt.abs`.
-/

public section


open Set Filter Function

open scoped Topology

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [OrderTopology G]

-- see Note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrderedCommGroup.toIsTopologicalGroup :
    IsTopologicalGroup G where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, Prod.forall, ContinuousAt,
      LinearOrderedCommGroup.tendsto_nhds]
    intro a b ε hε
    rcases dense_or_discrete 1 ε with ⟨δ, hδ₁, hδε⟩ | ⟨-, hε_min⟩
    · filter_upwards [(eventually_mabs_div_lt _ hδ₁).prod_nhds
        (eventually_mabs_div_lt _ (one_lt_div'.mpr hδε))]
      rintro ⟨c, d⟩ ⟨hc, hd⟩
      calc
        |c * d / (a * b)|ₘ = |(c / a) * (d / b)|ₘ := by rw [div_mul_div_comm]
        _ ≤ |c / a|ₘ * |d / b|ₘ := mabs_mul_le ..
        _ < δ * (ε / δ) := mul_lt_mul_of_lt_of_lt hc hd
        _ = ε := mul_div_cancel ..
    · have (x : G) : ∀ᶠ y in 𝓝 x, y = x :=
        (eventually_mabs_div_lt _ hε).mono fun y hy ↦ mabs_div_le_one.mp <| hε_min _ hy
      filter_upwards [(this _).prod_nhds (this _)]
      simp [hε]
  continuous_inv := continuous_iff_continuousAt.2 fun a ↦
    LinearOrderedCommGroup.tendsto_nhds.2 fun ε ε0 ↦
      (eventually_mabs_div_lt a ε0).mono fun x hx ↦ by rwa [inv_div_inv, mabs_div_comm]

@[to_additive (attr := continuity)]
/-
**continuous_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_mabs : Continuous (mabs : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.max`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `LinearOrderedCommGroup.toIsTopologicalGroup`：∀ {G : Type u_1} [inst : To
pologicalSpace G] [inst_1 : CommGroup G] [inst_2 : LinearOrder G] [IsOrderedMono
id G]   [OrderTopology G], IsTopo…
-/
theorem continuous_mabs : Continuous (mabs : G → G) :=
  continuous_id.max continuous_inv

section Tendsto

variable {α : Type*} {l : Filter α} {f : α → G}

@[to_additive]
/-
**Filter.Tendsto.mabs** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : CommGroup G] [inst_
2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G] {α : Type u_2} {l : F
ilter α} {f : α → G} {a : G},   Filter.Tendsto f l (nhds a) → Filter.Tendsto (fu
n x => |f x|ₘ) l (nhds |a|ₘ)
参数：nhds a；fun x => |f x|ₘ；nhds |a|ₘ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_mabs`：continuous_mabs : Continuous (mabs : G -> G)
-/
protected theorem Filter.Tendsto.mabs {a : G} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => |f x|ₘ) l (𝓝 |a|ₘ) :=
  (continuous_mabs.tendsto _).comp h

@[to_additive (attr := simp)]
/-
**comap_mabs_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_mabs_nhds_one : comap mabs (𝓝 (1 : G)) = 𝓝 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_iInf_mabs_div`：nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 
{ b | |a / b|ₘ < r }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `mabs_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLe
ftMono α] [MulRightMono α] (a : α), |(|a|ₘ)|ₘ = |a|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_mabs_nhds_one : comap mabs (𝓝 (1 : G)) = 𝓝 1 := by
  simp [nhds_eq_iInf_mabs_div]

@[to_additive]
/-
**tendsto_one_iff_mabs_tendsto_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_one_iff_mabs_tendsto_one (f : α -> G) : Tendsto f l (𝓝 1) ↔ Tendst
o (mabs ∘ f) l (𝓝 1)
参数：f : α -> G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `comap_mabs_nhds_one`：comap_mabs_nhds_one : comap mabs (𝓝 (1 : G)) = 𝓝 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_one_iff_mabs_tendsto_one (f : α → G) :
    Tendsto f l (𝓝 1) ↔ Tendsto (mabs ∘ f) l (𝓝 1) := by
  rw [← tendsto_comap_iff, comap_mabs_nhds_one]

end Tendsto

variable {X : Type*} [TopologicalSpace X] {f : X → G} {s : Set X} {x : X}

@[to_additive (attr := fun_prop)]
/-
**Continuous.mabs** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : CommGroup G] [inst_
2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G] {X : Type u_2} [inst_
5 : TopologicalSpace X] {f : X → G}, Continuous f → Continuous fun x => |f x|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_mabs`：continuous_mabs : Continuous (mabs : G -> G)
-/
protected theorem Continuous.mabs (h : Continuous f) : Continuous fun x => |f x|ₘ :=
  continuous_mabs.comp h

@[to_additive (attr := fun_prop)]
/-
**ContinuousAt.mabs** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : CommGroup G] [inst_
2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G] {X : Type u_2} [inst_
5 : TopologicalSpace X] {f : X → G} {x : X},   ContinuousAt f x → ContinuousAt (
fun x => |f x|ₘ) x
参数：fun x => |f x|ₘ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mabs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_
1 : CommGroup G] [inst_2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G
] {α : Ty…
-/
protected theorem ContinuousAt.mabs (h : ContinuousAt f x) : ContinuousAt (fun x => |f x|ₘ) x :=
  Filter.Tendsto.mabs h

@[to_additive]
/-
**ContinuousWithinAt.mabs** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWithinAt`。
形式化陈述：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : CommGroup G] [inst_
2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G] {X : Type u_2} [inst_
5 : TopologicalSpace X] {f : X → G} {s : Set X} {x : X},   ContinuousWithinAt f 
s x → ContinuousWithinAt (fun x => |f x|ₘ) s x
参数：fun x => |f x|ₘ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mabs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_
1 : CommGroup G] [inst_2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G
] {α : Ty…
-/
protected theorem ContinuousWithinAt.mabs (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => |f x|ₘ) s x :=
  Filter.Tendsto.mabs h

@[to_additive (attr := fun_prop)]
/-
**ContinuousOn.mabs** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : CommGroup G] [inst_
2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopology G] {X : Type u_2} [inst_
5 : TopologicalSpace X] {f : X → G} {s : Set X},   ContinuousOn f s → Continuous
On (fun x => |f x|ₘ) s
参数：fun x => |f x|ₘ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mabs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [i
nst_1 : CommGroup G] [inst_2 : LinearOrder G] [IsOrderedMonoid G]   [OrderTopolo
gy G] {X : Ty…
-/
protected theorem ContinuousOn.mabs (h : ContinuousOn f s) : ContinuousOn (fun x => |f x|ₘ) s :=
  fun x hx => (h x hx).mabs

@[to_additive]
/-
**tendsto_mabs_nhdsNE_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mabs_nhdsNE_one : Tendsto (mabs : G -> G) (𝓝[!=] 1) (𝓝[>] 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `continuous_mabs`：continuous_mabs : Continuous (mabs : G -> G)
· 使用定理 `mabs_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLef
tMono α], |1|ₘ = 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `one_lt_mabs`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α}, 1 < |a|ₘ ↔ a ≠ 1
-/
theorem tendsto_mabs_nhdsNE_one : Tendsto (mabs : G → G) (𝓝[≠] 1) (𝓝[>] 1) :=
  (continuous_mabs.tendsto' (1 : G) 1 mabs_one).inf <|
    tendsto_principal_principal.2 fun _x => one_lt_mabs.2

/-- In a linearly ordered multiplicative group, the integer powers of an element are dense
iff they are the whole group. -/
@[to_additive /-- In a linearly ordered additive group, the integer multiples of an element are
dense iff they are the whole group. -/]
/-
**denseRange_zpow_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_zpow_iff_surjective {a : G} : DenseRange (a ^ · : Int -> G) ↔ S
urjective (a ^ · : Int -> G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DenseRange.exists_mem_open`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 {α : Type u_4} {f : α → X} {s : Set X},   DenseRange f → IsOpen s → s.Nonempty 
→ ∃ a, f a ∈ s
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
· 使用引理 `zpow_lt_zpow_iff_right`：zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a 
^ n ↔ m < n
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `closure_singleton`：closure_singleton [T1Space X] {x : X} : closure ({x} 
: Set X) = {x}
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
（共 37 条，此处仅展示前 30 条）
-/
theorem denseRange_zpow_iff_surjective {a : G} :
    DenseRange (a ^ · : ℤ → G) ↔ Surjective (a ^ · : ℤ → G) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.denseRange⟩
  wlog! ha₀ : 1 < a generalizing a
  · simp only [← range_eq_univ, DenseRange] at *
    rcases ha₀.eq_or_lt with rfl | hlt
    · simpa only [one_zpow, range_const, dense_iff_closure_eq, closure_singleton] using h
    · have H : range (a⁻¹ ^ · : ℤ → G) = range (a ^ · : ℤ → G) := by
        simpa only [← inv_zpow, zpow_neg, comp_def] using neg_surjective.range_comp (a ^ · : ℤ → G)
      rw [← H]
      apply this <;> simpa only [H, one_lt_inv']
  intro b
  obtain ⟨m, hm, hm'⟩ : ∃ m : ℤ, a ^ m ∈ Ioo b (b * a * a) := by
    have hne : (Ioo b (b * a * a)).Nonempty := ⟨b * a, by simpa⟩
    simpa using h.exists_mem_open isOpen_Ioo hne
  rcases eq_or_ne b (a ^ (m - 1)) with rfl | hne; · simp
  suffices (Ioo (a ^ m) (a ^ (m + 1))).Nonempty by
    rcases h.exists_mem_open isOpen_Ioo this with ⟨l, hl⟩
    have : m < l ∧ l < m + 1 := by simpa [zpow_lt_zpow_iff_right ha₀] using hl
    lia
  rcases hne.lt_or_gt with hlt | hlt
  · refine ⟨b * a * a, hm', ?_⟩
    simpa only [zpow_add, zpow_sub, zpow_one, ← div_eq_mul_inv, lt_div_iff_mul_lt,
      mul_lt_mul_iff_right] using hlt
  · use b * a
    simp only [mem_Ioo, zpow_add, zpow_sub, zpow_one, ← div_eq_mul_inv,
      mul_lt_mul_iff_right] at hlt ⊢
    exact ⟨div_lt_iff_lt_mul.1 hlt, hm⟩

/-- In a nontrivial densely linearly ordered commutative group,
the integer powers of an element can't be dense. -/
@[to_additive /-- In a nontrivial densely linearly ordered additive group,
the integer multiples of an element can't be dense. -/]
/-
**not_denseRange_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_denseRange_zpow [Nontrivial G] [DenselyOrdered G] {a : G} : ¬DenseRang
e (a ^ · : Int -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `denseRange_zpow_iff_surjective`：denseRange_zpow_iff_surjective {a : G} :
 DenseRange (a ^ · : Int -> G) ↔ Surjective (a ^ · : Int -> G)
· 使用定理 `not_isCyclic_of_denselyOrdered`：not_isCyclic_of_denselyOrdered [DenselyO
rdered α] [Nontrivial α] : ¬IsCyclic α
-/
theorem not_denseRange_zpow [Nontrivial G] [DenselyOrdered G] {a : G} :
    ¬DenseRange (a ^ · : ℤ → G) :=
  denseRange_zpow_iff_surjective.not.mpr fun h ↦
    not_isCyclic_of_denselyOrdered G ⟨⟨a, h⟩⟩
