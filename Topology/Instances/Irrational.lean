/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Topology of irrational numbers

In this file we prove the following theorems:

* `IsGδ.setOfPred_irrational`, `dense_irrational`, `eventually_residual_irrational`: irrational
  numbers form a dense Gδ set;

* `Irrational.eventually_forall_le_dist_cast_div`,
  `Irrational.eventually_forall_le_dist_cast_div_of_denom_le`;
  `Irrational.eventually_forall_le_dist_cast_rat_of_denom_le`: a sufficiently small neighborhood of
  an irrational number is disjoint with the set of rational numbers with bounded denominator.

We also provide `OrderTopology`, `NoMinOrder`, `NoMaxOrder`, and `DenselyOrdered`
instances for `{x // Irrational x}`.

## Tags

irrational, residual
-/

public section


open Set Filter Metric

open Filter Topology

/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsGδ.setOfPred_irrational : IsGδ { x | Irrational x } :=
  (countable_range _).isGδ_compl

@[deprecated (since := "2026-07-09")] alias IsGδ.setOf_irrational := IsGδ.setOfPred_irrational
/-
**dense_irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_irrational : Dense { x : Real | Irrational x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.dense_iff`：∀ {α : Type u} [t : Topol
ogicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis b → ∀ {s
 : Set α}, Dense s ↔ ∀ o ∈ b, o.Non…
· 使用定理 `Real.isTopologicalBasis_Ioo_rat`：Real.isTopologicalBasis_Ioo_rat : @IsTo
pologicalBasis Real _ (⋃ (a : Rat) (b : Rat) (_ : a < b), {Ioo (a : Real) b})
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `exists_irrational_btwn`：exists_irrational_btwn {x y : Real} (h : x < y) 
: exists r, Irrational r ∧ x < r ∧ r < y
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dense_irrational : Dense { x : ℝ | Irrational x } := by
  refine Real.isTopologicalBasis_Ioo_rat.dense_iff.2 ?_
  simp only [mem_iUnion, mem_singleton_iff, exists_prop, forall_exists_index, and_imp]
  rintro _ a b hlt rfl _
  rw [inter_comm]
  exact exists_irrational_btwn (Rat.cast_lt.2 hlt)
/-
**eventually_residual_irrational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_residual_irrational : forallᶠ x in residual Real, Irrational x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `residual_of_dense_Gδ`：residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd
 : Dense s) : s in residual X
· 使用定理 `IsGδ.setOfPred_irrational`：IsGδ {x | Irrational x}
· 使用定理 `dense_irrational`：dense_irrational : Dense { x : Real | Irrational x }
-/
theorem eventually_residual_irrational : ∀ᶠ x in residual ℝ, Irrational x :=
  residual_of_dense_Gδ .setOfPred_irrational dense_irrational

namespace Irrational

variable {x : ℝ}

/-
**Irrational.** 是 Mathlib 中的一个实例，位于命名空间 `Irrational`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology { x // Irrational x } :=
  induced_orderTopology _ Iff.rfl <| @fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩
/-
**Irrational.** 是 Mathlib 中的一个实例，位于命名空间 `Irrational`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMaxOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x + (1 : ℕ), hx.add_natCast 1⟩, by simp⟩⟩
/-
**Irrational.** 是 Mathlib 中的一个实例，位于命名空间 `Irrational`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMinOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x - (1 : ℕ), hx.sub_natCast 1⟩, by simp⟩⟩
/-
**Irrational.** 是 Mathlib 中的一个实例，位于命名空间 `Irrational`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DenselyOrdered { x // Irrational x } :=
  ⟨fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩⟩
/-
**Irrational.eventually_forall_le_dist_cast_div** 是 Mathlib 中的一个定理，位于命名空间 `Irrat
ional`。
形式化陈述：eventually_forall_le_dist_cast_div (hx : Irrational x) (n : Nat) : forallᶠ
 ε : Real in 𝓝 0, forall m : Int, ε <= dist x (m / n)
参数：hx : Irrational x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
· 使用定理 `isClosedMap_smul₀`：isClosedMap_smul₀ {E : Type*} [Zero E] [MulActionWith
Zero G₀ E] [TopologicalSpace E] [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) 
: IsClo…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Int.isClosedEmbedding_coe_real`：isClosedEmbedding_coe_real : IsClosedEmb
edding ((↑) : Int -> Real)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ge_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x ≤ a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eventually_forall_le_dist_cast_div (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ m : ℤ, ε ≤ dist x (m / n) := by
  have A : IsClosed (range (fun m => (n : ℝ)⁻¹ * m : ℤ → ℝ)) :=
    ((isClosedMap_smul₀ (n⁻¹ : ℝ)).comp Int.isClosedEmbedding_coe_real.isClosedMap).isClosed_range
  have B : x ∉ range (fun m => (n : ℝ)⁻¹ * m : ℤ → ℝ) := by
    rintro ⟨m, rfl⟩
    simp at hx
  rcases Metric.mem_nhds_iff.1 (A.isOpen_compl.mem_nhds B) with ⟨ε, ε0, hε⟩
  refine (ge_mem_nhds ε0).mono fun δ hδ m => not_lt.1 fun hlt => ?_
  rw [dist_comm] at hlt
  refine hε (ball_subset_ball hδ hlt) ⟨m, ?_⟩
  simp [div_eq_inv_mul]
/-
**Irrational.eventually_forall_le_dist_cast_div_of_denom_le** 是 Mathlib 中的一个定理，位
于命名空间 `Irrational`。
形式化陈述：eventually_forall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : Na
t) : forallᶠ ε : Real in 𝓝 0, forall k <= n, forall (m : Int), ε <= dist x (m / 
k)
参数：hx : Irrational x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `Irrational.eventually_forall_le_dist_cast_div`：eventually_forall_le_dist
_cast_div (hx : Irrational x) (n : Nat) : forallᶠ ε : Real in 𝓝 0, forall m : In
t, ε <= dist x (m / n)
-/
theorem eventually_forall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ k ≤ n, ∀ (m : ℤ), ε ≤ dist x (m / k) :=
  (finite_le_nat n).eventually_all.2 fun k _ => hx.eventually_forall_le_dist_cast_div k
/-
**Irrational.eventually_forall_le_dist_cast_rat_of_den_le** 是 Mathlib 中的一个定理，位于命
名空间 `Irrational`。
形式化陈述：eventually_forall_le_dist_cast_rat_of_den_le (hx : Irrational x) (n : Nat)
 : forallᶠ ε : Real in 𝓝 0, forall r : Rat, r.den <= n -> ε <= dist x r
参数：hx : Irrational x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Irrational.eventually_forall_le_dist_cast_div_of_denom_le`：eventually_fo
rall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : Nat) : forallᶠ ε : Re
al in 𝓝 0, forall k <= n, forall (m : Int), ε <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
-/
theorem eventually_forall_le_dist_cast_rat_of_den_le (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ r : ℚ, r.den ≤ n → ε ≤ dist x r :=
  (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono fun ε H r hr => by
    simpa only [Rat.cast_def] using H r.den hr r.num

end Irrational

