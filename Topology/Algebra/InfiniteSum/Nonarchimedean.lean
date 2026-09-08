/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion

/-!
# Infinite sums and products in nonarchimedean abelian groups

Let `G` be a complete nonarchimedean abelian group and let `f : α → G` be a function. We prove that
`f` is unconditionally summable if and only if `f a` tends to zero on the cofinite filter on `α`
(`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`). We also prove the analogous result in
the multiplicative setting (`NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one`).

We also prove that multiplication distributes over arbitrarily indexed sums in a nonarchimedean
ring. That is, let `R` be a nonarchimedean ring, let `f : α → R` be a function that sums to `a : R`,
and let `g : β → R` be a function that sums to `b : R`. Then `fun (i : α × β) ↦ (f i.1) * (g i.2)`
sums to `a * b` (`HasSum.mul_of_nonarchimedean`).

-/

public section

open Filter Topology

namespace NonarchimedeanGroup

variable {α G : Type*}
variable [CommGroup G] [UniformSpace G] [IsUniformGroup G] [NonarchimedeanGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a nonarchimedean multiplicative abelian group, and let `f : α → G` be a function that
tends to one on the filter of cofinite sets. For each finite subset of `α`, consider the partial
product of `f` on that subset. These partial products form a Cauchy filter. -/
@[to_additive /-- Let `G` be a nonarchimedean additive abelian group, and let `f : α → G` be a
function that tends to zero on the filter of cofinite sets. For each finite subset of `α`, consider
the partial sum of `f` on that subset. These partial sums form a Cauchy filter. -/]
/-
**NonarchimedeanGroup.cauchySeq_prod_of_tendsto_cofinite_one** 是 Mathlib 中的一个定理，
位于命名空间 `NonarchimedeanGroup`。
形式化陈述：cauchySeq_prod_of_tendsto_cofinite_one {f : α -> G} (hf : Tendsto f cofini
te (𝓝 1)) : CauchySeq (fun s => ∏ i in s, f i)
参数：hf : Tendsto f cofinite (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cauchySeq_finset_iff_prod_vanishing`：cauchySeq_finset_iff_prod_vanishing
 : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔ forall e in 𝓝 (1 : α), exists
 s : Finset β, forall t, …
· 使用定理 `NonarchimedeanGroup.is_nonarchimedean`：∀ {G : Type u_1} {inst : Group G}
 {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G],   ∀ U ∈ nhds 1, ∃
 V, ↑V ⊆ U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `OpenSubgroup.mem_nhds_one`：mem_nhds_one : (U : Set G) in 𝓝 (1 : G)
· 使用定理 `Subgroup.prod_mem`：∀ {G : Type u_3} [inst : CommGroup G] (K : Subgroup G
) {ι : Type u_4} {t : Finset ι} {f : ι → G},   (∀ c ∈ t, f c ∈ K) → ∏ c ∈ t, f c
 ∈ K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
-/
theorem cauchySeq_prod_of_tendsto_cofinite_one {f : α → G} (hf : Tendsto f cofinite (𝓝 1)) :
    CauchySeq (fun s ↦ ∏ i ∈ s, f i) := by
  /- Let `U` be a neighborhood of `1`. It suffices to show that there exists `s : Finset α` such
  that for any `t : Finset α` disjoint from `s`, we have `∏ i ∈ t, f i ∈ U`. -/
  apply cauchySeq_finset_iff_prod_vanishing.mpr
  intro U hU
  -- Since `G` is nonarchimedean, `U` contains an open subgroup `V`.
  rcases is_nonarchimedean U hU with ⟨V, hV⟩
  /- Let `s` be the set of all indices `i : α` such that `f i ∉ V`. By our assumption `hf`, this is
  finite. -/
  use (tendsto_def.mp hf V V.mem_nhds_one).toFinset
  /- For any `t : Finset α` disjoint from `s`, the product `∏ i ∈ t, f i` is a product of elements
  of `V`, so it is an element of `V` too. Thus, `∏ i ∈ t, f i ∈ U`, as desired. -/
  intro t ht
  apply hV
  apply Subgroup.prod_mem
  intro i hi
  simpa using Finset.disjoint_left.mp ht hi

/-- Let `G` be a nonarchimedean abelian group, and let `f : ℕ → G` be a function
such that the quotients `f (n + 1) / f n` tend to one. Then the function is a Cauchy sequence. -/
@[to_additive /-- Let `G` be a nonarchimedean additive abelian group, and let `f : ℕ → G` be a
function such that the differences `f (n + 1) - f n` tend to zero.
Then the function is a Cauchy sequence. -/]
/-
**NonarchimedeanGroup.cauchySeq_of_tendsto_div_nhds_one** 是 Mathlib 中的一个引理，位于命名空
间 `NonarchimedeanGroup`。
形式化陈述：cauchySeq_of_tendsto_div_nhds_one {f : Nat -> G} (hf : Tendsto (fun n => f
 (n + 1) / f n) atTop (𝓝 1)) : CauchySeq f
参数：hf : Tendsto (fun n => f (n + 1) / f n) atTop (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `NonarchimedeanGroup.is_nonarchimedean`：∀ {G : Type u_1} {inst : Group G}
 {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G],   ∀ U ∈ nhds 1, ∃
 V, ↑V ⊆ U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `OpenSubgroup.mem_nhds_one`：mem_nhds_one : (U : Set G) in 𝓝 (1 : G)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `OpenSubgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G] [inst_
1 : TopologicalSpace G], SubgroupClass (OpenSubgroup G) G
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
（共 35 条，此处仅展示前 30 条）
-/
lemma cauchySeq_of_tendsto_div_nhds_one {f : ℕ → G}
    (hf : Tendsto (fun n ↦ f (n + 1) / f n) atTop (𝓝 1)) :
    CauchySeq f := by
  suffices Tendsto (fun p : ℕ × ℕ ↦ f p.2 / f p.1) atTop (𝓝 1) by simpa [CauchySeq,
      cauchy_map_iff, prod_atTop_atTop_eq, uniformity_eq_comap_nhds_one G, atTop_neBot]
  rw [tendsto_atTop']
  intro s hs
  obtain ⟨t, ht⟩ := is_nonarchimedean s hs
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b, N ≤ b → f (b + 1) / f b ∈ t := by
    simpa using! tendsto_def.mp hf t t.mem_nhds_one
  refine ⟨(N, N), ?_⟩
  rintro ⟨M, M'⟩ ⟨(hMN : N ≤ M), (hMN' : N ≤ M')⟩
  apply ht
  wlog h : M ≤ M' generalizing M M'
  · simpa [inv_div] using! t.inv_mem <| this _ _ hMN' hMN (le_of_not_ge h)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h hMN'
  induction k with
  | zero => simp
  | succ k ih => simpa using! t.mul_mem (hN _ (by lia : N ≤ M + k)) ih

/-- Let `G` be a complete nonarchimedean multiplicative abelian group, and let `f : α → G` be a
function that tends to one on the filter of cofinite sets. Then `f` is unconditionally
multipliable. -/
@[to_additive /-- Let `G` be a complete nonarchimedean additive abelian group, and let `f : α → G`
be a function that tends to zero on the filter of cofinite sets. Then `f` is unconditionally
summable. -/]
/-
**NonarchimedeanGroup.multipliable_of_tendsto_cofinite_one** 是 Mathlib 中的一个定理，位于
命名空间 `NonarchimedeanGroup`。
形式化陈述：multipliable_of_tendsto_cofinite_one [CompleteSpace G] {f : α -> G} (hf : 
Tendsto f cofinite (𝓝 1)) : Multipliable f
参数：hf : Tendsto f cofinite (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `NonarchimedeanGroup.cauchySeq_prod_of_tendsto_cofinite_one`：cauchySeq_pr
od_of_tendsto_cofinite_one {f : α -> G} (hf : Tendsto f cofinite (𝓝 1)) : Cauchy
Seq (fun s => ∏ i in s, f i)
-/
theorem multipliable_of_tendsto_cofinite_one [CompleteSpace G] {f : α → G}
    (hf : Tendsto f cofinite (𝓝 1)) : Multipliable f :=
  CompleteSpace.complete (cauchySeq_prod_of_tendsto_cofinite_one hf)

/-- Let `G` be a complete nonarchimedean multiplicative abelian group. Then a function `f : α → G`
is unconditionally multipliable if and only if it tends to one on the filter of cofinite sets. -/
@[to_additive /-- Let `G` be a complete nonarchimedean additive abelian group. Then a function
`f : α → G` is unconditionally summable if and only if it tends to zero on the filter of cofinite
sets. -/]
/-
**NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one** 是 Mathlib 中的一个定理，位
于命名空间 `NonarchimedeanGroup`。
形式化陈述：multipliable_iff_tendsto_cofinite_one [CompleteSpace G] (f : α -> G) : Mul
tipliable f ↔ Tendsto f cofinite (𝓝 1)
参数：f : α -> G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tendsto_cofinite_one`：Multipliable.tendsto_cofinite_one (hf
 : Multipliable f) : Tendsto f cofinite (𝓝 1)
· 使用定理 `NonarchimedeanGroup.toIsTopologicalGroup`：∀ {G : Type u_1} {inst : Group
 G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G], IsTopologicalG
roup G
· 使用定理 `NonarchimedeanGroup.multipliable_of_tendsto_cofinite_one`：multipliable_o
f_tendsto_cofinite_one [CompleteSpace G] {f : α -> G} (hf : Tendsto f cofinite (
𝓝 1)) : Multipliable f
-/
theorem multipliable_iff_tendsto_cofinite_one [CompleteSpace G] (f : α → G) :
    Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨Multipliable.tendsto_cofinite_one, multipliable_of_tendsto_cofinite_one⟩

end NonarchimedeanGroup

section NonarchimedeanRing

variable {α β R : Type*}
variable [Ring R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]

/-- Let `R` be a complete nonarchimedean ring. If functions `f : α → R` and `g : β → R` are
summable, then so is `fun i : α × β ↦ f i.1 * g i.2`. We will prove later that the assumption that
`R` is complete is not necessary. -/
/-
**Summable.mul_of_complete_nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a complete nonarchimedean ring. If functions `f : α → R` and `g : β →
 R` are
summable, then so is `fun i : α × β ↦ f i.1 * g i.2`. We will prove later that t
he assumption that
`R` is complete is not necessary.
-/
private theorem Summable.mul_of_complete_nonarchimedean [CompleteSpace R] {f : α → R} {g : β → R}
    (hf : Summable f) (hg : Summable g) : Summable (fun i : α × β ↦ f i.1 * g i.2) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero] at *
  exact tendsto_mul_cofinite_nhds_zero hf hg

/-- Let `R` be a nonarchimedean ring, let `f : α → R` be a function that sums to `a : R`,
and let `g : β → R` be a function that sums to `b : R`. Then `fun i : α × β ↦ f i.1 * g i.2`
sums to `a * b`. -/
/-
**HasSum.mul_of_nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.mul_of_nonarchimedean {f : α -> R} {g : β -> R} {a b : R} (hf : Has
Sum f a) (hg : HasSum g b) : HasSum (fun i : α × β => f i.1 * g i.2) (a * b)
参数：hf : HasSum f a；hg : HasSum g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasSum_iff_hasSum_compl`：hasSum_iff_hasSum_compl (f : β -> α) (a : α) : 
HasSum (toCompl ∘ f) a L ↔ HasSum f a L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformSpace.Completion.toCompl_apply`：∀ {α : Type u_3} [inst : UniformS
pace α] [inst_1 : AddGroup α] [inst_2 : IsUniformAddGroup α] (a : α),   UniformS
pace.Completion.toCompl a =…
· 使用定理 `UniformSpace.Completion.coe_mul`：coe_mul (a b : α) : ((a * b : α) : Comp
letion α) = a * b
· 使用定理 `NonarchimedeanRing.toIsTopologicalRing`：∀ {R : Type u_1} {inst : Ring R}
 {inst_1 : TopologicalSpace R} [self : NonarchimedeanRing R], IsTopologicalRing 
R
· 使用定理 `HasSum.mul`：HasSum.mul (hf : HasSum f s) (hg : HasSum g t) (hfg : Summab
le fun x : ι × κ => f x.1 * g x.2) : HasSum (fun x : ι × κ => f x.1 * g x.2) (s 
…
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `instNonarchimedeanAddGroupCompletion`：∀ {G : Type u_1} [inst : AddGroup 
G] [inst_1 : UniformSpace G] [inst_2 : IsUniformAddGroup G]   [NonarchimedeanAdd
Group G], NonarchimedeanAd…
· 使用定理 `NonarchimedeanRing.to_nonarchimedeanAddGroup`：∀ (R : Type u_1) [inst : R
ing R] [inst_1 : TopologicalSpace R] [t : NonarchimedeanRing R], NonarchimedeanA
ddGroup R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `_private.Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean.0.Summable.
mul_of_complete_nonarchimedean`：∀ {α : Type u_1} {β : Type u_2} {R : Type u_3} [
inst : Ring R] [inst_1 : UniformSpace R] [IsUniformAddGroup R]   [Nonarchimedean
Ring R] [Com…
· 使用定理 `instNonarchimedeanRingCompletion`：∀ {R : Type u_1} [inst : Ring R] [inst
_1 : UniformSpace R] [inst_2 : IsUniformAddGroup R]   [inst_3 : NonarchimedeanRi
ng R], NonarchimedeanR…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…

--- 原说明 ---
Let `R` be a nonarchimedean ring, let `f : α → R` be a function that sums to `a 
: R`,
and let `g : β → R` be a function that sums to `b : R`. Then `fun i : α × β ↦ f 
i.1 * g i.2`
sums to `a * b`.
-/
theorem HasSum.mul_of_nonarchimedean {f : α → R} {g : β → R} {a b : R} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun i : α × β ↦ f i.1 * g i.2) (a * b) := by
  rw [← hasSum_iff_hasSum_compl] at *
  simp only [Function.comp_def, UniformSpace.Completion.toCompl_apply,
    UniformSpace.Completion.coe_mul]
  exact (hf.mul hg) (hf.summable.mul_of_complete_nonarchimedean hg.summable :)

/-- Let `R` be a nonarchimedean ring. If functions `f : α → R` and `g : β → R` are summable, then
so is `fun i : α × β ↦ f i.1 * g i.2`. -/
/-
**Summable.mul_of_nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.mul_of_nonarchimedean {f : α -> R} {g : β -> R} (hf : Summable f)
 (hg : Summable g) : Summable (fun i : α × β => f i.1 * g i.2)
参数：hf : Summable f；hg : Summable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.mul_of_nonarchimedean`：HasSum.mul_of_nonarchimedean {f : α -> R} 
{g : β -> R} {a b : R} (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun i : α ×
 β => f i.1 * g i.…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
Let `R` be a nonarchimedean ring. If functions `f : α → R` and `g : β → R` are s
ummable, then
so is `fun i : α × β ↦ f i.1 * g i.2`.
-/
theorem Summable.mul_of_nonarchimedean {f : α → R} {g : β → R} (hf : Summable f)
    (hg : Summable g) : Summable (fun i : α × β ↦ f i.1 * g i.2) :=
  (hf.hasSum.mul_of_nonarchimedean hg.hasSum).summable
/-
**tsum_mul_tsum_of_nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_mul_tsum_of_nonarchimedean [T0Space R] {f : α -> R} {g : β -> R} (hf 
: Summable f) (hg : Summable g) : (∑' i, f i) * (∑' i, g i) = ∑' i : α × β, f i.
1 * g i.2
参数：hf : Summable f；hg : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `NonarchimedeanRing.to_nonarchimedeanAddGroup`：∀ (R : Type u_1) [inst : R
ing R] [inst_1 : TopologicalSpace R] [t : NonarchimedeanRing R], NonarchimedeanA
ddGroup R
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.mul_of_nonarchimedean`：HasSum.mul_of_nonarchimedean {f : α -> R} 
{g : β -> R} {a b : R} (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun i : α ×
 β => f i.1 * g i.…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem tsum_mul_tsum_of_nonarchimedean [T0Space R] {f : α → R} {g : β → R} (hf : Summable f)
    (hg : Summable g) : (∑' i, f i) * (∑' i, g i) = ∑' i : α × β, f i.1 * g i.2 :=
  (hf.hasSum.mul_of_nonarchimedean hg.hasSum).tsum_eq.symm

end NonarchimedeanRing

