/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of series of functions

We show that series of functions are continuous when each individual function in the series is and
additionally suitable uniform summable bounds are satisfied, in `continuous_tsum`.

For smoothness of series of functions, see the file `Mathlib/Analysis/Calculus/SmoothSeries.lean`.

TODO: update this to use `SummableUniformlyOn`.

-/

public section

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with general index set. -/
/-
**tendstoUniformlyOn_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu : Summable u) {s : Set β} (h
fu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoUniformlyOn (fun t : Finset 
α => fun x => ∑ n in t, f n x) (fun x => ∑' n, f n x) atTop s
参数：hu : Summable u；hfu : forall n x, x in s -> ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_tsum_compl_atTop_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : T
opologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   (f : α 
→ G), Filter.Tendst…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_subtype_compl`：∀ {α : Type u_1} {β : Type u_2} [in
st : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   [Complete
Space α] [T2Space α] {f :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_tsum_le_tsum_norm`：norm_tsum_le_tsum_norm {f : ι -> E} (hf : Summab
le fun i => ‖f i‖) : ‖∑' i, f i‖ <= ∑' i, ‖f i‖
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot

--- 原说明 ---
An infinite sum of functions with summable sup norm is the uniform limit of its 
partial sums.
Version relative to a set, with general index set.
-/
theorem tendstoUniformlyOn_tsum {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t : Finset α => fun x => ∑ n ∈ t, f n x) (fun x => ∑' n, f n x) atTop
      s := by
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have A : Summable fun n => ‖f n x‖ :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm, ← A.of_norm.sum_add_tsum_subtype_compl t, add_sub_cancel_left]
  apply lt_of_le_of_lt _ ht
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  exact (A.subtype _).tsum_le_tsum (fun n => hfu _ _ hx) (hu.subtype _)

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with index set `ℕ`. -/
/-
**tendstoUniformlyOn_tsum_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_tsum_nat {f : Nat -> β -> F} {u : Nat -> Real} (hu : Su
mmable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoUnif
ormlyOn (fun N x => ∑ n in Finset.range N, f n x) (fun x => ∑' n, f n x) atTop s
参数：hu : Summable u；hfu : forall n x, x in s -> ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…

--- 原说明 ---
An infinite sum of functions with summable sup norm is the uniform limit of its 
partial sums.
Version relative to a set, with index set `ℕ`.
-/
theorem tendstoUniformlyOn_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun N => fun x => ∑ n ∈ Finset.range N, f n x) (fun x => ∑' n, f n x) atTop
      s :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tsum hu hfu v hv)

set_option backward.isDefEq.respectTransparency false in
/-- An infinite sum of functions with eventually summable sup norm is the uniform limit of its
partial sums. Version relative to a set, with general index set. -/
/-
**tendstoUniformlyOn_tsum_of_cofinite_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_tsum_of_cofinite_eventually {ι : Type*} {f : ι -> β -> 
F} {u : ι -> Real} (hu : Summable u) {s : Set β} (hfu : forallᶠ n in cofinite, f
orall x in s, ‖f n x‖ <= u n) : TendstoUniformlyOn (fun t x => ∑ n in t, f n x) 
(fun x => ∑' n, f n x) atTop s
参数：hu : Summable u；hfu : forallᶠ n in cofinite, forall x in s, ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_tsum_compl_atTop_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : T
opologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   (f : α 
→ G), Filter.Tendst…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Summable.add_compl`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d α] [inst_1 : TopologicalSpace α] {f : β → α} [ContinuousAdd α]   {s : Set β}, 
Summable…
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
· 使用定理 `Summable.of_finite`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [Finite β] [L.HasSu
pport] {…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
An infinite sum of functions with eventually summable sup norm is the uniform li
mit of its
partial sums. Version relative to a set, with general index set.
-/
theorem tendstoUniformlyOn_tsum_of_cofinite_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t x => ∑ n ∈ t, f n x) (fun x => ∑' n, f n x) atTop s := by
  classical
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos
  simp only [eventually_atTop] at *
  obtain ⟨t, ht⟩ := this
  rw [eventually_iff_exists_mem] at hfu
  obtain ⟨N, hN, HN⟩ := hfu
  refine ⟨hN.toFinset ∪ t, fun n hn x hx => ?_⟩
  have A : Summable fun n => ‖f n x‖ := by
    apply Summable.add_compl (s := hN.toFinset) Summable.of_finite
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ (hu.subtype _)
    simp only [comp_apply, Subtype.forall, Set.mem_compl_iff, Finset.mem_coe]
    aesop
  rw [dist_eq_norm, ← A.of_norm.sum_add_tsum_subtype_compl n, add_sub_cancel_left]
  apply lt_of_le_of_lt _ (ht n (Finset.union_subset_right hn))
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  apply (A.subtype _).tsum_le_tsum _ (hu.subtype _)
  simp only [comp_apply, Subtype.forall]
  apply fun i hi => HN i ?_ x hx
  have : i ∉ hN.toFinset := fun hg ↦ hi (Finset.union_subset_left hn hg)
  simp_all
/-
**tendstoUniformlyOn_tsum_nat_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_tsum_nat_eventually {α F : Type*} [NormedAddCommGroup F
] [CompleteSpace F] {f : Nat -> α -> F} {u : Nat -> Real} (hu : Summable u) {s :
 Set α} (hfu : forallᶠ n in atTop, forall x in s, ‖f n x‖ <= u n) : TendstoUnifo
rmlyOn (fun N x => ∑ n in Finset.range N, f n x) (fun x => ∑' n, f n x) atTop s
参数：hu : Summable u；hfu : forallᶠ n in atTop, forall x in s, ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`：tendstoUniformlyOn_tsum_
of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real} (hu : Summa
ble u) {s : Set β} (hfu : forallᶠ n …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem tendstoUniformlyOn_tsum_nat_eventually {α F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] {f : ℕ → α → F} {u : ℕ → ℝ} (hu : Summable u) {s : Set α}
    (hfu : ∀ᶠ n in atTop, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, f n x)
       (fun x => ∑' n, f n x) atTop s :=
  fun v hv ↦ tendsto_finset_range.eventually <|
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu (Nat.cofinite_eq_atTop ▸ hfu) v hv

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with general index set. -/
/-
**tendstoUniformly_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformly_tsum {f : α -> β -> F} (hu : Summable u) (hfu : forall n 
x, ‖f n x‖ <= u n) : TendstoUniformly (fun t : Finset α => fun x => ∑ n in t, f 
n x) (fun x => ∑' n, f n x) atTop
参数：hu : Summable u；hfu : forall n x, ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…

--- 原说明 ---
An infinite sum of functions with summable sup norm is the uniform limit of its 
partial sums.
Version with general index set.
-/
theorem tendstoUniformly_tsum {f : α → β → F} (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun t : Finset α => fun x => ∑ n ∈ t, f n x)
      (fun x => ∑' n, f n x) atTop := by
  rw [← tendstoUniformlyOn_univ]; exact tendstoUniformlyOn_tsum hu fun n x _ => hfu n x

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with index set `ℕ`. -/
/-
**tendstoUniformly_tsum_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformly_tsum_nat {f : Nat -> β -> F} {u : Nat -> Real} (hu : Summ
able u) (hfu : forall n x, ‖f n x‖ <= u n) : TendstoUniformly (fun N x => ∑ n in
 Finset.range N, f n x) (fun x => ∑' n, f n x) atTop
参数：hu : Summable u；hfu : forall n x, ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `tendstoUniformly_tsum`：tendstoUniformly_tsum {f : α -> β -> F} (hu : Sum
mable u) (hfu : forall n x, ‖f n x‖ <= u n) : TendstoUniformly (fun t : Finset α
 => fun x =…

--- 原说明 ---
An infinite sum of functions with summable sup norm is the uniform limit of its 
partial sums.
Version with index set `ℕ`.
-/
theorem tendstoUniformly_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : Summable u)
    (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun N => fun x => ∑ n ∈ Finset.range N, f n x) (fun x => ∑' n, f n x)
      atTop :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformly_tsum hu hfu v hv)

/-- An infinite sum of functions with eventually summable sup norm is the uniform limit of its
partial sums. Version with general index set. -/
/-
**tendstoUniformly_tsum_of_cofinite_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformly_tsum_of_cofinite_eventually {ι : Type*} {f : ι -> β -> F}
 {u : ι -> Real} (hu : Summable u) (hfu : forallᶠ (n : ι) in cofinite, forall x 
: β, ‖f n x‖ <= u n) : TendstoUniformly (fun t x => ∑ n in t, f n x) (fun x => ∑
' n, f n x) atTop
参数：hu : Summable u；hfu : forallᶠ (n : ι) in cofinite, forall x : β, ‖f n x‖ <= u
 n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`：tendstoUniformlyOn_tsum_
of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real} (hu : Summa
ble u) {s : Set β} (hfu : forallᶠ n …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
An infinite sum of functions with eventually summable sup norm is the uniform li
mit of its
partial sums. Version with general index set.
-/
theorem tendstoUniformly_tsum_of_cofinite_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) (hfu : ∀ᶠ (n : ι) in cofinite, ∀ x : β, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun t x => ∑ n ∈ t, f n x) (fun x => ∑' n, f n x) atTop := by
  rw [← tendstoUniformlyOn_univ]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu
  simpa using hfu

/-- An infinite sum of functions with summable sup norm is continuous on a set if each individual
function is. -/
/-
**continuousOn_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_tsum [TopologicalSpace β] {f : α -> β -> F} {s : Set β} (hf :
 forall i, ContinuousOn (f i) s) (hu : Summable u) (hfu : forall n x, x in s -> 
‖f n x‖ <= u n) : ContinuousOn (fun x => ∑' n, f n x) s
参数：hf : forall i, ContinuousOn (f i) s；hu : Summable u；hfu : forall n x, x in s 
-> ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.continuousOn`：∀ {α : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α → β}   
{f : α → β} {s : Set …
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `continuousOn_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMono
id M] [Conti…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
An infinite sum of functions with summable sup norm is continuous on a set if ea
ch individual
function is.
-/
theorem continuousOn_tsum [TopologicalSpace β] {f : α → β → F} {s : Set β}
    (hf : ∀ i, ContinuousOn (f i) s) (hu : Summable u) (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    ContinuousOn (fun x => ∑' n, f n x) s := by
  refine (tendstoUniformlyOn_tsum hu hfu).continuousOn (Frequently.of_forall ?_)
  intro t
  exact continuousOn_finsetSum _ fun i _ => hf i

/-- An infinite sum of functions with summable sup norm is continuous if each individual
function is. -/
/-
**continuous_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_tsum [TopologicalSpace β] {f : α -> β -> F} (hf : forall i, Con
tinuous (f i)) (hu : Summable u) (hfu : forall n x, ‖f n x‖ <= u n) : Continuous
 fun x => ∑' n, f n x
参数：hf : forall i, Continuous (f i)；hu : Summable u；hfu : forall n x, ‖f n x‖ <= 
u n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_tsum`：continuousOn_tsum [TopologicalSpace β] {f : α -> β ->
 F} {s : Set β} (hf : forall i, ContinuousOn (f i) s) (hu : Summable u) (hfu : f
orall n…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
An infinite sum of functions with summable sup norm is continuous if each indivi
dual
function is.
-/
theorem continuous_tsum [TopologicalSpace β] {f : α → β → F} (hf : ∀ i, Continuous (f i))
    (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) : Continuous fun x => ∑' n, f n x := by
  simp_rw [← continuousOn_univ] at hf ⊢
  exact continuousOn_tsum hf hu fun n x _ => hfu n x
