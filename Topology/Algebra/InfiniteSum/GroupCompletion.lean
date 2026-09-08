/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums in the completion of a topological group
-/

public section

open UniformSpace.Completion

variable {α β : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  {L : SummationFilter β}

/-- A function `f` has a sum in a uniform additive group `α` if and only if it has that sum in the
completion of `α`. -/
/-
**hasSum_iff_hasSum_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_iff_hasSum_compl (f : β -> α) (a : α) : HasSum (toCompl ∘ f) a L ↔ 
HasSum f a L
参数：f : β -> α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFi
lter β} [inst_2 : Ad…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsDenseInducing.toIsInducing`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i
 → Topology.IsIndu…
· 使用定理 `UniformSpace.Completion.isDenseInducing_toCompl`：isDenseInducing_toCompl
 : IsDenseInducing (toCompl : α -> Completion α)

--- 原说明 ---
A function `f` has a sum in a uniform additive group `α` if and only if it has t
hat sum in the
completion of `α`.
-/
theorem hasSum_iff_hasSum_compl (f : β → α) (a : α) :
    HasSum (toCompl ∘ f) a L ↔ HasSum f a L := (isDenseInducing_toCompl α).hasSum_iff f a

/-- A function `f` is summable in a uniform additive group `α` if and only if it is summable in
`Completion α` and its sum in `Completion α` lies in the range of `toCompl : α →+ Completion α`. -/
/-
**summable_iff_summable_compl_and_tsum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_iff_summable_compl_and_tsum_mem (f : β -> α) : Summable f L ↔ Sum
mable (toCompl ∘ f) L ∧ ∑'[L] i, toCompl (f i) in Set.range toCompl
参数：f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.summable_iff_tsum_comp_mem_range`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace
 α]   {L : SummationFilter β} [inst_2 : Ad…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsDenseInducing.toIsInducing`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i
 → Topology.IsIndu…
· 使用定理 `UniformSpace.Completion.isDenseInducing_toCompl`：isDenseInducing_toCompl
 : IsDenseInducing (toCompl : α -> Completion α)

--- 原说明 ---
A function `f` is summable in a uniform additive group `α` if and only if it is 
summable in
`Completion α` and its sum in `Completion α` lies in the range of `toCompl : α →
+ Completion α`.
-/
theorem summable_iff_summable_compl_and_tsum_mem (f : β → α) :
    Summable f L ↔ Summable (toCompl ∘ f) L ∧ ∑'[L] i, toCompl (f i) ∈ Set.range toCompl :=
  (isDenseInducing_toCompl α).summable_iff_tsum_comp_mem_range f

/-- A function `f` is summable in a uniform additive group `α` if and only if the net of its partial
sums is Cauchy and its sum in `Completion α` lies in the range of `toCompl : α →+ Completion α`.
(The condition that the net of partial sums is Cauchy can be checked using
`cauchySeq_finset_iff_sum_vanishing` or `cauchySeq_finset_iff_tsum_vanishing`.) -/
/-
**summable_iff_cauchySeq_finset_and_tsum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_iff_cauchySeq_finset_and_tsum_mem (f : β -> α) : Summable f ↔ Cau
chySeq (fun s : Finset β => ∑ b in s, f b) ∧ ∑' i, toCompl (f i) in Set.range to
Compl
参数：f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_iff_summable_compl_and_tsum_mem`：summable_iff_summable_compl_an
d_tsum_mem (f : β -> α) : Summable f L ↔ Summable (toCompl ∘ f) L ∧ ∑'[L] i, toC
ompl (f i) in Set.range toComp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_iff_cauchySeq_finset`：∀ {α : Type u_1} {β : Type u_2} [inst : U
niformSpace α] [inst_1 : AddCommMonoid α] [CompleteSpace α] {f : β → α},   Summa
ble f ↔ CauchySeq f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `UniformSpace.Completion.uniformContinuous_coe`：uniformContinuous_coe : U
niformContinuous ((↑) : α -> Completion α)

--- 原说明 ---
A function `f` is summable in a uniform additive group `α` if and only if the ne
t of its partial
sums is Cauchy and its sum in `Completion α` lies in the range of `toCompl : α →
+ Completion α`.
(The condition that the net of partial sums is Cauchy can be checked using
`cauchySeq_finset_iff_sum_vanishing` or `cauchySeq_finset_iff_tsum_vanishing`.)
-/
theorem summable_iff_cauchySeq_finset_and_tsum_mem (f : β → α) :
    Summable f ↔ CauchySeq (fun s : Finset β ↦ ∑ b ∈ s, f b) ∧
      ∑' i, toCompl (f i) ∈ Set.range toCompl := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((summable_iff_summable_compl_and_tsum_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summable_iff_summable_compl_and_tsum_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [Function.comp_apply, ← map_sum]
      exact h_cauchy.map (uniformContinuous_coe α)
    · exact h_tsum

/-- If a function `f` is summable in a uniform additive group `α`, then its sum in `α` is the same
as its sum in `Completion α`. -/
/-
**Summable.toCompl_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.toCompl_tsum [L.NeBot] {f : β -> α} (hf : Summable f L) : ∑'[L] i
, toCompl (f i) = ∑'[L] i, f i
参数：hf : Summable f L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFil
ter β} …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)

--- 原说明 ---
If a function `f` is summable in a uniform additive group `α`, then its sum in `
α` is the same
as its sum in `Completion α`.
-/
theorem Summable.toCompl_tsum [L.NeBot] {f : β → α} (hf : Summable f L) :
    ∑'[L] i, toCompl (f i) = ∑'[L] i, f i :=
  (hf.map_tsum toCompl (continuous_coe α)).symm
