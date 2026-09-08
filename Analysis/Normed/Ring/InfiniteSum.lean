/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Multiplying two infinite sums in a normed ring

In this file, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean` (e.g.
`tsum_mul_tsum`), but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `ι` and `ι'`, and then we specialize to
`ι = ι' = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
-/

public section


variable {R : Type*} {ι : Type*} {ι' : Type*} [NormedRing R]

open scoped Topology

open Finset Filter

/-! ### Arbitrary index types -/

/-
**Summable.mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.mul_of_nonneg {f : ι -> Real} {g : ι' -> Real} (hf : Summable f) 
(hg : Summable g) (hf' : 0 <= f) (hg' : 0 <= g) : Summable fun x : ι × ι' => f x
.1 * g x.2
参数：hf : Summable f；hg : Summable g；hf' : 0 <= f；hg' : 0 <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_prod_of_nonneg`：summable_prod_of_nonneg {α β} {f : (α × β) -> R
eal} (hf : 0 <= f) : Summable f ↔ (forall x, Summable fun y => f (x, y)) ∧ Summa
ble fun x => …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Summable.tsum_mul_left`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFi
lter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [Is
TopologicalS…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Summable.mul_right`：Summable.mul_right (a) (hf : Summable f L) : Summabl
e (fun i => f i * a) L

--- 原说明 ---
### Arbitrary index types
-/
theorem Summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g)
    (hf' : 0 ≤ f) (hg' : 0 ≤ g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (summable_prod_of_nonneg fun _ ↦ mul_nonneg (hf' _) (hg' _)).2 ⟨fun x ↦ hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩
/-
**Summable.mul_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.mul_norm {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖
) (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' => ‖f x.1 * g x.2‖
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `Summable.mul_of_nonneg`：Summable.mul_of_nonneg {f : ι -> Real} {g : ι' -
> Real} (hf : Summable f) (hg : Summable g) (hf' : 0 <= f) (hg' : 0 <= g) : Summ
able fun x :…
-/
theorem Summable.mul_norm {f : ι → R} {g : ι' → R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' => ‖f x.1 * g x.2‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x :)
/-
**summable_mul_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_mul_of_summable_norm [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
 (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : Summable fun x 
: ι × ι' => f x.1 * g x.2
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Summable.mul_norm`：Summable.mul_norm {f : ι -> R} {g : ι' -> R} (hf : Su
mmable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' 
=> ‖f x…
-/
theorem summable_mul_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (hf.mul_norm hg).of_norm
/-
**summable_mul_of_summable_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_mul_of_summable_norm' {f : ι -> R} {g : ι' -> R} (hf : Summable f
un x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖) (h'g : Summable
 g) : Summable fun x : ι × ι' => f x.1 * g x.2
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_of_subseq_of_summable`：hasSum_of_subseq_of_summable {f : ι -> E} 
(hf : Summable fun a => ‖f a‖) {s : α -> Finset ι} {p : Filter α} [NeBot p] (hs 
: Tendsto s p atTo…
· 使用定理 `Summable.mul_norm`：Summable.mul_norm {f : ι -> R} {g : ι' -> R} (hf : Su
mmable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' 
=> ‖f x…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Filter.tendsto_finsetProd_atTop`：tendsto_finsetProd_atTop : Tendsto (fun
 (p : Finset ι × Finset ι') => p.1 ×ˢ p.2) atTop atTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
-/
theorem summable_mul_of_summable_norm' {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    Summable fun x : ι × ι' => f x.1 * g x.2 := by
  classical
  suffices HasSum (fun x : ι × ι' => f x.1 * g x.2) ((∑' i, f i) * (∑' j, g j)) from this.summable
  let s : Finset ι × Finset ι' → Finset (ι × ι') := fun p ↦ p.1 ×ˢ p.2
  apply hasSum_of_subseq_of_summable (hf.mul_norm hg) tendsto_finsetProd_atTop
  rw [← prod_atTop_atTop_eq]
  have := Tendsto.prodMap h'f.hasSum h'g.hasSum
  rw [← nhds_prod_eq] at this
  convert!
    ((continuous_mul (M := R)).continuousAt (x := (∑' (i : ι), f i, ∑' (j : ι'), g j))).tendsto.comp
      this with
    p
  simp [sum_product, ← mul_sum, ← sum_mul]

/-- Product of two infinite sums indexed by arbitrary types.
See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable, and
`tsum_mul_tsum_of_summable_norm'` when the space is not complete. -/
/-
**tsum_mul_tsum_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_mul_tsum_of_summable_norm [CompleteSpace R] {f : ι -> R} {g : ι' -> R
} (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : ((∑' x, f x) *
 ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_mul_tsum`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [
inst : TopologicalSpace α] [T3Space α]   [inst_2 : NonUnitalNonAssocSemiring α] 
[IsTopologic…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `summable_mul_of_summable_norm`：summable_mul_of_summable_norm [CompleteSp
ace R] {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (hg : Summable 
fun x => ‖g x‖) : S…

--- 原说明 ---
Product of two infinite sums indexed by arbitrary types.
See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable, and
`tsum_mul_tsum_of_summable_norm'` when the space is not complete.
-/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  hf.of_norm.tsum_mul_tsum hg.of_norm (summable_mul_of_summable_norm hf hg)
/-
**tsum_mul_tsum_of_summable_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_mul_tsum_of_summable_norm' {f : ι -> R} {g : ι' -> R} (hf : Summable 
fun x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖) (h'g : Summabl
e g) : ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_mul_tsum`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [
inst : TopologicalSpace α] [T3Space α]   [inst_2 : NonUnitalNonAssocSemiring α] 
[IsTopologic…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `summable_mul_of_summable_norm'`：summable_mul_of_summable_norm' {f : ι ->
 R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (h'f : Summable f) (hg : Summab
le fun x => ‖g x‖) (…
-/
theorem tsum_mul_tsum_of_summable_norm' {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  h'f.tsum_mul_tsum h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`Finset.range (n+1)` involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`. -/

section Nat

open Finset.Nat

/-
**summable_norm_sum_mul_antidiagonal_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : Nat -> R} (hf :
 Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ 
kl in antidiagonal n, f kl.1 * g kl.2‖
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_sum_mul_antidiagonal_of_summable_mul`：summable_sum_mul_antidiag
onal_of_summable_mul (h : Summable fun x : A × A => f x.1 * g x.2) : Summable fu
n n => ∑ kl in antidiagonal n, f kl…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Summable.mul_of_nonneg`：Summable.mul_of_nonneg {f : ι -> Real} {g : ι' -
> Real} (hf : Summable f) (hg : Summable g) (hf' : 0 <= f) (hg' : 0 <= g) : Summ
able fun x :…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun n => ‖∑ kl ∈ antidiagonal n, f kl.1 * g kl.2‖ := by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine this.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n ↦ ?_)
  calc
    ‖∑ kl ∈ antidiagonal n, f kl.1 * g kl.2‖ ≤ ∑ kl ∈ antidiagonal n, ‖f kl.1 * g kl.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ kl ∈ antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by gcongr; apply norm_mul_le
/-
**summable_sum_mul_antidiagonal_of_summable_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_sum_mul_antidiagonal_of_summable_norm' {f g : Nat -> R} (hf : Sum
mable fun x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖) (h'g : S
ummable g) : Summable fun n => ∑ kl in antidiagonal n, f kl.1 * g kl.2
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_sum_mul_antidiagonal_of_summable_mul`：summable_sum_mul_antidiag
onal_of_summable_mul (h : Summable fun x : A × A => f x.1 * g x.2) : Summable fu
n n => ∑ kl in antidiagonal n, f kl…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `summable_mul_of_summable_norm'`：summable_mul_of_summable_norm' {f : ι ->
 R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (h'f : Summable f) (hg : Summab
le fun x => ‖g x‖) (…
-/
theorem summable_sum_mul_antidiagonal_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    Summable fun n => ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  summable_sum_mul_antidiagonal_of_summable_mul (summable_mul_of_summable_norm' hf h'f hg h'g)

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
expressed by summing on `Finset.antidiagonal`.
See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
*not* absolutely summable, and `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'`
when the space is not complete. -/
/-
**tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] 
{f g : Nat -> R} (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
 ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`：∀ {α : Type u_3} {A : T
ype u_4} [inst : AddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A]   [inst_2 
: TopologicalSpace α] [inst_3 : NonUn…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `summable_mul_of_summable_norm`：summable_mul_of_summable_norm [CompleteSp
ace R] {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (hg : Summable 
fun x => ‖g x‖) : S…

--- 原说明 ---
The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
expressed by summing on `Finset.antidiagonal`.
See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
*not* absolutely summable, and `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summab
le_norm'`
when the space is not complete.
-/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  hf.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.of_norm (summable_mul_of_summable_norm hf hg)
/-
**tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' {f g : Nat -> R} 
(hf : Summable fun x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖)
 (h'g : Summable g) : ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, 
f kl.1 * g kl.2
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`：∀ {α : Type u_3} {A : T
ype u_4} [inst : AddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A]   [inst_2 
: TopologicalSpace α] [inst_3 : NonUn…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `summable_mul_of_summable_norm'`：summable_mul_of_summable_norm' {f : ι ->
 R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (h'f : Summable f) (hg : Summab
le fun x => ‖g x‖) (…
-/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  h'f.tsum_mul_tsum_eq_tsum_sum_antidiagonal h'g (summable_mul_of_summable_norm' hf h'f hg h'g)
/-
**summable_norm_sum_mul_range_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_norm_sum_mul_range_of_summable_norm {f g : Nat -> R} (hf : Summab
le fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ k in ra
nge (n + 1), f k * g (n - k)‖
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `summable_norm_sum_mul_antidiagonal_of_summable_norm`：summable_norm_sum_m
ul_antidiagonal_of_summable_norm {f g : Nat -> R} (hf : Summable fun x => ‖f x‖)
 (hg : Summable fun x => ‖g x‖) : Summabl…
-/
theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ k ∈ range (n + 1), f k * g (n - k)‖ := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
/-
**summable_sum_mul_range_of_summable_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_sum_mul_range_of_summable_norm' {f g : Nat -> R} (hf : Summable f
un x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖) (h'g : Summable
 g) : Summable fun n => ∑ k in range (n + 1), f k * g (n - k)
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `summable_sum_mul_antidiagonal_of_summable_norm'`：summable_sum_mul_antidi
agonal_of_summable_norm' {f g : Nat -> R} (hf : Summable fun x => ‖f x‖) (h'f : 
Summable f) (hg : Summable fun x => ‖…
-/
theorem summable_sum_mul_range_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    Summable fun n => ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_norm' hf h'f hg h'g

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
expressed by summing on `Finset.range`.
See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
not absolutely summable, and `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'` when the
space is not complete. -/
/-
**tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace R] {f g : 
Nat -> R} (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : ((∑' n
, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k)
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`：tsum_mul_tsum_e
q_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : Nat -> R} (hf 
: Summable fun x => ‖f x‖) (hg : Summable fun…

--- 原说明 ---
The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
expressed by summing on `Finset.range`.
See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
not absolutely summable, and `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'`
 when the
space is not complete.
-/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
/-
**hasSum_sum_range_mul_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_sum_range_mul_of_summable_norm [CompleteSpace R] {f g : Nat -> R} (
hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) : HasSum (fun n => 
∑ k in range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n)
参数：hf : Summable fun x => ‖f x‖；hg : Summable fun x => ‖g x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`：tsum_mul_tsum_eq_tsum_
sum_range_of_summable_norm [CompleteSpace R] {f g : Nat -> R} (hf : Summable fun
 x => ‖f x‖) (hg : Summable fun x => ‖…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `summable_norm_sum_mul_range_of_summable_norm`：summable_norm_sum_mul_rang
e_of_summable_norm {f g : Nat -> R} (hf : Summable fun x => ‖f x‖) (hg : Summabl
e fun x => ‖g x‖) : Summable fun n…
-/
theorem hasSum_sum_range_mul_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    HasSum (fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n) := by
  convert! (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm.hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
/-
**tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' {f g : Nat -> R} (hf : S
ummable fun x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖) (h'g :
 Summable g) : ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (
n - k)
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'`：tsum_mul_tsum_
eq_tsum_sum_antidiagonal_of_summable_norm' {f g : Nat -> R} (hf : Summable fun x
 => ‖f x‖) (h'f : Summable f) (hg : Summable f…
-/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hf h'f hg h'g
/-
**hasSum_sum_range_mul_of_summable_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_sum_range_mul_of_summable_norm' {f g : Nat -> R} (hf : Summable fun
 x => ‖f x‖) (h'f : Summable f) (hg : Summable fun x => ‖g x‖) (h'g : Summable g
) : HasSum (fun n => ∑ k in range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n,
 g n)
参数：hf : Summable fun x => ‖f x‖；h'f : Summable f；hg : Summable fun x => ‖g x‖；h'
g : Summable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'`：tsum_mul_tsum_eq_tsum
_sum_range_of_summable_norm' {f g : Nat -> R} (hf : Summable fun x => ‖f x‖) (h'
f : Summable f) (hg : Summable fun x =>…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `summable_sum_mul_range_of_summable_norm'`：summable_sum_mul_range_of_summ
able_norm' {f g : Nat -> R} (hf : Summable fun x => ‖f x‖) (h'f : Summable f) (h
g : Summable fun x => ‖g x‖) (…
-/
theorem hasSum_sum_range_mul_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    HasSum (fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n) := by
  convert! (summable_sum_mul_range_of_summable_norm' hf h'f hg h'g).hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' hf h'f hg h'g

end Nat

/-
**summable_of_absolute_convergence_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {f : ℕ → ℝ}, (∃ r, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, |f i|)
 Filter.atTop (nhds r)) → Summable f
参数：∃ r, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, |f i|) Filter.atTop (nhds
 r)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasSum_iff_tendsto_nat_of_nonneg`：hasSum_iff_tendsto_nat_of_nonneg {f : 
Nat -> Real} (hf : forall i, 0 <= f i) (r : Real) : HasSum f r ↔ Tendsto (fun n 
: Nat => ∑ i in Finset…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n ↦ ∑ i ∈ range n, |f i|) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ => by
    refine .of_norm ⟨r, (hasSum_iff_tendsto_nat_of_nonneg ?_ _).2 ?_⟩
    · exact fun i ↦ norm_nonneg _
    · simpa only using! hr
