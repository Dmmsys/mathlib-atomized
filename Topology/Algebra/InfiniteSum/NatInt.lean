/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Logic.Encodable.Lattice
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums and products over `ℕ` and `ℤ`

This file contains lemmas about `HasSum`, `Summable`, `tsum`, `HasProd`, `Multipliable`, and `tprod`
applied to the important special cases where the domain is `ℕ` or `ℤ`. For instance, we prove the
formula `∑ i ∈ range k, f i + ∑' i, f (i + k) = ∑' i, f i`, ∈ `sum_add_tsum_nat_add`, as well as
several results relating sums and products on `ℕ` to sums and products on `ℤ`.
-/

public section

noncomputable section

open Filter Finset Function Encodable

open scoped Topology

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] {m m' : M}

variable {G : Type*} [CommGroup G] {g g' : G}
-- don't declare `[IsTopologicalAddGroup G]`, here as some results require
-- `[IsUniformAddGroup G]` instead

/-!
## Sums over `ℕ`
-/

section Nat

section Monoid

/-- If `f : ℕ → M` has product `m`, then the partial products `∏ i ∈ range n, f i` converge
to `m`. -/
@[to_additive /-- If `f : ℕ → M` has sum `m`, then the partial sums `∑ i ∈ range n, f i` converge
to `m`. -/]
/-
**HasProd.tendsto_prod_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.tendsto_prod_nat {f : Nat -> M} (h : HasProd f m) : Tendsto (fun n
 => ∏ i in range n, f i) atTop (𝓝 m)
参数：h : HasProd f m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
-/
theorem HasProd.tendsto_prod_nat {f : ℕ → M} (h : HasProd f m) :
    Tendsto (fun n ↦ ∏ i ∈ range n, f i) atTop (𝓝 m) :=
  h.comp tendsto_finset_range

/-- If `f : ℕ → M` is multipliable, then the partial products `∏ i ∈ range n, f i` converge
to `∏' i, f i`. -/
@[to_additive /-- If `f : ℕ → M` is summable, then the partial sums `∑ i ∈ range n, f i` converge
to `∑' i, f i`. -/]
/-
**Multipliable.tendsto_prod_tprod_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.tendsto_prod_tprod_nat {f : Nat -> M} (h : Multipliable f) : 
Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 (∏' i, f i))
参数：h : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tendsto_prod_nat`：HasProd.tendsto_prod_nat {f : Nat -> M} (h : H
asProd f m) : Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.tendsto_prod_tprod_nat {f : ℕ → M} (h : Multipliable f) :
    Tendsto (fun n ↦ ∏ i ∈ range n, f i) atTop (𝓝 (∏' i, f i)) :=
  h.hasProd.tendsto_prod_nat

namespace HasProd

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
/-
**HasProd.prod_range_mul** 是 Mathlib 中的一个定理，位于命名空间 `HasProd`。
形式化陈述：prod_range_mul {f : Nat -> M} {k : Nat} (h : HasProd (fun n => f (n + k)) 
m) : HasProd f ((∏ i in range k, f i) * m)
参数：h : HasProd (fun n => f (n + k)) m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.mul_compl`：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) 
: s -> α) a) (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
· 使用定理 `Finset.hasProd`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [i
nst_1 : TopologicalSpace α] (s : Finset β) (f : β → α)   (L : optParam (Summatio
nFil…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
-/
theorem prod_range_mul {f : ℕ → M} {k : ℕ} (h : HasProd (fun n ↦ f (n + k)) m) :
    HasProd f ((∏ i ∈ range k, f i) * m) :=
  ((range k).hasProd f).mul_compl <| (notMemRangeEquiv k).symm.hasProd_iff.mp h

@[to_additive]
/-
**HasProd.zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `HasProd`。
形式化陈述：zero_mul {f : Nat -> M} (h : HasProd (fun n => f (n + 1)) m) : HasProd f (
f 0 * m)
参数：h : HasProd (fun n => f (n + 1)) m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_one`：prod_range_one (f : Nat -> M) : ∏ k in range 1, f
 k = f 0
· 使用定理 `HasProd.prod_range_mul`：prod_range_mul {f : Nat -> M} {k : Nat} (h : Has
Prod (fun n => f (n + k)) m) : HasProd f ((∏ i in range k, f i) * m)
-/
theorem zero_mul {f : ℕ → M} (h : HasProd (fun n ↦ f (n + 1)) m) :
    HasProd f (f 0 * m) := by
  simpa only [prod_range_one] using h.prod_range_mul

@[to_additive]
/-
**HasProd.even_mul_odd** 是 Mathlib 中的一个定理，位于命名空间 `HasProd`。
形式化陈述：even_mul_odd {f : Nat -> M} (he : HasProd (fun k => f (2 * k)) m) (ho : Ha
sProd (fun k => f (2 * k + 1)) m') : HasProd f (m * m')
参数：he : HasProd (fun k => f (2 * k)) m；ho : HasProd (fun k => f (2 * k + 1)) m'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.hasProd_range_iff`：Function.Injective.hasProd_range_i
ff {g : γ -> β} (hg : Injective g) : HasProd (fun x : Set.range g => f x) a ↔ Ha
sProd (f ∘ g) a
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HasProd.mul_isCompl`：HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t
) (ha : HasProd (f ∘ (↑) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : HasP
rod f (a …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `range_two_mul`：∀ (α : Type u_4) [inst : NonAssocSemiring α], (Set.range 
fun x => 2 * x) = {a | Even a}
· 使用定理 `range_two_mul_add_one`：∀ (α : Type u_4) [inst : Semiring α], (Set.range 
fun x => 2 * x + 1) = {a | Odd a}
· 使用引理 `Nat.isCompl_even_odd`：isCompl_even_odd : IsCompl { n : Nat | Even n } { 
n | Odd n }
-/
theorem even_mul_odd {f : ℕ → M} (he : HasProd (fun k ↦ f (2 * k)) m)
    (ho : HasProd (fun k ↦ f (2 * k + 1)) m') : HasProd f (m * m') := by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace ho := ((add_left_injective 1).comp this).hasProd_range_iff.2 ho
  refine (this.hasProd_range_iff.2 he).mul_isCompl ?_ ho
  simpa [Function.comp_def] using Nat.isCompl_even_odd

end ContinuousMul

end HasProd

namespace Multipliable

@[to_additive]
/-
**Multipliable.hasProd_iff_tendsto_nat** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：hasProd_iff_tendsto_nat [T2Space M] {f : Nat -> M} (hf : Multipliable f) :
 HasProd f m ↔ Tendsto (fun n : Nat => ∏ i in range n, f i) atTop (𝓝 m)
参数：hf : Multipliable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tendsto_prod_nat`：HasProd.tendsto_prod_nat {f : Nat -> M} (h : H
asProd f m) : Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem hasProd_iff_tendsto_nat [T2Space M] {f : ℕ → M} (hf : Multipliable f) :
    HasProd f m ↔ Tendsto (fun n : ℕ ↦ ∏ i ∈ range n, f i) atTop (𝓝 m) := by
  refine ⟨fun h ↦ h.tendsto_prod_nat, fun h ↦ ?_⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_prod_nat]
  exact hf.hasProd

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
/-
**Multipliable.comp_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：comp_nat_add {f : Nat -> M} {k : Nat} (h : Multipliable fun n => f (n + k)
) : Multipliable f
参数：h : Multipliable fun n => f (n + k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.prod_range_mul`：prod_range_mul {f : Nat -> M} {k : Nat} (h : Has
Prod (fun n => f (n + k)) m) : HasProd f ((∏ i in range k, f i) * m)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem comp_nat_add {f : ℕ → M} {k : ℕ} (h : Multipliable fun n ↦ f (n + k)) : Multipliable f :=
  h.hasProd.prod_range_mul.multipliable

@[to_additive]
/-
**Multipliable.even_mul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：even_mul_odd {f : Nat -> M} (he : Multipliable fun k => f (2 * k)) (ho : M
ultipliable fun k => f (2 * k + 1)) : Multipliable f
参数：he : Multipliable fun k => f (2 * k)；ho : Multipliable fun k => f (2 * k + 1)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.even_mul_odd`：even_mul_odd {f : Nat -> M} (he : HasProd (fun k =
> f (2 * k)) m) (ho : HasProd (fun k => f (2 * k + 1)) m') : HasProd f (m * m')
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem even_mul_odd {f : ℕ → M} (he : Multipliable fun k ↦ f (2 * k))
    (ho : Multipliable fun k ↦ f (2 * k + 1)) : Multipliable f :=
  (he.hasProd.even_mul_odd ho.hasProd).multipliable

end ContinuousMul

end Multipliable

section tprod

variable {α β γ : Type*}

section Encodable

variable [Encodable β]

/-- You can compute a product over an encodable type by multiplying over the natural numbers and
taking a supremum. -/
@[to_additive /-- You can compute a sum over an encodable type by summing over the natural numbers
and taking a supremum. This is useful for outer measures. -/]
/-
**tprod_iSup_decode** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tprod_iSup_decode₂ [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (s : β → α) :
    ∏' i : ℕ, m (⨆ b ∈ decode₂ β i, s b) = ∏' b : β, m (s b) := by
  rw [← tprod_extend_one (@encode_injective β _)]
  refine tprod_congr fun n ↦ ?_
  rcases em (n ∈ Set.range (encode : β → ℕ)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff, ne_eq, not_not] at hn
    simp [hn, m0]

/-- `tprod_iSup_decode₂` specialized to the complete lattice of sets. -/
@[to_additive /-- `tsum_iSup_decode₂` specialized to the complete lattice of sets. -/]
/-
**tprod_iUnion_decode** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tprod_iSup_decode₂` specialized to the complete lattice of sets.
-/
theorem tprod_iUnion_decode₂ (m : Set α → M) (m0 : m ∅ = 1) (s : β → Set α) :
    ∏' i, m (⋃ b ∈ decode₂ β i, s b) = ∏' b, m (s b) :=
  tprod_iSup_decode₂ m m0 s

end Encodable

/-! Some properties about measure-like functions. These could also be functions defined on complete
  sublattices of sets, with the property that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/
section Countable

variable [Countable β]

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on countable
types -/
@[to_additive
/-- If a function is countably sub-additive then it is sub-additive on countable types -/]
/-
**rel_iSup_tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_iSup_tprod [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M
 -> Prop) (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : 
β -> α) : R (m (⨆ b : β, s b)) (∏' b : β, m (s b))
参数：m : α -> M；m0 : m ⊥ = 1；R : M -> M -> Prop；m_iSup : forall s : Nat -> α, R (m
 (⨆ i, s i)) (∏' i, m (s i))；s : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Encodable.iSup_decode₂`：iSup_decode₂ [CompleteLattice α] (f : β -> α) : 
⨆ (i : Nat) (b in decode₂ β i), f b = (⨆ b, f b)
· 使用定理 `tprod_iSup_decode₂`：tprod_iSup_decode₂ [CompleteLattice α] (m : α -> M) 
(m0 : m ⊥ = 1) (s : β -> α) : ∏' i : Nat, m (⨆ b in decode₂ β i, s b) = ∏' b : β
, m (s b…
-/
theorem rel_iSup_tprod [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : β → α) :
    R (m (⨆ b : β, s b)) (∏' b : β, m (s b)) := by
  cases nonempty_encodable β
  rw [← iSup_decode₂, ← tprod_iSup_decode₂ _ m0 s]
  exact m_iSup _

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on finite sets -/
@[to_additive /-- If a function is countably sub-additive then it is sub-additive on finite sets -/]
/-
**rel_iSup_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_iSup_prod [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M 
-> Prop) (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : γ
 -> α) (t : Finset γ) : R (m (⨆ d in t, s d)) (∏ d in t, m (s d))
参数：m : α -> M；m0 : m ⊥ = 1；R : M -> M -> Prop；m_iSup : forall s : Nat -> α, R (m
 (⨆ i, s i)) (∏' i, m (s i))；s : γ -> α；t : Finset γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.tprod_subtype`：Finset.tprod_subtype (s : Finset β) (f : β -> α) :
 ∏' x : { x // x in s }, f x = ∏ x in s, f x
· 使用定理 `rel_iSup_tprod`：rel_iSup_tprod [CompleteLattice α] (m : α -> M) (m0 : m 
⊥ = 1) (R : M -> M -> Prop) (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' 
i, m…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If a function is countably sub-multiplicative then it is sub-multiplicative on f
inite sets
-/
theorem rel_iSup_prod [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : γ → α) (t : Finset γ) :
    R (m (⨆ d ∈ t, s d)) (∏ d ∈ t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tprod_subtype]
  exact rel_iSup_tprod m m0 R m_iSup _

/-- If a function is countably sub-multiplicative then it is binary sub-multiplicative -/
@[to_additive /-- If a function is countably sub-additive then it is binary sub-additive -/]
/-
**rel_sup_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_sup_mul [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M ->
 Prop) (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ :
 α) : R (m (s₁ ⊔ s₂)) (m s₁ * m s₂)
参数：m : α -> M；m0 : m ⊥ = 1；R : M -> M -> Prop；m_iSup : forall s : Nat -> α, R (m
 (⨆ i, s i)) (∏' i, m (s i))；s₁ s₂ : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tprod_fintype`：tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L
] b, f b = ∏ b, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Fintype.prod_bool`：prod_bool [CommMonoid α] (f : Bool -> α) : ∏ b, f b =
 f true * f false
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `cond.eq_2`：∀ {α : Sort u} (x y : α), (bif false then x else y) = y
· 使用定理 `rel_iSup_tprod`：rel_iSup_tprod [CompleteLattice α] (m : α -> M) (m0 : m 
⊥ = 1) (R : M -> M -> Prop) (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' 
i, m…

--- 原说明 ---
If a function is countably sub-multiplicative then it is binary sub-multiplicati
ve
-/
theorem rel_sup_mul [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ : α) :
    R (m (s₁ ⊔ s₂)) (m s₁ * m s₂) := by
  convert! rel_iSup_tprod m m0 R m_iSup fun b ↦ cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]

end Countable

section ContinuousMul

variable [T2Space M] [ContinuousMul M]

@[to_additive]
/-
**Multipliable.prod_mul_tprod_nat_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] [inst_1 : TopologicalSpace M] [T2Sp
ace M] [ContinuousMul M] {f : ℕ → M} {k : ℕ},   (Multipliable fun n => f (n + k)
) → (∏ i ∈ Finset.range k, f i) * ∏' (i : ℕ), f (i + k) = ∏' (i : ℕ), f i
参数：Multipliable fun n => f (n + k)；∏ i ∈ Finset.range k, f i；i : ℕ；i + k；i : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.prod_range_mul`：prod_range_mul {f : Nat -> M} {k : Nat} (h : Has
Prod (fun n => f (n + k)) m) : HasProd f ((∏ i in range k, f i) * m)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.prod_mul_tprod_nat_mul'
    {f : ℕ → M} {k : ℕ} (h : Multipliable (fun n ↦ f (n + k))) :
    ((∏ i ∈ range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  h.hasProd.prod_range_mul.tprod_eq.symm

@[to_additive]
/-
**tprod_eq_zero_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_zero_mul' {f : Nat -> M} (hf : Multipliable (fun n => f (n + 1)))
 : ∏' b, f b = f 0 * ∏' b, f (b + 1)
参数：hf : Multipliable (fun n => f (n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_range_one`：prod_range_one (f : Nat -> M) : ∏ k in range 1, f
 k = f 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multipliable.prod_mul_tprod_nat_mul'`：∀ {M : Type u_1} [inst : CommMonoi
d M] [inst_1 : TopologicalSpace M] [T2Space M] [ContinuousMul M] {f : ℕ → M} {k 
: ℕ},   (Multipliable fun …
-/
theorem tprod_eq_zero_mul'
    {f : ℕ → M} (hf : Multipliable (fun n ↦ f (n + 1))) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) := by
  simpa only [prod_range_one] using hf.prod_mul_tprod_nat_mul'.symm

@[to_additive]
/-
**tprod_even_mul_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_even_mul_odd {f : Nat -> M} (he : Multipliable fun k => f (2 * k)) (
ho : Multipliable fun k => f (2 * k + 1)) : (∏' k, f (2 * k)) * ∏' k, f (2 * k +
 1) = ∏' k, f k
参数：he : Multipliable fun k => f (2 * k)；ho : Multipliable fun k => f (2 * k + 1)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.even_mul_odd`：even_mul_odd {f : Nat -> M} (he : HasProd (fun k =
> f (2 * k)) m) (ho : HasProd (fun k => f (2 * k + 1)) m') : HasProd f (m * m')
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem tprod_even_mul_odd {f : ℕ → M} (he : Multipliable fun k ↦ f (2 * k))
    (ho : Multipliable fun k ↦ f (2 * k + 1)) :
    (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' k, f k :=
  (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm

end ContinuousMul

end tprod

end Monoid

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/-
**hasProd_nat_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_nat_add_iff {f : Nat -> G} (k : Nat) : HasProd (fun n => f (n + k)
) g ↔ HasProd f (g * ∏ i in range k, f i)
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `coe_notMemRangeEquiv_symm`：coe_notMemRangeEquiv_symm (k : Nat) : ((notMe
mRangeEquiv k).symm : Nat -> { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Finset.hasProd_compl_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : CommGr
oup α] [inst_1 : TopologicalSpace α] [IsTopologicalGroup α] {f : β → α}   {a : α
} (s : Finset …
-/
theorem hasProd_nat_add_iff {f : ℕ → G} (k : ℕ) :
    HasProd (fun n ↦ f (n + k)) g ↔ HasProd f (g * ∏ i ∈ range k, f i) := by
  refine Iff.trans ?_ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff, Function.comp_def, coe_notMemRangeEquiv_symm]

@[to_additive]
/-
**multipliable_nat_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_nat_add_iff {f : Nat -> G} (k : Nat) : (Multipliable fun n =>
 f (n + k)) ↔ Multipliable f
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Surjective.multipliable_iff_of_hasProd_iff`：Function.Surjective
.multipliable_iff_of_hasProd_iff {α' : Type*} [CommMonoid α'] [TopologicalSpace 
α'] {e : α' -> α} (hes : Function.Surject…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `hasProd_nat_add_iff`：hasProd_nat_add_iff {f : Nat -> G} (k : Nat) : HasP
rod (fun n => f (n + k)) g ↔ HasProd f (g * ∏ i in range k, f i)
-/
theorem multipliable_nat_add_iff {f : ℕ → G} (k : ℕ) :
    (Multipliable fun n ↦ f (n + k)) ↔ Multipliable f :=
  Iff.symm <|
    (Equiv.mulRight (∏ i ∈ range k, f i)).surjective.multipliable_iff_of_hasProd_iff
      (hasProd_nat_add_iff k).symm

@[to_additive]
/-
**hasProd_nat_add_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_nat_add_iff' {f : Nat -> G} (k : Nat) : HasProd (fun n => f (n + k
)) (g / ∏ i in range k, f i) ↔ HasProd f g
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasProd_nat_add_iff' {f : ℕ → G} (k : ℕ) :
    HasProd (fun n ↦ f (n + k)) (g / ∏ i ∈ range k, f i) ↔ HasProd f g := by
  simp [hasProd_nat_add_iff]

@[to_additive]
/-
**Multipliable.prod_mul_tprod_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {G : Type u_2} [inst : CommGroup G] [inst_1 : TopologicalSpace G] [IsTop
ologicalGroup G] [T2Space G] {f : ℕ → G}   (k : ℕ), Multipliable f → (∏ i ∈ Fins
et.range k, f i) * ∏' (i : ℕ), f (i + k) = ∏' (i : ℕ), f i
参数：k : ℕ；∏ i ∈ Finset.range k, f i；i : ℕ；i + k；i : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.prod_mul_tprod_nat_mul'`：∀ {M : Type u_1} [inst : CommMonoi
d M] [inst_1 : TopologicalSpace M] [T2Space M] [ContinuousMul M] {f : ℕ → M} {k 
: ℕ},   (Multipliable fun …
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `multipliable_nat_add_iff`：multipliable_nat_add_iff {f : Nat -> G} (k : N
at) : (Multipliable fun n => f (n + k)) ↔ Multipliable f
-/
protected theorem Multipliable.prod_mul_tprod_nat_add [T2Space G] {f : ℕ → G} (k : ℕ)
    (h : Multipliable f) : ((∏ i ∈ range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  Multipliable.prod_mul_tprod_nat_mul' <| (multipliable_nat_add_iff k).2 h

@[to_additive]
/-
**Multipliable.tprod_eq_zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {G : Type u_2} [inst : CommGroup G] [inst_1 : TopologicalSpace G] [IsTop
ologicalGroup G] [T2Space G] {f : ℕ → G},   Multipliable f → ∏' (b : ℕ), f b = f
 0 * ∏' (b : ℕ), f (b + 1)
参数：b : ℕ；b : ℕ；b + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_eq_zero_mul'`：tprod_eq_zero_mul' {f : Nat -> M} (hf : Multipliable
 (fun n => f (n + 1))) : ∏' b, f b = f 0 * ∏' b, f (b + 1)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `multipliable_nat_add_iff`：multipliable_nat_add_iff {f : Nat -> G} (k : N
at) : (Multipliable fun n => f (n + k)) ↔ Multipliable f
-/
protected theorem Multipliable.tprod_eq_zero_mul [T2Space G] {f : ℕ → G} (hf : Multipliable f) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) :=
  tprod_eq_zero_mul' <| (multipliable_nat_add_iff 1).2 hf

/-- For `f : ℕ → G`, the product `∏' k, f (k + i)` tends to one. This does not require a
multipliability assumption on `f`, as otherwise all such products are one. -/
@[to_additive /-- For `f : ℕ → G`, the sum `∑' k, f (k + i)` tends to zero. This does not require a
summability assumption on `f`, as otherwise all such sums are zero. -/]
/-
**tendsto_prod_nat_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_prod_nat_add [T2Space G] (f : Nat -> G) : Tendsto (fun i => ∏' k, 
f (k + i)) atTop (𝓝 1)
参数：f : Nat -> G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_iff_eq_mul`：div_eq_iff_eq_mul : a / b = c ↔ a = c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Multipliable.prod_mul_tprod_nat_add`：∀ {G : Type u_2} [inst : CommGroup 
G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {f : ℕ → G} 
  (k : ℕ), Multipliable f…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用定理 `HasProd.tendsto_prod_nat`：HasProd.tendsto_prod_nat {f : Nat -> M} (h : H
asProd f m) : Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `multipliable_nat_add_iff`：multipliable_nat_add_iff {f : Nat -> G} (k : N
at) : (Multipliable fun n => f (n + k)) ↔ Multipliable f
-/
theorem tendsto_prod_nat_add [T2Space G] (f : ℕ → G) :
    Tendsto (fun i ↦ ∏' k, f (k + i)) atTop (𝓝 1) := by
  by_cases hf : Multipliable f
  · have h₀ : (fun i ↦ (∏' i, f i) / ∏ j ∈ range i, f j) = fun i ↦ ∏' k : ℕ, f (k + i) := by
      ext1 i
      rw [div_eq_iff_eq_mul, mul_comm, hf.prod_mul_tprod_nat_add i]
    have h₁ : Tendsto (fun _ : ℕ ↦ ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_prod_nat
  · refine tendsto_const_nhds.congr fun n ↦ (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [multipliable_nat_add_iff n]

end IsTopologicalGroup

section IsUniformGroup

variable [UniformSpace G] [IsUniformGroup G]

@[to_additive]
/-
**cauchySeq_finset_iff_nat_tprod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_iff_nat_tprod_vanishing {f : Nat -> G} : (CauchySeq fun s
 : Finset Nat => ∏ n in s, f n) ↔ forall e in 𝓝 (1 : G), exists N : Nat, forall 
t subseteq {n | N <= n}, (∏' n : t, f n) in e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `cauchySeq_finset_iff_tprod_vanishing`：cauchySeq_finset_iff_tprod_vanishi
ng : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔ forall e in 𝓝 (1 : α), exis
ts s : Finset β, forall t …
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
-/
theorem cauchySeq_finset_iff_nat_tprod_vanishing {f : ℕ → G} :
    (CauchySeq fun s : Finset ℕ ↦ ∏ n ∈ s, f n) ↔
      ∀ e ∈ 𝓝 (1 : G), ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e := by
  refine cauchySeq_finset_iff_tprod_vanishing.trans ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0,
      fun t ht ↦ hs _ <| Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms ↦ (s.le_max' _ hms).not_gt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs ↦ h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht ↦ hN _ fun n hnt ↦
      le_of_not_gt fun h ↦ Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

variable [CompleteSpace G]

@[to_additive]
/-
**multipliable_iff_nat_tprod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_iff_nat_tprod_vanishing {f : Nat -> G} : Multipliable f ↔ for
all e in 𝓝 1, exists N : Nat, forall t subseteq {n | N <= n}, (∏' n : t, f n) in
 e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multipliable_iff_cauchySeq_finset`：multipliable_iff_cauchySeq_finset [Co
mmMonoid α] [CompleteSpace α] {f : β -> α} : Multipliable f ↔ CauchySeq fun s : 
Finset β => ∏ b in s, f…
· 使用定理 `cauchySeq_finset_iff_nat_tprod_vanishing`：cauchySeq_finset_iff_nat_tprod
_vanishing {f : Nat -> G} : (CauchySeq fun s : Finset Nat => ∏ n in s, f n) ↔ fo
rall e in 𝓝 (1 : G), exists N …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem multipliable_iff_nat_tprod_vanishing {f : ℕ → G} : Multipliable f ↔
    ∀ e ∈ 𝓝 1, ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_nat_tprod_vanishing]

end IsUniformGroup

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/-
**Multipliable.nat_tprod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.nat_tprod_vanishing {f : Nat -> G} (hf : Multipliable f) ⦃e :
 Set G⦄ (he : e in 𝓝 1) : exists N : Nat, forall t subseteq {n | N <= n}, (∏' n 
: t, f n) in e
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformGroup_of_commGroup`：isUniformGroup_of_commGroup : IsUniformGrou
p G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_finset_iff_nat_tprod_vanishing`：cauchySeq_finset_iff_nat_tprod
_vanishing {f : Nat -> G} : (CauchySeq fun s : Finset Nat => ∏ n in s, f n) ↔ fo
rall e in 𝓝 (1 : G), exists N …
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.nat_tprod_vanishing {f : ℕ → G} (hf : Multipliable f) ⦃e : Set G⦄
    (he : e ∈ 𝓝 1) : ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  cauchySeq_finset_iff_nat_tprod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
/-
**Multipliable.tendsto_atTop_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.tendsto_atTop_one {f : Nat -> G} (hf : Multipliable f) : Tend
sto f atTop (𝓝 1)
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Multipliable.tendsto_cofinite_one`：Multipliable.tendsto_cofinite_one (hf
 : Multipliable f) : Tendsto f cofinite (𝓝 1)
-/
theorem Multipliable.tendsto_atTop_one {f : ℕ → G} (hf : Multipliable f) :
    Tendsto f atTop (𝓝 1) := by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_one

end IsTopologicalGroup

end Nat

/-!
## Sums over `ℤ`

In this section we prove a variety of lemmas relating sums over `ℕ` to sums over `ℤ`.
-/

section Int

section Monoid

@[to_additive HasSum.nat_add_neg_add_one]
/-
**HasProd.nat_mul_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.nat_mul_neg_add_one {f : Int -> M} (hf : HasProd f m) : HasProd (f
un n : Nat => f n * f (-(n + 1))) m
参数：hf : HasProd f m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.negSucc.inj`：∀ {a a_1 : ℕ}, Int.negSucc a = Int.negSucc a_1 → a = a_
1
· 使用定理 `HasProd.hasProd_of_prod_eq`：HasProd.hasProd_of_prod_eq {g : γ -> α} (h_e
q : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' -> exists
 u', u subseteq …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
-/
lemma HasProd.nat_mul_neg_add_one {f : ℤ → M} (hf : HasProd f m) :
    HasProd (fun n : ℕ ↦ f n * f (-(n + 1))) m := by
  change HasProd (fun n : ℕ ↦ f n * f (Int.negSucc n)) m
  have : Injective Int.negSucc := @Int.negSucc.inj
  refine hf.hasProd_of_prod_eq fun u ↦ ?_
  refine ⟨u.preimage _ Nat.cast_injective.injOn ∪ u.preimage _ this.injOn,
      fun v' hv' ↦ ⟨v'.image Nat.cast ∪ v'.image Int.negSucc, fun x hx ↦ ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [prod_union, prod_image Nat.cast_injective.injOn, prod_image this.injOn,
      prod_mul_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, reduceCtorEq]

@[to_additive Summable.nat_add_neg_add_one]
/-
**Multipliable.nat_mul_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.nat_mul_neg_add_one {f : Int -> M} (hf : Multipliable f) : Mu
ltipliable (fun n : Nat => f n * f (-(n + 1)))
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用引理 `HasProd.nat_mul_neg_add_one`：HasProd.nat_mul_neg_add_one {f : Int -> M} 
(hf : HasProd f m) : HasProd (fun n : Nat => f n * f (-(n + 1))) m
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma Multipliable.nat_mul_neg_add_one {f : ℤ → M} (hf : Multipliable f) :
    Multipliable (fun n : ℕ ↦ f n * f (-(n + 1))) :=
  hf.hasProd.nat_mul_neg_add_one.multipliable

@[to_additive tsum_nat_add_neg_add_one]
/-
**tprod_nat_mul_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_nat_mul_neg_add_one [T2Space M] {f : Int -> M} (hf : Multipliable f)
 : ∏' (n : Nat), (f n * f (-(n + 1))) = ∏' (n : Int), f n
参数：hf : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HasProd.nat_mul_neg_add_one`：HasProd.nat_mul_neg_add_one {f : Int -> M} 
(hf : HasProd f m) : HasProd (fun n : Nat => f n * f (-(n + 1))) m
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma tprod_nat_mul_neg_add_one [T2Space M] {f : ℤ → M} (hf : Multipliable f) :
    ∏' (n : ℕ), (f n * f (-(n + 1))) = ∏' (n : ℤ), f n :=
  hf.hasProd.nat_mul_neg_add_one.tprod_eq

section ContinuousMul

variable [ContinuousMul M]

@[to_additive HasSum.of_nat_of_neg_add_one]
/-
**HasProd.of_nat_of_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.of_nat_of_neg_add_one {f : Int -> M} (hf₁ : HasProd (fun n : Nat =
> f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n + 1))) m') : HasProd f (m * m')
参数：hf₁ : HasProd (fun n : Nat => f n) m；hf₂ : HasProd (fun n : Nat => f (-(n + 1
))) m'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.negSucc.inj`：∀ {a a_1 : ℕ}, Int.negSucc a = Int.negSucc a_1 → a = a_
1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Int.negSucc.injEq`：∀ (a a_1 : ℕ), (Int.negSucc a = Int.negSucc a_1) = (a
 = a_1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `HasProd.mul_isCompl`：HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t
) (ha : HasProd (f ∘ (↑) : s -> α) a) (hb : HasProd (f ∘ (↑) : t -> α) b) : HasP
rod f (a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.hasProd_range_iff`：Function.Injective.hasProd_range_i
ff {g : γ -> β} (hg : Injective g) : HasProd (fun x : Set.range g => f x) a ↔ Ha
sProd (f ∘ g) a
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
lemma HasProd.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : HasProd (fun n : ℕ ↦ f n) m) (hf₂ : HasProd (fun n : ℕ ↦ f (-(n + 1))) m') :
    HasProd f (m * m') := by
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (Nat.cast_injective.hasProd_range_iff.mpr hf₁).mul_isCompl
    this (hi₂.hasProd_range_iff.mpr hf₂)


@[to_additive Summable.of_nat_of_neg_add_one]
/-
**Multipliable.of_nat_of_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.of_nat_of_neg_add_one {f : Int -> M} (hf₁ : Multipliable fun 
n : Nat => f n) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) : Multipliable 
f
参数：hf₁ : Multipliable fun n : Nat => f n；hf₂ : Multipliable fun n : Nat => f (-(
n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用引理 `HasProd.of_nat_of_neg_add_one`：HasProd.of_nat_of_neg_add_one {f : Int ->
 M} (hf₁ : HasProd (fun n : Nat => f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n
 + 1))) m') : HasPr…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma Multipliable.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_nat_of_neg_add_one]
/-
**tprod_of_nat_of_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_of_nat_of_neg_add_one [T2Space M] {f : Int -> M} (hf₁ : Multipliable
 fun n : Nat => f n) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) : ∏' n : I
nt, f n = (∏' n : Nat, f n) * ∏' n : Nat, f (-(n + 1))
参数：hf₁ : Multipliable fun n : Nat => f n；hf₂ : Multipliable fun n : Nat => f (-(
n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HasProd.of_nat_of_neg_add_one`：HasProd.of_nat_of_neg_add_one {f : Int ->
 M} (hf₁ : HasProd (fun n : Nat => f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n
 + 1))) m') : HasPr…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma tprod_of_nat_of_neg_add_one [T2Space M] {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f n) * ∏' n : ℕ, f (-(n + 1)) :=
  (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).tprod_eq

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have products `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
product `a * b`. -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have sums `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
sum `a + b`. -/]
/-
**HasProd.int_rec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.int_rec {f g : Nat -> M} (hf : HasProd f m) (hg : HasProd g m') : 
HasProd (Int.rec f g) (m * m')
参数：hf : HasProd f m；hg : HasProd g m'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProd.of_nat_of_neg_add_one`：HasProd.of_nat_of_neg_add_one {f : Int ->
 M} (hf₁ : HasProd (fun n : Nat => f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n
 + 1))) m') : HasPr…
-/
lemma HasProd.int_rec {f g : ℕ → M} (hf : HasProd f m) (hg : HasProd g m') :
    HasProd (Int.rec f g) (m * m') :=
  HasProd.of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/]
/-
**Multipliable.int_rec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.int_rec {f g : Nat -> M} (hf : Multipliable f) (hg : Multipli
able g) : Multipliable (Int.rec f g)
参数：hf : Multipliable f；hg : Multipliable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multipliable.of_nat_of_neg_add_one`：Multipliable.of_nat_of_neg_add_one {
f : Int -> M} (hf₁ : Multipliable fun n : Nat => f n) (hf₂ : Multipliable fun n 
: Nat => f (-(n + 1))) :…
-/
lemma Multipliable.int_rec {f g : ℕ → M} (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable (Int.rec f g) :=
  .of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable, then the product of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`(∏' n, f n) * ∏' n, g n`. -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable, then the sum of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`∑' n, f n + ∑' n, g n`. -/]
/-
**tprod_int_rec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_int_rec [T2Space M] {f g : Nat -> M} (hf : Multipliable f) (hg : Mul
tipliable g) : ∏' n : Int, Int.rec f g n = (∏' n : Nat, f n) * ∏' n : Nat, g n
参数：hf : Multipliable f；hg : Multipliable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HasProd.int_rec`：HasProd.int_rec {f g : Nat -> M} (hf : HasProd f m) (hg
 : HasProd g m') : HasProd (Int.rec f g) (m * m')
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma tprod_int_rec [T2Space M] {f g : ℕ → M} (hf : Multipliable f) (hg : Multipliable g) :
    ∏' n : ℤ, Int.rec f g n = (∏' n : ℕ, f n) * ∏' n : ℕ, g n :=
  (hf.hasProd.int_rec hg.hasProd).tprod_eq

@[to_additive]
/-
**HasProd.nat_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.nat_mul_neg {f : Int -> M} (hf : HasProd f m) : HasProd (fun n : N
at => f n * f (-n)) (m * f 0)
参数：hf : HasProd f m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.hasProd_of_prod_eq`：HasProd.hasProd_of_prod_eq {g : γ -> α} (h_e
q : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' -> exists
 u', u subseteq …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset_one_on_sdiff`：prod_subset_one_on_sdiff [DecidableEq ι
] (h : s₁ subseteq s₂) (hg : forall x in s₂ \ s₁, g x = 1) (hfg : forall x in s₁
, f x = g x) : ∏ i in…
· 使用定理 `Finset.inter_subset_union`：inter_subset_union : s inter t subseteq s uni
on t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Finset.prod_union_inter`：prod_union_inter [DecidableEq ι] : (∏ x in s₁ u
nion s₂, f x) * ∏ x in s₁ inter s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 33 条，此处仅展示前 30 条）
-/
theorem HasProd.nat_mul_neg {f : ℤ → M} (hf : HasProd f m) :
    HasProd (fun n : ℕ ↦ f n * f (-n)) (m * f 0) := by
  -- Note this is much easier to prove if you assume more about the target space, but we have to
  -- work hard to prove it under the very minimal assumptions here.
  apply (hf.mul (hasProd_ite_eq (0 : ℤ) (f 0))).hasProd_of_prod_eq fun u ↦ ?_
  refine ⟨u.image Int.natAbs, fun v' hv' ↦ ?_⟩
  let u1 := v'.image fun x : ℕ ↦ (x : ℤ)
  let u2 := v'.image fun x : ℕ ↦ -(x : ℤ)
  have A : u ⊆ u1 ∪ u2 := by
    intro x hx
    simp only [u1, u2, mem_union, mem_image]
    rcases le_total 0 x with (h'x | h'x)
    · refine Or.inl ⟨_, hv' <| mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [Int.natCast_natAbs, abs_eq_self, h'x]
    · refine Or.inr ⟨_, hv' <| mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [abs_of_nonpos h'x, Int.natCast_natAbs, neg_neg]
  exact ⟨_, A, calc
    (∏ x ∈ u1 ∪ u2, (f x * if x = 0 then f 0 else 1)) =
        (∏ x ∈ u1 ∪ u2, f x) * ∏ x ∈ u1 ∩ u2, f x := by
      rw [prod_mul_distrib]
      congr 1
      refine (prod_subset_one_on_sdiff inter_subset_union ?_ ?_).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simp [u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image] at hx
        suffices x = 0 by simp only [this, if_true]
        lia
    _ = (∏ x ∈ u1, f x) * ∏ x ∈ u2, f x := prod_union_inter
    _ = (∏ b ∈ v', f b) * ∏ b ∈ v', f (-b) := by simp [u1, u2]
    _ = ∏ b ∈ v', (f b * f (-b)) := prod_mul_distrib.symm⟩

@[to_additive]
/-
**Multipliable.nat_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.nat_mul_neg {f : Int -> M} (hf : Multipliable f) : Multipliab
le fun n : Nat => f n * f (-n)
参数：hf : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.nat_mul_neg`：HasProd.nat_mul_neg {f : Int -> M} (hf : HasProd f 
m) : HasProd (fun n : Nat => f n * f (-n)) (m * f 0)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.nat_mul_neg {f : ℤ → M} (hf : Multipliable f) :
    Multipliable fun n : ℕ ↦ f n * f (-n) :=
  hf.hasProd.nat_mul_neg.multipliable

@[to_additive]
/-
**tprod_nat_mul_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_nat_mul_neg [T2Space M] {f : Int -> M} (hf : Multipliable f) : ∏' n 
: Nat, (f n * f (-n)) = (∏' n : Int, f n) * f 0
参数：hf : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.nat_mul_neg`：HasProd.nat_mul_neg {f : Int -> M} (hf : HasProd f 
m) : HasProd (fun n : Nat => f n * f (-n)) (m * f 0)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma tprod_nat_mul_neg [T2Space M] {f : ℤ → M} (hf : Multipliable f) :
    ∏' n : ℕ, (f n * f (-n)) = (∏' n : ℤ, f n) * f 0 :=
  hf.hasProd.nat_mul_neg.tprod_eq

@[to_additive HasSum.of_add_one_of_neg_add_one]
/-
**HasProd.of_add_one_of_neg_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.of_add_one_of_neg_add_one {f : Int -> M} (hf₁ : HasProd (fun n : N
at => f (n + 1)) m) (hf₂ : HasProd (fun n : Nat => f (-(n + 1))) m') : HasProd f
 (m * f 0 * m')
参数：hf₁ : HasProd (fun n : Nat => f (n + 1)) m；hf₂ : HasProd (fun n : Nat => f (-
(n + 1))) m'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProd.of_nat_of_neg_add_one`：HasProd.of_nat_of_neg_add_one {f : Int ->
 M} (hf₁ : HasProd (fun n : Nat => f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n
 + 1))) m') : HasPr…
· 使用定理 `HasProd.zero_mul`：zero_mul {f : Nat -> M} (h : HasProd (fun n => f (n + 
1)) m) : HasProd f (f 0 * m)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem HasProd.of_add_one_of_neg_add_one {f : ℤ → M}
    (hf₁ : HasProd (fun n : ℕ ↦ f (n + 1)) m) (hf₂ : HasProd (fun n : ℕ ↦ f (-(n + 1))) m') :
    HasProd f (m * f 0 * m') :=
  HasProd.of_nat_of_neg_add_one (mul_comm _ m ▸ HasProd.zero_mul hf₁) hf₂

@[to_additive Summable.of_add_one_of_neg_add_one]
/-
**Multipliable.of_add_one_of_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.of_add_one_of_neg_add_one {f : Int -> M} (hf₁ : Multipliable 
fun n : Nat => f (n + 1)) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) : Mul
tipliable f
参数：hf₁ : Multipliable fun n : Nat => f (n + 1)；hf₂ : Multipliable fun n : Nat =>
 f (-(n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.of_add_one_of_neg_add_one`：HasProd.of_add_one_of_neg_add_one {f 
: Int -> M} (hf₁ : HasProd (fun n : Nat => f (n + 1)) m) (hf₂ : HasProd (fun n :
 Nat => f (-(n + 1))) m…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma Multipliable.of_add_one_of_neg_add_one {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f (n + 1)) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    Multipliable f :=
  (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_add_one_of_neg_add_one]
/-
**tprod_of_add_one_of_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_of_add_one_of_neg_add_one [T2Space M] {f : Int -> M} (hf₁ : Multipli
able fun n : Nat => f (n + 1)) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) 
: ∏' n : Int, f n = (∏' n : Nat, f (n + 1)) * f 0 * ∏' n : Nat, f (-(n + 1))
参数：hf₁ : Multipliable fun n : Nat => f (n + 1)；hf₂ : Multipliable fun n : Nat =>
 f (-(n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.of_add_one_of_neg_add_one`：HasProd.of_add_one_of_neg_add_one {f 
: Int -> M} (hf₁ : HasProd (fun n : Nat => f (n + 1)) m) (hf₂ : HasProd (fun n :
 Nat => f (-(n + 1))) m…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma tprod_of_add_one_of_neg_add_one [T2Space M] {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f (n + 1)) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f (n + 1)) * f 0 * ∏' n : ℕ, f (-(n + 1)) :=
  (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).tprod_eq

end ContinuousMul

end Monoid

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/-
**HasProd.of_nat_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.of_nat_of_neg {f : Int -> G} (hf₁ : HasProd (fun n : Nat => f n) g
) (hf₂ : HasProd (fun n : Nat => f (-n)) g') : HasProd f (g * g' / f 0)
参数：hf₁ : HasProd (fun n : Nat => f n) g；hf₂ : HasProd (fun n : Nat => f (-n)) g'
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProd.of_nat_of_neg_add_one`：HasProd.of_nat_of_neg_add_one {f : Int ->
 M} (hf₁ : HasProd (fun n : Nat => f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n
 + 1))) m') : HasPr…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.prod_range_one`：prod_range_one (f : Nat -> M) : ∏ k in range 1, f
 k = f 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasProd_nat_add_iff'`：hasProd_nat_add_iff' {f : Nat -> G} (k : Nat) : Ha
sProd (fun n => f (n + k)) (g / ∏ i in range k, f i) ↔ HasProd f g
· 使用定理 `mul_div_assoc'`：mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c
-/
lemma HasProd.of_nat_of_neg {f : ℤ → G} (hf₁ : HasProd (fun n : ℕ ↦ f n) g)
    (hf₂ : HasProd (fun n : ℕ ↦ f (-n)) g') : HasProd f (g * g' / f 0) := by
  refine mul_div_assoc' g .. ▸ hf₁.of_nat_of_neg_add_one (m' := g' / f 0) ?_
  rwa [← hasProd_nat_add_iff' 1, prod_range_one, Nat.cast_zero, neg_zero] at hf₂

@[to_additive]
/-
**Multipliable.of_nat_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.of_nat_of_neg {f : Int -> G} (hf₁ : Multipliable fun n : Nat 
=> f n) (hf₂ : Multipliable fun n : Nat => f (-n)) : Multipliable f
参数：hf₁ : Multipliable fun n : Nat => f n；hf₂ : Multipliable fun n : Nat => f (-n
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用引理 `HasProd.of_nat_of_neg`：HasProd.of_nat_of_neg {f : Int -> G} (hf₁ : HasPr
od (fun n : Nat => f n) g) (hf₂ : HasProd (fun n : Nat => f (-n)) g') : HasProd 
f (g * g' /…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma Multipliable.of_nat_of_neg {f : ℤ → G} (hf₁ : Multipliable fun n : ℕ ↦ f n)
    (hf₂ : Multipliable fun n : ℕ ↦ f (-n)) : Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).multipliable

@[to_additive]
/-
**Multipliable.tprod_of_nat_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {G : Type u_2} [inst : CommGroup G] [inst_1 : TopologicalSpace G] [IsTop
ologicalGroup G] [T2Space G] {f : ℤ → G},   (Multipliable fun n => f ↑n) →     (
Multipliable fun n => f (-↑n)) → ∏' (n : ℤ), f n = ((∏' (n : ℕ), f ↑n) * ∏' (n :
 ℕ), f (-↑n)) / f 0
参数：Multipliable fun n => f ↑n；Multipliable fun n => f (-↑n)；n : ℤ；(∏' (n : ℕ), f
 ↑n) * ∏' (n : ℕ), f (-↑n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HasProd.of_nat_of_neg`：HasProd.of_nat_of_neg {f : Int -> G} (hf₁ : HasPr
od (fun n : Nat => f n) g) (hf₂ : HasProd (fun n : Nat => f (-n)) g') : HasProd 
f (g * g' /…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected lemma Multipliable.tprod_of_nat_of_neg [T2Space G] {f : ℤ → G}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-n)) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f n) * (∏' n : ℕ, f (-n)) / f 0 :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).tprod_eq

end IsTopologicalGroup

section IsUniformGroup -- results which depend on completeness

variable [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]

/-- "iff" version of `Multipliable.of_nat_of_neg_add_one`. -/
@[to_additive /-- "iff" version of `Summable.of_nat_of_neg_add_one`. -/]
/-
**multipliable_int_iff_multipliable_nat_and_neg_add_one** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：multipliable_int_iff_multipliable_nat_and_neg_add_one {f : Int -> G} : Mul
tipliable f ↔ (Multipliable fun n : Nat => f n) ∧ (Multipliable fun n : Nat => f
 (-(n + 1)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Int.negSucc.inj`：∀ {a a_1 : ℕ}, Int.negSucc a = Int.negSucc a_1 → a = a_
1
· 使用引理 `Multipliable.of_nat_of_neg_add_one`：Multipliable.of_nat_of_neg_add_one {
f : Int -> M} (hf₁ : Multipliable fun n : Nat => f n) (hf₂ : Multipliable fun n 
: Nat => f (-(n + 1))) :…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α

--- 原说明 ---
"iff" version of `Multipliable.of_nat_of_neg_add_one`.
-/
lemma multipliable_int_iff_multipliable_nat_and_neg_add_one {f : ℤ → G} : Multipliable f ↔
    (Multipliable fun n : ℕ ↦ f n) ∧ (Multipliable fun n : ℕ ↦ f (-(n + 1))) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Multipliable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

/-- "iff" version of `Multipliable.of_nat_of_neg`. -/
@[to_additive /-- "iff" version of `Summable.of_nat_of_neg`. -/]
/-
**multipliable_int_iff_multipliable_nat_and_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_int_iff_multipliable_nat_and_neg {f : Int -> G} : Multipliabl
e f ↔ (Multipliable fun n : Nat => f n) ∧ (Multipliable fun n : Nat => f (-n))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用引理 `Multipliable.of_nat_of_neg`：Multipliable.of_nat_of_neg {f : Int -> G} (h
f₁ : Multipliable fun n : Nat => f n) (hf₂ : Multipliable fun n : Nat => f (-n))
 : Multipliable …
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α

--- 原说明 ---
"iff" version of `Multipliable.of_nat_of_neg`.
-/
lemma multipliable_int_iff_multipliable_nat_and_neg {f : ℤ → G} :
    Multipliable f ↔ (Multipliable fun n : ℕ ↦ f n) ∧ (Multipliable fun n : ℕ ↦ f (-n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Multipliable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

-- We're not really using the ring structure here:
-- we only use multiplication by `-1`, so perhaps this can be generalised further.
/-
**Summable.alternating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.alternating {α} [Ring α] [UniformSpace α] [IsUniformAddGroup α] [
CompleteSpace α] {f : Nat -> α} (hf : Summable f) : Summable (fun n => (-1) ^ n 
* f n)
参数：hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.even_add_odd`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1
 : TopologicalSpace M] [ContinuousAdd M] {f : ℕ → M},   (Summable fun k => f (2 
* k)) → (Su…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Summable.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 32 条，此处仅展示前 30 条）
-/
theorem Summable.alternating {α} [Ring α]
    [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α] {f : ℕ → α} (hf : Summable f) :
    Summable (fun n => (-1) ^ n * f n) := by
  apply Summable.even_add_odd
  · simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul]
    exact hf.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  · simp only [pow_add, even_two, Even.mul_right, Even.neg_pow, one_pow, pow_one, mul_neg, mul_one,
      neg_mul, one_mul]
    apply Summable.neg
    apply hf.comp_injective
    exact (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ))

end IsUniformGroup

end Int

section PNat

@[to_additive]
/-
**multipliable_pnat_iff_multipliable_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_pnat_iff_multipliable_succ {f : Nat -> M} : Multipliable (fun
 x : Nat+ => f x) ↔ Multipliable fun x => f (x + 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.multipliable_iff`：Equiv.multipliable_iff (e : γ ≃ β) : Multipliabl
e (f ∘ e) ↔ Multipliable f
-/
theorem multipliable_pnat_iff_multipliable_succ {f : ℕ → M} :
    Multipliable (fun x : ℕ+ ↦ f x) ↔ Multipliable fun x ↦ f (x + 1) :=
  Equiv.pnatEquivNat.symm.multipliable_iff.symm

@[to_additive]
/-
**multipliable_pnat_iff_multipliable_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_pnat_iff_multipliable_nat [TopologicalSpace G] [IsTopological
Group G] {f : Nat -> G} : Multipliable (fun n : Nat+ => f n) ↔ Multipliable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multipliable_pnat_iff_multipliable_succ`：multipliable_pnat_iff_multiplia
ble_succ {f : Nat -> M} : Multipliable (fun x : Nat+ => f x) ↔ Multipliable fun 
x => f (x + 1)
· 使用定理 `multipliable_nat_add_iff`：multipliable_nat_add_iff {f : Nat -> G} (k : N
at) : (Multipliable fun n => f (n + k)) ↔ Multipliable f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma multipliable_pnat_iff_multipliable_nat [TopologicalSpace G] [IsTopologicalGroup G]
    {f : ℕ → G} : Multipliable (fun n : ℕ+ ↦ f n) ↔ Multipliable f := by
  rw [multipliable_pnat_iff_multipliable_succ, multipliable_nat_add_iff]

@[to_additive]
/-
**hasProd_pnat_iff_hasProd_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_pnat_iff_hasProd_succ {f : Nat -> M} : HasProd (fun x : Nat+ => f 
x) m ↔ HasProd (fun x : Nat => f (x + 1)) m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
-/
theorem hasProd_pnat_iff_hasProd_succ {f : ℕ → M} :
    HasProd (fun x : ℕ+ ↦ f x) m ↔ HasProd (fun x : ℕ ↦ f (x + 1)) m :=
  Equiv.pnatEquivNat.symm.hasProd_iff.symm

@[to_additive]
/-
**hasProd_pnat_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_pnat_iff [TopologicalSpace G] [IsTopologicalGroup G] {f : Nat -> G
} {a : G} : HasProd (fun x : Nat+ => f x) a ↔ HasProd f (a * f 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasProd_pnat_iff [TopologicalSpace G] [IsTopologicalGroup G] {f : ℕ → G} {a : G} :
    HasProd (fun x : ℕ+ ↦ f x) a ↔ HasProd f (a * f 0) := by
  simp [hasProd_pnat_iff_hasProd_succ, hasProd_nat_add_iff]

@[to_additive]
/-
**tprod_pnat_eq_tprod_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_pnat_eq_tprod_succ {f : Nat -> M} : ∏' n : Nat+, f n = ∏' n, f (n + 
1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.tprod_eq`：Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) 
= ∏' b, f b
-/
theorem tprod_pnat_eq_tprod_succ {f : ℕ → M} : ∏' n : ℕ+, f n = ∏' n, f (n + 1) :=
  (Equiv.pnatEquivNat.symm.tprod_eq _).symm

@[to_additive]
/-
**tprod_pnat_eq_tprod_of_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_pnat_eq_tprod_of_eq_one {f : Nat -> M} (hf : f 0 = 1) : ∏' n : Nat+,
 f n = ∏' n : Nat, f n
参数：hf : f 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tprod_eq`：Function.Injective.tprod_eq {g : γ -> β} (h
g : Injective g) {f : β -> α} (hf : mulSupport f subseteq Set.range g) : ∏' c, f
 (g c) = ∏' b, f …
· 使用定理 `PNat.coe_injective`：coe_injective : Function.Injective PNat.val
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tprod_pnat_eq_tprod_of_eq_one {f : ℕ → M} (hf : f 0 = 1) :
    ∏' n : ℕ+, f n = ∏' n : ℕ, f n :=
  PNat.coe_injective.tprod_eq fun n hn ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hf hn
    · exact ⟨⟨n, h⟩, rfl⟩

@[to_additive]
/-
**tprod_zero_pnat_eq_tprod_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_zero_pnat_eq_tprod_nat [TopologicalSpace G] [IsTopologicalGroup G] [
T2Space G] {f : Nat -> G} (hf : Multipliable f) : f 0 * ∏' n : Nat+, f ↑n = ∏' n
, f n
参数：hf : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multipliable.tprod_eq_zero_mul`：∀ {G : Type u_2} [inst : CommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {f : ℕ → G},   Mu
ltipliable f → ∏' (b…
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `tprod_pnat_eq_tprod_succ`：tprod_pnat_eq_tprod_succ {f : Nat -> M} : ∏' n
 : Nat+, f n = ∏' n, f (n + 1)
-/
lemma tprod_zero_pnat_eq_tprod_nat [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {f : ℕ → G} (hf : Multipliable f) :
    f 0 * ∏' n : ℕ+, f ↑n = ∏' n, f n := by
  simpa [hf.tprod_eq_zero_mul] using tprod_pnat_eq_tprod_succ

@[to_additive]
/-
**tprod_int_eq_zero_mul_tprod_pnat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_int_eq_zero_mul_tprod_pnat [UniformSpace G] [IsUniformGroup G] [Comp
leteSpace G] [T2Space G] {f : Int -> G} (hf2 : Multipliable f) : ∏' n, f n = f 0
 * (∏' n : Nat+, f n) * (∏' n : Nat+, f (-n))
参数：hf2 : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `multipliable_int_iff_multipliable_nat_and_neg`：multipliable_int_iff_mult
ipliable_nat_and_neg {f : Int -> G} : Multipliable f ↔ (Multipliable fun n : Nat
 => f n) ∧ (Multipliable fun n : Na…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multipliable_pnat_iff_multipliable_succ`：multipliable_pnat_iff_multiplia
ble_succ {f : Nat -> M} : Multipliable (fun x : Nat+ => f x) ↔ Multipliable fun 
x => f (x + 1)
· 使用定理 `multipliable_nat_add_iff`：multipliable_nat_add_iff {f : Nat -> G} (k : N
at) : (Multipliable fun n => f (n + k)) ↔ Multipliable f
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用引理 `tprod_nat_mul_neg`：tprod_nat_mul_neg [T2Space M] {f : Int -> M} (hf : Mu
ltipliable f) : ∏' n : Nat, (f n * f (-n)) = (∏' n : Int, f n) * f 0
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `tprod_zero_pnat_eq_tprod_nat`：tprod_zero_pnat_eq_tprod_nat [TopologicalS
pace G] [IsTopologicalGroup G] [T2Space G] {f : Nat -> G} (hf : Multipliable f) 
: f 0 * ∏' n : Nat…
· 使用定理 `Multipliable.mul`：Multipliable.mul (hf : Multipliable f L) (hg : Multipl
iable g L) : Multipliable (fun b => f b * g b) L
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Multipliable.tprod_mul`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMono
id α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2S
pace α] [Con…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprod_int_eq_zero_mul_tprod_pnat [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] {f : ℤ → G} (hf2 : Multipliable f) :
    ∏' n, f n = f 0 * (∏' n : ℕ+, f n) * (∏' n : ℕ+, f (-n)) := by
  have h1 : Multipliable fun n : ℕ ↦ f n :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).1
  have h2 : Multipliable fun n : ℕ ↦ f (-n) :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).2
  have h3 : Multipliable fun n : ℕ+ ↦ f n := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (f ·)),
      multipliable_nat_add_iff 1 (f := (f ·))]
  have h4 : Multipliable fun n : ℕ+ ↦ f (-n) := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (fun x ↦ f (-x))),
      multipliable_nat_add_iff 1 (f := (fun x ↦ f (-x)))]
  have := tprod_nat_mul_neg hf2
  simp only [← tprod_zero_pnat_eq_tprod_nat (by simpa using h1.mul h2), Nat.cast_zero, neg_zero,
    mul_comm _ (f 0), mul_assoc, mul_right_inj] at this
  simp [← this, h3.tprod_mul h4, ← mul_assoc]

@[to_additive tsum_int_eq_zero_add_two_mul_tsum_pnat]
/-
**tprod_int_eq_zero_mul_tprod_pnat_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_int_eq_zero_mul_tprod_pnat_sq [UniformSpace G] [IsUniformGroup G] [C
ompleteSpace G] [T2Space G] {f : Int -> G} (hf : f.Even) (hf2 : Multipliable f) 
: ∏' n, f n = f 0 * (∏' n : Nat+, f n) ^ 2
参数：hf : f.Even；hf2 : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tprod_int_eq_zero_mul_tprod_pnat`：tprod_int_eq_zero_mul_tprod_pnat [Unif
ormSpace G] [IsUniformGroup G] [CompleteSpace G] [T2Space G] {f : Int -> G} (hf2
 : Multipliable f) : ∏…
-/
theorem tprod_int_eq_zero_mul_tprod_pnat_sq [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] {f : ℤ → G} (hf : f.Even) (hf2 : Multipliable f) :
    ∏' n, f n = f 0 * (∏' n : ℕ+, f n) ^ 2 := by
  simpa only [sq, ← mul_assoc, hf _] using tprod_int_eq_zero_mul_tprod_pnat hf2

end PNat

