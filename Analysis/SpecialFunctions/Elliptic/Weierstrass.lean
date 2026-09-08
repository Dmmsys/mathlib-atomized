/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!

# Weierstrass `℘` functions

## Main definitions and results
- `PeriodPair.weierstrassP`: The Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_weierstrassP`:
  The summands of `℘` sums to `℘` locally uniformly.
- `PeriodPair.differentiableOn_weierstrassP`: `℘` is differentiable away from the lattice points.
- `PeriodPair.weierstrassP_add_coe`: The Weierstrass `℘`-function is periodic.
- `PeriodPair.weierstrassP_neg`: The Weierstrass `℘`-function is even.

- `PeriodPair.derivWeierstrassP`:
  The derivative of the Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_derivWeierstrassP`:
  The summands of `℘'` sums to `℘'` locally uniformly.
- `PeriodPair.differentiableOn_derivWeierstrassP`:
  `℘'` is differentiable away from the lattice points.
- `PeriodPair.derivWeierstrassP_add_coe`: `℘'` is periodic.
- `PeriodPair.weierstrassP_neg`: `℘'` is odd.
- `PeriodPair.deriv_weierstrassP`: `deriv ℘ = ℘'`. This is true globally because of junk values.
- `PeriodPair.analyticOnNhd_weierstrassP`: `℘` is analytic away from the lattice points.
- `PeriodPair.meromorphic_weierstrassP`: `℘` is meromorphic on the whole plane.
- `PeriodPair.order_weierstrassP`: `℘` has a pole of order 2 at each of the lattice points.
- `PeriodPair.derivWeierstrassP_sq` : `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`

## tags

Weierstrass p-functions, Weierstrass p functions

-/

@[expose] public section

open Module Filter
open scoped Topology Nat

noncomputable section

/-- A pair of `ℝ`-linearly independent complex numbers.
They span the period lattice in `lattice`,
and are the periods of the elliptic functions we shall construct. -/
/-
**PeriodPair** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of `ℝ`-linearly independent complex numbers.
They span the period lattice in `lattice`,
and are the periods of the elliptic functions we shall construct.
-/
structure PeriodPair : Type where
  /-- The first period in a `PeriodPair`. -/
  ω₁ : ℂ
  /-- The second period in a `PeriodPair`. -/
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

/-- The `ℝ`-basis of `ℂ` determined by a pair of periods. -/
/-
**PeriodPair.basis** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：PeriodPair → Module.Basis (Fin 2) ℝ ℂ
参数：Fin 2。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PeriodPair.indep`：∀ (self : PeriodPair), LinearIndependent ℝ ![self.ω₁, 
self.ω₂]

--- 原说明 ---
The `ℝ`-basis of `ℂ` determined by a pair of periods.
-/
protected def basis : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)
/-
**PeriodPair.basis_zero** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair), L.basis 0 = L.ω₁
参数：L : PeriodPair。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PeriodPair.indep`：∀ (self : PeriodPair), LinearIndependent ℝ ![self.ω₁, 
self.ω₂]
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma basis_zero : L.basis 0 = L.ω₁ := by simp [PeriodPair.basis]
/-
**PeriodPair.basis_one** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair), L.basis 1 = L.ω₂
参数：L : PeriodPair。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PeriodPair.indep`：∀ (self : PeriodPair), LinearIndependent ℝ ![self.ω₁, 
self.ω₂]
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma basis_one : L.basis 1 = L.ω₂ := by simp [PeriodPair.basis]

/-- The lattice spanned by a pair of periods. -/
/-
**PeriodPair.lattice** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：lattice : Submodule Int Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lattice spanned by a pair of periods.
-/
def lattice : Submodule ℤ ℂ := Submodule.span ℤ {L.ω₁, L.ω₂}
/-
**PeriodPair.mem_lattice** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：mem_lattice {L : PeriodPair} {x : Complex} : x in L.lattice ↔ exists m n :
 Int, m * L.ω₁ + n * L.ω₂ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_lattice {L : PeriodPair} {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, m * L.ω₁ + n * L.ω₂ = x := by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]
/-
**PeriodPair.** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω₁_mem_lattice : L.ω₁ ∈ L.lattice := Submodule.subset_span (by simp)
/-
**PeriodPair.** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω₂_mem_lattice : L.ω₂ ∈ L.lattice := Submodule.subset_span (by simp)
/-
**PeriodPair.mul_** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_ω₁_add_mul_ω₂_mem_lattice {L : PeriodPair} {α β : ℚ} :
    α * L.ω₁ + β * L.ω₂ ∈ L.lattice ↔ α.den = 1 ∧ β.den = 1 := by
  refine ⟨fun H ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simp; linear_combination e)
    simp only [sub_eq_zero] at this
    norm_cast at this
    aesop
  · lift α to ℤ using h₁
    lift β to ℤ using h₂
    simp only [Rat.cast_intCast, ← zsmul_eq_mul]
    exact add_mem (Submodule.smul_mem _ _ L.ω₁_mem_lattice)
      (Submodule.smul_mem _ _ L.ω₂_mem_lattice)
/-
**PeriodPair.** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω₁_div_two_notMem_lattice : L.ω₁ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 0)).not.mpr (by norm_num)
/-
**PeriodPair.** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω₂_div_two_notMem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by norm_num)

-- helper lemma to connect to the ZLattice API
/-
**PeriodPair.lattice_eq_span_range_basis** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：lattice_eq_span_range_basis : L.lattice = Submodule.span Int (Set.range L.
basis)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PeriodPair.lattice.eq_1`：∀ (L : PeriodPair), L.lattice = Submodule.span 
ℤ {L.ω₁, L.ω₂}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PeriodPair.basis_zero`：∀ (L : PeriodPair), L.basis 0 = L.ω₁
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `PeriodPair.basis_one`：∀ (L : PeriodPair), L.basis 1 = L.ω₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lattice_eq_span_range_basis :
    L.lattice = Submodule.span ℤ (Set.range L.basis) := by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [lattice, ← Set.image_univ, ← Finset.coe_univ, this]
  simp [Set.image_insert_eq]
/-
**PeriodPair.** 是 Mathlib 中的一个实例，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology L.lattice := L.lattice_eq_span_range_basis ▸ inferInstance
/-
**PeriodPair.** 是 Mathlib 中的一个实例，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZLattice ℝ L.lattice := by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance
/-
**PeriodPair.isClosed_lattice** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：isClosed_lattice : IsClosed (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
-/
lemma isClosed_lattice : IsClosed (X := ℂ) L.lattice :=
  @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))
/-
**PeriodPair.isClosed_of_subset_lattice** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：isClosed_of_subset_lattice {s : Set Complex} (hs : s subseteq L.lattice) :
 IsClosed s
参数：hs : s subseteq L.lattice。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
· 使用引理 `PeriodPair.isClosed_lattice`：isClosed_lattice : IsClosed (X
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `PeriodPair.instDiscreteTopologySubtypeComplexMemSubmoduleIntLattice`：∀ (
L : PeriodPair), DiscreteTopology ↥L.lattice
-/
lemma isClosed_of_subset_lattice {s : Set ℂ} (hs : s ⊆ L.lattice) : IsClosed s := by
  convert!
    L.isClosed_lattice.isClosedMap_subtype_val _ (isClosed_discrete (α := L.lattice) ((↑) ⁻¹' s))
  convert! Set.image_preimage_eq_inter_range.symm using 1
  simpa
/-
**PeriodPair.isOpen_compl_lattice_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：isOpen_compl_lattice_sdiff {s : Set Complex} : IsOpen (L.lattice \ s)ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `PeriodPair.isClosed_of_subset_lattice`：isClosed_of_subset_lattice {s : S
et Complex} (hs : s subseteq L.lattice) : IsClosed s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma isOpen_compl_lattice_sdiff {s : Set ℂ} : IsOpen (L.lattice \ s)ᶜ :=
  (L.isClosed_of_subset_lattice Set.sdiff_subset).isOpen_compl

@[deprecated (since := "2026-06-03")] alias isOpen_compl_lattice_diff := isOpen_compl_lattice_sdiff

open scoped Topology in
/-
**PeriodPair.compl_lattice_sdiff_singleton_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 `P
eriodPair`。
形式化陈述：compl_lattice_sdiff_singleton_mem_nhds (x : Complex) : (↑L.lattice \ {x})ᶜ
 in 𝓝 x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `PeriodPair.isOpen_compl_lattice_sdiff`：isOpen_compl_lattice_sdiff {s : S
et Complex} : IsOpen (L.lattice \ s)ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma compl_lattice_sdiff_singleton_mem_nhds (x : ℂ) : (↑L.lattice \ {x})ᶜ ∈ 𝓝 x :=
  L.isOpen_compl_lattice_sdiff.mem_nhds (by simp)

@[deprecated (since := "2026-06-03")]
alias compl_lattice_diff_singleton_mem_nhds := compl_lattice_sdiff_singleton_mem_nhds
/-
**PeriodPair.** 是 Mathlib 中的一个实例，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace L.lattice := .of_isClosed L.isClosed_lattice

/-- The `ℤ`-basis of the lattice determined by a pair of periods. -/
/-
**PeriodPair.latticeBasis** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：latticeBasis : Basis (Fin 2) Int L.lattice
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℤ`-basis of the lattice determined by a pair of periods.
-/
def latticeBasis : Basis (Fin 2) ℤ L.lattice :=
  (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))
/-
**PeriodPair.latticeBasis_zero** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair), ↑(L.latticeBasis 0) = L.ω₁
参数：L : PeriodPair；L.latticeBasis 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma latticeBasis_zero : L.latticeBasis 0 = L.ω₁ := by simp [latticeBasis]
/-
**PeriodPair.latticeBasis_one** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair), ↑(L.latticeBasis 1) = L.ω₂
参数：L : PeriodPair；L.latticeBasis 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma latticeBasis_one : L.latticeBasis 1 = L.ω₂ := by simp [latticeBasis]
/-
**PeriodPair.finrank_lattice** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair), Module.finrank ℤ ↥L.lattice = 2
参数：L : PeriodPair。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
@[simp] lemma finrank_lattice : finrank ℤ L.lattice = 2 := finrank_eq_card_basis L.latticeBasis

/-- The equivalence from the lattice generated by a pair of periods to `ℤ × ℤ`. -/
/-
**PeriodPair.latticeEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：latticeEquivProd : L.lattice ≃ₗ[Int] Int × Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence from the lattice generated by a pair of periods to `ℤ × ℤ`.
-/
def latticeEquivProd : L.lattice ≃ₗ[ℤ] ℤ × ℤ :=
  L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow ℤ ℤ
/-
**PeriodPair.latticeEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：latticeEquiv_symm_apply (x : Int × Int) : (L.latticeEquivProd.symm x).1 = 
x.1 * L.ω₁ + x.2 * L.ω₂
参数：x : Int × Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearEquiv.finTwoArrow_symm_apply`：∀ (R : Type u) (M : Type v) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   ⇑(LinearE
quiv.finTwoArrow R M).sy…
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.sum_zsmul`：∀ {α : Type u_1} {N : Type u_16} [inst : SubtractionC
ommMonoid N] [inst_1 : Fintype α] (f : α →₀ ℤ) (g : α → N),   (f.sum fun a b => 
b • g a…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PeriodPair.latticeBasis_zero`：∀ (L : PeriodPair), ↑(L.latticeBasis 0) = 
L.ω₁
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `PeriodPair.latticeBasis_one`：∀ (L : PeriodPair), ↑(L.latticeBasis 1) = L
.ω₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma latticeEquiv_symm_apply (x : ℤ × ℤ) :
    (L.latticeEquivProd.symm x).1 = x.1 * L.ω₁ + x.2 * L.ω₂ := by
  simp [latticeEquivProd, Finsupp.linearCombination]
/-
**PeriodPair.hasSumLocallyUniformly_aux** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：hasSumLocallyUniformly_aux (f : L.lattice -> Complex -> Complex) (u : Real
 -> L.lattice -> Real) (hu : forall r > 0, Summable (u r)) (hf : forall r > 0, f
orallᶠ R in atTop, forall x, ‖x‖ < r -> forall l : L.lattice, ‖l.1‖ = R -> ‖f l 
x‖ <= u r l) : HasSumLocallyUniformly f (∑' j, f j ·)
参数：f : L.lattice -> Complex -> Complex；u : Real -> L.lattice -> Real；hu : forall
 r > 0, Summable (u r)；hf : forall r > 0, forallᶠ R in atTop, forall x, ‖x‖ < r 
-> forall l : L.lattice, ‖l.1‖ = R -> ‖f l x‖ <= u r l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasSumLocallyUniformly_iff_tendstoLocallyUniformly`：∀ {α : Type u_1} {β 
: Type u_2} {ι : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} 
  [inst_1 : UniformSpace α] [inst_2 : To…
· 使用定理 `tendstoLocallyUniformly_iff_filter`：tendstoLocallyUniformly_iff_filter :
 TendstoLocallyUniformly F f p ↔ forall x, TendstoUniformlyOnFilter F f p (𝓝 x)
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `TendstoUniformlyOnFilter.mono_right`：TendstoUniformlyOnFilter.mono_right
 {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p') (hp : p'' <= p') : Ten
dstoUniformlyOnFilter F f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`：tendstoUniformlyOn_tsum_
of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real} (hu : Summa
ble u) {s : Set β} (hfu : forallᶠ n …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
（共 41 条，此处仅展示前 30 条）
-/
lemma hasSumLocallyUniformly_aux (f : L.lattice → ℂ → ℂ)
    (u : ℝ → L.lattice → ℝ) (hu : ∀ r > 0, Summable (u r))
    (hf : ∀ r > 0, ∀ᶠ R in atTop, ∀ x, ‖x‖ < r → ∀ l : L.lattice, ‖l.1‖ = R → ‖f l x‖ ≤ u r l) :
    HasSumLocallyUniformly f (∑' j, f j ·) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : ∃ r, 0 < r ∧ 𝓝 x ≤ 𝓟 (Metric.ball 0 r) :=
    ⟨‖x‖ + 1, by positivity, Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds (by simp))⟩
  refine .mono_right ?_ hr'
  rw [← tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hu r hr) ?_
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hf r hr)
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intros l hl
  obtain ⟨s, hs, hs'⟩ : ∃ x, ‖x‖ < r ∧ u r l < ‖f l x‖ := by simpa using hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  contrapose! hs'
  exact hR _ hs'.le _ hs _ rfl

-- Only the asymptotics matter and `10` is just a convenient constant to pick.
/-
**PeriodPair.weierstrassP_bound** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP_bound (r : Real) (hr : 0 < r) (s : Complex) (hs : ‖s‖ < r) (l
 : Complex) (h : 2 * r <= ‖l‖) : ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ <= 10 * r * ‖l‖ ^
 (-3 : Real)
参数：r : Real；hr : 0 < r；s : Complex；hs : ‖s‖ < r；l : Complex；h : 2 * r <= ‖l‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 167 条，此处仅展示前 30 条）
-/
lemma weierstrassP_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ ≤ 10 * r * ‖l‖ ^ (-3 : ℝ) := by
  have : s ≠ ↑l := by rintro rfl; linarith
  have : 0 < ‖l‖ := by linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div, one_mul, mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2) := by simp
    _ ≤ ‖l ^ 2 - (s - l) ^ 2‖ / ((‖l‖ / 2) ^ 2 * ‖l‖ ^ 2) := by
      gcongr
      rw [norm_sub_rev]
      exact .trans (by linarith) (norm_sub_norm_le l s)
    _ = ‖s * (2 * l - s)‖ / (‖l‖ ^ 4 / 4) := by
      congr 1
      · rw [sq_sub_sq]; simp [← sub_add, two_mul, sub_add_eq_add_sub]
      · ring
    _ = (‖s‖ * ‖2 * l - s‖) / (‖l‖ ^ 4 / 4) := by simp
    _ = (4 * ‖s‖ * ‖2 * l - s‖) / ‖l‖ ^ 4 := by field
    _ ≤ (4 * r * (2.5 * ‖l‖)) / ‖l‖ ^ 4 := by
      gcongr (4 * ?_ * ?_) / ‖l‖ ^ 4
      refine (norm_sub_le _ _).trans ?_
      simp only [Complex.norm_mul, Complex.norm_ofNat]
      linarith
    _ = 10 * r / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

section weierstrassPExcept

/-- The Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging term.
This has the notation `℘[L - l₀]` in the namespace `PeriodPairs`. -/
/-
**PeriodPair.weierstrassPExcept** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExcept (l₀ : Complex) (z : Complex) : Complex
参数：l₀ : Complex；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging 
term.
This has the notation `℘[L - l₀]` in the namespace `PeriodPairs`.
-/
def weierstrassPExcept (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassPExcept]
scoped notation3 "℘[" L:max " - " l₀ "]" => weierstrassPExcept L l₀
/-
**PeriodPair.hasSumLocallyUniformly_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间
 `PeriodPair`。
形式化陈述：hasSumLocallyUniformly_weierstrassPExcept (l₀ : Complex) : HasSumLocallyUn
iformly (fun (l : L.lattice) (z : Complex) => if l.1 = l₀ then 0 else (1 / (z - 
l) ^ 2 - 1 / l ^ 2)) ℘[L - l₀]
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.hasSumLocallyUniformly_aux`：hasSumLocallyUniformly_aux (f : L
.lattice -> Complex -> Complex) (u : Real -> L.lattice -> Real) (hu : forall r >
 0, Summable (u r)) (hf : f…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ZLattice.summable_norm_rpow`：summable_norm_rpow (r : Real) (hr : r < -Mo
dule.finrank Int L) : Summable fun z : L => ‖z‖ ^ r
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `PeriodPair.instDiscreteTopologySubtypeComplexMemSubmoduleIntLattice`：∀ (
L : PeriodPair), DiscreteTopology ↥L.lattice
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PeriodPair.finrank_lattice`：∀ (L : PeriodPair), Module.finrank ℤ ↥L.latt
ice = 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 51 条，此处仅展示前 30 条）
-/
lemma hasSumLocallyUniformly_weierstrassPExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l.1 = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      ℘[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := (10 * · * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simpa using! show 0 ≤ 10 * r * (‖↑l‖ ^ 3)⁻¹ by positivity
  · exact weierstrassP_bound r hr s hs l h
/-
**PeriodPair.hasSum_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：hasSum_weierstrassPExcept (l₀ : Complex) (z : Complex) : HasSum (fun l : L
.lattice => if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)) (℘[L - l₀] z)
参数：l₀ : Complex；z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSumLocallyUniformly.hasSum`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {x : β}   [inst_1 : U
niformSpace α] [ins…
· 使用引理 `PeriodPair.hasSumLocallyUniformly_weierstrassPExcept`：hasSumLocallyUnifo
rmly_weierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (l : L.latt
ice) (z : Complex) => if l.1 = l₀ then 0 e…
-/
lemma hasSum_weierstrassPExcept (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice ↦ if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      (℘[L - l₀] z) :=
  (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSum

/-- `weierstrassPExcept l₀` is differentiable on non-lattice points and `l₀`. -/
/-
**PeriodPair.differentiableOn_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `Peri
odPair`。
形式化陈述：differentiableOn_weierstrassPExcept (l₀ : Complex) : DifferentiableOn Comp
lex ℘[L - l₀] (L.lattice \ {l₀})ᶜ
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.differentiableOn`：∀ {E : Type u_1} {ι : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Fi
lter ι}   {F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasSumLocallyUniformly.hasSumLocallyUniformlyOn`：∀ {α : Type u_1} {β : T
ype u_2} {ι : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {s 
: Set β}   [inst_1 : UniformSpace α] …
· 使用引理 `PeriodPair.hasSumLocallyUniformly_weierstrassPExcept`：hasSumLocallyUnifo
rmly_weierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (l : L.latt
ice) (z : Complex) => if l.1 = l₀ then 0 e…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_sum`：DifferentiableOn.fun_sum (h : forall i in u, D
ifferentiableOn 𝕜 (A i) s) : DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DifferentiableOn.sub`：DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f - g) s
· 使用定理 `DifferentiableOn.div`：DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s)
 (hd : DifferentiableOn 𝕜 d s) (hx : forall x in s, d x != 0) : DifferentiableOn
 𝕜 (c / d)…
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `DifferentiableOn.sub_const`：DifferentiableOn.sub_const (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`weierstrassPExcept l₀` is differentiable on non-lattice points and `l₀`.
-/
lemma differentiableOn_weierstrassPExcept (l₀ : ℂ) :
    DifferentiableOn ℂ ℘[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun i hi ↦ ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  · exact .sub (.div (by fun_prop) (by fun_prop) (by aesop (add simp sub_eq_zero))) (by fun_prop)
/-
**PeriodPair.weierstrassPExcept_neg** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExcept_neg (l₀ : Complex) (z : Complex) : ℘[L - l₀] (-z) = ℘[L
 - -l₀] z
参数：l₀ : Complex；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 61 条，此处仅展示前 30 条）
-/
lemma weierstrassPExcept_neg (l₀ : ℂ) (z : ℂ) :
    ℘[L - l₀] (-z) = ℘[L - -l₀] z := by
  simp only [weierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  simp
  ring
/-
**PeriodPair.weierstrassPExcept_zero** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair) (l₀ : ℂ), L.weierstrassPExcept l₀ 0 = 0
参数：L : PeriodPair；l₀ : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma weierstrassPExcept_zero (l₀ : ℂ) :
    ℘[L - l₀] 0 = 0 := by simp [weierstrassPExcept]

end weierstrassPExcept

section weierstrassP

/-- The Weierstrass `℘` function. This has the notation `℘[L]` in the namespace `PeriodPairs`. -/
/-
**PeriodPair.weierstrassP** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP (z : Complex) : Complex
参数：z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass `℘` function. This has the notation `℘[L]` in the namespace `Per
iodPairs`.
-/
def weierstrassP (z : ℂ) : ℂ := ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L
/-
**PeriodPair.weierstrassPExcept_add** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExcept_add (l₀ : L.lattice) (z : Complex) : ℘[L - l₀] z + (1 /
 (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z
参数：l₀ : L.lattice；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PeriodPair.weierstrassPExcept.eq_1`：∀ (L : PeriodPair) (l₀ z : ℂ),   L.w
eierstrassPExcept l₀ z = ∑' (l : ↥L.lattice), if ↑l = l₀ then 0 else 1 / (z - ↑l
) ^ 2 - 1 / ↑l ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `PeriodPair.hasSum_weierstrassPExcept`：hasSum_weierstrassPExcept (l₀ : Co
mplex) (z : Complex) : HasSum (fun l : L.lattice => if l = l₀ then 0 else (1 / (
z - l) ^ 2 - 1 / l ^ 2)) (…
· 使用定理 `summable_of_hasFiniteSupport`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [L.HasSupport],…
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
（共 33 条，此处仅展示前 30 条）
-/
lemma weierstrassPExcept_add (l₀ : L.lattice) (z : ℂ) :
    ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z := by
  trans ℘[L - l₀] z + ∑' i : L.lattice, if i = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [weierstrassPExcept, ← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))
/-
**PeriodPair.weierstrassPExcept_def** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExcept_def (l₀ : L.lattice) (z : Complex) : ℘[L - l₀] z = ℘[L]
 z + (1 / l₀.1 ^ 2 - 1 / (z - l₀.1) ^ 2)
参数：l₀ : L.lattice；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExcept_add`：weierstrassPExcept_add (l₀ : L.lattic
e) (z : Complex) : ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.0.Period
Pair.weierstrassPExcept_def._abel_1_1`：∀ (L : PeriodPair) (l₀ : ↥L.lattice) (z :
 ℂ),   L.weierstrassPExcept (↑l₀) z =     L.weierstrassPExcept (↑l₀) z + (1 / (z
 - ↑l₀) ^ 2 - 1 / ↑…
-/
lemma weierstrassPExcept_def (l₀ : L.lattice) (z : ℂ) :
    ℘[L - l₀] z = ℘[L] z + (1 / l₀.1 ^ 2 - 1 / (z - l₀.1) ^ 2) := by
  rw [← L.weierstrassPExcept_add l₀]
  abel
/-
**PeriodPair.weierstrassPExcept_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`
。
形式化陈述：weierstrassPExcept_of_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - 
l₀] = ℘[L]
参数：l₀ : Complex；hl : l₀ ∉ L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weierstrassPExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    ℘[L - l₀] = ℘[L] := by
  delta weierstrassPExcept weierstrassP
  congr! 3 with z l
  have : l.1 ≠ l₀ := by rintro rfl; simp at hl
  simp [this]
/-
**PeriodPair.hasSumLocallyUniformly_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `Peri
odPair`。
形式化陈述：hasSumLocallyUniformly_weierstrassP : HasSumLocallyUniformly (fun (l : L.l
attice) (z : Complex) => 1 / (z - ↑l) ^ 2 - 1 / l ^ 2) ℘[L]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `PeriodPair.weierstrassPExcept_of_notMem`：weierstrassPExcept_of_notMem (l
₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - l₀] = ℘[L]
· 使用引理 `PeriodPair.hasSumLocallyUniformly_weierstrassPExcept`：hasSumLocallyUnifo
rmly_weierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (l : L.latt
ice) (z : Complex) => if l.1 = l₀ then 0 e…
-/
lemma hasSumLocallyUniformly_weierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - ↑l) ^ 2 - 1 / l ^ 2) ℘[L] := by
  convert! L.hasSumLocallyUniformly_weierstrassPExcept (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e ↦ L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
/-
**PeriodPair.hasSum_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：hasSum_weierstrassP (z : Complex) : HasSum (fun l : L.lattice => (1 / (z -
 l) ^ 2 - 1 / l ^ 2)) (℘[L] z)
参数：z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSumLocallyUniformly.hasSum`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {x : β}   [inst_1 : U
niformSpace α] [ins…
· 使用引理 `PeriodPair.hasSumLocallyUniformly_weierstrassP`：hasSumLocallyUniformly_w
eierstrassP : HasSumLocallyUniformly (fun (l : L.lattice) (z : Complex) => 1 / (
z - ↑l) ^ 2 - 1 / l ^ 2) ℘[L]
-/
lemma hasSum_weierstrassP (z : ℂ) :
    HasSum (fun l : L.lattice ↦ (1 / (z - l) ^ 2 - 1 / l ^ 2)) (℘[L] z) :=
  L.hasSumLocallyUniformly_weierstrassP.hasSum
/-
**PeriodPair.differentiableOn_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair
`。
形式化陈述：differentiableOn_weierstrassP : DifferentiableOn Complex ℘[L] L.latticeᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExcept_of_notMem`：weierstrassPExcept_of_notMem (l
₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - l₀] = ℘[L]
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `PeriodPair.differentiableOn_weierstrassPExcept`：differentiableOn_weierst
rassPExcept (l₀ : Complex) : DifferentiableOn Complex ℘[L - l₀] (L.lattice \ {l₀
})ᶜ
-/
lemma differentiableOn_weierstrassP :
    DifferentiableOn ℂ ℘[L] L.latticeᶜ := by
  rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_weierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]
/-
**PeriodPair.weierstrassP_neg** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP_neg (z : Complex) : ℘[L] (-z) = ℘[L] z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 58 条，此处仅展示前 30 条）
-/
lemma weierstrassP_neg (z : ℂ) : ℘[L] (-z) = ℘[L] z := by
  simp only [weierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr with l
  simp
  ring
/-
**PeriodPair.not_continuousAt_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair
`。
形式化陈述：not_continuousAt_weierstrassP (x : Complex) (hx : x in L.lattice) : ¬ Cont
inuousAt ℘[L] x
参数：x : Complex；hx : x in L.lattice。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExcept_add`：weierstrassPExcept_add (l₀ : L.lattic
e) (z : Complex) : ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NormedField.continuousAt_zpow`：∀ {𝕜 : Type u_4} [inst : NontriviallyNorm
edField 𝕜] {n : ℤ} {x : 𝕜}, ContinuousAt (fun x => x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `ContinuousAt.comp_of_eq`：ContinuousAt.comp_of_eq {g : Y -> Z} (hg : Cont
inuousAt g y) (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
（共 42 条，此处仅展示前 30 条）
-/
lemma not_continuousAt_weierstrassP (x : ℂ) (hx : x ∈ L.lattice) : ¬ ContinuousAt ℘[L] x := by
  eta_expand
  simp_rw [← L.weierstrassPExcept_add ⟨x, hx⟩]
  intro H
  apply (NormedField.continuousAt_zpow (n := -2) (x := (0 : ℂ))).not.mpr (by simp)
  simpa [Function.comp_def] using!
    (((H.sub ((L.differentiableOn_weierstrassPExcept x).differentiableAt
      (L.compl_lattice_sdiff_singleton_mem_nhds x)).continuousAt).add
      (continuous_const (y := 1 / x ^ 2)).continuousAt).comp_of_eq
      (continuous_const_add x).continuousAt (add_zero _) :)

end weierstrassP

section derivWeierstrassPExcept

/-- The derivative of Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging term.
This has the notation `℘'[L - l₀]` in the namespace `PeriodPairs`. -/
/-
**PeriodPair.derivWeierstrassPExcept** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassPExcept (l₀ : Complex) (z : Complex) : Complex
参数：l₀ : Complex；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging 
term.
This has the notation `℘'[L - l₀]` in the namespace `PeriodPairs`.
-/
def derivWeierstrassPExcept (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3

@[inherit_doc derivWeierstrassPExcept]
scoped notation3 "℘'[" L:max " - " l₀ "]" => derivWeierstrassPExcept L l₀
/-
**PeriodPair.hasSumLocallyUniformly_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位
于命名空间 `PeriodPair`。
形式化陈述：hasSumLocallyUniformly_derivWeierstrassPExcept (l₀ : Complex) : HasSumLoca
llyUniformly (fun (l : L.lattice) (z : Complex) => if l.1 = l₀ then 0 else -2 / 
(z - l) ^ 3) ℘'[L - l₀]
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.hasSumLocallyUniformly_aux`：hasSumLocallyUniformly_aux (f : L
.lattice -> Complex -> Complex) (u : Real -> L.lattice -> Real) (hu : forall r >
 0, Summable (u r)) (hf : f…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ZLattice.summable_norm_rpow`：summable_norm_rpow (r : Real) (hr : r < -Mo
dule.finrank Int L) : Summable fun z : L => ‖z‖ ^ r
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `PeriodPair.instDiscreteTopologySubtypeComplexMemSubmoduleIntLattice`：∀ (
L : PeriodPair), DiscreteTopology ↥L.lattice
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PeriodPair.finrank_lattice`：∀ (L : PeriodPair), Module.finrank ℤ ↥L.latt
ice = 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 127 条，此处仅展示前 30 条）
-/
lemma hasSumLocallyUniformly_derivWeierstrassPExcept (l₀ : ℂ) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ if l.1 = l₀ then 0 else -2 / (z - l) ^ 3)
      ℘'[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := fun _ ↦ (16 * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp
  have : s ≠ ↑l := by rintro rfl; exfalso; linarith
  have : l ≠ 0 := by rintro rfl; simp_all; linarith
  simp only [Complex.norm_div, norm_neg, Complex.norm_ofNat, norm_pow]
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, div_le_div_iff₀, norm_sub_rev]
  · refine LE.le.trans_eq (b := 2 * (2 * ‖l - s‖) ^ 3) ?_ (by ring)
    norm_cast
    gcongr
    refine le_trans ?_ (mul_le_mul le_rfl (norm_sub_norm_le _ _) (by linarith) (by linarith))
    norm_cast at *
    linarith
  · exact pow_pos (by simpa [sub_eq_zero]) _
  · exact Real.rpow_pos_of_pos (by simpa) _
/-
**PeriodPair.hasSum_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPai
r`。
形式化陈述：hasSum_derivWeierstrassPExcept (l₀ : Complex) (z : Complex) : HasSum (fun 
l : L.lattice => if l.1 = l₀ then 0 else -2 / (z - l) ^ 3) (℘'[L - l₀] z)
参数：l₀ : Complex；z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用引理 `PeriodPair.hasSumLocallyUniformly_derivWeierstrassPExcept`：hasSumLocally
Uniformly_derivWeierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (
l : L.lattice) (z : Complex) => if l.1 = l₀ the…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma hasSum_derivWeierstrassPExcept (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice ↦ if l.1 = l₀ then 0 else -2 / (z - l) ^ 3) (℘'[L - l₀] z) :=
  (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ z)
/-
**PeriodPair.differentiableOn_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 
`PeriodPair`。
形式化陈述：differentiableOn_derivWeierstrassPExcept (l₀ : Complex) : DifferentiableOn
 Complex ℘'[L - l₀] (L.lattice \ {l₀})ᶜ
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.differentiableOn`：∀ {E : Type u_1} {ι : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Fi
lter ι}   {F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用引理 `PeriodPair.hasSumLocallyUniformly_derivWeierstrassPExcept`：hasSumLocally
Uniformly_derivWeierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (
l : L.lattice) (z : Complex) => if l.1 = l₀ the…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_sum`：DifferentiableOn.fun_sum (h : forall i in u, D
ifferentiableOn 𝕜 (A i) s) : DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DifferentiableOn.div`：DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s)
 (hd : DifferentiableOn 𝕜 d s) (hx : forall x in s, d x != 0) : DifferentiableOn
 𝕜 (c / d)…
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `DifferentiableOn.sub_const`：DifferentiableOn.sub_const (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `PeriodPair.isOpen_compl_lattice_sdiff`：isOpen_compl_lattice_sdiff {s : S
et Complex} : IsOpen (L.lattice \ s)ᶜ
-/
lemma differentiableOn_derivWeierstrassPExcept (l₀ : ℂ) :
    DifferentiableOn ℂ ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀
    |>.tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s ↦ .fun_sum fun i hi ↦ ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  refine .div (by fun_prop) (by fun_prop) fun x hx ↦ ?_
  have : x ≠ i := by rintro rfl; simp_all
  simpa [sub_eq_zero]
/-
**PeriodPair.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept** 是 Mathlib 中
的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (l₀ : Complex) : Set
.EqOn (deriv ℘[L - l₀]) ℘'[L - l₀] (L.lattice \ {l₀})ᶜ
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.unique`：TendstoLocallyUniformlyOn.unique [p.Ne
Bot] [T2Space β] {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p s) (hg : Ten
dstoLocallyUniformlyOn…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `TendstoLocallyUniformlyOn.deriv`：∀ {E : Type u_1} {ι : Type u_2} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Filter ι}   {
F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用引理 `PeriodPair.hasSumLocallyUniformly_weierstrassPExcept`：hasSumLocallyUnifo
rmly_weierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (l : L.latt
ice) (z : Complex) => if l.1 = l₀ then 0 e…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_sum`：DifferentiableOn.fun_sum (h : forall i in u, D
ifferentiableOn 𝕜 (A i) s) : DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DifferentiableOn.sub`：DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f - g) s
· 使用定理 `DifferentiableOn.div`：DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s)
 (hd : DifferentiableOn 𝕜 d s) (hx : forall x in s, d x != 0) : DifferentiableOn
 𝕜 (c / d)…
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `DifferentiableOn.sub_const`：DifferentiableOn.sub_const (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 94 条，此处仅展示前 30 条）
-/
lemma eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (l₀ : ℂ) :
    Set.EqOn (deriv ℘[L - l₀]) ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine ((L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ ?_) L.isOpen_compl_lattice_sdiff).unique ?_
  · refine .fun_sum fun i hi ↦ ?_
    split_ifs
    · simp
    refine .sub (.div (by fun_prop) (by fun_prop) fun x hx ↦ ?_) (by fun_prop)
    have : x ≠ i := by rintro rfl; simp_all
    simpa [sub_eq_zero]
  · refine (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.congr ?_
    intro s l hl
    simp only [Function.comp_apply]
    rw [deriv_fun_sum]
    · congr with x
      split_ifs with hl₁
      · simp
      have hl₁ : l - x ≠ 0 := fun e ↦ hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      rw [deriv_fun_sub (.fun_div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop),
        deriv_const]
      simp_rw [← zpow_natCast, one_div, ← zpow_neg, Nat.cast_ofNat]
      rw [deriv_comp_sub_const (f := (· ^ (-2 : ℤ))), deriv_zpow]
      simp
      field_simp
    · intros x hxs
      split_ifs with hl₁
      · simp
      have hl₁ : l - x ≠ 0 := fun e ↦ hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      exact .sub (.div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop)
/-
**PeriodPair.deriv_weierstrassPExcept_same** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair
`。
形式化陈述：∀ (L : PeriodPair) (l : ℂ), deriv (L.weierstrassPExcept l) l = L.derivWeie
rstrassPExcept l l
参数：L : PeriodPair；l : ℂ；L.weierstrassPExcept l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept`：eqOn_d
eriv_weierstrassPExcept_derivWeierstrassPExcept (l₀ : Complex) : Set.EqOn (deriv
 ℘[L - l₀]) ℘'[L - l₀] (L.lattice \ {l₀})ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma deriv_weierstrassPExcept_same (l : ℂ) : deriv ℘[L - l] l = ℘'[L - l] l :=
  L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l (x := l) (by simp)
/-
**PeriodPair.derivWeierstrassPExcept_neg** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassPExcept_neg (l₀ : Complex) (z : Complex) : ℘'[L - l₀] (-z)
 = - ℘'[L - (-l₀)] z
参数：l₀ : Complex；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 65 条，此处仅展示前 30 条）
-/
lemma derivWeierstrassPExcept_neg (l₀ : ℂ) (z : ℂ) :
    ℘'[L - l₀] (-z) = - ℘'[L - (-l₀)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring
/-
**PeriodPair.derivWeierstrassPExcept_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Period
Pair`。
形式化陈述：∀ (L : PeriodPair), L.derivWeierstrassPExcept 0 0 = 0
参数：L : PeriodPair。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `PeriodPair.derivWeierstrassPExcept_neg`：derivWeierstrassPExcept_neg (l₀ 
: Complex) (z : Complex) : ℘'[L - l₀] (-z) = - ℘'[L - (-l₀)] z
-/
@[simp] lemma derivWeierstrassPExcept_zero_zero : ℘'[L - 0] 0 = 0 := by
  simpa [CharZero.eq_neg_self_iff] using L.derivWeierstrassPExcept_neg 0 0

end derivWeierstrassPExcept

section Periodicity

/-
**PeriodPair.derivWeierstrassPExcept_add_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPa
ir`。
形式化陈述：derivWeierstrassPExcept_add_coe (l₀ : Complex) (z : Complex) (l : L.lattic
e) : ℘'[L - l₀] (z + l) = ℘'[L - (l₀ - l)] z
参数：l₀ : Complex；z : Complex；l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma derivWeierstrassPExcept_add_coe (l₀ : ℂ) (z : ℂ) (l : L.lattice) :
    ℘'[L - l₀] (z + l) = ℘'[L - (l₀ - l)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub, eq_sub_iff_add_eq]

-- Subsumed by `weierstrassP_add_coe`
/-
**PeriodPair.weierstrassPExcept_add_coe_aux** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPai
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma weierstrassPExcept_add_coe_aux
    (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    Set.EqOn (℘[L - l₀] <| · + l) (℘[L - (l₀ - l)] · + (1 / l₀ ^ 2 - 1 / (l₀ - ↑l) ^ 2))
      (L.lattice \ {l₀ - l})ᶜ := by
  apply IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isOpen_compl_lattice_sdiff
    ?_ ?_ ?_ ?_ (x := -(l / 2)) ?_ ?_
  · refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact .mono sdiff_le (countable_of_Lindelof_of_discrete (X := L.lattice))
  · refine (L.differentiableOn_weierstrassPExcept l₀).comp (f := (· + l.1)) (by fun_prop) ?_
    rintro x h₁ ⟨h₂ : x + l ∈ _, h₃ : x + l ≠ l₀⟩
    exact h₁ ⟨by simpa using sub_mem h₂ l.2, by rintro rfl; simp at h₃⟩
  · refine .add (L.differentiableOn_weierstrassPExcept _) (by simp)
  · intro x hx
    simp only [deriv_add_const', deriv_comp_add_const]
    rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept,
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept, L.derivWeierstrassPExcept_add_coe]
    · simpa using hx
    · simp only [Set.mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, not_and,
        Decidable.not_not, eq_sub_iff_add_eq] at hx ⊢
      exact fun H ↦ hx (by simpa using sub_mem H l.2)
  · simp [hl]
  · rw [L.weierstrassPExcept_neg, L.weierstrassPExcept_def ⟨l₀, hl₀⟩,
      L.weierstrassPExcept_def ⟨_, neg_mem (sub_mem hl₀ l.2)⟩, add_assoc]
    congr 2 <;> ring

-- Subsumed by `weierstrassP_add_coe`
/-
**PeriodPair.weierstrassP_add_coe_aux** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma weierstrassP_add_coe_aux (z : ℂ) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    ℘[L] (z + l) = ℘[L] z := by
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl
  by_cases hz : z ∈ L.lattice
  · have := L.weierstrassPExcept_add_coe_aux (z + l) (add_mem hz l.2) l hl (x := z) (by simp)
    dsimp at this
    rw [← L.weierstrassPExcept_add ⟨z + l, add_mem hz l.2⟩, this,
      ← L.weierstrassPExcept_add ⟨z, hz⟩]
    simp
    ring
  · have := L.weierstrassPExcept_add_coe_aux 0 (zero_mem _) l hl (x := z) (by simp [hz])
    simp only [zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      even_two, Even.neg_pow, one_div] at this
    rw [← L.weierstrassPExcept_add 0, Submodule.coe_zero, this, ← L.weierstrassPExcept_add (-l)]
    simp
    ring

@[simp]
/-
**PeriodPair.weierstrassP_add_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP_add_coe (z : Complex) (l : L.lattice) : ℘[L] (z + l) = ℘[L] z
参数：z : Complex；l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `PeriodPair.lattice.eq_1`：∀ (L : PeriodPair), L.lattice = Submodule.span 
ℤ {L.ω₁, L.ω₂}
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.0.Period
Pair.weierstrassP_add_coe_aux`：∀ (L : PeriodPair) (z : ℂ) (l : ↥L.lattice), ↑l /
 2 ∉ L.lattice → L.weierstrassP (z + ↑l) = L.weierstrassP z
· 使用引理 `PeriodPair.ω₁_mem_lattice`：ω₁_mem_lattice : L.ω₁ in L.lattice
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用引理 `PeriodPair.ω₂_mem_lattice`：ω₂_mem_lattice : L.ω₂ in L.lattice
· 使用引理 `PeriodPair.ω₂_div_two_notMem_lattice`：ω₂_div_two_notMem_lattice : L.ω₂ /
 2 ∉ L.lattice
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma weierstrassP_add_coe (z : ℂ) (l : L.lattice) : ℘[L] (z + l) = ℘[L] z := by
  let G : AddSubgroup ℂ :=
    { carrier := { z | (℘[L] <| · + z) = ℘[L] }
      add_mem' := by simp_all [funext_iff, ← add_assoc]
      zero_mem' := by simp
      neg_mem' {z} hz := funext fun i ↦ by conv_lhs => rw [← hz]; simp }
  have : L.lattice ≤ G.toIntSubmodule := by
    rw [lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    · ext i
      exact L.weierstrassP_add_coe_aux _ ⟨_, L.ω₁_mem_lattice⟩ L.ω₁_div_two_notMem_lattice
    · ext i
      exact L.weierstrassP_add_coe_aux _ ⟨_, L.ω₂_mem_lattice⟩ L.ω₂_div_two_notMem_lattice
  exact congr_fun (this l.2) _
/-
**PeriodPair.periodic_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：periodic_weierstrassP (l : L.lattice) : ℘[L].Periodic l
参数：l : L.lattice。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.weierstrassP_add_coe`：weierstrassP_add_coe (z : Complex) (l :
 L.lattice) : ℘[L] (z + l) = ℘[L] z
-/
lemma periodic_weierstrassP (l : L.lattice) : ℘[L].Periodic l :=
  (L.weierstrassP_add_coe · l)

@[simp]
/-
**PeriodPair.weierstrassP_zero** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP_zero : ℘[L] 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weierstrassP_zero : ℘[L] 0 = 0 := by simp [weierstrassP]

@[simp]
/-
**PeriodPair.weierstrassP_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP_coe (l : L.lattice) : ℘[L] l = 0
参数：l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `PeriodPair.weierstrassP_add_coe`：weierstrassP_add_coe (z : Complex) (l :
 L.lattice) : ℘[L] (z + l) = ℘[L] z
· 使用引理 `PeriodPair.weierstrassP_zero`：weierstrassP_zero : ℘[L] 0 = 0
-/
lemma weierstrassP_coe (l : L.lattice) : ℘[L] l = 0 := by
  rw [← zero_add l.1, L.weierstrassP_add_coe, L.weierstrassP_zero]

@[simp]
/-
**PeriodPair.weierstrassP_sub_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassP_sub_coe (z : Complex) (l : L.lattice) : ℘[L] (z - l) = ℘[L] z
参数：z : Complex；l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassP_add_coe`：weierstrassP_add_coe (z : Complex) (l :
 L.lattice) : ℘[L] (z + l) = ℘[L] z
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma weierstrassP_sub_coe (z : ℂ) (l : L.lattice) : ℘[L] (z - l) = ℘[L] z := by
  rw [← L.weierstrassP_add_coe _ l, sub_add_cancel]

end Periodicity

section derivWeierstrassP

/-- The derivative of Weierstrass `℘` function.
This has the notation `℘'[L]` in the namespace `PeriodPairs`. -/
/-
**PeriodPair.derivWeierstrassP** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP (z : Complex) : Complex
参数：z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of Weierstrass `℘` function.
This has the notation `℘'[L]` in the namespace `PeriodPairs`.
-/
def derivWeierstrassP (z : ℂ) : ℂ := - ∑' l : L.lattice, 2 / (z - l) ^ 3

@[inherit_doc weierstrassP] scoped notation3 "℘'[" L "]" => derivWeierstrassP L
/-
**PeriodPair.derivWeierstrassPExcept_sub** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassPExcept_sub (l₀ : L.lattice) (z : Complex) : ℘'[L - l₀] z 
- 2 / (z - l₀) ^ 3 = ℘'[L] z
参数：l₀ : L.lattice；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PeriodPair.derivWeierstrassP.eq_1`：∀ (L : PeriodPair) (z : ℂ), L.derivWe
ierstrassP z = -∑' (l : ↥L.lattice), 2 / (z - ↑l) ^ 3
· 使用定理 `PeriodPair.derivWeierstrassPExcept.eq_1`：∀ (L : PeriodPair) (l₀ z : ℂ), 
  L.derivWeierstrassPExcept l₀ z = ∑' (l : ↥L.lattice), if ↑l = l₀ then 0 else -
2 / (z - ↑l) ^ 3
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `PeriodPair.hasSum_derivWeierstrassPExcept`：hasSum_derivWeierstrassPExcep
t (l₀ : Complex) (z : Complex) : HasSum (fun l : L.lattice => if l.1 = l₀ then 0
 else -2 / (z - l) ^ 3) (℘'[L -…
· 使用定理 `summable_of_hasFiniteSupport`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [L.HasSupport],…
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
（共 43 条，此处仅展示前 30 条）
-/
lemma derivWeierstrassPExcept_sub (l₀ : L.lattice) (z : ℂ) :
    ℘'[L - l₀] z - 2 / (z - l₀) ^ 3 = ℘'[L] z := by
  trans ℘'[L - l₀] z + ∑' i : L.lattice, if i.1 = l₀.1 then (- 2 / (z - l₀) ^ 3) else 0
  · simp [sub_eq_add_neg, neg_div]
  rw [derivWeierstrassP, derivWeierstrassPExcept, ← Summable.tsum_add, ← tsum_neg]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *, neg_div]
  · exact ⟨_, L.hasSum_derivWeierstrassPExcept _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))
/-
**PeriodPair.derivWeierstrassPExcept_def** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassPExcept_def (l₀ : L.lattice) (z : Complex) : ℘'[L - l₀] z 
= ℘'[L] z + 2 / (z - l₀) ^ 3
参数：l₀ : L.lattice；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.derivWeierstrassPExcept_sub`：derivWeierstrassPExcept_sub (l₀ 
: L.lattice) (z : Complex) : ℘'[L - l₀] z - 2 / (z - l₀) ^ 3 = ℘'[L] z
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma derivWeierstrassPExcept_def (l₀ : L.lattice) (z : ℂ) :
    ℘'[L - l₀] z = ℘'[L] z + 2 / (z - l₀) ^ 3 := by
  rw [← L.derivWeierstrassPExcept_sub l₀, sub_add_cancel]
/-
**PeriodPair.derivWeierstrassPExcept_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Period
Pair`。
形式化陈述：derivWeierstrassPExcept_of_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘
'[L - l₀] = ℘'[L]
参数：l₀ : Complex；hl : l₀ ∉ L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma derivWeierstrassPExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    ℘'[L - l₀] = ℘'[L] := by
  delta derivWeierstrassPExcept derivWeierstrassP
  simp_rw [← tsum_neg]
  congr! 3 with z l
  have : l.1 ≠ l₀ := by rintro rfl; simp at hl
  simp [this, neg_div]
/-
**PeriodPair.hasSumLocallyUniformly_derivWeierstrassP** 是 Mathlib 中的一个引理，位于命名空间 
`PeriodPair`。
形式化陈述：hasSumLocallyUniformly_derivWeierstrassP : HasSumLocallyUniformly (fun (l 
: L.lattice) (z : Complex) => - 2 / (z - l) ^ 3) ℘'[L]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用引理 `PeriodPair.derivWeierstrassPExcept_of_notMem`：derivWeierstrassPExcept_of
_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘'[L - l₀] = ℘'[L]
· 使用引理 `PeriodPair.hasSumLocallyUniformly_derivWeierstrassPExcept`：hasSumLocally
Uniformly_derivWeierstrassPExcept (l₀ : Complex) : HasSumLocallyUniformly (fun (
l : L.lattice) (z : Complex) => if l.1 = l₀ the…
-/
lemma hasSumLocallyUniformly_derivWeierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ - 2 / (z - l) ^ 3) ℘'[L] := by
  convert! L.hasSumLocallyUniformly_derivWeierstrassPExcept (L.ω₁ / 2) using 3 with l z
  · rw [if_neg, neg_div]; exact fun e ↦ L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
/-
**PeriodPair.hasSum_derivWeierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：hasSum_derivWeierstrassP (z : Complex) : HasSum (fun l : L.lattice => - 2 
/ (z - l) ^ 3) (℘'[L] z)
参数：z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用引理 `PeriodPair.hasSumLocallyUniformly_derivWeierstrassP`：hasSumLocallyUnifor
mly_derivWeierstrassP : HasSumLocallyUniformly (fun (l : L.lattice) (z : Complex
) => - 2 / (z - l) ^ 3) ℘'[L]
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma hasSum_derivWeierstrassP (z : ℂ) :
    HasSum (fun l : L.lattice ↦ - 2 / (z - l) ^ 3) (℘'[L] z) :=
  L.hasSumLocallyUniformly_derivWeierstrassP.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)
/-
**PeriodPair.differentiableOn_derivWeierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：differentiableOn_derivWeierstrassP : DifferentiableOn Complex ℘'[L] L.latt
iceᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.derivWeierstrassPExcept_of_notMem`：derivWeierstrassPExcept_of
_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘'[L - l₀] = ℘'[L]
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `PeriodPair.differentiableOn_derivWeierstrassPExcept`：differentiableOn_de
rivWeierstrassPExcept (l₀ : Complex) : DifferentiableOn Complex ℘'[L - l₀] (L.la
ttice \ {l₀})ᶜ
-/
lemma differentiableOn_derivWeierstrassP :
    DifferentiableOn ℂ ℘'[L] L.latticeᶜ := by
  rw [← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_derivWeierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]
/-
**PeriodPair.derivWeierstrassP_neg** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP_neg (z : Complex) : ℘'[L] (-z) = - ℘'[L] z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 57 条，此处仅展示前 30 条）
-/
lemma derivWeierstrassP_neg (z : ℂ) : ℘'[L] (-z) = - ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg]
  congr! with l
  ring

@[simp]
/-
**PeriodPair.derivWeierstrassP_add_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP_add_coe (z : Complex) (l : L.lattice) : ℘'[L] (z + l) = 
℘'[L] z
参数：z : Complex；l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma derivWeierstrassP_add_coe (z : ℂ) (l : L.lattice) :
    ℘'[L] (z + l) = ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]
/-
**PeriodPair.periodic_derivWeierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：periodic_derivWeierstrassP (l : L.lattice) : ℘'[L].Periodic l
参数：l : L.lattice。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.derivWeierstrassP_add_coe`：derivWeierstrassP_add_coe (z : Com
plex) (l : L.lattice) : ℘'[L] (z + l) = ℘'[L] z
-/
lemma periodic_derivWeierstrassP (l : L.lattice) : ℘'[L].Periodic l :=
  (L.derivWeierstrassP_add_coe · l)

@[simp]
/-
**PeriodPair.derivWeierstrassP_zero** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP_zero : ℘'[L] 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharZero.eq_neg_self_iff`：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZe
roDivisors R] [CharZero R] {a : R}, a = -a ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `PeriodPair.derivWeierstrassP_neg`：derivWeierstrassP_neg (z : Complex) : 
℘'[L] (-z) = - ℘'[L] z
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma derivWeierstrassP_zero : ℘'[L] 0 = 0 := by
  rw [← CharZero.eq_neg_self_iff, ← L.derivWeierstrassP_neg, neg_zero]

@[simp]
/-
**PeriodPair.derivWeierstrassP_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP_coe (l : L.lattice) : ℘'[L] l = 0
参数：l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `PeriodPair.derivWeierstrassP_add_coe`：derivWeierstrassP_add_coe (z : Com
plex) (l : L.lattice) : ℘'[L] (z + l) = ℘'[L] z
· 使用引理 `PeriodPair.derivWeierstrassP_zero`：derivWeierstrassP_zero : ℘'[L] 0 = 0
-/
lemma derivWeierstrassP_coe (l : L.lattice) : ℘'[L] l = 0 := by
  rw [← zero_add l.1, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_zero]

@[simp]
/-
**PeriodPair.derivWeierstrassP_sub_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP_sub_coe (z : Complex) (l : L.lattice) : ℘'[L] (z - l) = 
℘'[L] z
参数：z : Complex；l : L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.derivWeierstrassP_add_coe`：derivWeierstrassP_add_coe (z : Com
plex) (l : L.lattice) : ℘'[L] (z + l) = ℘'[L] z
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma derivWeierstrassP_sub_coe (z : ℂ) (l : L.lattice) :
    ℘'[L] (z - l) = ℘'[L] z := by
  rw [← L.derivWeierstrassP_add_coe _ l, sub_add_cancel]

/-- `deriv ℘ = ℘'`. This is true globally because of junk values. -/
/-
**PeriodPair.deriv_weierstrassP** 是 Mathlib 中的一个定理，位于命名空间 `PeriodPair`。
形式化陈述：∀ (L : PeriodPair), deriv L.weierstrassP = L.derivWeierstrassP
参数：L : PeriodPair。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用引理 `PeriodPair.not_continuousAt_weierstrassP`：not_continuousAt_weierstrassP 
(x : Complex) (hx : x in L.lattice) : ¬ ContinuousAt ℘[L] x
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `PeriodPair.derivWeierstrassP_coe`：derivWeierstrassP_coe (l : L.lattice) 
: ℘'[L] l = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExcept_of_notMem`：weierstrassPExcept_of_notMem (l
₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - l₀] = ℘[L]
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用引理 `PeriodPair.derivWeierstrassPExcept_of_notMem`：derivWeierstrassPExcept_of
_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘'[L - l₀] = ℘'[L]
· 使用引理 `PeriodPair.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept`：eqOn_d
eriv_weierstrassPExcept_derivWeierstrassPExcept (l₀ : Complex) : Set.EqOn (deriv
 ℘[L - l₀]) ℘'[L - l₀] (L.lattice \ {l₀})ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
`deriv ℘ = ℘'`. This is true globally because of junk values.
-/
@[simp] lemma deriv_weierstrassP : deriv ℘[L] = ℘'[L] := by
  ext x
  by_cases hx : x ∈ L.lattice
  · rw [deriv_zero_of_not_differentiableAt, L.derivWeierstrassP_coe ⟨x, hx⟩]
    exact fun H ↦ L.not_continuousAt_weierstrassP x hx H.continuousAt
  · rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      ← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (L.ω₁ / 2) (x := x) (by simp [hx])]

end derivWeierstrassP

section AnalyticWeierstrassPExcept

/-- The sum `∑ (l - x)⁻ʳ` over `l ∈ L`. This converges when `2 < r`, see `hasSum_sumInvPow`. -/
/-
**PeriodPair.sumInvPow** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：sumInvPow (x : Complex) (r : Nat) : Complex
参数：x : Complex；r : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum `∑ (l - x)⁻ʳ` over `l ∈ L`. This converges when `2 < r`, see `hasSum_sum
InvPow`.
-/
def sumInvPow (x : ℂ) (r : ℕ) : ℂ := ∑' l : L.lattice, ((l - x) ^ r)⁻¹
/-
**PeriodPair.hasSum_sumInvPow** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：hasSum_sumInvPow (x : Complex) {r : Nat} (hr : 2 < r) : HasSum (fun l : L.
lattice => ((l - x) ^ r)⁻¹) (L.sumInvPow x r)
参数：x : Complex；hr : 2 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `ZLattice.summable_norm_sub_zpow`：summable_norm_sub_zpow (n : Int) (hn : 
n < -Module.finrank Int L) (x : E) : Summable fun z : L => ‖z - x‖ ^ n
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `PeriodPair.instDiscreteTopologySubtypeComplexMemSubmoduleIntLattice`：∀ (
L : PeriodPair), DiscreteTopology ↥L.lattice
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PeriodPair.finrank_lattice`：∀ (L : PeriodPair), Module.finrank ℤ ↥L.latt
ice = 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma hasSum_sumInvPow (x : ℂ) {r : ℕ} (hr : 2 < r) :
    HasSum (fun l : L.lattice ↦ ((l - x) ^ r)⁻¹) (L.sumInvPow x r) := by
  refine Summable.hasSum (.of_norm_bounded (ZLattice.summable_norm_sub_zpow _
    (-r) (by simpa) x) fun l ↦ ?_)
  rw [← zpow_natCast, ← zpow_neg, ← norm_zpow]

/-- In the power series expansion of `℘(z) = ∑ aᵢ (z - x)ⁱ` at some `x ∉ L`,
each `aᵢ` can be written as an infinite sum over `l ∈ L`.
This is the summand of this infinite sum with the `l₀`-th term omitted.
See `PeriodPair.coeff_weierstrassPExceptSeries`. -/
/-
**PeriodPair.weierstrassPExceptSummand** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExceptSummand (l₀ x : Complex) (i : Nat) (l : L.lattice) : Com
plex
参数：l₀ x : Complex；i : Nat；l : L.lattice。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the power series expansion of `℘(z) = ∑ aᵢ (z - x)ⁱ` at some `x ∉ L`,
each `aᵢ` can be written as an infinite sum over `l ∈ L`.
This is the summand of this infinite sum with the `l₀`-th term omitted.
See `PeriodPair.coeff_weierstrassPExceptSeries`.
-/
def weierstrassPExceptSummand (l₀ x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

/-- The power series expansion of `℘[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept`. -/
/-
**PeriodPair.weierstrassPExceptSeries** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExceptSeries (l₀ x : Complex) : FormalMultilinearSeries Comple
x Complex Complex
参数：l₀ x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series expansion of `℘[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept`.
-/
def weierstrassPExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ if i = 0 then (℘[L - l₀] x) else (i + 1) *
    (L.sumInvPow x (i + 2) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 2))⁻¹ else 0)
/-
**PeriodPair.coeff_weierstrassPExceptSeries** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPai
r`。
形式化陈述：coeff_weierstrassPExceptSeries (l₀ x : Complex) (i : Nat) : (L.weierstrass
PExceptSeries l₀ x).coeff i = ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x
 i l
参数：l₀ x : Complex；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `sub_sq_comm`：sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
（共 121 条，此处仅展示前 30 条）
-/
lemma coeff_weierstrassPExceptSeries (l₀ x : ℂ) (i : ℕ) :
    (L.weierstrassPExceptSeries l₀ x).coeff i =
      ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x i l := by
  delta weierstrassPExceptSummand weierstrassPExceptSeries
  cases i with
  | zero => simp [weierstrassPExcept, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : ℤ) else 0)
      · rw [FormalMultilinearSeries.coeff_ofScalars, tsum_ite_eq, zpow_neg, zpow_natCast]
        simp [add_assoc, one_add_one_eq_two]
      · rw [sumInvPow, ← (hasSum_sumInvPow _ _ (by linarith)).summable.tsum_sub, ← tsum_mul_left]
        · simp_rw [Subtype.ext_iff, zpow_neg]
          congr with l
          split_ifs with e
          · simp only [e, zpow_natCast, sub_self, mul_zero]
          · dsimp; norm_cast; ring
        · exact summable_of_hasFiniteSupport ((Set.finite_singleton ⟨l₀, hl₀⟩).subset (by simp))
    · have h₁ (l : L.lattice) : l.1 ≠ l₀ := fun e ↦ hl₀ (e ▸ l.2)
      simp [h₁, tsum_mul_left, sumInvPow, add_assoc,
        one_add_one_eq_two, ← zpow_natCast, -neg_add_rev]

set_option backward.isDefEq.respectTransparency.types false in
/--
In the power series expansion of `℘(z) = ∑ᵢ aᵢ (z - x)ⁱ` at some `x ∉ L`,
each `aᵢ` can be written as a sum over `l ∈ L`, i.e.
`aᵢ = ∑ₗ, (i + 1) * (l - x)⁻ⁱ⁻²` for `i ≠ 0` and `a₀ = ∑ₗ, (l - x)⁻² - l⁻²`.

We show that the double sum converges if `z` falls in a ball centered at `x` that doesn't touch `L`.
-/
-- We should be able to skip this computation via some general complex-analytic machinery but
-- they are missing at the moment.
-- Consider refactoring once we have developed more of the missing API.
/-
**PeriodPair.summable_weierstrassPExceptSummand** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：summable_weierstrassPExceptSummand (l₀ z x : Complex) (hx : forall l : L.l
attice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) : Summable (Function.uncurry fun b c => 
L.weierstrassPExceptSummand l₀ x b c * (z - x) ^ b)
参数：l₀ z x : Complex；hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
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
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `IsClosed.upperClosure`：∀ {α : Type u_3} [inst : ConditionallyCompleteLin
earOrder α] [inst_1 : TopologicalSpace α] [OrderTopology α]   {s : Set α}, IsClo
sed s → IsC…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `isClosedMap_dist`：isClosedMap_dist (x : α) : IsClosedMap (dist x)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用引理 `PeriodPair.isClosed_of_subset_lattice`：isClosed_of_subset_lattice {s : S
et Complex} (hs : s subseteq L.lattice) : IsClosed s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Complex.dist_eq`：dist_eq (z w : Complex) : dist z w = ‖z - w‖
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 243 条，此处仅展示前 30 条）
-/
lemma summable_weierstrassPExceptSummand (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.weierstrassPExceptSummand l₀ x b c * (z - x) ^ b) := by
  -- We first find a `κ > 1`,
  -- such that the ball centered at `x` with radius `κ * ‖z - x‖` does not touch `L`.
  obtain ⟨κ, hκ, hκ'⟩ : ∃ κ : ℝ, 1 < κ ∧ ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ * κ < ‖l - x‖ := by
    obtain ⟨κ, hκ, hκ'⟩ := Metric.isOpen_iff.mp ((continuous_mul_const ‖z - x‖).isOpen_preimage _
      (isClosedMap_dist x _
      (L.isClosed_of_subset_lattice (Set.sdiff_subset (t := {l₀})))).upperClosure.isOpen_compl) 1
      (by simpa [Complex.dist_eq, @forall_comm ℝ, norm_sub_rev x] using hx)
    refine ⟨κ / 2 + 1, by simpa, fun l hl ↦ ?_⟩
    have : ∀ l ∈ L.lattice, l ≠ l₀ → (κ / 2 + 1) * ‖z - x‖ < dist x l := by
      simpa using @hκ' (κ / 2 + 1) (by simp [div_lt_iff₀, abs_eq_self.mpr hκ.le, hκ])
    simpa only [Complex.dist_eq, norm_sub_rev x, mul_comm] using this _ l.2 hl
  -- We single out the degree zero term via this equiv.
  let e : ℕ × L.lattice ≃ L.lattice ⊕ (ℕ × L.lattice) :=
    (Equiv.prodCongrLeft fun _ ↦ (Denumerable.eqv (Option ℕ)).symm).trans optionProdEquiv
  rw [← e.symm.summable_iff]
  apply Summable.sum
  · -- for the degree zero term, this is the usual summability of the definition of `℘`.
    simpa [weierstrassPExceptSummand, e, Function.comp_def, Function.uncurry, sub_sq_comm x,
      Denumerable.eqv] using! (L.hasSum_weierstrassPExcept l₀ x).summable
  · -- for the remaining terms, we bound it by `(i + 2) κ⁻ⁱ * ‖l - x‖⁻³ * ‖z - x‖`.
    dsimp [e, Function.comp_def, Function.uncurry_def, Denumerable.eqv, weierstrassPExceptSummand]
    have H₁ : Summable fun i : ℕ ↦ ((i + 2) * κ ^ (-i : ℤ)) := by
      have : |κ⁻¹| < 1 := by grind [abs_inv, inv_lt_one_iff₀]
      simpa [mul_comm] using ((Real.hasFPowerSeriesOnBall_ofScalars_mul_add_zero 1 2).hasSum
        (y := κ⁻¹) (by simpa [enorm_eq_nnnorm])).summable
    have H₂ : Summable fun l : L.lattice ↦ ‖l - x‖ ^ (-3 : ℤ) * ‖z - x‖ :=
      (ZLattice.summable_norm_sub_zpow _ _ (by simp) _).mul_right _
    refine (H₁.mul_of_nonneg H₂ (by intro; positivity) (by intro; positivity)).of_norm_bounded ?_
    intro p
    split_ifs with hp
    · simp only [zero_mul, norm_zero, zpow_neg, zpow_natCast, Int.reduceNeg]; positivity
    have hpx : ‖p.2 - x‖ ≠ 0 := fun h ↦ by
      obtain rfl : p.2 = x := by simpa [sub_eq_zero] using h
      simpa [(norm_nonneg _).not_gt] using hx p.2 hp
    obtain rfl | hxz := eq_or_ne z x
    · simp
    calc
      _ = ‖(p.1 + 2 : ℂ)‖ * ‖p.2 - x‖ ^ (-3 - p.1 : ℤ) * ‖z - x‖ ^ (p.1 + 1) := by
        norm_num; ring_nf; simp
      _ = ‖(p.1 + 2 : ℂ)‖ * ((‖↑p.2 - x‖ / ‖z - x‖) ^ p.1)⁻¹ * ((‖p.2 - x‖ ^ 3)⁻¹ * ‖z - x‖) := by
        simp [hpx, zpow_sub₀, div_pow]; field
      _ ≤ (p.1 + 2) * (κ ^ p.1)⁻¹ * ((‖p.2 - x‖ ^ 3)⁻¹ * ‖z - x‖) := by
        gcongr
        · norm_cast
        · exact (le_div_iff₀ (by simpa [sub_eq_zero])).mpr ((mul_comm _ _).trans_le (hκ' p.2 hp).le)
      _ = _ := by simp [zpow_ofNat]
/-
**PeriodPair.weierstrassPExcept_eq_tsum** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPExcept_eq_tsum (l₀ z x : Complex) (hx : forall l : L.lattice, 
l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) : ℘[L - l₀] z = ∑' i : Nat, (L.weierstrassPExcep
tSeries l₀ x).coeff i * (z - x) ^ i
参数：l₀ z x : Complex；hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `FormalMultilinearSeries.ofScalars.congr_simp`：∀ {𝕜 : Type u_1} (E : Type
 u_2) [inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : Topolo
gicalSpace E]   [inst_4 : IsTopolo…
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
（共 48 条，此处仅展示前 30 条）
-/
lemma weierstrassPExcept_eq_tsum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    ℘[L - l₀] z = ∑' i : ℕ, (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i := by
  trans ∑' (l : L.lattice) (i : ℕ), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0) * (z - x) ^ i
  · delta weierstrassPExcept
    congr 1 with l
    split_ifs with h
    · simp
    simpa [mul_comm] using ((Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero l x
      (by simpa [sub_eq_zero] using (norm_nonneg _).trans_lt (hx l h))).hasSum (y := z - x)
      (by simpa [enorm_eq_nnnorm] using hx _ h)).tsum_eq.symm
  trans ∑' (l : ↥L.lattice) (i : ℕ), L.weierstrassPExceptSummand l₀ x i l * (z - x) ^ i
  · simp only [weierstrassPExceptSummand, ite_mul, zero_mul]
  · simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
    apply Summable.tsum_comm
    exact L.summable_weierstrassPExceptSummand l₀ z x hx
/-
**PeriodPair.weierstrassPExceptSeries_hasSum** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPa
ir`。
形式化陈述：weierstrassPExceptSeries_hasSum (l₀ z x : Complex) (hx : forall l : L.latt
ice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) : HasSum (fun i => (L.weierstrassPExceptSer
ies l₀ x).coeff i * (z - x) ^ i) (℘[L - l₀] z)
参数：l₀ z x : Complex；hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Summable.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α
} [T2Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PeriodPair.coeff_weierstrassPExceptSeries`：coeff_weierstrassPExceptSerie
s (l₀ x : Complex) (i : Nat) : (L.weierstrassPExceptSeries l₀ x).coeff i = ∑' l 
: L.lattice, L.weierstrassPExce…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Summable.prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommGroup α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSpace α
] {…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.summable_weierstrassPExceptSummand`：summable_weierstrassPExce
ptSummand (l₀ z x : Complex) (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < 
‖l - x‖) : Summable (Function.uncur…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExcept_eq_tsum`：weierstrassPExcept_eq_tsum (l₀ z 
x : Complex) (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) : ℘[L -
 l₀] z = ∑' i : Nat, (L.wei…
-/
lemma weierstrassPExceptSeries_hasSum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i ↦ (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i) (℘[L - l₀] z) := by
  refine (Summable.hasSum_iff ?_).mpr (L.weierstrassPExcept_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
  exact (L.summable_weierstrassPExceptSummand l₀ z x hx).prod
/-
**PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 
`PeriodPair`。
形式化陈述：hasFPowerSeriesOnBall_weierstrassPExcept (l₀ x : Complex) (r : NNReal) (hr
0 : 0 < r) (hr : Metric.closedBall x r subseteq (L.lattice \ {l₀})ᶜ) : HasFPower
SeriesOnBall ℘[L - l₀] (L.weierstrassPExceptSeries l₀ x) x r
参数：l₀ x : Complex；r : NNReal；hr0 : 0 < r；hr : Metric.closedBall x r subseteq (L.
lattice \ {l₀})ᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.le_radius_of_tendsto`：le_radius_of_tendsto (p : 
FormalMultilinearSeries 𝕜 E F) {l : Real} (h : Tendsto (fun n => ‖p n‖ * (r : Re
al) ^ n) atTop (𝓝 l)) : ↑r <= p.ra…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.norm_apply_eq_norm_coef`：norm_apply_eq_norm_coef
 : ‖p n‖ = ‖coeff p n‖
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E] {x : E}, Fi
lter.Tendsto (fun a => ‖a‖) (nhds x) (nhds ‖x‖)
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用引理 `PeriodPair.weierstrassPExceptSeries_hasSum`：weierstrassPExceptSeries_has
Sum (l₀ z x : Complex) (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x
‖) : HasSum (fun i => (L.weierst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
（共 48 条，此处仅展示前 30 条）
-/
lemma hasFPowerSeriesOnBall_weierstrassPExcept (l₀ x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘[L - l₀] (L.weierstrassPExceptSeries l₀ x) x r := by
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert!
      tendsto_norm.comp
        (L.weierstrassPExceptSeries_hasSum l₀ (x + r) x ?_).summable.tendsto_atTop_zero using
      2 with i
    · simp
    · simp
    · intro l hl
      simpa [-Metric.mem_closedBall, mem_closedBall_iff_norm]
        using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
  · exact ENNReal.coe_pos.mpr hr0
  · intro z hz
    replace hz : ‖z‖ < r := by simpa using hz
    have := L.weierstrassPExceptSeries_hasSum l₀ (x + z) x
    simp only [add_sub_cancel_left] at this
    have A (l : ↥L.lattice) (hl : ↑l ≠ l₀) : r < ‖↑l - x‖ := by
      simpa [-Metric.mem_closedBall, mem_closedBall_iff_norm] using
        Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
    convert! this (fun l hl ↦ hz.trans (A l hl)) with i
    rw [weierstrassPExceptSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
/-
**PeriodPair.hasFPowerSeriesAt_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `Per
iodPair`。
形式化陈述：hasFPowerSeriesAt_weierstrassPExcept (l : Complex) : HasFPowerSeriesAt ℘[L
 - l] (.ofScalars (𝕜
参数：l : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用引理 `PeriodPair.compl_lattice_sdiff_singleton_mem_nhds`：compl_lattice_sdiff_s
ingleton_mem_nhds (x : Complex) : (↑L.lattice \ {x})ᶜ in 𝓝 x
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
（共 32 条，此处仅展示前 30 条）
-/
lemma hasFPowerSeriesAt_weierstrassPExcept (l : ℂ) :
    HasFPowerSeriesAt ℘[L - l] (.ofScalars (𝕜 := ℂ) ℂ fun i : ℕ ↦
      if i = 0 then ℘[L - l] l else (i + 1) * L.sumInvPow l (i + 2)) l := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  lift r to NNReal using h₁.le
  simpa [weierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_weierstrassPExcept l l r h₁ h₂).hasFPowerSeriesAt
/-
**PeriodPair.analyticOnNhd_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `PeriodP
air`。
形式化陈述：analyticOnNhd_weierstrassPExcept (l₀ : Complex) : AnalyticOnNhd Complex ℘[
L - l₀] (L.lattice \ {l₀})ᶜ
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.differentiableOn_weierstrassPExcept`：differentiableOn_weierst
rassPExcept (l₀ : Complex) : DifferentiableOn Complex ℘[L - l₀] (L.lattice \ {l₀
})ᶜ
· 使用引理 `PeriodPair.isOpen_compl_lattice_sdiff`：isOpen_compl_lattice_sdiff {s : S
et Complex} : IsOpen (L.lattice \ s)ᶜ
-/
lemma analyticOnNhd_weierstrassPExcept (l₀ : ℂ) : AnalyticOnNhd ℂ ℘[L - l₀] (L.lattice \ {l₀})ᶜ :=
  (L.differentiableOn_weierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]
/-
**PeriodPair.analyticAt_weierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair
`。
形式化陈述：analyticAt_weierstrassPExcept (l₀ : Complex) : AnalyticAt Complex ℘[L - l₀
] l₀
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.analyticOnNhd_weierstrassPExcept`：analyticOnNhd_weierstrassPE
xcept (l₀ : Complex) : AnalyticOnNhd Complex ℘[L - l₀] (L.lattice \ {l₀})ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma analyticAt_weierstrassPExcept (l₀ : ℂ) : AnalyticAt ℂ ℘[L - l₀] l₀ :=
  L.analyticOnNhd_weierstrassPExcept _ _ (by simp)

attribute [local simp] Nat.factorial_ne_zero in
/-
**PeriodPair.iteratedDeriv_weierstrassPExcept_self** 是 Mathlib 中的一个引理，位于命名空间 `Pe
riodPair`。
形式化陈述：iteratedDeriv_weierstrassPExcept_self (l : Complex) {n : Nat} : iteratedDe
riv n ℘[L - l] l = if n = 0 then ℘[L - l] l else (n + 1)! * L.sumInvPow l (n + 2
)
参数：l : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`：HasFPowerSeriesAt.eq_forma
lMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} 
(h₁ : HasFPowerSeriesAt f p₁ x) (h…
· 使用引理 `AnalyticAt.hasFPowerSeriesAt`：AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [
NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (
h : AnalyticAt 𝕜 f…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.analyticAt_weierstrassPExcept`：analyticAt_weierstrassPExcept 
(l₀ : Complex) : AnalyticAt Complex ℘[L - l₀] l₀
· 使用引理 `PeriodPair.hasFPowerSeriesAt_weierstrassPExcept`：hasFPowerSeriesAt_weier
strassPExcept (l : Complex) : HasFPowerSeriesAt ℘[L - l] (.ofScalars (𝕜
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 80 条，此处仅展示前 30 条）
-/
lemma iteratedDeriv_weierstrassPExcept_self (l : ℂ) {n : ℕ} :
    iteratedDeriv n ℘[L - l] l =
      if n = 0 then ℘[L - l] l else (n + 1)! * L.sumInvPow l (n + 2) := by
  rw [← div_mul_cancel₀ (a := iteratedDeriv _ _ _) (b := ↑n !) (by simp),
    ← eq_div_iff_mul_eq (by simp)]
  trans if n = 0 then ℘[L - l] l else (n + 1) * L.sumInvPow l (n + 2)
  · simpa using congr($((L.analyticAt_weierstrassPExcept l).hasFPowerSeriesAt
      |>.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_weierstrassPExcept l)).coeff n)
  · cases n <;> simp [Nat.factorial_succ]; field

end AnalyticWeierstrassPExcept

section AnalyticderivWeierstrassPExcept

/-- The power series expansion of `℘'[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_derivWeierstrassPExcept`. -/
/-
**PeriodPair.derivWeierstrassPExceptSeries** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair
`。
形式化陈述：derivWeierstrassPExceptSeries (l₀ x : Complex) : FormalMultilinearSeries C
omplex Complex Complex
参数：l₀ x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series expansion of `℘'[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_derivWeierstrassPExcept`.
-/
def derivWeierstrassPExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ (i + 1) * (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)
/-
**PeriodPair.hasFPowerSeriesOnBall_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位于
命名空间 `PeriodPair`。
形式化陈述：hasFPowerSeriesOnBall_derivWeierstrassPExcept (l₀ x : Complex) (r : NNReal
) (hr0 : 0 < r) (hr : Metric.closedBall x r subseteq (L.lattice \ {l₀})ᶜ) : HasF
PowerSeriesOnBall ℘'[L - l₀] (L.derivWeierstrassPExceptSeries l₀ x) x r
参数：l₀ x : Complex；r : NNReal；hr0 : 0 < r；hr : Metric.closedBall x r subseteq (L.
lattice \ {l₀})ᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesOnBall.congr`：HasFPowerSeriesOnBall.congr (hf : HasFPower
SeriesOnBall f p x r) (hg : EqOn f g (Metric.eball x r)) : HasFPowerSeriesOnBall
 g p x r
· 使用定理 `HasFPowerSeriesOnBall.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type v} […
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept`：hasFPowerSeriesOnBa
ll_weierstrassPExcept (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r) (hr : Metric.c
losedBall x r subseteq (L.lattice \ {l₀})…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 79 条，此处仅展示前 30 条）
-/
lemma hasFPowerSeriesOnBall_derivWeierstrassPExcept (l₀ x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘'[L - l₀] (L.derivWeierstrassPExceptSeries l₀ x) x r := by
  refine .congr ?_
    ((L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l₀).mono (.trans ?_ hr))
  · have := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x r hr0 hr).fderiv
    convert! (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall this
    ext n
    simp [weierstrassPExceptSeries, derivWeierstrassPExceptSeries]
    ring
  · simpa using Metric.ball_subset_closedBall
/-
**PeriodPair.hasFPowerSeriesAt_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间
 `PeriodPair`。
形式化陈述：hasFPowerSeriesAt_derivWeierstrassPExcept (l : Complex) : HasFPowerSeriesA
t ℘'[L - l] (.ofScalars Complex fun i => (i + 1) * (i + 2) * L.sumInvPow l (i + 
3)) l
参数：l : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用引理 `PeriodPair.compl_lattice_sdiff_singleton_mem_nhds`：compl_lattice_sdiff_s
ingleton_mem_nhds (x : Complex) : (↑L.lattice \ {x})ᶜ in 𝓝 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `PeriodPair.hasFPowerSeriesOnBall_derivWeierstrassPExcept`：hasFPowerSerie
sOnBall_derivWeierstrassPExcept (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r) (hr 
: Metric.closedBall x r subseteq (L.lattice \ …
-/
lemma hasFPowerSeriesAt_derivWeierstrassPExcept (l : ℂ) :
    HasFPowerSeriesAt ℘'[L - l]
      (.ofScalars ℂ fun i ↦ (i + 1) * (i + 2) * L.sumInvPow l (i + 3)) l := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  simpa [derivWeierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l l ⟨r, h₁.le⟩ h₁ h₂).hasFPowerSeriesAt
/-
**PeriodPair.analyticOnNhd_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `Pe
riodPair`。
形式化陈述：analyticOnNhd_derivWeierstrassPExcept (l₀ : Complex) : AnalyticOnNhd Compl
ex ℘'[L - l₀] (L.lattice \ {l₀})ᶜ
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.differentiableOn_derivWeierstrassPExcept`：differentiableOn_de
rivWeierstrassPExcept (l₀ : Complex) : DifferentiableOn Complex ℘'[L - l₀] (L.la
ttice \ {l₀})ᶜ
· 使用引理 `PeriodPair.isOpen_compl_lattice_sdiff`：isOpen_compl_lattice_sdiff {s : S
et Complex} : IsOpen (L.lattice \ s)ᶜ
-/
lemma analyticOnNhd_derivWeierstrassPExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ ℘'[L - l₀] (L.lattice \ {l₀})ᶜ :=
  (L.differentiableOn_derivWeierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]
/-
**PeriodPair.analyticAt_derivWeierstrassPExcept** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：analyticAt_derivWeierstrassPExcept (l₀ : Complex) : AnalyticAt Complex ℘'[
L - l₀] l₀
参数：l₀ : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PeriodPair.analyticOnNhd_derivWeierstrassPExcept`：analyticOnNhd_derivWei
erstrassPExcept (l₀ : Complex) : AnalyticOnNhd Complex ℘'[L - l₀] (L.lattice \ {
l₀})ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma analyticAt_derivWeierstrassPExcept (l₀ : ℂ) :
    AnalyticAt ℂ ℘'[L - l₀] l₀ :=
  L.analyticOnNhd_derivWeierstrassPExcept l₀ _ (by simp)
/-
**PeriodPair.iteratedDeriv_derivWeierstrassPExcept_self** 是 Mathlib 中的一个引理，位于命名空
间 `PeriodPair`。
形式化陈述：iteratedDeriv_derivWeierstrassPExcept_self (l : Complex) {n : Nat} : itera
tedDeriv n ℘'[L - l] l = (n + 2)! * L.sumInvPow l (n + 3)
参数：l : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`：HasFPowerSeriesAt.eq_forma
lMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} 
(h₁ : HasFPowerSeriesAt f p₁ x) (h…
· 使用引理 `AnalyticAt.hasFPowerSeriesAt`：AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [
NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (
h : AnalyticAt 𝕜 f…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.analyticAt_derivWeierstrassPExcept`：analyticAt_derivWeierstra
ssPExcept (l₀ : Complex) : AnalyticAt Complex ℘'[L - l₀] l₀
· 使用引理 `PeriodPair.hasFPowerSeriesAt_derivWeierstrassPExcept`：hasFPowerSeriesAt_
derivWeierstrassPExcept (l : Complex) : HasFPowerSeriesAt ℘'[L - l] (.ofScalars 
Complex fun i => (i + 1) * (i + 2) * L.sum…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma iteratedDeriv_derivWeierstrassPExcept_self (l : ℂ) {n : ℕ} :
    iteratedDeriv n ℘'[L - l] l = (n + 2)! * L.sumInvPow l (n + 3) := by
  have : iteratedDeriv n ℘'[L - l] l / n ! = (↑n + 1) * (↑n + 2) * L.sumInvPow l (n + 3) := by
    simpa using congr($((L.analyticAt_derivWeierstrassPExcept l).hasFPowerSeriesAt
      |>.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_derivWeierstrassPExcept l)).coeff n)
  simp [div_eq_iff, Nat.factorial_ne_zero, Nat.factorial_succ] at this ⊢
  grind

@[simp]
/-
**PeriodPair.deriv_derivWeierstrassPExcept_self** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：deriv_derivWeierstrassPExcept_self (l : Complex) : deriv ℘'[L - l] l = 6 *
 L.sumInvPow l 4
参数：l : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用引理 `PeriodPair.iteratedDeriv_derivWeierstrassPExcept_self`：iteratedDeriv_der
ivWeierstrassPExcept_self (l : Complex) {n : Nat} : iteratedDeriv n ℘'[L - l] l 
= (n + 2)! * L.sumInvPow l (n + 3)
-/
lemma deriv_derivWeierstrassPExcept_self (l : ℂ) :
    deriv ℘'[L - l] l = 6 * L.sumInvPow l 4 := by
  simpa using! L.iteratedDeriv_derivWeierstrassPExcept_self l (n := 1)
/-
**PeriodPair.analyticOnNhd_derivWeierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPa
ir`。
形式化陈述：analyticOnNhd_derivWeierstrassP : AnalyticOnNhd Complex ℘'[L] L.latticeᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.differentiableOn_derivWeierstrassP`：differentiableOn_derivWei
erstrassP : DifferentiableOn Complex ℘'[L] L.latticeᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `PeriodPair.isClosed_lattice`：isClosed_lattice : IsClosed (X
-/
lemma analyticOnNhd_derivWeierstrassP : AnalyticOnNhd ℂ ℘'[L] L.latticeᶜ :=
  L.differentiableOn_derivWeierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

end AnalyticderivWeierstrassPExcept

section Analytic

/-- In the power series expansion of `℘(z) = ∑ aᵢzⁱ` at some `x ∉ L`,
each `aᵢ` can be written as an infinite sum over `l ∈ L`.
This is the summand of this infinite sum. See `PeriodPair.coeff_weierstrassPSeries`. -/
/-
**PeriodPair.weierstrassPSummand** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPSummand (x : Complex) (i : Nat) (l : L.lattice) : Complex
参数：x : Complex；i : Nat；l : L.lattice。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the power series expansion of `℘(z) = ∑ aᵢzⁱ` at some `x ∉ L`,
each `aᵢ` can be written as an infinite sum over `l ∈ L`.
This is the summand of this infinite sum. See `PeriodPair.coeff_weierstrassPSeri
es`.
-/
def weierstrassPSummand (x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

/-- The power series expansion of `℘` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassP`. -/
/-
**PeriodPair.weierstrassPSeries** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPSeries (x : Complex) : FormalMultilinearSeries Complex Complex
 Complex
参数：x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series expansion of `℘` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassP`.
-/
def weierstrassPSeries (x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars _ fun i ↦ if i = 0 then (℘[L] x) else (i + 1) * L.sumInvPow x (i + 2)
/-
**PeriodPair.weierstrassPExceptSeries_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：weierstrassPExceptSeries_of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) :
 L.weierstrassPExceptSeries l₀ = L.weierstrassPSeries
参数：l₀ : Complex；hl₀ : l₀ ∉ L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PeriodPair.weierstrassPExcept_of_notMem`：weierstrassPExcept_of_notMem (l
₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - l₀] = ℘[L]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weierstrassPExceptSeries_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSeries l₀ = L.weierstrassPSeries := by
  delta weierstrassPSeries weierstrassPExceptSeries
  congr! with z i f
  · rw [L.weierstrassPExcept_of_notMem _ hl₀]
  · simp [hl₀]
/-
**PeriodPair.weierstrassPExceptSummand_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Peri
odPair`。
形式化陈述：weierstrassPExceptSummand_of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) 
: L.weierstrassPExceptSummand l₀ = L.weierstrassPSummand
参数：l₀ : Complex；hl₀ : l₀ ∉ L.lattice。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weierstrassPExceptSummand_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSummand l₀ = L.weierstrassPSummand := by
  grind [weierstrassPSummand, weierstrassPExceptSummand]
/-
**PeriodPair.coeff_weierstrassPSeries** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：coeff_weierstrassPSeries (x : Complex) (i : Nat) : (L.weierstrassPSeries x
).coeff i = ∑' l : L.lattice, L.weierstrassPSummand x i l
参数：x : Complex；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExceptSeries_of_notMem`：weierstrassPExceptSeries_
of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) : L.weierstrassPExceptSeries l₀ 
= L.weierstrassPSeries
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用引理 `PeriodPair.coeff_weierstrassPExceptSeries`：coeff_weierstrassPExceptSerie
s (l₀ x : Complex) (i : Nat) : (L.weierstrassPExceptSeries l₀ x).coeff i = ∑' l 
: L.lattice, L.weierstrassPExce…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PeriodPair.weierstrassPExceptSummand_of_notMem`：weierstrassPExceptSumman
d_of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) : L.weierstrassPExceptSummand 
l₀ = L.weierstrassPSummand
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_weierstrassPSeries (x : ℂ) (i : ℕ) :
    (L.weierstrassPSeries x).coeff i = ∑' l : L.lattice, L.weierstrassPSummand x i l := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.coeff_weierstrassPExceptSeries,
    ← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]
/-
**PeriodPair.summable_weierstrassPSummand** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`
。
形式化陈述：summable_weierstrassPSummand (z x : Complex) (hx : forall l : L.lattice, ‖
z - x‖ < ‖l - x‖) : Summable (Function.uncurry fun b c => L.weierstrassPSummand 
x b c * (z - x) ^ b)
参数：z x : Complex；hx : forall l : L.lattice, ‖z - x‖ < ‖l - x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExceptSummand_of_notMem`：weierstrassPExceptSumman
d_of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) : L.weierstrassPExceptSummand 
l₀ = L.weierstrassPSummand
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用引理 `PeriodPair.summable_weierstrassPExceptSummand`：summable_weierstrassPExce
ptSummand (l₀ z x : Complex) (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < 
‖l - x‖) : Summable (Function.uncur…
-/
lemma summable_weierstrassPSummand (z x : ℂ)
    (hx : ∀ l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.weierstrassPSummand x b c * (z - x) ^ b) := by
  simp_rw [← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]
  refine L.summable_weierstrassPExceptSummand _ z x fun l hl ↦ hx l
/-
**PeriodPair.weierstrassPSeries_hasSum** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：weierstrassPSeries_hasSum (z x : Complex) (hx : forall l : L.lattice, ‖z -
 x‖ < ‖l - x‖) : HasSum (fun i => (L.weierstrassPSeries x).coeff i * (z - x) ^ i
) (℘[L] z)
参数：z x : Complex；hx : forall l : L.lattice, ‖z - x‖ < ‖l - x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExceptSeries_of_notMem`：weierstrassPExceptSeries_
of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) : L.weierstrassPExceptSeries l₀ 
= L.weierstrassPSeries
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用引理 `PeriodPair.weierstrassPExcept_of_notMem`：weierstrassPExcept_of_notMem (l
₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - l₀] = ℘[L]
· 使用引理 `PeriodPair.weierstrassPExceptSeries_hasSum`：weierstrassPExceptSeries_has
Sum (l₀ z x : Complex) (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x
‖) : HasSum (fun i => (L.weierst…
-/
lemma weierstrassPSeries_hasSum (z x : ℂ) (hx : ∀ l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i ↦ (L.weierstrassPSeries x).coeff i * (z - x) ^ i) (℘[L] z) := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.weierstrassPExceptSeries_hasSum _ z x fun l hl ↦ hx l
/-
**PeriodPair.hasFPowerSeriesOnBall_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：hasFPowerSeriesOnBall_weierstrassP (x : Complex) (r : NNReal) (hr0 : 0 < r
) (hr : Metric.closedBall x r subseteq L.latticeᶜ) : HasFPowerSeriesOnBall ℘[L] 
(L.weierstrassPSeries x) x r
参数：x : Complex；r : NNReal；hr0 : 0 < r；hr : Metric.closedBall x r subseteq L.latt
iceᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PeriodPair.weierstrassPExceptSeries_of_notMem`：weierstrassPExceptSeries_
of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) : L.weierstrassPExceptSeries l₀ 
= L.weierstrassPSeries
· 使用引理 `PeriodPair.ω₁_div_two_notMem_lattice`：ω₁_div_two_notMem_lattice : L.ω₁ /
 2 ∉ L.lattice
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `PeriodPair.weierstrassPExcept_of_notMem`：weierstrassPExcept_of_notMem (l
₀ : Complex) (hl : l₀ ∉ L.lattice) : ℘[L - l₀] = ℘[L]
· 使用引理 `PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept`：hasFPowerSeriesOnBa
ll_weierstrassPExcept (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r) (hr : Metric.c
losedBall x r subseteq (L.lattice \ {l₀})…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma hasFPowerSeriesOnBall_weierstrassP (x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ L.latticeᶜ) :
    HasFPowerSeriesOnBall ℘[L] (L.weierstrassPSeries x) x r := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.hasFPowerSeriesOnBall_weierstrassPExcept _ x r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.sdiff_subset))
/-
**PeriodPair.analyticOnNhd_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：analyticOnNhd_weierstrassP : AnalyticOnNhd Complex ℘[L] L.latticeᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.differentiableOn_weierstrassP`：differentiableOn_weierstrassP 
: DifferentiableOn Complex ℘[L] L.latticeᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `PeriodPair.isClosed_lattice`：isClosed_lattice : IsClosed (X
-/
lemma analyticOnNhd_weierstrassP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ :=
  L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl
/-
**PeriodPair.ite_eq_one_sub_sq_mul_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
形式化陈述：ite_eq_one_sub_sq_mul_weierstrassP (l₀ : Complex) (hl₀ : l₀ in L.lattice) 
(z : Complex) : (if z = l₀ then 1 else (z - l₀) ^ 2 * ℘[L] z) = (z - l₀) ^ 2 * ℘
[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2
参数：l₀ : Complex；hl₀ : l₀ in L.lattice；z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ite_eq_one_sub_sq_mul_weierstrassP (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (z : ℂ) :
    (if z = l₀ then 1 else (z - l₀) ^ 2 * ℘[L] z) =
      (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2 := by
  grind [L.weierstrassPExcept_add ⟨_, hl₀⟩]

@[fun_prop]
/-
**PeriodPair.meromorphic_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：meromorphic_weierstrassP : Meromorphic ℘[L]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PeriodPair.weierstrassPExcept_add`：weierstrassPExcept_add (l₀ : L.lattic
e) (z : Complex) : ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `PeriodPair.analyticOnNhd_weierstrassPExcept`：analyticOnNhd_weierstrassPE
xcept (l₀ : Complex) : AnalyticOnNhd Complex ℘[L - l₀] (L.lattice \ {l₀})ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeromorphicAt.fun_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用定理 `MeromorphicAt.fun_div`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgeb
ra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `MeromorphicAt.fun_pow`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgeb
ra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `PeriodPair.analyticOnNhd_weierstrassP`：analyticOnNhd_weierstrassP : Anal
yticOnNhd Complex ℘[L] L.latticeᶜ
-/
lemma meromorphic_weierstrassP : Meromorphic ℘[L] := by
  intro x
  by_cases hx : x ∈ L.lattice
  · simp_rw [← funext <| L.weierstrassPExcept_add ⟨x, hx⟩]
    have := (analyticOnNhd_weierstrassPExcept L x x (by simp)).meromorphicAt
    fun_prop
  · exact (L.analyticOnNhd_weierstrassP x hx).meromorphicAt

@[fun_prop]
/-
**PeriodPair.meromorphic_derivWeierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair
`。
形式化陈述：meromorphic_derivWeierstrassP : Meromorphic ℘'[L]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PeriodPair.deriv_weierstrassP`：∀ (L : PeriodPair), deriv L.weierstrassP 
= L.derivWeierstrassP
· 使用定理 `Meromorphic.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 
𝕜 → E} …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `PeriodPair.meromorphic_weierstrassP`：meromorphic_weierstrassP : Meromorp
hic ℘[L]
-/
lemma meromorphic_derivWeierstrassP : Meromorphic ℘'[L] := by
  rw [← deriv_weierstrassP]
  fun_prop
/-
**PeriodPair.order_weierstrassP** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：order_weierstrassP (l₀ : Complex) (h : l₀ in L.lattice) : meromorphicOrder
At ℘[L] l₀ = -2
参数：l₀ : Complex；h : l₀ in L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `PeriodPair.meromorphic_weierstrassP`：meromorphic_weierstrassP : Meromorp
hic ℘[L]
· 使用引理 `PeriodPair.analyticOnNhd_weierstrassPExcept`：analyticOnNhd_weierstrassPE
xcept (l₀ : Complex) : AnalyticOnNhd Complex ℘[L - l₀] (L.lattice \ {l₀})ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `AnalyticAt.div_const`：AnalyticAt.div_const {f : E -> 𝕝} (hf : AnalyticAt
 𝕜 f x) {c : 𝕝} : AnalyticAt 𝕜 (f · / c) x
· 使用定理 `AnalyticAt.fun_pow`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `AnalyticAt.fun_add`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `AnalyticAt.fun_mul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用引理 `PeriodPair.analyticAt_weierstrassPExcept`：analyticAt_weierstrassPExcept 
(l₀ : Complex) : AnalyticAt Complex ℘[L - l₀] l₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
（共 42 条，此处仅展示前 30 条）
-/
lemma order_weierstrassP (l₀ : ℂ) (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt ℘[L] l₀ = -2 := by
  trans ↑(-2 : ℤ)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_weierstrassP l₀)]
    refine ⟨fun z ↦ (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · have : AnalyticAt ℂ ℘[L - l₀] l₀ := L.analyticOnNhd_weierstrassPExcept l₀ l₀ (by simp)
      suffices AnalyticAt ℂ (fun z ↦ (z - l₀) ^ 2 / l₀ ^ 2) l₀ by fun_prop
      by_cases hl₀ : l₀ = 0
      · simpa [hl₀] using analyticAt_const
      · fun_prop (disch := simpa)
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z (hz : _ ≠ _)
      have : (z - l₀) ^ 2 ≠ 0 := by simpa [sub_eq_zero]
      simp [← L.ite_eq_one_sub_sq_mul_weierstrassP l₀ h,
        if_neg hz, inv_mul_cancel_left₀ this, zpow_ofNat]
  · norm_num

end Analytic

section Relation

/-- The Eisenstein series as a function on lattices.
It takes `L` to the sum `∑ l⁻ʳ` over `l ∈ L`.
TODO: Establish connections with the `ModularForm` library. -/
/-
**PeriodPair.G** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
形式化陈述：G (n : Nat) : Complex
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Eisenstein series as a function on lattices.
It takes `L` to the sum `∑ l⁻ʳ` over `l ∈ L`.
TODO: Establish connections with the `ModularForm` library.
-/
def G (n : ℕ) : ℂ := ∑' l : L.lattice, (l ^ n)⁻¹

@[simp]
/-
**PeriodPair.sumInvPow_zero** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：sumInvPow_zero : L.sumInvPow 0 = L.G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumInvPow_zero : L.sumInvPow 0 = L.G := by
  ext; simp [sumInvPow, G]
/-
**PeriodPair.G_eq_zero_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：G_eq_zero_of_odd (n : Nat) (hn : Odd n) : L.G n = 0
参数：n : Nat；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharZero.eq_neg_self_iff`：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZe
roDivisors R] [CharZero R] {a : R}, a = -a ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `PeriodPair.G.eq_1`：∀ (L : PeriodPair) (n : ℕ), L.G n = ∑' (l : ↥L.lattic
e), (↑l ^ n)⁻¹
· 使用定理 `tsum_neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [inst 
: AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma G_eq_zero_of_odd (n : ℕ) (hn : Odd n) : L.G n = 0 := by
  rw [← CharZero.eq_neg_self_iff, G, ← tsum_neg, ← (Equiv.neg _).tsum_eq]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_inv, hn.neg_pow]

/-- The lattice invariant `g₂ := 60 G₄`. -/
/-
**PeriodPair.g** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lattice invariant `g₂ := 60 G₄`.
-/
def g₂ : ℂ := 60 * L.G 4

/-- The lattice invariant `g₃ := 140 G₆`. -/
/-
**PeriodPair.g** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lattice invariant `g₃ := 140 G₆`.
-/
def g₃ : ℂ := 140 * L.G 6

/-- (Implementation detail) The relation that `℘'` and `℘` satisfies.
We will show that this is constant zero. See `PeriodPair.relation_eq_zero` -/
/-
**PeriodPair.relation** 是 Mathlib 中的一个定义，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail) The relation that `℘'` and `℘` satisfies.
We will show that this is constant zero. See `PeriodPair.relation_eq_zero`
-/
private def relation (z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice then 0 else ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃

@[local fun_prop]
/-
**PeriodPair.meromorphic_relation** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma meromorphic_relation : Meromorphic L.relation := by
  have : Meromorphic fun z ↦ ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ := by fun_prop
  refine fun z ↦ (this _).congr ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds _)] with w hw hw'
  rw [relation, if_neg (by simp_all)]
/-
**PeriodPair.relation_mul_id_pow_six_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 `Per
iodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relation_mul_id_pow_six_eventuallyEq :
    (L.relation * id ^ 6) =ᶠ[nhds 0] fun z ↦
      (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2 - 4 *
      (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3 + L.g₂ *
      (℘[L - (0 : ℂ)] z * z ^ 6 + z ^ 4) + L.g₃ * z ^ 6 := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds _] with z hz
  by_cases hz0 : z = 0
  · simp [hz0, relation]; norm_num
  replace hz : z ∉ L.lattice := by simp_all
  simp only [Pi.mul_apply, Pi.pow_apply, relation, ↓reduceIte, hz,
    ← ZeroMemClass.coe_zero L.lattice, L.derivWeierstrassPExcept_def, L.weierstrassPExcept_def]
  simp
  field

@[local fun_prop]
/-
**PeriodPair.analyticAt_relation_mul_id_pow_six** 是 Mathlib 中的一个引理，位于命名空间 `Perio
dPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma analyticAt_relation_mul_id_pow_six :
    AnalyticAt ℂ (L.relation * id ^ 6) 0 := by
  refine .congr ?_ L.relation_mul_id_pow_six_eventuallyEq.symm
  fun_prop

@[local simp]
/-
**PeriodPair.relation_neg** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relation_neg (x) : L.relation (-x) = L.relation x := by
  classical simp [relation]

attribute [local fun_prop] AnalyticAt.contDiffAt in
/-
**PeriodPair.iteratedDeriv_six_relation_mul_id_pow_six** 是 Mathlib 中的一个引理，位于命名空间
 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iteratedDeriv_six_relation_mul_id_pow_six :
    iteratedDeriv 6 (L.relation * id ^ 6) 0 = 0 := by
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_weierstrassPExcept_self]
  simp [Finset.sum_range_succ, L.G_eq_zero_of_odd 3 (by decide), g₃,
    show Nat.choose 6 4 = 15 by rfl, show Nat.choose 6 3 = 20 by rfl]
  ring

attribute [local fun_prop] AnalyticAt.contDiffAt in
/-
**PeriodPair.analyticAt_relation_zero** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma analyticAt_relation_zero : AnalyticAt ℂ L.relation 0 := by
  refine .of_meromorphicOrderAt_pos (one_pos.trans_le ?_) (by simp [relation])
  suffices 7 ≤ meromorphicOrderAt (L.relation * id ^ 6) 0 by
    rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
      meromorphicOrderAt_pow (by fun_prop)] at this
    rw [← WithTop.add_le_add_iff_right (z := 6) (by simp)]
    simpa [-add_le_add_iff_left_of_ne_top] using! this
  rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop)]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi₁ ↦ ?_)
  by_cases hi₂ : Odd i
  · simpa [← CharZero.eq_neg_self_iff, hi₂, (show Even 6 by decide).neg_pow] using!
      (iteratedDeriv_comp_neg i (L.relation * id ^ 6) 0 :)
  by_cases hi₃ : i = 0
  · simp [hi₃]
  by_cases hi₄ : i = 6
  · exact hi₄ ▸ L.iteratedDeriv_six_relation_mul_id_pow_six
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_weierstrassPExcept_self]
  obtain rfl | rfl : i = 2 ∨ i = 4 := by grind
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ, show Nat.choose 4 2 = 6 by rfl, g₂]; ring

@[local simp]
/-
**PeriodPair.relation_add_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relation_add_coe (x : ℂ) (l : L.lattice) :
    L.relation (x + l) = L.relation x := by
  simp only [relation, derivWeierstrassP_add_coe, weierstrassP_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[local simp]
/-
**PeriodPair.relation_sub_coe** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relation_sub_coe (x : ℂ) (l : L.lattice) :
    L.relation (x - l) = L.relation x := by
  rw [← L.relation_add_coe _ l, sub_add_cancel]
/-
**PeriodPair.analyticAt_relation** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma analyticAt_relation (x : ℂ) : AnalyticAt ℂ L.relation x := by
  by_cases hx : x ∈ L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation_zero
    rw [← sub_self x.1] at this
    convert! this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt ℂ (fun z ↦ ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃) x := by
      have := L.analyticOnNhd_derivWeierstrassP _ hx
      have := L.analyticOnNhd_weierstrassP _ hx
      fun_prop
    apply this.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with x hx
    simp_all [relation]
/-
**PeriodPair.relation_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relation_eq_zero : L.relation = 0 := by
  ext x
  have : Differentiable ℂ L.relation := fun x ↦ (L.analyticAt_relation x).differentiableAt
  exact (this.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
    this.continuous fun z w hw ↦ by lift w to L.lattice using hw; simp).isBounded x 0).trans
    (if_pos (by simp))

/-- `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃` -/
/-
**PeriodPair.derivWeierstrassP_sq** 是 Mathlib 中的一个引理，位于命名空间 `PeriodPair`。
形式化陈述：derivWeierstrassP_sq (z : Complex) (hz : z ∉ L.lattice) : ℘'[L] z ^ 2 = 4 
* ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃
参数：z : Complex；hz : z ∉ L.lattice。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.0.Period
Pair.relation_eq_zero`：∀ (L : PeriodPair), PeriodPair.relation✝ L = 0

--- 原说明 ---
`℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`
-/
lemma derivWeierstrassP_sq (z : ℂ) (hz : z ∉ L.lattice) :
    ℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃ := by
  simpa [sub_eq_zero, relation, hz, sub_add] using congr($L.relation_eq_zero z)

end Relation

end PeriodPair

