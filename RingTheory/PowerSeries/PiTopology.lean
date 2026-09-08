/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Product topology on power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `PowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficients maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped PowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2][bourbaki1981].

It corresponds with the adic topology but this is not proved here.

- `PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `PowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `PowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `PowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `PowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `PowerSeries σ R`.
- If `R` is complete, then so is `PowerSeries σ R`.

-/

public section


namespace PowerSeries

open Filter Function
open scoped  MvPowerSeries.WithPiTopology

variable (R : Type*)

section Topological

variable [TopologicalSpace R]

namespace WithPiTopology

open scoped Topology

/-!
The instances defined in this file are copies of instances on `MvPowerSeries`.
Those instances are scoped in `MvPowerSeries.WithPiTopology`,
while these are scoped in `PowerSeries.WithPiTopology`.
It would probably be better to remove these instances, and use one shared scope.
-/

/-- The pointwise topology on `PowerSeries` -/
/-
**PowerSeries.WithPiTopology.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries.WithPiTopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise topology on `PowerSeries`
-/
scoped instance : TopologicalSpace (PowerSeries R) :=
  inferInstance

/-- Separation of the topology on `PowerSeries` -/
@[scoped instance]
/-
**PowerSeries.WithPiTopology.instT0Space** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.
WithPiTopology`。
形式化陈述：instT0Space [T0Space R] : T0Space (PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instT0Space`：instT0Space [T0Space R] : T0Sp
ace (MvPowerSeries σ R)

--- 原说明 ---
Separation of the topology on `PowerSeries`
-/
theorem instT0Space [T0Space R] : T0Space (PowerSeries R) :=
  inferInstance

/-- `PowerSeries` on a `T2Space` form a `T2Space` -/
@[scoped instance]
/-
**PowerSeries.WithPiTopology.instT2Space** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.
WithPiTopology`。
形式化陈述：instT2Space [T2Space R] : T2Space (PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)

--- 原说明 ---
`PowerSeries` on a `T2Space` form a `T2Space`
-/
theorem instT2Space [T2Space R] : T2Space (PowerSeries R) :=
  inferInstance

/-- Coefficients are continuous -/
/-
**PowerSeries.WithPiTopology.continuous_coeff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.WithPiTopology`。
形式化陈述：continuous_coeff [Semiring R] (d : Nat) : Continuous (PowerSeries.coeff (R
参数：d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
Coefficients are continuous
-/
theorem continuous_coeff [Semiring R] (d : ℕ) : Continuous (PowerSeries.coeff (R := R) d) :=
  continuous_pi_iff.mp continuous_id (Finsupp.single () d)

/-- The constant coefficient is continuous -/
/-
**PowerSeries.WithPiTopology.continuous_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 
`PowerSeries.WithPiTopology`。
形式化陈述：continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.WithPiTopology.continuous_coeff`：continuous_coeff [Semiring 
R] (d : Nat) : Continuous (PowerSeries.coeff (R
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R

--- 原说明 ---
The constant coefficient is continuous
-/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (R := R)) :=
  coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0

/-- A family of power series converges iff it converges coefficientwise -/
/-
**PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto** 是 Mathlib 中的一个定理，位于命名空间
 `PowerSeries.WithPiTopology`。
形式化陈述：tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*} (f : ι -> PowerSeries R
) (u : Filter ι) (g : PowerSeries R) : Tendsto f u (nhds g) ↔ forall d : Nat, Te
ndsto (fun i => coeff d (f i)) u (nhds (coeff d g))
参数：f : ι -> PowerSeries R；u : Filter ι；g : PowerSeries R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coef
f_tendsto [Semiring R] {ι : Type*} (f : ι -> MvPowerSeries σ R) (u : Filter ι) (
g : MvPowerSeries σ R) : Tendsto f u (nhds g…
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.uniqueLinearEquiv_apply`：∀ (R : Type u_1) {α : Type u_3} (M : Ty
pe u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.Module
 R M] [inst_3 : Subsi…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A family of power series converges iff it converges coefficientwise
-/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → PowerSeries R) (u : Filter ι) (g : PowerSeries R) :
    Tendsto f u (nhds g) ↔
    ∀ d : ℕ, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g)) := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.uniqueLinearEquiv ℕ ℕ ()).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.uniqueLinearEquiv_apply, coeff]
  apply iff_of_eq
  congr
  · ext _; congr; ext; simp
  · ext; simp
/-
**PowerSeries.WithPiTopology.tendsto_trunc_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries.WithPiTopology`。
形式化陈述：tendsto_trunc_atTop [CommSemiring R] (f : R⟦X⟧) : Tendsto (fun d => (trunc
 d f : R⟦X⟧)) atTop (𝓝 f)
参数：f : R⟦X⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coeff_
tendsto [Semiring R] {ι : Type*} (f : ι -> PowerSeries R) (u : Filter ι) (g : Po
werSeries R) : Tendsto f u (nhds g) ↔ fora…
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tendsto_trunc_atTop [CommSemiring R] (f : R⟦X⟧) :
    Tendsto (fun d ↦ (trunc d f : R⟦X⟧)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d < n) ↦ (by simp [coeff_trunc, hdn])

/-- The inclusion of polynomials into power series has dense image -/
/-
**PowerSeries.WithPiTopology.denseRange_toPowerSeries** 是 Mathlib 中的一个定理，位于命名空间 
`PowerSeries.WithPiTopology`。
形式化陈述：denseRange_toPowerSeries [CommSemiring R] : DenseRange (Polynomial.toPower
Series (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `PowerSeries.WithPiTopology.tendsto_trunc_atTop`：tendsto_trunc_atTop [Com
mSemiring R] (f : R⟦X⟧) : Tendsto (fun d => (trunc d f : R⟦X⟧)) atTop (𝓝 f)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The inclusion of polynomials into power series has dense image
-/
theorem denseRange_toPowerSeries [CommSemiring R] :
    DenseRange (Polynomial.toPowerSeries (R := R)) := fun f =>
  mem_closure_of_tendsto (tendsto_trunc_atTop R f) <| .of_forall fun _ ↦ Set.mem_range_self _

/-- The semiring topology on `PowerSeries` of a topological semiring -/
@[scoped instance]
/-
**PowerSeries.WithPiTopology.instIsTopologicalSemiring** 是 Mathlib 中的一个定理，位于命名空间
 `PowerSeries.WithPiTopology`。
形式化陈述：instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] : IsTopol
ogicalSemiring (PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalSemiring`：instIsTopologica
lSemiring [Semiring R] [IsTopologicalSemiring R] : IsTopologicalSemiring (MvPowe
rSeries σ R) where continuous_add

--- 原说明 ---
The semiring topology on `PowerSeries` of a topological semiring
-/
theorem instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (PowerSeries R) :=
  inferInstance

/-- The ring topology on `PowerSeries` of a topological ring -/
@[scoped instance]
/-
**PowerSeries.WithPiTopology.instIsTopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 `Po
werSeries.WithPiTopology`。
形式化陈述：instIsTopologicalRing [Ring R] [IsTopologicalRing R] : IsTopologicalRing (
PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)

--- 原说明 ---
The ring topology on `PowerSeries` of a topological ring
-/
theorem instIsTopologicalRing [Ring R] [IsTopologicalRing R] :
    IsTopologicalRing (PowerSeries R) :=
  inferInstance

section Sum
variable [Semiring R] {ι : Type*} {f : ι → R⟦X⟧}

/-
**PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.WithPiTopology`。
形式化陈述：hasSum_iff_hasSum_coeff {g : R⟦X⟧} : HasSum f g ↔ forall d, HasSum (fun i 
=> coeff d (f i)) (coeff d g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coeff_
tendsto [Semiring R] {ι : Type*} (f : ι -> PowerSeries R) (u : Filter ι) (g : Po
werSeries R) : Tendsto f u (nhds g) ↔ fora…
-/
theorem hasSum_iff_hasSum_coeff {g : R⟦X⟧} :
    HasSum f g ↔ ∀ d, HasSum (fun i ↦ coeff d (f i)) (coeff d g) := by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto
/-
**PowerSeries.WithPiTopology.summable_iff_summable_coeff** 是 Mathlib 中的一个定理，位于命名
空间 `PowerSeries.WithPiTopology`。
形式化陈述：summable_iff_summable_coeff : Summable f ↔ forall d : Nat, Summable (fun i
 => coeff d (f i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem summable_iff_summable_coeff :
    Summable f ↔ ∀ d : ℕ, Summable (fun i ↦ coeff d (f i)) := by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨mk a, by simpa using h⟩

/-- A family of `PowerSeries` is summable if their order tends to infinity. -/
/-
**PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top** 是 Mathli
b 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：summable_of_tendsto_order_atTop_nhds_top [LinearOrder ι] [LocallyFiniteOrd
erBot ι] (h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)) : Summable f
参数：h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `summable_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [IsEmpty β]
, Su…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.WithPiTopology.summable_iff_summable_coeff`：summable_iff_sum
mable_coeff : Summable f ↔ forall d : Nat, Summable (fun i => coeff d (f i))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `summable_of_hasFiniteSupport`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [L.HasSupport],…
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_Iic`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iic a).Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A family of `PowerSeries` is summable if their order tends to infinity.
-/
theorem summable_of_tendsto_order_atTop_nhds_top [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable f := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  intro n
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  refine summable_of_hasFiniteSupport <| (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
  exact coeff_of_lt_order _ <| by simpa using (hi k hk.le)

variable {R} in
/-- The geometric series converges if the constant term is zero. -/
/-
**PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero** 是 Mathlib 中
的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：summable_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantC
oeff = 0) : Summable (f ^ ·)
参数：h : f.constantCoeff = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero`：summ
able_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R} (h : f.constantCoeff =
 0) : Summable (f ^ ·)

--- 原说明 ---
The geometric series converges if the constant term is zero.
-/
theorem summable_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantCoeff = 0) :
    Summable (f ^ ·) :=
  MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero h

section GeomSeries
variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
variable {f : PowerSeries R}

/-- Formula for geometric series. -/
/-
**PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero** 是 M
athlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) : 
(∑' (i : Nat), f ^ i) * (1 - f) = 1
参数：h : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_pow_mul_one_sub`：Summable.tsum_pow_mul_one_sub {x : α} (h 
: Summable (x ^ ·)) : (∑' (i : Nat), x ^ i) * (1 - x) = 1
· 使用定理 `PowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRing 
[Ring R] [IsTopologicalRing R] : IsTopologicalRing (PowerSeries R)
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero`：summab
le_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantCoeff = 0) : 
Summable (f ^ ·)

--- 原说明 ---
Formula for geometric series.
-/
theorem tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (∑' (i : ℕ), f ^ i) * (1 - f) = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).tsum_pow_mul_one_sub

/-- Formula for geometric series. -/
/-
**PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero** 是 M
athlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) : 
(1 - f) * ∑' (i : Nat), f ^ i = 1
参数：h : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.one_sub_mul_tsum_pow`：Summable.one_sub_mul_tsum_pow {x : α} (h 
: Summable (x ^ ·)) : (1 - x) * ∑' (i : Nat), x ^ i = 1
· 使用定理 `PowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRing 
[Ring R] [IsTopologicalRing R] : IsTopologicalRing (PowerSeries R)
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero`：summab
le_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantCoeff = 0) : 
Summable (f ^ ·)

--- 原说明 ---
Formula for geometric series.
-/
theorem one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (1 - f) * ∑' (i : ℕ), f ^ i = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).one_sub_mul_tsum_pow

end GeomSeries

end Sum

section Prod
variable [CommSemiring R] {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {f : ι → R⟦X⟧}

/-- If the order of a family of `PowerSeries` tends to infinity, the collection of all
possible products over `Finset` is summable. -/
/-
**PowerSeries.WithPiTopology.summable_prod_of_tendsto_order_atTop_nhds_top** 是 M
athlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：summable_prod_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i => (f i)
.order) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i)
参数：h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Summable.of_finite`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [Finite β] [L.HasSu
pport] {…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.WithPiTopology.summable_iff_summable_coeff`：summable_iff_sum
mable_coeff : Summable f ↔ forall d : Nat, Summable (fun i => coeff d (f i))
· 使用定理 `summable_of_hasFiniteSupport`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [L.HasSupport],…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If the order of a family of `PowerSeries` tends to infinity, the collection of a
ll
possible products over `Finset` is summable.
-/
theorem summable_prod_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable (∏ i ∈ ·, f i) := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine (summable_iff_summable_coeff _).mpr fun n ↦ summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices ∀ s : Finset ι, coeff n (∏ i ∈ s, f i) ≠ 0 → ↑s ⊆ Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio, not_lt] at hxi
  refine coeff_of_lt_order _ <| (hi x hxi).trans_le <| le_trans ?_ (le_order_prod _ _)
  apply Finset.single_le_sum (by simp) hxs

/-- A family of `PowerSeries` in the form `1 + f i` is multipliable if the order of `f i` tends to
infinity. -/
/-
**PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_to
p** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：multipliable_one_add_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i =
> (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·)
参数：h : Tendsto (fun i => (f i).order) atTop (nhds ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multipliable_one_add_of_summable_prod`：multipliable_one_add_of_summable_
prod (h : Summable (∏ i in ·, f i)) : Multipliable (1 + f ·)
· 使用定理 `PowerSeries.WithPiTopology.summable_prod_of_tendsto_order_atTop_nhds_top
`：summable_prod_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i => (f i).ord
er) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i)

--- 原说明 ---
A family of `PowerSeries` in the form `1 + f i` is multipliable if the order of 
`f i` tends to
infinity.
-/
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
  multipliable_one_add_of_summable_prod <| summable_prod_of_tendsto_order_atTop_nhds_top _ h

end Prod

section ProdOneSubPow
variable (R : Type*) [CommRing R] [TopologicalSpace R]

/-
**PowerSeries.WithPiTopology.multipliable_one_sub_X_pow** 是 Mathlib 中的一个定理，位于命名空
间 `PowerSeries.WithPiTopology`。
形式化陈述：multipliable_one_sub_X_pow : Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_n
hds_top`：multipliable_one_add_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun 
i => (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.tendsto_nhds_top_iff_natCast_lt`：tendsto_nhds_top_iff_natCast_lt {α
 : Type*} {l : Filter α} {f : α -> Nat∞} : Tendsto f l (𝓝 ⊤) ↔ forall n : Nat, f
orallᶠ a in l, n < f a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `PowerSeries.order_neg`：order_neg {R : Type*} [Ring R] (φ : PowerSeries R
) : (-φ).order = φ.order
· 使用定理 `PowerSeries.order_X_pow`：order_X_pow (n : Nat) : order ((X : R⟦X⟧) ^ n) 
= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
-/
theorem multipliable_one_sub_X_pow : Multipliable fun n ↦ (1 : R⟦X⟧) - X ^ (n + 1) := by
  nontriviality R
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [order_neg, order_X_pow]
  norm_cast
  exact Nat.lt_add_one_iff.mpr hm
/-
**PowerSeries.WithPiTopology.tprod_one_sub_X_pow_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `PowerSeries.WithPiTopology`。
形式化陈述：tprod_one_sub_X_pow_ne_zero [T2Space R] [Nontrivial R] : ∏' i, (1 - X ^ (i
 + 1)) != (0 : R⟦X⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Multipliable.map_tprod`：Multipliable.map_tprod [L.NeBot] [CommMonoid γ] 
[TopologicalSpace γ] [T2Space γ] (hf : Multipliable f L) {G} [FunLike G α γ] [Mo
noidHomClass…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`：multipliable_one_
sub_X_pow : Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PowerSeries.WithPiTopology.continuous_constantCoeff`：continuous_constant
Coeff [Semiring R] : Continuous (constantCoeff (R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
-/
theorem tprod_one_sub_X_pow_ne_zero [T2Space R] [Nontrivial R] :
    ∏' i, (1 - X ^ (i + 1)) ≠ (0 : R⟦X⟧) := by
  by_contra! h
  obtain h := PowerSeries.ext_iff.mp h 0
  simp [coeff_zero_eq_constantCoeff, (multipliable_one_sub_X_pow R).map_tprod _
    (continuous_constantCoeff R)] at h

end ProdOneSubPow

end WithPiTopology

end Topological

section Uniform

namespace WithPiTopology

variable [UniformSpace R]

/-- The product uniformity on `PowerSeries` -/
/-
**PowerSeries.WithPiTopology.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries.WithPiTopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product uniformity on `PowerSeries`
-/
scoped instance : UniformSpace (PowerSeries R) :=
  inferInstance

/-- Coefficients are uniformly continuous -/
/-
**PowerSeries.WithPiTopology.uniformContinuous_coeff** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.WithPiTopology`。
形式化陈述：uniformContinuous_coeff [Semiring R] (d : Nat) : UniformContinuous fun f :
 PowerSeries R => coeff d f
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)

--- 原说明 ---
Coefficients are uniformly continuous
-/
theorem uniformContinuous_coeff [Semiring R] (d : ℕ) :
    UniformContinuous fun f : PowerSeries R ↦ coeff d f :=
  uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)

/-- Completeness of the uniform structure on `PowerSeries` -/
@[scoped instance]
/-
**PowerSeries.WithPiTopology.instCompleteSpace** 是 Mathlib 中的一个定理，位于命名空间 `PowerS
eries.WithPiTopology`。
形式化陈述：instCompleteSpace [CompleteSpace R] : CompleteSpace (PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)

--- 原说明 ---
Completeness of the uniform structure on `PowerSeries`
-/
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (PowerSeries R) :=
  inferInstance

/-- The `IsUniformAddGroup` structure on `PowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
/-
**PowerSeries.WithPiTopology.instIsUniformAddGroup** 是 Mathlib 中的一个定理，位于命名空间 `Po
werSeries.WithPiTopology`。
形式化陈述：instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGro
up (PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)

--- 原说明 ---
The `IsUniformAddGroup` structure on `PowerSeries` of a `IsUniformAddGroup`
-/
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (PowerSeries R) :=
  inferInstance

end WithPiTopology

end Uniform

section

variable {R}

variable [TopologicalSpace R]

namespace WithPiTopology

open MvPowerSeries.WithPiTopology

/-
**PowerSeries.WithPiTopology.continuous_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries
.WithPiTopology`。
形式化陈述：continuous_C [Semiring R] : Continuous (C (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_C`：continuous_C [Semiring R] : C
ontinuous (C (σ
-/
theorem continuous_C [Semiring R] : Continuous (C (R := R)) :=
  MvPowerSeries.WithPiTopology.continuous_C
/-
**PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpote
nt** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R] {f 
: PowerSeries R} (hf : IsNilpotent (constantCoeff (R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_i
sNilpotent`：isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring 
R] {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsTopo…
-/
theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f : PowerSeries R} (hf : IsNilpotent (constantCoeff (R := R) f)) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent hf
/-
**PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero** 是 
Mathlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R] {f : Power
Series R} (hf : constantCoeff (R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_z
ero`：isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R] {f : MvPowe
rSeries σ R} (hf : constantCoeff f = 0) : Tendsto (fun n : Nat =>…
-/
theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f : PowerSeries R} (hf : constantCoeff (R := R) f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf

/-- Assuming the base ring has a discrete topology, the powers of a `PowerSeries` converge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki1981] -/
/-
**PowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpot
ent** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.WithPiTopology`。
形式化陈述：isTopologicallyNilpotent_iff_constantCoeff_isNilpotent [CommRing R] [Discr
eteTopology R] (f : PowerSeries R) : Tendsto (fun n : Nat => f ^ n) atTop (nhds 
0) ↔ IsNilpotent (constantCoeff f)
参数：f : PowerSeries R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_
isNilpotent`：isTopologicallyNilpotent_iff_constantCoeff_isNilpotent [CommRing R]
 [DiscreteTopology R] (f : MvPowerSeries σ R) : IsTopologicallyNilpotent …

--- 原说明 ---
Assuming the base ring has a discrete topology, the powers of a `PowerSeries` co
nverge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki19
81]
-/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f : PowerSeries R) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff f) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f

end WithPiTopology

end

section Summable

variable [Semiring R] [TopologicalSpace R]

open WithPiTopology MvPowerSeries.WithPiTopology

variable {R}

-- NOTE : one needs an API to apply `Finsupp.uniqueLinearEquiv`
/-- A power series is the sum (in the sense of summable families) of its monomials -/
/-
**PowerSeries.hasSum_of_monomials_self** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：hasSum_of_monomials_self (f : PowerSeries R) : HasSum (fun d : Nat => mono
mial d (coeff d f)) f
参数：f : PowerSeries R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} (e : γ ≃ β
), Has…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.uniqueLinearEquiv_apply`：∀ (R : Type u_1) {α : Type u_3} (M : Ty
pe u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.Module
 R M] [inst_3 : Subsi…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self`：hasSum_of_monomia
ls_self (f : MvPowerSeries σ R) : HasSum (fun d : σ ->₀ Nat => monomial d (coeff
 d f)) f

--- 原说明 ---
A power series is the sum (in the sense of summable families) of its monomials
-/
theorem hasSum_of_monomials_self (f : PowerSeries R) :
    HasSum (fun d : ℕ => monomial d (coeff d f)) f := by
  rw [← (Finsupp.uniqueLinearEquiv ℕ ℕ ()).toEquiv.hasSum_iff]
  convert! MvPowerSeries.WithPiTopology.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff]
  congr
  all_goals { ext; simp }

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
/-
**PowerSeries.as_tsum** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：as_tsum [T2Space R] (f : PowerSeries R) : f = tsum fun d : Nat => monomial
 d (coeff d f)
参数：f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PowerSeries.hasSum_of_monomials_self`：hasSum_of_monomials_self (f : Powe
rSeries R) : HasSum (fun d : Nat => monomial d (coeff d f)) f

--- 原说明 ---
If the coefficient space is T2, then the power series is `tsum` of its monomials
-/
theorem as_tsum [T2Space R] (f : PowerSeries R) :
    f = tsum fun d : ℕ => monomial d (coeff d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm

end Summable

end PowerSeries

