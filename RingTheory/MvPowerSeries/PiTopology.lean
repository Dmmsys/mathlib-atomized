/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-! # Product topology on multivariate power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `MvPowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficient maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped MvPowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2][bourbaki1981].

It is *not* the adic topology in general.

## Main results

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `MvPowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `MvPowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `MvPowerSeries σ R`.
- If `R` is complete, then so is `MvPowerSeries σ R`.

## Implementation Notes

In `Mathlib/RingTheory/MvPowerSeries/LinearTopology.lean`, we generalize the criterion for
topological nilpotency by proving that, if the base ring is equipped with a *linear* topology, then
a power series is topologically nilpotent if and only if its constant coefficient is.
This is lemma `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`.

Mathematically, everything proven in this file follows from that general statement. However,
formalizing this yields a few (minor) annoyances:

- we would need to push the results in this file slightly lower in the import tree
  (likely, in a new dedicated file);
- we would have to work in `CommRing`s rather than `CommSemiring`s (this probably does not
  matter in any way though);
- because `isTopologicallyNilpotent_of_constantCoeff_isNilpotent` holds for *any* topology,
  not necessarily discrete nor linear, the proof going through the general case involves
  juggling a bit with the topologies.

Since the code duplication is rather minor (the interesting part of the proof is already extracted
as `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`), we just leave this as is for now.
But future contributors wishing to clean this up should feel free to give it a try!

-/

public section

namespace MvPowerSeries

open Function Filter

open scoped Topology

variable {σ R : Type*}

namespace WithPiTopology

section Topology

variable [TopologicalSpace R]

variable (R) in
/-- The pointwise topology on `MvPowerSeries` -/
/-
**MvPowerSeries.WithPiTopology.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries.WithPiT
opology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise topology on `MvPowerSeries`
-/
scoped instance : TopologicalSpace (MvPowerSeries σ R) :=
  inferInstanceAs <| TopologicalSpace ((σ →₀ ℕ) → R)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.WithPiTopology.instTopologicalSpace_mono** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：instTopologicalSpace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace 
R} (htu : t <= u) : @instTopologicalSpace σ R t <= @instTopologicalSpace σ R u
参数：σ : Type*；htu : t <= u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `induced_mono`：induced_mono (h : t₁ <= t₂) : t₁.induced g <= t₂.induced g
-/
theorem instTopologicalSpace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t ≤ u) :
    @instTopologicalSpace σ R t ≤ @instTopologicalSpace σ R u := by
  change ⨅ i, _ ≤ ⨅ i, _
  gcongr

/-- `MvPowerSeries` on a `T0Space` form a `T0Space` -/
@[scoped instance]
/-
**MvPowerSeries.WithPiTopology.instT0Space** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSer
ies.WithPiTopology`。
形式化陈述：instT0Space [T0Space R] : T0Space (MvPowerSeries σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPowerSeries` on a `T0Space` form a `T0Space`
-/
theorem instT0Space [T0Space R] : T0Space (MvPowerSeries σ R) := Pi.instT0Space

/-- `MvPowerSeries` on a `T2Space` form a `T2Space` -/
@[scoped instance]
/-
**MvPowerSeries.WithPiTopology.instT2Space** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSer
ies.WithPiTopology`。
形式化陈述：instT2Space [T2Space R] : T2Space (MvPowerSeries σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPowerSeries` on a `T2Space` form a `T2Space`
-/
theorem instT2Space [T2Space R] : T2Space (MvPowerSeries σ R) := Pi.t2Space

variable (R) in
/-- `MvPowerSeries.coeff` is continuous. -/
@[fun_prop]
/-
**MvPowerSeries.WithPiTopology.continuous_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPow
erSeries.WithPiTopology`。
形式化陈述：continuous_coeff [Semiring R] (d : σ ->₀ Nat) : Continuous (MvPowerSeries.
coeff (R
参数：d : σ ->₀ Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
`MvPowerSeries.coeff` is continuous.
-/
theorem continuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    Continuous (MvPowerSeries.coeff (R := R) d) :=
  continuous_pi_iff.mp continuous_id d

variable (R) in
/-- `MvPowerSeries.constantCoeff` is continuous -/
/-
**MvPowerSeries.WithPiTopology.continuous_constantCoeff** 是 Mathlib 中的一个定理，位于命名空
间 `MvPowerSeries.WithPiTopology`。
形式化陈述：continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_coeff`：continuous_coeff [Semirin
g R] (d : σ ->₀ Nat) : Continuous (MvPowerSeries.coeff (R

--- 原说明 ---
`MvPowerSeries.constantCoeff` is continuous
-/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (σ := σ) (R := R)) :=
  continuous_coeff (R := R) 0

set_option backward.isDefEq.respectTransparency false in
/-- A family of power series converges iff it converges coefficientwise -/
/-
**MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*} (f : ι -> MvPowerSeries
 σ R) (u : Filter ι) (g : MvPowerSeries σ R) : Tendsto f u (nhds g) ↔ forall d :
 σ ->₀ Nat, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g))
参数：f : ι -> MvPowerSeries σ R；u : Filter ι；g : MvPowerSeries σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.tendsto_pi`：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : 
Filter β} : Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A family of power series converges iff it converges coefficientwise
-/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g)) := by
  rw [nhds_pi, tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)
/-
**MvPowerSeries.WithPiTopology.tendsto_trunc'_atTop** 是 Mathlib 中的一个定理，位于命名空间 `M
vPowerSeries.WithPiTopology`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : TopologicalSpace R] [inst_1 : Deci
dableEq σ] [inst_2 : CommSemiring R]   (f : MvPowerSeries σ R), Filter.Tendsto (
fun d => ↑((MvPowerSeries.trunc' R d) f)) Filter.atTop (nhds f)
参数：f : MvPowerSeries σ R；fun d => ↑((MvPowerSeries.trunc' R d) f)；nhds f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coef
f_tendsto [Semiring R] {ι : Type*} (f : ι -> MvPowerSeries σ R) (u : Filter ι) (
g : MvPowerSeries σ R) : Tendsto f u (nhds g…
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_trunc'`：coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerS
eries σ R) : (trunc' R n φ).coeff m = if m <= n then coeff m φ else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tendsto_trunc'_atTop [DecidableEq σ] [CommSemiring R] (f : MvPowerSeries σ R) :
    Tendsto (fun d ↦ (trunc' R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d ≤ n) ↦ (by simp [coeff_trunc', hdn])
/-
**MvPowerSeries.WithPiTopology.tendsto_trunc_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries.WithPiTopology`。
形式化陈述：tendsto_trunc_atTop [DecidableEq σ] [CommSemiring R] [Nonempty σ] (f : MvP
owerSeries σ R) : Tendsto (fun d => (trunc R d f : MvPowerSeries σ R)) atTop (𝓝 
f)
参数：f : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coef
f_tendsto [Semiring R] {ι : Type*} (f : ι -> MvPowerSeries σ R) (u : Filter ι) (
g : MvPowerSeries σ R) : Tendsto f u (nhds g…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_const`：∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∃ x, b) ↔ b
· 使用定理 `trivial`：True
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `MvPolynomial.coeff_coe`：coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff 
n ↑φ = coeff n φ
· 使用定理 `MvPowerSeries.coeff_trunc`：coeff_trunc (m n : σ ->₀ Nat) (φ : MvPowerSer
ies σ R) : (trunc R n φ).coeff m = if m < n then coeff m φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tendsto_trunc_atTop [DecidableEq σ] [CommSemiring R] [Nonempty σ] (f : MvPowerSeries σ R) :
    Tendsto (fun d ↦ (trunc R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  obtain ⟨s, _⟩ := (exists_const σ).mpr trivial
  apply tendsto_atTop_of_eventually_const (i₀ := d + Finsupp.single s 1)
  intro n hn
  rw [MvPolynomial.coeff_coe, coeff_trunc, if_pos]
  apply lt_of_lt_of_le _ hn
  simpa [Finsupp.lt_def] using ⟨s, by simp⟩

/-- The inclusion of polynomials into power series has dense image -/
/-
**MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries** 是 Mathlib 中的一个定理，位于命
名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：denseRange_toMvPowerSeries [CommSemiring R] : DenseRange (MvPolynomial.toM
vPowerSeries (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MvPowerSeries.WithPiTopology.tendsto_trunc'_atTop`：∀ {σ : Type u_1} {R :
 Type u_2} [inst : TopologicalSpace R] [inst_1 : DecidableEq σ] [inst_2 : CommSe
miring R]   (f : MvPowerSeries σ R), Fi…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The inclusion of polynomials into power series has dense image
-/
theorem denseRange_toMvPowerSeries [CommSemiring R] :
    DenseRange (MvPolynomial.toMvPowerSeries (R := R) (σ := σ)) := fun f ↦ by
  classical
  exact mem_closure_of_tendsto (tendsto_trunc'_atTop f) <| .of_forall fun _ ↦ Set.mem_range_self _

variable (σ R)

/-- The semiring topology on `MvPowerSeries` of a topological semiring -/
@[scoped instance]
/-
**MvPowerSeries.WithPiTopology.instIsTopologicalSemiring** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] : IsTopol
ogicalSemiring (MvPowerSeries σ R) where continuous_add
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_coeff`：continuous_coeff [Semirin
g R] (d : σ ->₀ Nat) : Continuous (MvPowerSeries.coeff (R
· 使用定理 `Continuous.snd'`：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.snd
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R

--- 原说明 ---
The semiring topology on `MvPowerSeries` of a topological semiring
-/
theorem instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (MvPowerSeries σ R) where
  continuous_add := continuous_pi fun d => continuous_add.comp
    (((continuous_coeff R d).fst').prodMk (continuous_coeff R d).snd')
  continuous_mul := continuous_pi fun _ =>
    continuous_finsetSum _ fun i _ => continuous_mul.comp
      ((continuous_coeff R i.fst).fst'.prodMk (continuous_coeff R i.snd).snd')

/-- The ring topology on `MvPowerSeries` of a topological ring -/
@[scoped instance]
/-
**MvPowerSeries.WithPiTopology.instIsTopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries.WithPiTopology`。
形式化陈述：instIsTopologicalRing [Ring R] [IsTopologicalRing R] : IsTopologicalRing (
MvPowerSeries σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalSemiring`：instIsTopologica
lSemiring [Semiring R] [IsTopologicalSemiring R] : IsTopologicalSemiring (MvPowe
rSeries σ R) where continuous_add
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_coeff`：continuous_coeff [Semirin
g R] (d : σ ->₀ Nat) : Continuous (MvPowerSeries.coeff (R

--- 原说明 ---
The ring topology on `MvPowerSeries` of a topological ring
-/
theorem instIsTopologicalRing [Ring R] [IsTopologicalRing R] :
    IsTopologicalRing (MvPowerSeries σ R) :=
  { instIsTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_coeff R d) }

variable {σ R}

@[fun_prop]
/-
**MvPowerSeries.WithPiTopology.continuous_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries.WithPiTopology`。
形式化陈述：continuous_C [Semiring R] : Continuous (C (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coef
f_tendsto [Semiring R] {ι : Type*} (f : ι -> MvPowerSeries σ R) (u : Filter ι) (
g : MvPowerSeries σ R) : Tendsto f u (nhds g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.coeff_C`：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
 coeff n (C a) = if n = 0 then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem continuous_C [Semiring R] :
    Continuous (C (σ := σ) (R := R)) := by
  classical
  simp only [continuous_iff_continuousAt]
  refine fun r ↦ (tendsto_iff_coeff_tendsto _ _ _).mpr fun d ↦ ?_
  simp only [coeff_C]
  split_ifs
  · exact tendsto_id
  · exact tendsto_const_nhds

/-- Scalar multiplication on `MvPowerSeries` is continuous. -/
/-
**MvPowerSeries.WithPiTopology.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries.WithPiT
opology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication on `MvPowerSeries` is continuous.
-/
instance {S : Type*} [Semiring S] [TopologicalSpace S]
    [CommSemiring R] [Algebra R S] [ContinuousSMul R S] :
    ContinuousSMul R (MvPowerSeries σ S) :=
  instContinuousSMulForall
/-
**MvPowerSeries.WithPiTopology.variables_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MvPowerSeries.WithPiTopology`。
形式化陈述：variables_tendsto_zero [Semiring R] : Tendsto (X · : σ -> MvPowerSeries σ 
R) cofinite (nhds 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_cofinite_ne`：eventually_cofinite_ne (x : α) : forallᶠ 
a in cofinite, a != x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem variables_tendsto_zero [Semiring R] :
    Tendsto (X · : σ → MvPowerSeries σ R) cofinite (nhds 0) := by
  classical
  simp only [tendsto_iff_coeff_tendsto, coeff_X, coeff_zero]
  refine fun d ↦ tendsto_nhds_of_eventually_eq ?_
  by_cases! h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' ↦ (h x h').elim
/-
**MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpo
tent** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R] {f 
: MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsTopologicallyNilpo
tent f
参数：hf : IsNilpotent (constantCoeff f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`：coeff_eq_zero_of
_constantCoeff_nilpotent {f : MvPowerSeries σ R} {m : Nat} (hf : constantCoeff f
 ^ m = 0) {d : σ ->₀ Nat} {n : Nat} (hn : m …
-/
theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) :
    IsTopologicallyNilpotent f := by
  obtain ⟨m, hm⟩ := hf
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d ↦ tendsto_atTop_of_eventually_const fun n hn ↦
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn
/-
**MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero** 
是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R] {f : MvPow
erSeries σ R} (hf : constantCoeff f = 0) : Tendsto (fun n : Nat => f ^ n) atTop 
(nhds 0)
参数：hf : constantCoeff f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_i
sNilpotent`：isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring 
R] {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsTopo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNilpotent.zero`：∀ {R : Type u_3} [inst : MonoidWithZero R], IsNilpoten
t 0
-/
theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) := by
  apply isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  rw [hf]
  exact IsNilpotent.zero

/-- Assuming the base ring has a discrete topology, the powers of a `MvPowerSeries` converge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki1981]

See also `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`. -/
/-
**MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilp
otent** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：isTopologicallyNilpotent_iff_constantCoeff_isNilpotent [CommRing R] [Discr
eteTopology R] (f : MvPowerSeries σ R) : IsTopologicallyNilpotent f ↔ IsNilpoten
t (constantCoeff f)
参数：f : MvPowerSeries σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.map`：map {F : Type*} [FunLike F R S] [MonoidWit
hZeroHomClass F R S] {φ : F} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNi
lpotent a) : IsTop…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_constantCoeff`：continuous_consta
ntCoeff [Semiring R] : Continuous (constantCoeff (σ
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_i
sNilpotent`：isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring 
R] {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsTopo…

--- 原说明 ---
Assuming the base ring has a discrete topology, the powers of a `MvPowerSeries` 
converge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki19
81]

See also `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoef
f`.
-/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f : MvPowerSeries σ R) :
    IsTopologicallyNilpotent f ↔ IsNilpotent (constantCoeff f) := by
  refine ⟨fun H ↦ ?_, isTopologicallyNilpotent_of_constantCoeff_isNilpotent⟩
  replace H := H.map (continuous_constantCoeff R)
  simp_rw [IsTopologicallyNilpotent, nhds_discrete, tendsto_pure] at H
  exact H.exists

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/-- A multivariate power series is the sum (in the sense of summable families) of its monomials -/
/-
**MvPowerSeries.WithPiTopology.hasSum_of_monomials_self** 是 Mathlib 中的一个定理，位于命名空
间 `MvPowerSeries.WithPiTopology`。
形式化陈述：hasSum_of_monomials_self (f : MvPowerSeries σ R) : HasSum (fun d : σ ->₀ N
at => monomial d (coeff d f)) f
参数：f : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.hasSum`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : (x
 : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `hasSum_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {f : β → α} (b : β),   (∀ (b' : β), b' ≠ b → f b' 
= 0…
· 使用定理 `MvPowerSeries.coeff_monomial_ne`：coeff_monomial_ne {m n : σ ->₀ Nat} (h 
: m != n) (a : R) : coeff m (monomial n a) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop

--- 原说明 ---
A multivariate power series is the sum (in the sense of summable families) of it
s monomials
-/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d : σ →₀ ℕ => monomial d (coeff d f)) f := by
  rw [Pi.hasSum]
  intro d
  simpa using! hasSum_single d (fun d' h ↦ coeff_monomial_ne h.symm _)

/-- If the coefficient space is T2, then the multivariate power series is `tsum` of its monomials -/
/-
**MvPowerSeries.WithPiTopology.as_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.
WithPiTopology`。
形式化陈述：as_tsum [T2Space R] (f : MvPowerSeries σ R) : f = tsum fun d : σ ->₀ Nat =
> monomial d (coeff d f)
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self`：hasSum_of_monomia
ls_self (f : MvPowerSeries σ R) : HasSum (fun d : σ ->₀ Nat => monomial d (coeff
 d f)) f

--- 原说明 ---
If the coefficient space is T2, then the multivariate power series is `tsum` of 
its monomials
-/
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d : σ →₀ ℕ => monomial d (coeff d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

section Sum
variable {ι : Type*} {f : ι → MvPowerSeries σ R}

/-
**MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff** 是 Mathlib 中的一个定理，位于命名空间
 `MvPowerSeries.WithPiTopology`。
形式化陈述：hasSum_iff_hasSum_coeff {g : MvPowerSeries σ R} : HasSum f g ↔ forall d : 
σ ->₀ Nat, HasSum (fun i => coeff d (f i)) (coeff d g)
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
· 使用定理 `MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coef
f_tendsto [Semiring R] {ι : Type*} (f : ι -> MvPowerSeries σ R) (u : Filter ι) (
g : MvPowerSeries σ R) : Tendsto f u (nhds g…
-/
theorem hasSum_iff_hasSum_coeff {g : MvPowerSeries σ R} :
    HasSum f g ↔ ∀ d : σ →₀ ℕ, HasSum (fun i ↦ coeff d (f i)) (coeff d g) := by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto
/-
**MvPowerSeries.WithPiTopology.summable_iff_summable_coeff** 是 Mathlib 中的一个定理，位于
命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：summable_iff_summable_coeff : Summable f ↔ forall d : σ ->₀ Nat, Summable 
(fun i => coeff d (f i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem summable_iff_summable_coeff :
    Summable f ↔ ∀ d : σ →₀ ℕ, Summable (fun i ↦ coeff d (f i)) := by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨a, by simpa using! h⟩

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- A family of `MvPowerSeries` is summable if their weighted order tends to infinity. -/
/-
**MvPowerSeries.WithPiTopology.summable_of_tendsto_weightedOrder_atTop_nhds_top*
* 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：summable_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat} (h : Tends
to (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable f
参数：h : Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `summable_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [IsEmpty β]
, Su…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.WithPiTopology.summable_iff_summable_coeff`：summable_iff_s
ummable_coeff : Summable f ↔ forall d : σ ->₀ Nat, Summable (fun i => coeff d (f
 i))
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
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A family of `MvPowerSeries` is summable if their weighted order tends to infinit
y.
-/
theorem summable_of_tendsto_weightedOrder_atTop_nhds_top {w : σ → ℕ}
    (h : Tendsto (fun i ↦ weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable f := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  intro d
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  refine summable_of_hasFiniteSupport <| (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
  exact coeff_eq_zero_of_lt_weightedOrder w <| hi k hk.le

/-- A family of `MvPowerSeries` is summable if their order tends to infinity. -/
/-
**MvPowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top** 是 Math
lib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：summable_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i => (f i).orde
r) atTop (𝓝 ⊤)) : Summable f
参数：h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.summable_of_tendsto_weightedOrder_atTop_nhd
s_top`：summable_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat} (h : Tend
sto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable f

--- 原说明 ---
A family of `MvPowerSeries` is summable if their order tends to infinity.
-/
theorem summable_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable f :=
  summable_of_tendsto_weightedOrder_atTop_nhds_top h

/-- The geometric series converges if the constant term is zero. -/
/-
**MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero** 是 Mathlib
 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：summable_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R} (h : f.const
antCoeff = 0) : Summable (f ^ ·)
参数：h : f.constantCoeff = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top`：s
ummable_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i => (f i).order) atTo
p (𝓝 ⊤)) : Summable f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `ENat.self_le_mul_right`：self_le_mul_right (a : Nat∞) (hc : c != 0) : a <
= a * c
· 使用定理 `MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero`：order_ne_zero_iff_co
nstCoeff_eq_zero : f.order != 0 ↔ f.constantCoeff = 0
· 使用定理 `MvPowerSeries.le_order_pow`：le_order_pow (n : Nat) : n • f.order <= (f ^
 n).order

--- 原说明 ---
The geometric series converges if the constant term is zero.
-/
theorem summable_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R}
    (h : f.constantCoeff = 0) : Summable (f ^ ·) := by
  apply summable_of_tendsto_order_atTop_nhds_top
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop]
  refine fun n ↦ ⟨n + 1, fun m hm ↦ lt_of_lt_of_le ?_ (le_order_pow _)⟩
  refine (ENat.natCast_lt_natCast.mpr (Nat.add_one_le_iff.mp hm)).trans_le ?_
  simpa [nsmul_eq_mul] using ENat.self_le_mul_right m (order_ne_zero_iff_constCoeff_eq_zero.mpr h)

section GeomSeries
variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
variable {f : MvPowerSeries σ R}

/-- Formula for geometric series. -/
/-
**MvPowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero** 是
 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) : 
(∑' (i : Nat), f ^ i) * (1 - f) = 1
参数：h : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_pow_mul_one_sub`：Summable.tsum_pow_mul_one_sub {x : α} (h 
: Summable (x ^ ·)) : (∑' (i : Nat), x ^ i) * (1 - x) = 1
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero`：summ
able_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R} (h : f.constantCoeff =
 0) : Summable (f ^ ·)

--- 原说明 ---
Formula for geometric series.
-/
theorem tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (∑' (i : ℕ), f ^ i) * (1 - f) = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).tsum_pow_mul_one_sub

/-- Formula for geometric series. -/
/-
**MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero** 是
 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) : 
(1 - f) * ∑' (i : Nat), f ^ i = 1
参数：h : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.one_sub_mul_tsum_pow`：Summable.one_sub_mul_tsum_pow {x : α} (h 
: Summable (x ^ ·)) : (1 - x) * ∑' (i : Nat), x ^ i = 1
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero`：summ
able_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R} (h : f.constantCoeff =
 0) : Summable (f ^ ·)

--- 原说明 ---
Formula for geometric series.
-/
theorem one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (1 - f) * ∑' (i : ℕ), f ^ i = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).one_sub_mul_tsum_pow

end GeomSeries

end Sum

section Prod
variable {σ R : Type*} [TopologicalSpace R] [CommSemiring R]
variable {ι : Type*} {f : ι → MvPowerSeries σ R} [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- If the weighted order of a family of `MvPowerSeries` tends to infinity, the collection of all
possible products over `Finset` is summable. -/
/-
**MvPowerSeries.WithPiTopology.summable_prod_of_tendsto_weightedOrder_atTop_nhds
_top** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：summable_prod_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat} (h : 
Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i)
参数：h : Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)。
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
· 使用定理 `MvPowerSeries.WithPiTopology.summable_iff_summable_coeff`：summable_iff_s
ummable_coeff : Summable f ↔ forall d : σ ->₀ Nat, Summable (fun i => coeff d (f
 i))
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
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
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
If the weighted order of a family of `MvPowerSeries` tends to infinity, the coll
ection of all
possible products over `Finset` is summable.
-/
theorem summable_prod_of_tendsto_weightedOrder_atTop_nhds_top {w : σ → ℕ}
    (h : Tendsto (fun i ↦ weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable (∏ i ∈ ·, f i) := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine summable_iff_summable_coeff.mpr fun d ↦ summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices ∀ s : Finset ι, coeff d (∏ i ∈ s, f i) ≠ 0 → ↑s ⊆ Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio, not_lt] at hxi
  refine coeff_eq_zero_of_lt_weightedOrder w <| (hi x hxi).trans_le <| ?_
  apply le_trans (Finset.single_le_sum (by simp) hxs) (le_weightedOrder_prod w _ _)

/-- If the order of a family of `MvPowerSeries` tends to infinity, the collection of all
possible products over `Finset` is summable. -/
/-
**MvPowerSeries.WithPiTopology.summable_prod_of_tendsto_order_atTop_nhds_top** 是
 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：summable_prod_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i => (f i)
.order) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i)
参数：h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.summable_prod_of_tendsto_weightedOrder_atTo
p_nhds_top`：summable_prod_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat}
 (h : Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable (…

--- 原说明 ---
If the order of a family of `MvPowerSeries` tends to infinity, the collection of
 all
possible products over `Finset` is summable.
-/
theorem summable_prod_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable (∏ i ∈ ·, f i) :=
  summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

/-- A family of `MvPowerSeries` in the form `1 + f i` is multipliable if the weighted order of `f i`
tends to infinity. -/
/-
**MvPowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_weightedOrder_atT
op_nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat
} (h : Tendsto (fun i => weightedOrder w (f i)) atTop (nhds ⊤)) : Multipliable (
1 + f ·)
参数：h : Tendsto (fun i => weightedOrder w (f i)) atTop (nhds ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multipliable_one_add_of_summable_prod`：multipliable_one_add_of_summable_
prod (h : Summable (∏ i in ·, f i)) : Multipliable (1 + f ·)
· 使用定理 `MvPowerSeries.WithPiTopology.summable_prod_of_tendsto_weightedOrder_atTo
p_nhds_top`：summable_prod_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat}
 (h : Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable (…

--- 原说明 ---
A family of `MvPowerSeries` in the form `1 + f i` is multipliable if the weighte
d order of `f i`
tends to infinity.
-/
theorem multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top {w : σ → ℕ}
    (h : Tendsto (fun i ↦ weightedOrder w (f i)) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
  multipliable_one_add_of_summable_prod <| summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

/-- A family of `MvPowerSeries` in the form `1 + f i` is multipliable if the order of `f i`
tends to infinity. -/
/-
**MvPowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_
top** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.WithPiTopology`。
形式化陈述：multipliable_one_add_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i =
> (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·)
参数：h : Tendsto (fun i => (f i).order) atTop (nhds ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multipliable_one_add_of_summable_prod`：multipliable_one_add_of_summable_
prod (h : Summable (∏ i in ·, f i)) : Multipliable (1 + f ·)
· 使用定理 `MvPowerSeries.WithPiTopology.summable_prod_of_tendsto_order_atTop_nhds_t
op`：summable_prod_of_tendsto_order_atTop_nhds_top (h : Tendsto (fun i => (f i).o
rder) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i)

--- 原说明 ---
A family of `MvPowerSeries` in the form `1 + f i` is multipliable if the order o
f `f i`
tends to infinity.
-/
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
  multipliable_one_add_of_summable_prod <| summable_prod_of_tendsto_order_atTop_nhds_top h

end Prod

end Topology

section Uniformity

variable [UniformSpace R]

/-- The componentwise uniformity on `MvPowerSeries` -/
/-
**MvPowerSeries.WithPiTopology.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries.WithPiT
opology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The componentwise uniformity on `MvPowerSeries`
-/
scoped instance : UniformSpace (MvPowerSeries σ R) :=
  inferInstanceAs <| UniformSpace ((σ →₀ ℕ) → R)

variable (R) in
/-- Coefficients of a multivariate power series are uniformly continuous -/
/-
**MvPowerSeries.WithPiTopology.uniformContinuous_coeff** 是 Mathlib 中的一个定理，位于命名空间
 `MvPowerSeries.WithPiTopology`。
形式化陈述：uniformContinuous_coeff [Semiring R] (d : σ ->₀ Nat) : UniformContinuous f
un f : MvPowerSeries σ R => coeff d f
参数：d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)

--- 原说明 ---
Coefficients of a multivariate power series are uniformly continuous
-/
theorem uniformContinuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    UniformContinuous fun f : MvPowerSeries σ R => coeff d f :=
  uniformContinuous_pi.mp uniformContinuous_id d

/-- Completeness of the uniform structure on `MvPowerSeries` -/
@[scoped instance]
/-
**MvPowerSeries.WithPiTopology.instCompleteSpace** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
werSeries.WithPiTopology`。
形式化陈述：instCompleteSpace [CompleteSpace R] : CompleteSpace (MvPowerSeries σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Completeness of the uniform structure on `MvPowerSeries`
-/
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) := Pi.complete _

/-- The `IsUniformAddGroup` structure on `MvPowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
/-
**MvPowerSeries.WithPiTopology.instIsUniformAddGroup** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries.WithPiTopology`。
形式化陈述：instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGro
up (MvPowerSeries σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instIsUniformAddGroup`：∀ {ι : Type u_4} {G : ι → Type u_5} [inst : (i
 : ι) → UniformSpace (G i)] [inst_1 : (i : ι) → AddGroup (G i)]   [∀ (i : ι), Is
UniformAddGrou…

--- 原说明 ---
The `IsUniformAddGroup` structure on `MvPowerSeries` of a `IsUniformAddGroup`
-/
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (MvPowerSeries σ R) := Pi.instIsUniformAddGroup

end Uniformity

end WithPiTopology

end MvPowerSeries

