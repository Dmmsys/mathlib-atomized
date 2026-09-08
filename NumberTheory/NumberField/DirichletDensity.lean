/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Dirichlet density of a set of prime ideals

Let `K` be a number field. Given a set `S` of nonzero prime ideals of `𝓞 K`, its Dirichlet
density is
$$
\delta(S) = \lim_{s \to 1^+}
  \frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
    {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
when this limit exists. The sum in the denominator runs over all nonzero prime ideals of `𝓞 K`.

This is captured by the predicate `HasDirichletDensity S δ`, stating that the ratio tends to `δ`,
and by the definition `dirichletDensity S`, the density as a real number (with junk value `0` when
it does not exist).

## Main results

* `NumberField.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is bounded
  above by the number of elements of `S`.
* `NumberField.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.
* `NumberField.dirichletDensity_nonneg` — the Dirichlet density is nonnegative.
* `NumberField.dirichletDensity_le_one` — the Dirichlet density is at most `1`.

-/

public section

noncomputable section

open Filter IsDedekindDomain Topology Set

namespace NumberField.Set

open NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The partial Dirichlet series $\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$. -/
/-
**NumberField.Set.primeIdealZetaSum** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Set`。
形式化陈述：primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : Real) : Real
参数：S : Set (HeightOneSpectrum (𝓞 K))；s : Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
The partial Dirichlet series $\sum_{\mathfrak p \in S} \operatorname{N} \mathfra
k p^{-s}$.
-/
def primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
/-
**NumberField.Set.primeIdealZetaSum_def** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.S
et`。
形式化陈述：primeIdealZetaSum_def (s : Real) : S.primeIdealZetaSum s = ∑' 𝔭 : S, (Idea
l.absNorm 𝔭.1.asIdeal : Real) ^ (-s)
参数：s : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primeIdealZetaSum_def (s : ℝ) :
    S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by rfl
/-
**NumberField.Set.primeIdealZetaSum_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.Set`。
形式化陈述：primeIdealZetaSum_nonneg (s : Real) : 0 <= S.primeIdealZetaSum s
参数：s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem primeIdealZetaSum_nonneg (s : ℝ) :
    0 ≤ S.primeIdealZetaSum s :=
  tsum_nonneg fun _ ↦ by positivity

variable {S} in
/-- For a finite set `S` of prime ideals, the partial sum
$\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$ is bounded above by the number of
elements of `S`. -/
/-
**NumberField.Set.primeIdealZetaSum_le_card_of_finite** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.Set`。
形式化陈述：primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : Real} (hs : 0 <= 
s) : S.primeIdealZetaSum s <= S.ncard
参数：hS : S.Finite；hs : 0 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Set.primeIdealZetaSum_def`：primeIdealZetaSum_def (s : Real) 
: S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Real.rpow_le_one_of_one_le_of_nonpos`：rpow_le_one_of_one_le_of_nonpos {x
 z : Real} (hx : 1 <= x) (hz : z <= 0) : x ^ z <= 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsum_const`：∀ {β : Type u_2} {G : Type u_4} [inst : TopologicalSpace G] 
[inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   [T2Space G] (a : G), ∑' (x
…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
For a finite set `S` of prime ideals, the partial sum
$\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$ is bounded above by
 the number of
elements of `S`.
-/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 ≤ s) :
    S.primeIdealZetaSum s ≤ S.ncard := by
  replace hS := hS.to_subtype
  grw [primeIdealZetaSum_def, Real.rpow_le_one_of_one_le_of_nonpos] <;>
  simp [Summable.of_finite, Nat.one_le_iff_ne_zero,
    Ideal.absNorm_eq_zero_iff, hs, HeightOneSpectrum.ne_bot]

/-- `S` has Dirichlet density `δ` when the ratio of the partial sum over `S` to the sum over all
nonzero prime ideals,
$$
\frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
  {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
tends to `δ` as $s \to 1^+$. -/
/-
**NumberField.Set.HasDirichletDensity** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Set
`。
形式化陈述：HasDirichletDensity (δ : Real) : Prop
参数：δ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S` has Dirichlet density `δ` when the ratio of the partial sum over `S` to the 
sum over all
nonzero prime ideals,
$$
\frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
  {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
tends to `δ` as $s \to 1^+$.
-/
def HasDirichletDensity (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

open scoped Classical in
/-- The Dirichlet density of `S` as a real number, taking the junk value `0` when `S` has no
density. As with `tsum`, this value only has content when `S` has a density; the genuine statement
that `S` has density `0` is `HasDirichletDensity S 0`. -/
/-
**NumberField.Set.dirichletDensity** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Set`。
形式化陈述：dirichletDensity : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirichlet density of `S` as a real number, taking the junk value `0` when `S
` has no
density. As with `tsum`, this value only has content when `S` has a density; the
 genuine statement
that `S` has density `0` is `HasDirichletDensity S 0`.
-/
def dirichletDensity : ℝ :=
  if h : ∃ δ, S.HasDirichletDensity δ then h.choose else 0

variable {S}

/-- If `S` has no Dirichlet density, then `dirichletDensity S = 0`. -/
/-
**NumberField.Set.dirichletDensity_eq_zero_of_not_hasDirichletDensity** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.Set`。
形式化陈述：dirichletDensity_eq_zero_of_not_hasDirichletDensity (h : forall δ, ¬ S.Has
DirichletDensity δ) : S.dirichletDensity = 0
参数：h : forall δ, ¬ S.HasDirichletDensity δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.DirichletDensity.0.NumberField
.Set.dirichletDensity.eq_1`：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberFi
eld K]   (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfInteger
s K))), …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x

--- 原说明 ---
If `S` has no Dirichlet density, then `dirichletDensity S = 0`.
-/
theorem dirichletDensity_eq_zero_of_not_hasDirichletDensity
    (h : ∀ δ, ¬ S.HasDirichletDensity δ) : S.dirichletDensity = 0 := by
  rw [dirichletDensity, dif_neg (not_exists.mpr h)]

/-- If `S` has Dirichlet density `δ`, then `dirichletDensity S = δ`. -/
/-
**NumberField.Set.HasDirichletDensity.dirichletDensity_eq** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.Set.HasDirichletDensity`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]   {S : Set (IsD
edekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ},   Numb
erField.Set.HasDirichletDensity S δ → NumberField.Set.dirichletDensity S = δ
参数：IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.DirichletDensity.0.NumberField
.Set.dirichletDensity.eq_1`：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberFi
eld K]   (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfInteger
s K))), …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
If `S` has Dirichlet density `δ`, then `dirichletDensity S = δ`.
-/
theorem HasDirichletDensity.dirichletDensity_eq {δ : ℝ} (h : S.HasDirichletDensity δ) :
    S.dirichletDensity = δ := by
  rw [dirichletDensity, dif_pos ⟨δ, h⟩, tendsto_nhds_unique (Exists.choose_spec ⟨δ, h⟩) h]

/-- The empty set has Dirichlet density `0`. -/
/-
**NumberField.Set.hasDirichletDensity_empty** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.Set`。
形式化陈述：hasDirichletDensity_empty : HasDirichletDensity (∅ : Set (HeightOneSpectru
m (𝓞 K))) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.Set.primeIdealZetaSum_def`：primeIdealZetaSum_def (s : Real) 
: S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s)
· 使用定理 `tsum_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [IsEmpty β], ∑'
…
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The empty set has Dirichlet density `0`.
-/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

/-- The Dirichlet density of the empty set is `0`. -/
@[simp]
/-
**NumberField.Set.dirichletDensity_empty** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
Set`。
形式化陈述：dirichletDensity_empty : dirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K
))) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.Set.HasDirichletDensity.dirichletDensity_eq`：∀ {K : Type u_1
} [inst : Field K] [inst_1 : NumberField K]   {S : Set (IsDedekindDomain.HeightO
neSpectrum (NumberField.RingOfIntegers K))} {…
· 使用定理 `NumberField.Set.hasDirichletDensity_empty`：hasDirichletDensity_empty : H
asDirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0

--- 原说明 ---
The Dirichlet density of the empty set is `0`.
-/
theorem dirichletDensity_empty :
    dirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) = 0 :=
  hasDirichletDensity_empty.dirichletDensity_eq

/-- The Dirichlet density is nonnegative. -/
/-
**NumberField.Set.HasDirichletDensity.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.Set.HasDirichletDensity`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]   {S : Set (IsD
edekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ},   Numb
erField.Set.HasDirichletDensity S δ → 0 ≤ δ
参数：IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `NumberField.Set.primeIdealZetaSum_nonneg`：primeIdealZetaSum_nonneg (s : 
Real) : 0 <= S.primeIdealZetaSum s

--- 原说明 ---
The Dirichlet density is nonnegative.
-/
theorem HasDirichletDensity.nonneg {δ : ℝ} (h : S.HasDirichletDensity δ) :
    0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun s ↦
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

variable (S) in
/-- The Dirichlet density of `S` is nonnegative. -/
/-
**NumberField.Set.dirichletDensity_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.Set`。
形式化陈述：dirichletDensity_nonneg : 0 <= S.dirichletDensity
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.DirichletDensity.0.NumberField
.Set.dirichletDensity.eq_1`：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberFi
eld K]   (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfInteger
s K))), …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `NumberField.Set.HasDirichletDensity.nonneg`：∀ {K : Type u_1} [inst : Fie
ld K] [inst_1 : NumberField K]   {S : Set (IsDedekindDomain.HeightOneSpectrum (N
umberField.RingOfIntegers K))} {…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The Dirichlet density of `S` is nonnegative.
-/
theorem dirichletDensity_nonneg : 0 ≤ S.dirichletDensity := by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.nonneg
  · exact le_rfl

/-- The Dirichlet density is at most `1`. -/
/-
**NumberField.Set.HasDirichletDensity.le_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.Set.HasDirichletDensity`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]   {S : Set (IsD
edekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ},   Numb
erField.Set.HasDirichletDensity S δ → δ ≤ 1
参数：IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Set.primeIdealZetaSum_def`：primeIdealZetaSum_def (s : Real) 
: S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s)
· 使用定理 `tsum_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α),   ∑' (x : ↑Set.univ), f ↑x = ∑' (x : β),…
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Summable.tsum_subtype_le`：∀ {κ : Type u_4} {γ : Type u_5} [inst : AddCom
mGroup γ] [inst_1 : PartialOrder γ] [IsOrderedAddMonoid γ]   [inst_3 : UniformSp
ace γ] [IsUnif…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The Dirichlet density is at most `1`.
-/
theorem HasDirichletDensity.le_one {δ : ℝ} (h : S.HasDirichletDensity δ) :
    δ ≤ 1 := by
  refine le_of_tendsto h (Eventually.of_forall fun s ↦ ?_)
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)
  · exact div_le_one_of_le₀ (hs.tsum_subtype_le _ S (fun _ ↦ by positivity))
      (tsum_nonneg fun _ ↦ by positivity)
  · grw [tsum_eq_zero_of_not_summable hs, div_zero, zero_le_one]

variable (S) in
/-- The Dirichlet density of `S` is at most `1`. -/
/-
**NumberField.Set.dirichletDensity_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.Set`。
形式化陈述：dirichletDensity_le_one : S.dirichletDensity <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.DirichletDensity.0.NumberField
.Set.dirichletDensity.eq_1`：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberFi
eld K]   (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfInteger
s K))), …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `NumberField.Set.HasDirichletDensity.le_one`：∀ {K : Type u_1} [inst : Fie
ld K] [inst_1 : NumberField K]   {S : Set (IsDedekindDomain.HeightOneSpectrum (N
umberField.RingOfIntegers K))} {…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
The Dirichlet density of `S` is at most `1`.
-/
theorem dirichletDensity_le_one : S.dirichletDensity ≤ 1 := by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.le_one
  · exact zero_le_one

end NumberField.Set

