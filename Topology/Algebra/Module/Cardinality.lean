/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Module.Card
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.CountableCover
public import Mathlib.Topology.MetricSpace.Perfect

/-!
# Cardinality of open subsets of vector spaces

Any nonempty open subset of a topological vector space over a nontrivially normed field has the same
cardinality as the whole space. This is proved in `cardinal_eq_of_isOpen`.

We deduce that a countable set in a nontrivial vector space over a complete nontrivially normed
field has dense complement, in `Set.Countable.dense_compl`. This follows from the previous
argument and the fact that a complete nontrivially normed field has cardinality at least
continuum, proved in `continuum_le_cardinal_of_nontriviallyNormedField`.
-/

public section
universe u v

open Filter Pointwise Set Function Cardinal
open scoped Cardinal Topology

/-- A complete nontrivially normed field has cardinality at least continuum. -/
/-
**continuum_le_cardinal_of_nontriviallyNormedField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuum_le_cardinal_of_nontriviallyNormedField (𝕜 : Type*) [Nontrivially
NormedField 𝕜] [CompleteSpace 𝕜] : 𝔠 <= #𝕜
参数：𝕜 : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfect.exists_nat_bool_injection`：Perfect.exists_nat_bool_injection (hC
 : Perfect C) (hnonempty : C.Nonempty) [CompleteSpace α] : exists f : (Nat -> Bo
ol) -> α, range f subse…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `preperfect_iff_nhds`：preperfect_iff_nhds : Preperfect C ↔ forall x in C,
 forall U in 𝓝 x, exists y in U inter C, y != x
· 使用定理 `NormedField.exists_norm_lt_one`：exists_norm_lt_one : exists x : α, 0 < ‖
x‖ ∧ ‖x‖ < 1
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
A complete nontrivially normed field has cardinality at least continuum.
-/
theorem continuum_le_cardinal_of_nontriviallyNormedField
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] : 𝔠 ≤ #𝕜 := by
  suffices ∃ f : (ℕ → Bool) → 𝕜, range f ⊆ univ ∧ Continuous f ∧ Injective f by
    rcases this with ⟨f, -, -, f_inj⟩
    simpa using lift_mk_le_lift_mk_of_injective f_inj
  apply Perfect.exists_nat_bool_injection _ univ_nonempty
  refine ⟨isClosed_univ, preperfect_iff_nhds.2 (fun x _ U hU ↦ ?_)⟩
  rcases NormedField.exists_norm_lt_one 𝕜 with ⟨c, c_pos, hc⟩
  have A : Tendsto (fun n ↦ x + c ^ n) atTop (𝓝 (x + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc)
  rw [add_zero] at A
  have B : ∀ᶠ n in atTop, x + c ^ n ∈ U := tendsto_def.1 A U hU
  rcases B.exists with ⟨n, hn⟩
  refine ⟨x + c^n, by simpa using hn, ?_⟩
  simp only [add_ne_left]
  apply pow_ne_zero
  simpa using c_pos

/-- A nontrivial module over a complete nontrivially normed field has cardinality at least
continuum. -/
/-
**continuum_le_cardinal_of_module** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuum_le_cardinal_of_module (𝕜 : Type u) (E : Type v) [NontriviallyNor
medField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nontrivial E] : 𝔠 <
= #E
参数：𝕜 : Type u；E : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_continuum`：lift_continuum : lift.{v} 𝔠 = 𝔠
· 使用定理 `continuum_le_cardinal_of_nontriviallyNormedField`：continuum_le_cardinal_
of_nontriviallyNormedField (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpac
e 𝕜] : 𝔠 <= #𝕜
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_of_module`：mk_le_of_module (R : Type u) (E : Type v) [Add
CommGroup E] [Ring R] [IsDomain R] [Module R E] [Nontrivial E] [Module.IsTorsion
Free R E] : Ca…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M

--- 原说明 ---
A nontrivial module over a complete nontrivially normed field has cardinality at
 least
continuum.
-/
theorem continuum_le_cardinal_of_module
    (𝕜 : Type u) (E : Type v) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Nontrivial E] : 𝔠 ≤ #E := by
  have A : lift.{v} (𝔠 : Cardinal.{u}) ≤ lift.{v} (#𝕜) := by
    simpa using continuum_le_cardinal_of_nontriviallyNormedField 𝕜
  simpa using A.trans (Cardinal.mk_le_of_module 𝕜 E)

/-- In a topological vector space over a nontrivially normed field, any neighborhood of zero has
the same cardinality as the whole space.

See also `cardinal_eq_of_mem_nhds`. -/
/-
**cardinal_eq_of_mem_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cardinal_eq_of_mem_nhds_zero {E : Type*} (𝕜 : Type*) [NontriviallyNormedFi
eld 𝕜] [Zero E] [MulActionWithZero 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E
] {s : Set E} (hs : s in 𝓝 (0 : E)) : #s = #E
参数：𝕜 : Type*；hs : s in 𝓝 (0 : E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.Tendsto.smul_const`：Filter.Tendsto.smul_const {f : α -> M} {l : F
ilter α} {c : M} (hf : Tendsto f l (𝓝 c)) (a : X) : Tendsto (fun x => f x • a) l
 (𝓝 (c • a))
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
In a topological vector space over a nontrivially normed field, any neighborhood
 of zero has
the same cardinality as the whole space.

See also `cardinal_eq_of_mem_nhds`.
-/
lemma cardinal_eq_of_mem_nhds_zero
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [Zero E] [MulActionWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} (hs : s ∈ 𝓝 (0 : E)) : #s = #E := by
  /- As `s` is a neighborhood of `0`, the space is covered by the rescaled sets `c^n • s`,
  where `c` is any element of `𝕜` with norm `> 1`. All these sets are in bijection and have
  therefore the same cardinality. The conclusion follows. -/
  obtain ⟨c, hc⟩ : ∃ x : 𝕜, 1 < ‖x‖ := NormedField.exists_lt_norm 𝕜 1
  have cn_ne : ∀ n, c ^ n ≠ 0 := by
    intro n
    apply pow_ne_zero
    rintro rfl
    simp only [norm_zero] at hc
    exact lt_irrefl _ (hc.trans zero_lt_one)
  have A : ∀ (x : E), ∀ᶠ n in (atTop : Filter ℕ), x ∈ c ^ n • s := by
    intro x
    have : Tendsto (fun n ↦ (c ^ n)⁻¹ • x) atTop (𝓝 ((0 : 𝕜) • x)) := by
      have : Tendsto (fun n ↦ (c ^ n)⁻¹) atTop (𝓝 0) := by
        simp_rw [← inv_pow]
        apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hc
      exact Tendsto.smul_const this x
    rw [zero_smul] at this
    filter_upwards [this hs] with n (hn : (c ^ n)⁻¹ • x ∈ s)
    exact (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).2 hn
  have B : ∀ n, #(c ^ n • s :) = #s := by
    intro n
    have : (c ^ n • s :) ≃ s :=
    { toFun := fun x ↦ ⟨(c ^ n)⁻¹ • x.1, (mem_smul_set_iff_inv_smul_mem₀ (cn_ne n) _ _).1 x.2⟩
      invFun := fun x ↦ ⟨(c^n) • x.1, smul_mem_smul_set x.2⟩
      left_inv := fun x ↦ by simp [smul_smul, mul_inv_cancel₀ (cn_ne n)]
      right_inv := fun x ↦ by simp [smul_smul, inv_mul_cancel₀ (cn_ne n)] }
    exact Cardinal.mk_congr this
  apply (Cardinal.mk_of_countable_eventually_mem A B).symm

/-- In a topological vector space over a nontrivially normed field, any neighborhood of a point has
the same cardinality as the whole space. -/
/-
**cardinal_eq_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinal_eq_of_mem_nhds {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜
] [AddGroup E] [MulActionWithZero 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [C
ontinuousSMul 𝕜 E] {s : Set E} {x : E} (hs : s in 𝓝 x) : #s = #E
参数：𝕜 : Type*；hs : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `cardinal_eq_of_mem_nhds_zero`：cardinal_eq_of_mem_nhds_zero {E : Type*} (
𝕜 : Type*) [NontriviallyNormedField 𝕜] [Zero E] [MulActionWithZero 𝕜 E] [Topolog
icalSpace E] [Cont…
· 使用定理 `Cardinal.mk_subtype_of_equiv`：mk_subtype_of_equiv {α β : Type u} (p : β 
-> Prop) (e : α ≃ β) : #{ a : α // p (e a) } = #{ b : β // p b }

--- 原说明 ---
In a topological vector space over a nontrivially normed field, any neighborhood
 of a point has
the same cardinality as the whole space.
-/
theorem cardinal_eq_of_mem_nhds
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [AddGroup E] [MulActionWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} {x : E} (hs : s ∈ 𝓝 x) : #s = #E := by
  let g := Homeomorph.addLeft x
  let t := g ⁻¹' s
  have : t ∈ 𝓝 0 := g.continuous.continuousAt.preimage_mem_nhds (by simpa [g] using hs)
  have A : #t = #E := cardinal_eq_of_mem_nhds_zero 𝕜 this
  have B : #t = #s := Cardinal.mk_subtype_of_equiv (· ∈ s) g.toEquiv
  rwa [B] at A

/-- In a topological vector space over a nontrivially normed field, any nonempty open set has
the same cardinality as the whole space. -/
/-
**cardinal_eq_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinal_eq_of_isOpen {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] 
[AddGroup E] [MulActionWithZero 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [Con
tinuousSMul 𝕜 E] {s : Set E} (hs : IsOpen s) (h's : s.Nonempty) : #s = #E
参数：𝕜 : Type*；hs : IsOpen s；h's : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cardinal_eq_of_mem_nhds`：cardinal_eq_of_mem_nhds {E : Type*} (𝕜 : Type*)
 [NontriviallyNormedField 𝕜] [AddGroup E] [MulActionWithZero 𝕜 E] [TopologicalSp
ace E] [Conti…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
In a topological vector space over a nontrivially normed field, any nonempty ope
n set has
the same cardinality as the whole space.
-/
theorem cardinal_eq_of_isOpen
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [AddGroup E] [MulActionWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsOpen s) (h's : s.Nonempty) : #s = #E := by
  rcases h's with ⟨x, hx⟩
  exact cardinal_eq_of_mem_nhds 𝕜 (hs.mem_nhds hx)

/-- In a nontrivial topological vector space over a complete nontrivially normed field, any nonempty
open set has cardinality at least continuum. -/
/-
**continuum_le_cardinal_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuum_le_cardinal_of_isOpen {E : Type*} (𝕜 : Type*) [NontriviallyNorme
dField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nontrivial E] [Topolo
gicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E} (hs : IsOpen s)
 (h's : s.Nonempty) : 𝔠 <= #s
参数：𝕜 : Type*；hs : IsOpen s；h's : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cardinal_eq_of_isOpen`：cardinal_eq_of_isOpen {E : Type*} (𝕜 : Type*) [No
ntriviallyNormedField 𝕜] [AddGroup E] [MulActionWithZero 𝕜 E] [TopologicalSpace 
E] [Continu…
· 使用定理 `continuum_le_cardinal_of_module`：continuum_le_cardinal_of_module (𝕜 : Ty
pe u) (E : Type v) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E
] [Module 𝕜 E] [Nontr…

--- 原说明 ---
In a nontrivial topological vector space over a complete nontrivially normed fie
ld, any nonempty
open set has cardinality at least continuum.
-/
theorem continuum_le_cardinal_of_isOpen
    {E : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Nontrivial E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} (hs : IsOpen s) (h's : s.Nonempty) : 𝔠 ≤ #s := by
  simpa [cardinal_eq_of_isOpen 𝕜 hs h's] using continuum_le_cardinal_of_module 𝕜 E

/-- In a nontrivial topological vector space over a complete nontrivially normed field, any
countable set has dense complement. -/
/-
**Set.Countable.dense_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.dense_compl {E : Type u} (𝕜 : Type*) [NontriviallyNormedFiel
d 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nontrivial E] [Topological
Space E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] {s : Set E} (hs : s.Countable) :
 Dense sᶜ
参数：𝕜 : Type*；hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_eq_empty_iff_dense_compl`：interior_eq_empty_iff_dense_compl : i
nterior s = ∅ ↔ Dense sᶜ
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
· 使用定理 `continuum_le_cardinal_of_isOpen`：continuum_le_cardinal_of_isOpen {E : Ty
pe*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] 
[Module 𝕜 E] [Nontriv…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.notMem_singleton_empty`：notMem_singleton_empty {s : Set α} : s ∉ ({∅
} : Set (Set α)) ↔ s.Nonempty
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.Countable.le_aleph0`：∀ {α : Type u} {s : Set α}, s.Countable → Cardi
nal.mk ↑s ≤ Cardinal.aleph0

--- 原说明 ---
In a nontrivial topological vector space over a complete nontrivially normed fie
ld, any
countable set has dense complement.
-/
theorem Set.Countable.dense_compl
    {E : Type u} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Nontrivial E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s : Set E} (hs : s.Countable) : Dense sᶜ := by
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra H
  apply lt_irrefl (ℵ₀ : Cardinal.{u})
  calc
    (ℵ₀ : Cardinal.{u}) < 𝔠 := aleph0_lt_continuum
    _ ≤ #(interior s) :=
      continuum_le_cardinal_of_isOpen 𝕜 isOpen_interior (notMem_singleton_empty.1 H)
    _ ≤ #s := mk_le_mk_of_subset interior_subset
    _ ≤ ℵ₀ := le_aleph0 hs
