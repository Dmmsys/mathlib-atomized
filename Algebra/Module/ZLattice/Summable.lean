/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Analysis.PSeries

/-!
# Convergence of `p`-series on lattices

Let `E` be a finite dimensional normed `ℝ`-space, and `L` a discrete subgroup of `E` of rank `d`.
We show that `∑ z ∈ L, ‖z - x‖ʳ` is convergent for `r < -d`.

## Main results
- `ZLattice.summable_norm_rpow`: `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`.
- `ZLattice.summable_norm_sub_rpow`: `∑ z ∈ L, ‖z - x‖ʳ` converges when `r < -d`.
- `ZLattice.tsum_norm_rpow_le`:
  `∑ z ∈ L, ‖z‖ʳ ≤ Aʳ * ∑ k : ℕ, kᵈ⁺ʳ⁻¹` for some `A > 0` depending only on `L`.

-/

@[expose] public section

noncomputable section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
variable {ι : Type*} (b : Basis ι ℤ L)

namespace ZLattice

/-
**ZLattice.exists_forall_abs_repr_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：exists_forall_abs_repr_le_norm : exists (ε : Real), 0 < ε ∧ forall (x : L)
, forall i, ε * |b.repr x i| <= ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
（共 101 条，此处仅展示前 30 条）
-/
lemma exists_forall_abs_repr_le_norm :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : L), ∀ i, ε * |b.repr x i| ≤ ‖x‖ := by
  wlog H : IsZLattice ℝ L
  · let E' := Submodule.span ℝ (L : Set E)
    let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
    have inst : DiscreteTopology L' :=
      comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
      Submodule.subset_span
    have inst : IsZLattice ℝ L' :=
      ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
    obtain ⟨ε, hε, H⟩ := this (b.map e.symm) inst
    exact ⟨ε, hε, fun x i ↦ by simpa using! H ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2⟩ i⟩
  have : Finite ι := Module.Finite.finite_basis b
  let b' : Basis ι ℝ E := Basis.ofZLatticeBasis ℝ L b
  let e := ((b'.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).toContinuousLinearEquiv (𝕜 := ℝ))
  have := e.continuous.1 (Set.univ.pi fun _ ↦ Set.Ioo (-1) 1)
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp this 0 (by simp)
  refine ⟨ε / 2, by positivity, fun x i ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hx : ‖x.1‖ ≠ 0 := by simpa
  have : |ε / 2 * (‖↑x‖⁻¹ * (b.repr x) i)| < 1 := by
    simpa [e, b', ← abs_lt] using! @hε' ((ε / 2) • ‖x‖⁻¹ • x)
      (by simpa [norm_smul, inv_mul_cancel₀ hx, abs_eq_self.mpr hε.le]) i trivial
  rw [abs_mul, abs_mul, abs_inv, mul_left_comm, abs_norm, inv_mul_lt_iff₀ (by positivity),
    mul_one, abs_eq_self.mpr (by positivity), ← Int.cast_abs] at this
  exact this.le

/--
Given a basis of a (possibly not full rank) `ℤ`-lattice, there exists a `ε > 0` such that
`|b.repr x i| < n` for all `‖x‖ < n * ε` (i.e. `b.repr x i = O(x)` depending only on `b`).
This is an arbitrary choice of such an `ε`.
-/
/-
**ZLattice.normBound** 是 Mathlib 中的一个定义，位于命名空间 `ZLattice`。
形式化陈述：normBound {ι : Type*} (b : Basis ι Int L) : Real
参数：b : Basis ι Int L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ZLattice.exists_forall_abs_repr_le_norm`：exists_forall_abs_repr_le_norm 
: exists (ε : Real), 0 < ε ∧ forall (x : L), forall i, ε * |b.repr x i| <= ‖x‖

--- 原说明 ---
Given a basis of a (possibly not full rank) `ℤ`-lattice, there exists a `ε > 0` 
such that
`|b.repr x i| < n` for all `‖x‖ < n * ε` (i.e. `b.repr x i = O(x)` depending onl
y on `b`).
This is an arbitrary choice of such an `ε`.
-/
def normBound {ι : Type*} (b : Basis ι ℤ L) : ℝ :=
  (exists_forall_abs_repr_le_norm b).choose
/-
**ZLattice.normBound_pos** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：normBound_pos {ι : Type*} (b : Basis ι Int L) : 0 < normBound b
参数：b : Basis ι Int L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ZLattice.exists_forall_abs_repr_le_norm`：exists_forall_abs_repr_le_norm 
: exists (ε : Real), 0 < ε ∧ forall (x : L), forall i, ε * |b.repr x i| <= ‖x‖
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma normBound_pos {ι : Type*} (b : Basis ι ℤ L) : 0 < normBound b :=
  (exists_forall_abs_repr_le_norm b).choose_spec.1
/-
**ZLattice.normBound_spec** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：normBound_spec {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι) : normBound
 b * |b.repr x i| <= ‖x‖
参数：b : Basis ι Int L；x : L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ZLattice.exists_forall_abs_repr_le_norm`：exists_forall_abs_repr_le_norm 
: exists (ε : Real), 0 < ε ∧ forall (x : L), forall i, ε * |b.repr x i| <= ‖x‖
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma normBound_spec {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    normBound b * |b.repr x i| ≤ ‖x‖ :=
  (exists_forall_abs_repr_le_norm b).choose_spec.2 x i
/-
**ZLattice.abs_repr_le** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：abs_repr_le {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι) : |b.repr x i|
 <= (normBound b)⁻¹ * ‖x‖
参数：b : Basis ι Int L；x : L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_inv_mul_iff₀`：le_inv_mul_iff₀ (hc : 0 < c) : a <= c⁻¹ * b ↔ c * a <= 
b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `ZLattice.normBound_pos`：normBound_pos {ι : Type*} (b : Basis ι Int L) : 
0 < normBound b
· 使用引理 `ZLattice.normBound_spec`：normBound_spec {ι : Type*} (b : Basis ι Int L) 
(x : L) (i : ι) : normBound b * |b.repr x i| <= ‖x‖
-/
lemma abs_repr_le {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    |b.repr x i| ≤ (normBound b)⁻¹ * ‖x‖ := by
  rw [le_inv_mul_iff₀ (normBound_pos b)]
  exact normBound_spec b x i
/-
**ZLattice.abs_repr_lt_of_norm_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：abs_repr_lt_of_norm_lt {ι : Type*} (b : Basis ι Int L) (x : L) (n : Nat) (
hxn : ‖x‖ < normBound b * n) (i : ι) : |b.repr x i| < n
参数：b : Basis ι Int L；x : L；n : Nat；hxn : ‖x‖ < normBound b * n；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `ZLattice.abs_repr_le`：abs_repr_le {ι : Type*} (b : Basis ι Int L) (x : L
) (i : ι) : |b.repr x i| <= (normBound b)⁻¹ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_mul_lt_iff₀`：inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `ZLattice.normBound_pos`：normBound_pos {ι : Type*} (b : Basis ι Int L) : 
0 < normBound b
-/
lemma abs_repr_lt_of_norm_lt {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ)
    (hxn : ‖x‖ < normBound b * n) (i : ι) : |b.repr x i| < n := by
  refine Int.cast_lt.mp ((abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (normBound_pos b)]
/-
**ZLattice.le_norm_of_le_abs_repr** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：le_norm_of_le_abs_repr {ι : Type*} (b : Basis ι Int L) (x : L) (n : Nat) (
i : ι) (hi : n <= |b.repr x i|) : normBound b * n <= ‖x‖
参数：b : Basis ι Int L；x : L；n : Nat；i : ι；hi : n <= |b.repr x i|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ZLattice.abs_repr_lt_of_norm_lt`：abs_repr_lt_of_norm_lt {ι : Type*} (b :
 Basis ι Int L) (x : L) (n : Nat) (hxn : ‖x‖ < normBound b * n) (i : ι) : |b.rep
r x i| < n
-/
lemma le_norm_of_le_abs_repr {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ) (i : ι)
    (hi : n ≤ |b.repr x i|) : normBound b * n ≤ ‖x‖ := by
  contrapose! hi
  exact abs_repr_lt_of_norm_lt b x n hi i

open Finset in
/-
**ZLattice.sum_piFinset_Icc_rpow_le** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basi
s ι Int L) {d : Nat} (hd : d = Fintype.card ι) (n : Nat) (r : Real) (hr : r < -d
) : ∑ p in Fintype.piFinset fun _ : ι => Icc (-n : Int) n, ‖∑ i, p i • b i‖ ^ r 
<= 2 * d * 3 ^ (d - 1) * normBound b ^ r * ∑' k : Nat, (k : Real) ^ (d - 1 + r)
参数：b : Basis ι Int L；hd : d = Fintype.card ι；n : Nat；r : Real；hr : r < -d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 181 条，此处仅展示前 30 条）
-/
lemma sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) {d : ℕ} (hd : d = Fintype.card ι)
    (n : ℕ) (r : ℝ) (hr : r < -d) :
    ∑ p ∈ Fintype.piFinset fun _ : ι ↦ Icc (-n : ℤ) n, ‖∑ i, p i • b i‖ ^ r ≤
      2 * d * 3 ^ (d - 1) * normBound b ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
  let s (n : ℕ) := Fintype.piFinset fun i : ι ↦ Icc (-n : ℤ) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    simp [hd, hr'.ne]
  replace hd : 1 ≤ d := by rwa [Nat.one_le_iff_ne_zero]
  have hs0 : s 0 = {0} := by ext; simp [s, funext_iff]
  have hs {a b : ℕ} (ha : a ≤ b) : s a ⊆ s b := by grind
  have (k : ℕ) : #(s (k + 1) \ s k) ≤ 2 * d * (2 * k + 3) ^ (d - 1) := by
    simp only [le_add_iff_nonneg_right, zero_le, hs, card_sdiff_of_subset, s, Fintype.card_piFinset,
      Int.card_Icc, prod_const]
    grind [abs_pow_sub_pow_le (α := ℤ) (2 * k + 3) (2 * k + 1) d]
  let ε := normBound b
  have hε : 0 < ε := normBound_pos b
  calc ∑ p ∈ s n, ‖∑ i, p i • b i‖ ^ r
      = ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ‖∑ i, p i • b i‖ ^ r := by
        simp [Finset.sum_eq_sum_range_sdiff _ @hs, hs0, hr'.ne]
    _ ≤ ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ((k + 1) * ε) ^ r := by
        gcongr ∑ k ∈ Finset.range n, ∑ p ∈ (s (k + 1) \ s k), ?_ with k hk v hv
        rw [← Nat.cast_one, ← Nat.cast_add]
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr'.le
        obtain ⟨j, hj⟩ : ∃ i, v i ∉ Icc (-k : ℤ) k := by simpa [s] using (mem_sdiff.mp hv).2
        refine mul_comm _ ε ▸ le_norm_of_le_abs_repr b _ _ j ?_
        suffices ↑k + 1 ≤ |v j| by simpa [Finsupp.single_apply] using this
        by_contra! H
        rw [Int.lt_add_one_iff, abs_le, ← Finset.mem_Icc] at H
        exact hj H
    _ ≤ ∑ k ∈ range n, ↑(2 * d * (3 * (k + 1)) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr with k hk
        refine (this _).trans ?_
        gcongr
        lia
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (k + 1) ^ (d - 1) * (k + 1 : ℝ) ^ r := by
        simp_rw [Finset.mul_sum]
        congr with k
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity), mul_pow]
        group
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (↑(k + 1) : ℝ) ^ (d - 1 + r) := by
        congr with k
        rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), Nat.cast_sub hd]
        norm_cast
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range (n + 1), (k : ℝ) ^ (d - 1 + r) := by
        grw [Finset.sum_range_succ', Nat.cast_zero, ← Real.rpow_nonneg le_rfl, add_zero]
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
        gcongr
        refine Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) (Real.summable_nat_rpow.mpr ?_)
        linarith

variable (L)

set_option backward.isDefEq.respectTransparency.types false in
/-
**ZLattice.exists_finsetSum_norm_rpow_le_tsum** 是 Mathlib 中的一个引理，位于命名空间 `ZLattic
e`。
形式化陈述：exists_finsetSum_norm_rpow_le_tsum : exists A > (0 : Real), forall r < (-M
odule.finrank Int L : Real), forall s : Finset L, ∑ z in s, ‖z‖ ^ r <= A ^ r * ∑
' k : Nat, (k : Real) ^ (Module.finrank Int L - 1 + r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
（共 125 条，此处仅展示前 30 条）
-/
lemma exists_finsetSum_norm_rpow_le_tsum :
    ∃ A > (0 : ℝ), ∀ r < (-Module.finrank ℤ L : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) := by
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s ↦ ?_⟩
    have hr : r ≠ 0 := by linarith
    simpa [Subsingleton.elim _ (0 : L), Real.zero_rpow hr] using tsum_nonneg fun _ ↦ by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex ℤ L
  have : Fintype I := inferInstance
  let b : Basis I ℤ L := Module.Free.chooseBasis ℤ L
  simp_rw [Module.finrank_eq_card_basis b]
  set d := Fintype.card I
  have hd : d ≠ 0 := by simp [d]
  let ε := normBound b
  obtain ⟨A, hA, B, hB, H⟩ : ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ r < (-d : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A * B ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
    refine ⟨2 * d * 3 ^ (d - 1), by positivity, ε, normBound_pos b, fun r hr u ↦ ?_⟩
    let e : (I → ℤ) ≃ₗ[ℤ] L := (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).symm
    obtain ⟨u, rfl⟩ : ∃ u' : Finset _, u = u'.image e.toEmbedding :=
      ⟨u.image e.symm.toEmbedding, Finset.coe_injective
        (by simpa using (e.image_symm_image _).symm)⟩
    dsimp
    simp only [EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq,
      Finset.sum_image, ge_iff_le]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ⊆ Fintype.piFinset fun _ : I ↦ Finset.Icc (-n : ℤ) n := by
      obtain ⟨r, hr, hr'⟩ := u.finite_toSet.isCompact.isBounded.subset_closedBall_lt 0 0
      refine ⟨⌊r⌋.toNat, fun x hx ↦ ?_⟩
      have hr'' : ⌊r⌋ ⊔ 0 = ⌊r⌋ := by rw [sup_eq_left]; positivity
      have := hr' hx
      simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le,
        Int.norm_eq_abs, ← Int.cast_abs, ← Int.le_floor] at this
      simpa only [Int.ofNat_toNat, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le, hr'']
    refine (Finset.sum_le_sum_of_subset_of_nonneg hn (by intros; positivity)).trans ?_
    simp only [Submodule.norm_coe]
    convert! sum_piFinset_Icc_rpow_le b rfl n r hr with x
    simp [e, Finsupp.linearCombination]
  by_cases hA' : A ≤ 1
  · refine ⟨B, hB, fun r hr s ↦ (H r hr s).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (by positivity)) hA'
  · refine ⟨A⁻¹ * B, mul_pos (inv_pos.mpr hA) hB, fun r hr s ↦ (H r hr s).trans ?_⟩
    rw [Real.mul_rpow (inv_pos.mpr hA).le hB.le, mul_assoc, mul_assoc]
    gcongr
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hA.le]
    refine Real.self_le_rpow_of_one_le (not_le.mp hA').le ?_
    simp only [neg_mul, one_mul, le_neg (b := r)]
    refine hr.le.trans ?_
    simpa [Nat.one_le_iff_ne_zero]

/--
Let `L` be a lattice with (possibly non-full) rank `d`, and `r : ℝ` such that `d < r`.
Then `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`.
This is an arbitrary choice of `A`. See `ZLattice.tsum_norm_rpow_le`.
-/
/-
**ZLattice.tsumNormRPowBound** 是 Mathlib 中的一个定义，位于命名空间 `ZLattice`。
形式化陈述：tsumNormRPowBound : Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ZLattice.exists_finsetSum_norm_rpow_le_tsum`：exists_finsetSum_norm_rpow_
le_tsum : exists A > (0 : Real), forall r < (-Module.finrank Int L : Real), fora
ll s : Finset L, ∑ z in s, ‖z‖ ^ …

--- 原说明 ---
Let `L` be a lattice with (possibly non-full) rank `d`, and `r : ℝ` such that `d
 < r`.
Then `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on
 `L`.
This is an arbitrary choice of `A`. See `ZLattice.tsum_norm_rpow_le`.
-/
def tsumNormRPowBound : ℝ :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose
/-
**ZLattice.tsumNormRPowBound_pos** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：tsumNormRPowBound_pos : 0 < tsumNormRPowBound L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ZLattice.exists_finsetSum_norm_rpow_le_tsum`：exists_finsetSum_norm_rpow_
le_tsum : exists A > (0 : Real), forall r < (-Module.finrank Int L : Real), fora
ll s : Finset L, ∑ z in s, ‖z‖ ^ …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma tsumNormRPowBound_pos : 0 < tsumNormRPowBound L :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.1
/-
**ZLattice.tsumNormRPowBound_spec** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：tsumNormRPowBound_spec (r : Real) (h : r < -Module.finrank Int L) (s : Fin
set L) : ∑ z in s, ‖z‖ ^ r <= tsumNormRPowBound L ^ r * ∑' k : Nat, (k : Real) ^
 (Module.finrank Int L - 1 + r)
参数：r : Real；h : r < -Module.finrank Int L；s : Finset L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ZLattice.exists_finsetSum_norm_rpow_le_tsum`：exists_finsetSum_norm_rpow_
le_tsum : exists A > (0 : Real), forall r < (-Module.finrank Int L : Real), fora
ll s : Finset L, ∑ z in s, ‖z‖ ^ …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma tsumNormRPowBound_spec (r : ℝ) (h : r < -Module.finrank ℤ L) (s : Finset L) :
    ∑ z ∈ s, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.2 r h s

/-- If `L` is a `ℤ`-lattice with rank `d` in `E`, then `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`. -/
/-
**ZLattice.summable_norm_rpow** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：summable_norm_rpow (r : Real) (hr : r < -Module.finrank Int L) : Summable 
fun z : L => ‖z‖ ^ r
参数：r : Real；hr : r < -Module.finrank Int L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_sum_le`：summable_of_sum_le {ι : Type*} {f : ι -> Real} {c : 
Real} (hf : 0 <= f) (h : forall u : Finset ι, ∑ x in u, f x <= c) : Summable f
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `ZLattice.tsumNormRPowBound_spec`：tsumNormRPowBound_spec (r : Real) (h : 
r < -Module.finrank Int L) (s : Finset L) : ∑ z in s, ‖z‖ ^ r <= tsumNormRPowBou
nd L ^ r * ∑' k : Nat…

--- 原说明 ---
If `L` is a `ℤ`-lattice with rank `d` in `E`, then `∑ z ∈ L, ‖z‖ʳ` converges whe
n `r < -d`.
-/
lemma summable_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ r :=
  summable_of_sum_le (fun _ ↦ by positivity) (tsumNormRPowBound_spec L r hr)

/-- `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`. -/
/-
**ZLattice.tsum_norm_rpow_le** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：tsum_norm_rpow_le (r : Real) (hr : r < -Module.finrank Int L) : ∑' z : L, 
‖z‖ ^ r <= tsumNormRPowBound L ^ r * ∑' k : Nat, (k : Real) ^ (Module.finrank In
t L - 1 + r)
参数：r : Real；hr : r < -Module.finrank Int L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_of_sum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : Summati
onFilter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topologic
alSpace α] [Orde…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `ZLattice.summable_norm_rpow`：summable_norm_rpow (r : Real) (hr : r < -Mo
dule.finrank Int L) : Summable fun z : L => ‖z‖ ^ r
· 使用引理 `ZLattice.tsumNormRPowBound_spec`：tsumNormRPowBound_spec (r : Real) (h : 
r < -Module.finrank Int L) (s : Finset L) : ∑ z in s, ‖z‖ ^ r <= tsumNormRPowBou
nd L ^ r * ∑' k : Nat…

--- 原说明 ---
`∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`.
-/
lemma tsum_norm_rpow_le (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    ∑' z : L, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (tsumNormRPowBound_spec L r hr)

set_option backward.isDefEq.respectTransparency false in
/-
**ZLattice.summable_norm_sub_rpow** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：summable_norm_sub_rpow (r : Real) (hr : r < -Module.finrank Int L) (x : E)
 : Summable fun z : L => ‖z - x‖ ^ r
参数：r : Real；hr : r < -Module.finrank Int L；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Summable.of_finite`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [Finite β] [L.HasSu
pport] {…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
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
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.preimage_embedding`：∀ {α : Type u} {β : Type v} {s : Set β} (
f : α ↪ β), s.Finite → (⇑f ⁻¹' s).Finite
· 使用定理 `Metric.finite_isBounded_inter_isClosed`：Metric.finite_isBounded_inter_is
Closed [ProperSpace α] {K s : Set α} (hsd : IsDiscrete s) (hK : IsBounded K) (hs
 : IsClosed s) : Set.Finite …
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用引理 `DiscreteTopology.isDiscrete`：DiscreteTopology.isDiscrete [DiscreteTopolo
gy s] : IsDiscrete s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 129 条，此处仅展示前 30 条）
-/
lemma summable_norm_sub_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ r := by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  refine ((Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * ‖x‖)) H).preimage_embedding
    (.subtype _)).subset ?_
  intro t ht
  by_cases ht₁ : ‖t‖ = 0
  · simp [show t = 0 by simpa using ht₁]
  by_cases ht₂ : ‖t - x‖ = 0
  · simpa [show t = x by simpa [sub_eq_zero] using ht₂, two_mul] using t.2
  have : 0 < Module.finrank ℤ L := Module.finrank_pos
  have : ‖t - x‖ < 2⁻¹ * ‖t‖ := by
    rw [← Real.rpow_lt_rpow_iff_of_neg (by positivity) (by positivity) (hr.trans (by simpa))]
    simpa [Real.mul_rpow, abs_eq_self.mpr (show 0 ≤ ‖t - x‖ ^ r by positivity)] using ht
  have := (norm_sub_norm_le _ _).trans_lt this
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', AddSubgroupClass.coe_norm] at this
  simpa using show ‖t.1‖ ≤ 2 * ‖x‖ by linarith
/-
**ZLattice.summable_norm_sub_zpow** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：summable_norm_sub_zpow (n : Int) (hn : n < -Module.finrank Int L) (x : E) 
: Summable fun z : L => ‖z - x‖ ^ n
参数：n : Int；hn : n < -Module.finrank Int L；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用引理 `ZLattice.summable_norm_sub_rpow`：summable_norm_sub_rpow (r : Real) (hr :
 r < -Module.finrank Int L) (x : E) : Summable fun z : L => ‖z - x‖ ^ r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma summable_norm_sub_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ n :=
  mod_cast summable_norm_sub_rpow L n (mod_cast hn) x
/-
**ZLattice.summable_norm_zpow** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：summable_norm_zpow (n : Int) (hn : n < -Module.finrank Int L) : Summable f
un z : L => ‖z‖ ^ n
参数：n : Int；hn : n < -Module.finrank Int L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `ZLattice.summable_norm_sub_zpow`：summable_norm_sub_zpow (n : Int) (hn : 
n < -Module.finrank Int L) (x : E) : Summable fun z : L => ‖z - x‖ ^ n
-/
lemma summable_norm_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ n := by
  simpa using summable_norm_sub_zpow L n hn 0
/-
**ZLattice.summable_norm_sub_inv_pow** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：summable_norm_sub_inv_pow (n : Nat) (hn : Module.finrank Int L < n) (x : E
) : Summable fun z : L => ‖z - x‖⁻¹ ^ n
参数：n : Nat；hn : Module.finrank Int L < n；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `ZLattice.summable_norm_sub_zpow`：summable_norm_sub_zpow (n : Int) (hn : 
n < -Module.finrank Int L) (x : E) : Summable fun z : L => ‖z - x‖ ^ n
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
-/
lemma summable_norm_sub_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) (x : E) :
    Summable fun z : L ↦ ‖z - x‖⁻¹ ^ n := by
  simpa using summable_norm_sub_zpow L (-n) (by gcongr) x
/-
**ZLattice.summable_norm_pow_inv** 是 Mathlib 中的一个引理，位于命名空间 `ZLattice`。
形式化陈述：summable_norm_pow_inv (n : Nat) (hn : Module.finrank Int L < n) : Summable
 fun z : L => ‖z‖⁻¹ ^ n
参数：n : Nat；hn : Module.finrank Int L < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `ZLattice.summable_norm_sub_inv_pow`：summable_norm_sub_inv_pow (n : Nat) 
(hn : Module.finrank Int L < n) (x : E) : Summable fun z : L => ‖z - x‖⁻¹ ^ n
-/
lemma summable_norm_pow_inv (n : ℕ) (hn : Module.finrank ℤ L < n) :
    Summable fun z : L ↦ ‖z‖⁻¹ ^ n := by
  simpa using summable_norm_sub_inv_pow L n hn 0

end ZLattice

