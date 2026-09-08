/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Disjoint

import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Data.Int.LeastGreatest

/-!
# The real numbers are an Archimedean floor ring, and a conditionally complete linear order.

-/

@[expose] public section

assert_not_exists Finset

open scoped Pointwise
open CauSeq

namespace Real
variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}

/-
**Real.instArchimedean** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instArchimedean : Archimedean Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `archimedean_iff_rat_le`：archimedean_iff_rat_le : Archimedean K ↔ forall 
x : K, exists q : Rat, x <= q
· 使用定理 `Real.ind_mk`：∀ {C : ℝ → Prop} (x : ℝ), (∀ (y : CauSeq ℚ abs), C (Real.mk
 y)) → C x
· 使用定理 `CauSeq.bounded'`：bounded' (f : CauSeq β abv) (x : α) : exists r > x, for
all i, abv (f i) < r
· 使用定理 `Real.mk_le_of_forall_le`：mk_le_of_forall_le {f : CauSeq Rat abs} {x : Re
al} (h : exists i, forall j >= i, (f j : Real) <= x) : mk f <= x
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _
/-
**Real.isCauSeq_iff_lift** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isCauSeq_iff_lift {f : Nat -> Rat} : IsCauSeq abs f ↔ IsCauSeq abs fun i =
> (f i : Real) where mp H ε ε0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pos_rat_lt`：exists_pos_rat_lt {x : K} (x0 : 0 < x) : exists q : R
at, 0 < q ∧ (q : K) < x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_pos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linear
Order K] [IsStrictOrderedRing K], 0 < ↑q ↔ 0 < q
-/
theorem isCauSeq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) where
  mp H ε ε0 :=
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij
/-
**Real.of_near** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：of_near (f : Nat -> Rat) (x : Real) (h : forall ε > 0, exists i, forall j 
>= i, |(f j : Real) - x| < ε) : exists h', Real.mk ⟨f, h'⟩ = x
参数：f : Nat -> Rat；x : Real；h : forall ε > 0, exists i, forall j >= i, |(f j : Re
al) - x| < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.isCauSeq_iff_lift`：isCauSeq_iff_lift {f : Nat -> Rat} : IsCauSeq ab
s f ↔ IsCauSeq abs fun i => (f i : Real) where mp H ε ε0
· 使用定理 `CauSeq.of_near`：of_near (f : Nat -> β) (g : CauSeq β abv) (h : forall ε 
> 0, exists i, forall j >= i, abv (f j - g j) < ε) : IsCauSeq abv f | ε, ε0 => l
et ⟨…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `abs_eq_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| = 0 ↔ a = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `eq_of_le_of_forall_lt_imp_le_of_dense`：eq_of_le_of_forall_lt_imp_le_of_d
ense (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ < a -> a₁ <= a) : a₁ = a₂
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
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Real.mk_near_of_forall_near`：mk_near_of_forall_near {f : CauSeq Rat abs}
 {x : Real} {ε : Real} (H : exists i, forall j >= i, |(f j : Real) - x| <= ε) : 
|mk f - x| <= ε
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩

@[deprecated _root_.exists_floor (since := "2026-01-29")]
/-
**Real.exists_floor** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_floor (x : Real) : exists ub : Int, (ub : Real) <= x ∧ forall z : I
nt, (z : Real) <= x -> z <= ub
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.le_floor`：le_floor : z <= ⌊a⌋ ↔ (z : α) <= a
-/
theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  ⟨⌊x⌋, Int.floor_le x, fun _ ↦ Int.le_floor.mpr⟩
/-
**Real.exists_isLUB** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) : exists x, IsLUB s x
参数：hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_int_gt`：exists_int_gt (x : R) : exists n : Int, x < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Int.sub_one_lt_floor`：sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
（共 73 条，此处仅展示前 30 条）
-/
theorem exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    gcongr
    exact (hU yS).trans hk.le
  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀ n > 0, ∃ y ∈ s, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀ n > 0, ∀ y ∈ s, (y - ((n : ℕ) : ℝ)⁻¹) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, gt_iff_lt]
    rwa [lt_div_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, inv_mul_cancel₀]
    exact (Nat.cast_pos.2 n0).ne'
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) := by
    intro ε ε0
    suffices ∀ j ≥ ⌈ε⁻¹⌉₊, ∀ k ≥ ⌈ε⁻¹⌉₊, (f j / j - f k / k : ℚ) < ε by
      refine ⟨_, fun j ij => abs_lt.2 ⟨?_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine lt_of_lt_of_le ((Rat.cast_lt (K := ℝ)).1 ?_) ((inv_le_comm₀ ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine ⟨mk g, ⟨fun x xS => ?_, fun y h => ?_⟩⟩
  · refine le_of_forall_lt_imp_le_of_dense fun z xz => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (x - z)⁻¹
    refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine le_trans ?_ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le_comm₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩

/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
/-
**Real.exists_isGLB** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_isGLB (hne : s.Nonempty) (hbdd : BddBelow s) : exists x, IsGLB s x
参数：hne : s.Nonempty；hbdd : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set α},
 (-s).Nonempty ↔ s.Nonempty
· 使用定理 `bddAbove_neg`：∀ {G : Type u_2} [inst : AddGroup G] [inst_1 : Preorder G]
 [AddLeftMono G] [AddRightMono G] {s : Set G},   BddAbove (-s) ↔ BddBelow s
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.exists_isLUB`：exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) :
 exists x, IsLUB s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLUB_neg`：∀ {G : Type u_2} [inst : AddGroup G] [inst_1 : Preorder G] [A
ddLeftMono G] [AddRightMono G] {s : Set G} {a : G},   IsLUB (-s) a ↔ IsGLB s (-…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A nonempty, bounded below set of real numbers has a greatest lower bound.
-/
theorem exists_isGLB (hne : s.Nonempty) (hbdd : BddBelow s) : ∃ x, IsGLB s x := by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

open scoped Classical in
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SupSet ℝ :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

open scoped Classical in
/-
**Real.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sSup_def (s : Set Real) : sSup s = if h : s.Nonempty ∧ BddAbove s then Cla
ssical.choose (exists_isLUB h.1 h.2) else 0
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_def (s : Set ℝ) :
    sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl
/-
**Real.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {s : Set ℝ}, s.Nonempty → BddAbove s → IsLUB s (sSup s)
参数：sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exists_isLUB`：exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) :
 exists x, IsLUB s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem isLUB_sSup (h₁ : s.Nonempty) (h₂ : BddAbove s) : IsLUB s (sSup s) := by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : InfSet ℝ :=
  ⟨fun s => -sSup (-s)⟩
/-
**Real.sInf_def** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_def (s : Set Real) : sInf s = -sSup (-s)
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_def (s : Set ℝ) : sInf s = -sSup (-s) := rfl
/-
**Real.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {s : Set ℝ}, s.Nonempty → BddBelow s → IsGLB s (sInf s)
参数：sInf s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sInf_def`：sInf_def (s : Set Real) : sInf s = -sSup (-s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLUB_neg'`：∀ {G : Type u_2} [inst : AddGroup G] [inst_1 : Preorder G] [
AddLeftMono G] [AddRightMono G] {s : Set G} {a : G},   IsLUB (-s) (-a) ↔ IsGLB s
…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.isLUB_sSup`：∀ {s : Set ℝ}, s.Nonempty → BddAbove s → IsLUB s (sSup 
s)
· 使用定理 `Set.Nonempty.neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set α},
 s.Nonempty → (-s).Nonempty
· 使用定理 `BddBelow.neg`：∀ {G : Type u_2} [inst : AddGroup G] [inst_1 : Preorder G]
 [AddLeftMono G] [AddRightMono G] {s : Set G},   BddBelow s → BddAbove (-s)
-/
protected theorem isGLB_sInf (h₁ : s.Nonempty) (h₂ : BddBelow s) : IsGLB s (sInf s) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ConditionallyCompleteLinearOrder ℝ where
  __ := Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]
/-
**Real.lt_sInf_add_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_sInf_add_pos (h : s.Nonempty) {ε : Real} (hε : 0 < ε) : exists a in s, 
a < sInf s + ε
参数：h : s.Nonempty；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem lt_sInf_add_pos (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) : ∃ a ∈ s, a < sInf s + ε :=
  exists_lt_of_csInf_lt h <| lt_add_of_pos_right _ hε
/-
**Real.add_neg_lt_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：add_neg_lt_sSup (h : s.Nonempty) {ε : Real} (hε : ε < 0) : exists a in s, 
sSup s + ε < a
参数：h : s.Nonempty；hε : ε < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_lt_iff_neg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] {a b : α},   a + b < a ↔ b < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem add_neg_lt_sSup (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) : ∃ a ∈ s, sSup s + ε < a :=
  exists_lt_of_lt_csSup h <| add_lt_iff_neg_left.2 hε
/-
**Real.sInf_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_le_iff (h : BddBelow s) (h' : s.Nonempty) : sInf s <= a ↔ forall ε, 0
 < ε -> exists x in s, x < a + ε
参数：h : BddBelow s；h' : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_forall_pos_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : L
inearOrder α] [AddLeftMono α] {a b : α},   a ≤ b ↔ ∀ (ε : α), 0 < ε → a < b + ε
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `csInf_lt_of_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → a ∈ s → a < b → sInf s < b
-/
theorem sInf_le_iff (h : BddBelow s) (h' : s.Nonempty) :
    sInf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx
/-
**Real.le_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_sSup_iff (h : BddAbove s) (h' : s.Nonempty) : a <= sSup s ↔ forall ε, ε
 < 0 -> exists x in s, a + ε < x
参数：h : BddAbove s；h' : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_forall_pos_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : L
inearOrder α] [AddLeftMono α] {a b : α},   a ≤ b ↔ ∀ (ε : α), 0 < ε → a < b + ε
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `lt_csSup_of_lt`：lt_csSup_of_lt (hs : BddAbove s) (ha : a in s) (h : b < 
a) : b < sSup s
-/
theorem le_sSup_iff (h : BddAbove s) (h' : s.Nonempty) :
    a ≤ sSup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in hx)

@[simp]
/-
**Real.sSup_empty** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sSup_empty : sSup (∅ : Set Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem sSup_empty : sSup (∅ : Set ℝ) = 0 :=
  dif_neg <| by simp
/-
**Real.sInf_univ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_univ : sInf (@Set.univ Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csInf_of_not_bddBelow`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α}, ¬BddBelow s → sInf s = sInf ∅
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_univ : sInf (@Set.univ ℝ) = 0 := by
  simp [sInf_def]
/-
**Real.iSup_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i = 0
参数：f : ι → ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_empty_iff`：range_eq_empty_iff {f : ι -> α} : range f = ∅ ↔ 
IsEmpty ι
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
-/
@[simp] lemma iSup_of_isEmpty [IsEmpty ι] (f : ι → ℝ) : ⨆ i, f i = 0 := by
  dsimp [iSup]
  convert! Real.sSup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance

@[simp]
/-
**Real.iSup_const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iSup_const_zero : ⨆ _ : ι, (0 : Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
-/
theorem iSup_const_zero : ⨆ _ : ι, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact Real.iSup_of_isEmpty _
  · exact ciSup_const
/-
**Real.sSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = 0
参数：hs : ¬BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = 0 := dif_neg fun h => hs h.2
/-
**Real.iSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_of_not_bddAbove (hf : ¬BddAbove (Set.range f)) : ⨆ i, f i = 0
参数：hf : ¬BddAbove (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
-/
lemma iSup_of_not_bddAbove (hf : ¬BddAbove (Set.range f)) : ⨆ i, f i = 0 := sSup_of_not_bddAbove hf
/-
**Real.sSup_univ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sSup_univ : sSup (@Set.univ Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
· 使用定理 `not_bddAbove_univ`：not_bddAbove_univ [NoTopOrder α] : ¬BddAbove (univ : 
Set α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem sSup_univ : sSup (@Set.univ ℝ) = 0 := Real.sSup_of_not_bddAbove not_bddAbove_univ

@[simp]
/-
**Real.sInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_empty : sInf (∅ : Set Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_empty : sInf (∅ : Set ℝ) = 0 := by simp [sInf_def, sSup_empty]

@[simp] nonrec lemma iInf_of_isEmpty [IsEmpty ι] (f : ι → ℝ) : ⨅ i, f i = 0 := by
  rw [iInf_of_isEmpty, sInf_empty]

@[simp]
/-
**Real.iInf_const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iInf_const_zero : ⨅ _ : ι, (0 : Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Real.iInf_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨅ i, f i
 = 0
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
-/
theorem iInf_const_zero : ⨅ _ : ι, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const
/-
**Real.sInf_of_not_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sInf s = 0
参数：hs : ¬BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddAbove_neg`：∀ {G : Type u_2} [inst : AddGroup G] [inst_1 : Preorder G]
 [AddLeftMono G] [AddRightMono G] {s : Set G},   BddAbove (-s) ↔ BddBelow s
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem sInf_of_not_bddBelow (hs : ¬BddBelow s) : sInf s = 0 :=
  neg_eq_zero.2 <| sSup_of_not_bddAbove <| mt bddAbove_neg.1 hs
/-
**Real.iInf_of_not_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iInf_of_not_bddBelow (hf : ¬BddBelow (Set.range f)) : ⨅ i, f i = 0
参数：hf : ¬BddBelow (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sInf_of_not_bddBelow`：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sIn
f s = 0
-/
theorem iInf_of_not_bddBelow (hf : ¬BddBelow (Set.range f)) : ⨅ i, f i = 0 :=
  sInf_of_not_bddBelow hf

@[simp]
/-
**Real.sSup_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sSup_neg (s : Set Real) : sSup (-s) = -sInf s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csSup_neg`：∀ {M : Type u_1} [inst : ConditionallyCompleteLattice M] [ins
t_1 : AddGroup M] [AddLeftMono M] [AddRightMono M]   {s : Set M}, s.Nonempty → …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `csInf_of_not_bddBelow`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α}, ¬BddBelow s → sInf s = sInf ∅
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `bddAbove_neg`：∀ {G : Type u_2} [inst : AddGroup G] [inst_1 : Preorder G]
 [AddLeftMono G] [AddRightMono G] {s : Set G},   BddAbove (-s) ↔ BddBelow s
-/
theorem sSup_neg (s : Set ℝ) : sSup (-s) = -sInf s := by
  obtain rfl | hn := s.eq_empty_or_nonempty; · simp
  by_cases hb : BddBelow s
  · rw [csSup_neg hn hb]
  · rw [csInf_of_not_bddBelow hb, Real.sInf_empty, csSup_of_not_bddAbove (bddAbove_neg.not.2 hb),
      Real.sSup_empty, neg_zero]

@[simp]
/-
**Real.sInf_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_neg (s : Set Real) : sInf (-s) = -sSup s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Real.sSup_neg`：sSup_neg (s : Set Real) : sSup (-s) = -sInf s
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem sInf_neg (s : Set ℝ) : sInf (-s) = -sSup s := by
  rw [← neg_eq_iff_eq_neg, ← Real.sSup_neg, neg_neg]

/-- As `sSup s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are at most some nonnegative number `a` to show that `sSup s ≤ a`.

See also `csSup_le`. -/
/-
**Real.sSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {s : Set ℝ} {a : ℝ}, (∀ x ∈ s, x ≤ a) → 0 ≤ a → sSup s ≤ a
参数：∀ x ∈ s, x ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a

--- 原说明 ---
As `sSup s = 0` when `s` is an empty set of reals, it suffices to show that all 
elements of `s`
are at most some nonnegative number `a` to show that `sSup s ≤ a`.

See also `csSup_le`.
-/
protected lemma sSup_le (hs : ∀ x ∈ s, x ≤ a) (ha : 0 ≤ a) : sSup s ≤ a := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [sSup_empty.trans_le ha, csSup_le hs' hs]

/-- As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty, it suffices to show
that all values of `f` are at most some nonnegative number `a` to show that `⨆ i, f i ≤ a`.

See also `ciSup_le`. -/
/-
**Real.iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), f i ≤ a) → 0 ≤ a → ⨆ i, 
f i ≤ a
参数：∀ (i : ι), f i ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sSup_le`：∀ {s : Set ℝ} {a : ℝ}, (∀ x ∈ s, x ≤ a) → 0 ≤ a → sSup s ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty, it s
uffices to show
that all values of `f` are at most some nonnegative number `a` to show that `⨆ i
, f i ≤ a`.

See also `ciSup_le`.
-/
protected lemma iSup_le (hf : ∀ i, f i ≤ a) (ha : 0 ≤ a) : ⨆ i, f i ≤ a :=
  Real.sSup_le (Set.forall_mem_range.2 hf) ha

/-- As `sInf s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are at least some nonpositive number `a` to show that `a ≤ sInf s`.

See also `le_csInf`. -/
/-
**Real.le_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {s : Set ℝ} {a : ℝ}, (∀ x ∈ s, a ≤ x) → a ≤ 0 → a ≤ sInf s
参数：∀ x ∈ s, a ≤ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s

--- 原说明 ---
As `sInf s = 0` when `s` is an empty set of reals, it suffices to show that all 
elements of `s`
are at least some nonpositive number `a` to show that `a ≤ sInf s`.

See also `le_csInf`.
-/
protected lemma le_sInf (hs : ∀ x ∈ s, a ≤ x) (ha : a ≤ 0) : a ≤ sInf s := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  exacts [ha.trans_eq sInf_empty.symm, le_csInf hs' hs]

/-- As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty, it suffices to show
that all values of `f` are at least some nonpositive number `a` to show that `a ≤ ⨅ i, f i`.

See also `le_ciInf`. -/
/-
**Real.le_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), a ≤ f i) → a ≤ 0 → a ≤ ⨅
 i, f i
参数：∀ (i : ι), a ≤ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_sInf`：∀ {s : Set ℝ} {a : ℝ}, (∀ x ∈ s, a ≤ x) → a ≤ 0 → a ≤ sInf
 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty, it s
uffices to show
that all values of `f` are at least some nonpositive number `a` to show that `a 
≤ ⨅ i, f i`.

See also `le_ciInf`.
-/
protected lemma le_iInf (hf : ∀ i, a ≤ f i) (ha : a ≤ 0) : a ≤ ⨅ i, f i :=
  Real.le_sInf (Set.forall_mem_range.2 hf) ha

/-- As `sSup s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are nonpositive to show that `sSup s ≤ 0`. -/
/-
**Real.sSup_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sSup_nonpos (hs : forall x in s, x <= 0) : sSup s <= 0
参数：hs : forall x in s, x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sSup_le`：∀ {s : Set ℝ} {a : ℝ}, (∀ x ∈ s, x ≤ a) → 0 ≤ a → sSup s ≤
 a
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
As `sSup s = 0` when `s` is an empty set of reals, it suffices to show that all 
elements of `s`
are nonpositive to show that `sSup s ≤ 0`.
-/
lemma sSup_nonpos (hs : ∀ x ∈ s, x ≤ 0) : sSup s ≤ 0 := Real.sSup_le hs le_rfl

/-- As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty,
it suffices to show that all values of `f` are nonpositive to show that `⨆ i, f i ≤ 0`. -/
/-
**Real.iSup_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_nonpos (hf : forall i, f i <= 0) : ⨆ i, f i <= 0
参数：hf : forall i, f i <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.iSup_le`：∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), f i ≤ a)
 → 0 ≤ a → ⨆ i, f i ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty,
it suffices to show that all values of `f` are nonpositive to show that `⨆ i, f 
i ≤ 0`.
-/
lemma iSup_nonpos (hf : ∀ i, f i ≤ 0) : ⨆ i, f i ≤ 0 := Real.iSup_le hf le_rfl

/-- As `sInf s = 0` when `s` is an empty set of reals, it suffices to show that all elements of `s`
are nonnegative to show that `0 ≤ sInf s`. -/
/-
**Real.sInf_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sInf_nonneg (hs : forall x in s, 0 <= x) : 0 <= sInf s
参数：hs : forall x in s, 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_sInf`：∀ {s : Set ℝ} {a : ℝ}, (∀ x ∈ s, a ≤ x) → a ≤ 0 → a ≤ sInf
 s
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
As `sInf s = 0` when `s` is an empty set of reals, it suffices to show that all 
elements of `s`
are nonnegative to show that `0 ≤ sInf s`.
-/
lemma sInf_nonneg (hs : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sInf s := Real.le_sInf hs le_rfl

/-- As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty,
it suffices to show that all values of `f` are nonnegative to show that `0 ≤ ⨅ i, f i`. -/
/-
**Real.iInf_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iInf_nonneg (hf : forall i, 0 <= f i) : 0 <= iInf f
参数：hf : forall i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_iInf`：∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), a ≤ f i)
 → a ≤ 0 → a ≤ ⨅ i, f i
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty,
it suffices to show that all values of `f` are nonnegative to show that `0 ≤ ⨅ i
, f i`.
-/
lemma iInf_nonneg (hf : ∀ i, 0 ≤ f i) : 0 ≤ iInf f := Real.le_iInf hf le_rfl

/-- As `sSup s = 0` when `s` is a set of reals that's unbounded above, it suffices to show that `s`
contains a nonnegative element to show that `0 ≤ sSup s`. -/
/-
**Real.sSup_nonneg'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sSup_nonneg' (hs : exists x in s, 0 <= x) : 0 <= sSup s
参数：hs : exists x in s, 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup_of_le`：le_csSup_of_le (hs : BddAbove s) (hb : b in s) (h : a <=
 b) : a <= sSup s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0

--- 原说明 ---
As `sSup s = 0` when `s` is a set of reals that's unbounded above, it suffices t
o show that `s`
contains a nonnegative element to show that `0 ≤ sSup s`.
-/
lemma sSup_nonneg' (hs : ∃ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h ↦ le_csSup_of_le h hxs hx) fun h ↦ (sSup_of_not_bddAbove h).ge

/-- As `⨆ i, f i = 0` when the real-valued function `f` is unbounded above,
it suffices to show that `f` takes a nonnegative value to show that `0 ≤ ⨆ i, f i`. -/
/-
**Real.iSup_nonneg'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_nonneg' (hf : exists i, 0 <= f i) : 0 <= ⨆ i, f i
参数：hf : exists i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sSup_nonneg'`：sSup_nonneg' (hs : exists x in s, 0 <= x) : 0 <= sSup
 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)

--- 原说明 ---
As `⨆ i, f i = 0` when the real-valued function `f` is unbounded above,
it suffices to show that `f` takes a nonnegative value to show that `0 ≤ ⨆ i, f 
i`.
-/
lemma iSup_nonneg' (hf : ∃ i, 0 ≤ f i) : 0 ≤ ⨆ i, f i := sSup_nonneg' <| Set.exists_range_iff.2 hf

/-- As `sInf s = 0` when `s` is a set of reals that's unbounded below, it suffices to show that `s`
contains a nonpositive element to show that `sInf s ≤ 0`. -/
/-
**Real.sInf_nonpos'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sInf_nonpos' (hs : exists x in s, x <= 0) : sInf s <= 0
参数：hs : exists x in s, x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le_of_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Real.sInf_of_not_bddBelow`：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sIn
f s = 0

--- 原说明 ---
As `sInf s = 0` when `s` is a set of reals that's unbounded below, it suffices t
o show that `s`
contains a nonpositive element to show that `sInf s ≤ 0`.
-/
lemma sInf_nonpos' (hs : ∃ x ∈ s, x ≤ 0) : sInf s ≤ 0 := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  exact dite _ (fun h ↦ csInf_le_of_le h hxs hx) fun h ↦ (sInf_of_not_bddBelow h).le

/-- As `⨅ i, f i = 0` when the real-valued function `f` is unbounded below,
it suffices to show that `f` takes a nonpositive value to show that `0 ≤ ⨅ i, f i`. -/
/-
**Real.iInf_nonpos'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iInf_nonpos' (hf : exists i, f i <= 0) : ⨅ i, f i <= 0
参数：hf : exists i, f i <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sInf_nonpos'`：sInf_nonpos' (hs : exists x in s, x <= 0) : sInf s <=
 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)

--- 原说明 ---
As `⨅ i, f i = 0` when the real-valued function `f` is unbounded below,
it suffices to show that `f` takes a nonpositive value to show that `0 ≤ ⨅ i, f 
i`.
-/
lemma iInf_nonpos' (hf : ∃ i, f i ≤ 0) : ⨅ i, f i ≤ 0 := sInf_nonpos' <| Set.exists_range_iff.2 hf

/-- As `sSup s = 0` when `s` is a set of reals that's either empty or unbounded above,
it suffices to show that all elements of `s` are nonnegative to show that `0 ≤ sSup s`. -/
/-
**Real.sSup_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sSup_nonneg (hs : forall x in s, 0 <= x) : 0 <= sSup s
参数：hs : forall x in s, 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.sSup_nonneg'`：sSup_nonneg' (hs : exists x in s, 0 <= x) : 0 <= sSup
 s

--- 原说明 ---
As `sSup s = 0` when `s` is a set of reals that's either empty or unbounded abov
e,
it suffices to show that all elements of `s` are nonnegative to show that `0 ≤ s
Sup s`.
-/
lemma sSup_nonneg (hs : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sSup_empty.ge
  · exact sSup_nonneg' ⟨x, hx, hs _ hx⟩

/-- As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty or unbounded above,
it suffices to show that all values of `f` are nonnegative to show that `0 ≤ ⨆ i, f i`. -/
/-
**Real.iSup_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i
参数：hf : forall i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sSup_nonneg`：sSup_nonneg (hs : forall x in s, 0 <= x) : 0 <= sSup s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
As `⨆ i, f i = 0` when the domain of the real-valued function `f` is empty or un
bounded above,
it suffices to show that all values of `f` are nonnegative to show that `0 ≤ ⨆ i
, f i`.
-/
lemma iSup_nonneg (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨆ i, f i := sSup_nonneg <| Set.forall_mem_range.2 hf
/-
**Real.iSup_nonneg_of_nonnegHomClass** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_nonneg_of_nonnegHomClass {ι F α : Type*} [FunLike F α Real] [NonnegHo
mClass F α Real] (f : F) (g : ι -> α) : 0 <= ⨆ i, f (g i)
参数：f : F；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.iSup_nonneg`：iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
-/
lemma iSup_nonneg_of_nonnegHomClass {ι F α : Type*} [FunLike F α ℝ] [NonnegHomClass F α ℝ] (f : F)
    (g : ι → α) :
    0 ≤ ⨆ i, f (g i) :=
  iSup_nonneg (fun i ↦ apply_nonneg f (g i))

/-- As `sInf s = 0` when `s` is a set of reals that's either empty or unbounded below,
it suffices to show that all elements of `s` are nonpositive to show that `sInf s ≤ 0`. -/
/-
**Real.sInf_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sInf_nonpos (hs : forall x in s, x <= 0) : sInf s <= 0
参数：hs : forall x in s, x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.sInf_nonpos'`：sInf_nonpos' (hs : exists x in s, x <= 0) : sInf s <=
 0

--- 原说明 ---
As `sInf s = 0` when `s` is a set of reals that's either empty or unbounded belo
w,
it suffices to show that all elements of `s` are nonpositive to show that `sInf 
s ≤ 0`.
-/
lemma sInf_nonpos (hs : ∀ x ∈ s, x ≤ 0) : sInf s ≤ 0 := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact sInf_empty.le
  · exact sInf_nonpos' ⟨x, hx, hs _ hx⟩

/-- As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty or unbounded below,
it suffices to show that all values of `f` are nonpositive to show that `0 ≤ ⨅ i, f i`. -/
/-
**Real.iInf_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iInf_nonpos (hf : forall i, f i <= 0) : ⨅ i, f i <= 0
参数：hf : forall i, f i <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sInf_nonpos`：sInf_nonpos (hs : forall x in s, x <= 0) : sInf s <= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
As `⨅ i, f i = 0` when the domain of the real-valued function `f` is empty or un
bounded below,
it suffices to show that all values of `f` are nonpositive to show that `0 ≤ ⨅ i
, f i`.
-/
lemma iInf_nonpos (hf : ∀ i, f i ≤ 0) : ⨅ i, f i ≤ 0 := sInf_nonpos <| Set.forall_mem_range.2 hf
/-
**Real.sInf_le_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sInf_le_sSup (s : Set Real) (h₁ : BddBelow s) (h₂ : BddAbove s) : sInf s <
= sSup s
参数：s : Set Real；h₁ : BddBelow s；h₂ : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csInf_le_csSup`：csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s
-/
theorem sInf_le_sSup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : sInf s ≤ sSup s := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [sInf_empty, sSup_empty]
  · exact csInf_le_csSup hne h₁ h₂
/-
**Real.cauSeq_converges** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cauSeq_converges (f : CauSeq Real abs) : exists x, f ≈ const abs x
参数：f : CauSeq Real abs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.exists_lt`：exists_lt (f : CauSeq α abs) : exists a : α, const a <
 f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_lt`：const_lt {x y : α} : const x < const y ↔ x < y
· 使用定理 `CauSeq.lt_trans`：lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < 
h) : f < h
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `CauSeq.exists_gt`：exists_gt (f : CauSeq α abs) : exists a : α, f < const
 a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `CauSeq.lt_total`：lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.sub_apply`：sub_apply (f g : CauSeq β abv) (i : Nat) : (f - g) i =
 f i - g i
· 使用定理 `CauSeq.const_apply`：const_apply (x : β) (i : Nat) : (const x : Nat -> β)
 i = x
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 43 条，此处仅展示前 30 条）
-/
theorem cauSeq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x := by
  let s := {x : ℝ | const abs x < f}
  have lb : ∃ x, x ∈ s := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀ y ∈ s, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ s, y ≤ x := (exists_gt f).imp ub'
  refine ⟨sSup s, ((lt_total _ _).resolve_left fun h => ?_).resolve_right fun h => ?_⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (csSup_le lb (ub' _ ?_)).not_gt (sub_lt_self _ (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (le_csSup ub ?_).not_gt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CauSeq.IsComplete ℝ abs :=
  ⟨cauSeq_converges⟩

open Set
/-
**Real.iInf_Ioi_eq_iInf_rat_gt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iInf_Ioi_eq_iInf_rat_gt {f : Real -> Real} (x : Real) (hf : BddBelow (f ''
 Ioi x)) (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : Rat // x < q' 
}, f q
参数：x : Real；hf : BddBelow (f '' Ioi x)；hf_mono : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ciInf_set_le`：ciInf_set_le {f : β -> α} {s : Set β} (H : BddBelow (f '' 
s)) {c : β} (hc : c in s) : ⨅ i : s, f i <= f c
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_Ioi_subtype`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [
NoMaxOrder α], Nonempty ↑(Set.Ioi a)
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem iInf_Ioi_eq_iInf_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : ℚ // x < q' }, f q := by
  refine le_antisymm ?_ ?_
  · have : Nonempty { r' : ℚ // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine le_ciInf fun r => ?_
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine ciInf_set_le hf (hxy.trans ?_)
    exact_mod_cast hyr
  · refine le_ciInf fun q => ?_
    have hq := q.prop
    rw [mem_Ioi] at hq
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    refine (ciInf_le ?_ ?_).trans ?_
    · refine ⟨hf.some, fun z => ?_⟩
      rintro ⟨u, rfl⟩
      suffices hfu : f u ∈ f '' Ioi x from hf.choose_spec hfu
      exact ⟨u, u.prop, rfl⟩
    · exact ⟨y, hxy⟩
    · refine hf_mono (le_trans ?_ hyq.le)
      norm_cast
/-
**Real.not_bddAbove_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：not_bddAbove_coe : ¬ (BddAbove <| range (fun (x : Rat) => (x : Real)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
-/
theorem not_bddAbove_coe : ¬ (BddAbove <| range (fun (x : ℚ) ↦ (x : ℝ))) := by
  dsimp only [BddAbove, upperBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_gt _
/-
**Real.not_bddBelow_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：not_bddBelow_coe : ¬ (BddBelow <| range (fun (x : Rat) => (x : Real)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `exists_rat_lt`：exists_rat_lt (x : K) : exists q : Rat, (q : K) < x
-/
theorem not_bddBelow_coe : ¬ (BddBelow <| range (fun (x : ℚ) ↦ (x : ℝ))) := by
  dsimp only [BddBelow, lowerBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_lt _
/-
**Real.iUnion_Iic_rat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iUnion_Iic_rat : ⋃ r : Rat, Iic (r : Real) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iUnion_Iic_of_not_bddAbove_range`：iUnion_Iic_of_not_bddAbove_range (hf :
 ¬ BddAbove (range f)) : ⋃ i, Iic (f i) = univ
· 使用定理 `Real.not_bddAbove_coe`：not_bddAbove_coe : ¬ (BddAbove <| range (fun (x :
 Rat) => (x : Real)))
-/
theorem iUnion_Iic_rat : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
  exact iUnion_Iic_of_not_bddAbove_range not_bddAbove_coe
/-
**Real.iInter_Iic_rat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iInter_Iic_rat : ⋂ r : Rat, Iic (r : Real) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInter_Iic_eq_empty_iff`：iInter_Iic_eq_empty_iff : ⋂ i, Iic (f i) = ∅ ↔ 
¬ BddBelow (range f)
· 使用定理 `Real.not_bddBelow_coe`：not_bddBelow_coe : ¬ (BddBelow <| range (fun (x :
 Rat) => (x : Real)))
-/
theorem iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe

/-- Exponentiation is eventually larger than linear growth. -/
/-
**Real.exists_natCast_add_one_lt_pow_of_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：exists_natCast_add_one_lt_pow_of_one_lt (ha : 1 < a) : exists m : Nat, (m 
+ 1 : Real) < a ^ m
参数：ha : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `le_of_forall_lt_rat_imp_le`：le_of_forall_lt_rat_imp_le (h : forall q : R
at, y < q -> x <= q) : x <= y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `one_lt_div`：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
Exponentiation is eventually larger than linear growth.
-/
lemma exists_natCast_add_one_lt_pow_of_one_lt (ha : 1 < a) : ∃ m : ℕ, (m + 1 : ℝ) < a ^ m := by
  obtain ⟨k, posk, hk⟩ : ∃ k : ℕ, 0 < k ∧ 1 / k + 1 < a := by
    contrapose! ha
    refine le_of_forall_lt_rat_imp_le ?_
    intro q hq
    refine (ha q.den (by positivity)).trans ?_
    rw [← le_sub_iff_add_le, div_le_iff₀ (by positivity), sub_mul, one_mul]
    norm_cast at hq ⊢
    rw [← q.num_div_den, one_lt_div (by positivity)] at hq
    rw [q.mul_den_eq_num]
    norm_cast at hq ⊢
    lia
  use 2 * k ^ 2
  calc
    ((2 * k ^ 2 : ℕ) + 1 : ℝ) ≤ 2 ^ (2 * k) := mod_cast Nat.two_mul_sq_add_one_le_two_pow_two_mul _
    _ = (1 / k * k + 1 : ℝ) ^ (2 * k) := by simp [posk.ne']; norm_num
    _ ≤ ((1 / k + 1) ^ k : ℝ) ^ (2 * k) := by gcongr; exact mul_add_one_le_add_one_pow (by simp) _
    _ = (1 / k + 1 : ℝ) ^ (2 * k ^ 2) := by rw [← pow_mul, mul_left_comm, sq]
    _ < a ^ (2 * k ^ 2) := by gcongr
/-
**Real.exists_nat_pos_inv_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：exists_nat_pos_inv_lt {b : Real} (hb : 0 < b) : exists (n : Nat), 0 < n ∧ 
(n : Real)⁻¹ < b
参数：hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_lt_comm₀`：inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
-/
lemma exists_nat_pos_inv_lt {b : ℝ} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ)⁻¹ < b := by
  refine (exists_nat_gt b⁻¹).imp fun k hk ↦ ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

end Real

