/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Existence of minimizers (Hilbert projection theorem)

This file shows the existence of minimizers (also known as the Hilbert projection theorem).
This is the key tool that is used to define `Submodule.orthogonalProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs ℝ _ _

open Topology RCLike Real Filter InnerProductSpace

/-- **Existence of minimizers**, aka the **Hilbert projection theorem**.

Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`. -/
/-
**exists_norm_eq_iInf_of_complete_convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ :
 IsComplete K) (h₂ : Convex Real K) : forall u : F, exists v in K, ‖u - v‖ = ⨅ w
 : K, ‖u - w‖
参数：ne : K.Nonempty；h₁ : IsComplete K；h₂ : Convex Real K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `lt_add_of_le_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddLeftStrictMono α] {a b c : α},   b ≤ c → 0 < a → b < c + a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.one_div_pos_of_nat`：one_div_pos_of_nat {n : Nat} : 0 < 1 / ((n : α) 
+ 1)
· 使用定理 `exists_lt_of_ciInf_lt`：exists_lt_of_ciInf_lt [Nonempty ι] {f : ι -> α} (
h : iInf f < a) : exists i, f i < a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_one_div_add_atTop_nhds_zero_nat`：tendsto_one_div_add_atTop_nhds_
zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [Con
tinuousSMul Rat>=0 𝕜] : Tends…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 155 条，此处仅展示前 30 条）

--- 原说明 ---
**Existence of minimizers**, aka the **Hilbert projection theorem**.

Let `u` be a point in a real inner product space, and let `K` be a nonempty comp
lete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to
 `u`.
-/
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := fun u => by
  let δ := ⨅ w : K, ‖u - w‖
  let : Nonempty K := ne.to_subtype
  have zero_le_δ : 0 ≤ δ := le_ciInf fun _ => norm_nonneg _
  have δ_le : ∀ w : K, δ ≤ ‖u - w‖ := ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
  have δ_le' : ∀ w ∈ K, δ ≤ ‖u - w‖ := fun w hw => δ_le ⟨w, hw⟩
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `‖u - w n‖ < δ + 1 / (n + 1)` (which implies `‖u - w n‖ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ‖u - w n‖ < δ + 1 / (n + 1) := by
    have hδ : ∀ n : ℕ, δ < δ + 1 / (n + 1) := fun n =>
      lt_add_of_le_of_pos le_rfl Nat.one_div_pos_of_nat
    have h := fun n => exists_lt_of_ciInf_lt (hδ n)
    let w : ℕ → K := fun n => Classical.choose (h n)
    exact ⟨w, fun n => Classical.choose_spec (h n)⟩
  rcases exists_seq with ⟨w, hw⟩
  have norm_tendsto : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 δ) := by
    have h : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
    have h' : Tendsto (fun n : ℕ => δ + 1 / (n + 1)) atTop (𝓝 δ) := by
      convert! h.add tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [add_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h' (fun x => δ_le _) fun x => le_of_lt (hw _)
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : CauchySeq fun n => (w n : F) := by
    rw [cauchySeq_iff_le_tendsto_0]
    -- splits into three goals
    let b := fun n : ℕ => 8 * δ * (1 / (n + 1)) + 4 * (1 / (n + 1)) * (1 / (n + 1))
    use fun n => √(b n)
    constructor
    -- first goal :  `∀ (n : ℕ), 0 ≤ √(b n)`
    · intro n
      exact sqrt_nonneg _
    constructor
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ √(b N)`
    · intro p q N hp hq
      let wp := (w p : F)
      let wq := (w q : F)
      let a := u - wq
      let b := u - wp
      let half := 1 / (2 : ℝ)
      let div := 1 / ((N : ℝ) + 1)
      have :
        4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
          2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) :=
        calc
          4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
              2 * ‖u - half • (wq + wp)‖ * (2 * ‖u - half • (wq + wp)‖) +
              ‖wp - wq‖ * ‖wp - wq‖ := by
            ring
          _ =
              absR 2 * ‖u - half • (wq + wp)‖ * (absR 2 * ‖u - half • (wq + wp)‖) +
                ‖wp - wq‖ * ‖wp - wq‖ := by
            rw [abs_of_nonneg]
            exact zero_le_two
          _ =
              ‖(2 : ℝ) • (u - half • (wq + wp))‖ * ‖(2 : ℝ) • (u - half • (wq + wp))‖ +
                ‖wp - wq‖ * ‖wp - wq‖ := by simp [norm_smul]
          _ = ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ := by
            rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0), ←
              one_add_one_eq_two, add_smul]
            simp only [one_smul]
            have eq₁ : wp - wq = a - b := (sub_sub_sub_cancel_left _ _ _).symm
            have eq₂ : u + u - (wq + wp) = a + b := by
              change u + u - (wq + wp) = u - wq + (u - wp)
              abel
            rw [eq₁, eq₂]
          _ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) := parallelogram_law_with_norm_mul ℝ _ _
      have eq : δ ≤ ‖u - half • (wq + wp)‖ := by
        rw [smul_add]
        apply δ_le'
        apply h₂
        repeat' exact Subtype.mem _
        repeat' exact le_of_lt one_half_pos
        exact add_halves 1
      have eq₂ : ‖a‖ ≤ δ + div := by grw [hw, Nat.one_div_le_one_div hq]
      have eq₂' : ‖b‖ ≤ δ + div := by grw [hw, Nat.one_div_le_one_div hp]
      rw [dist_eq_norm]
      apply nonneg_le_nonneg_of_sq_le_sq
      · exact sqrt_nonneg _
      rw [mul_self_sqrt]
      · calc
        ‖wp - wq‖ * ‖wp - wq‖ =
            2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ := by
          simp [← this]
        _ ≤ 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * δ * δ := by gcongr
        _ ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ := by gcongr
        _ = 8 * δ * div + 4 * div * div := by ring
      positivity
    -- third goal : `Tendsto (fun (n : ℕ) => √(b n)) atTop (𝓝 0)`
    suffices Tendsto (fun x ↦ √(8 * δ * x + 4 * x * x) : ℝ → ℝ) (𝓝 0) (𝓝 0)
      from this.comp tendsto_one_div_add_atTop_nhds_zero_nat
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchySeq_tendsto_of_isComplete h₁ (fun n => Subtype.mem _) seq_is_cauchy with
    ⟨v, hv, w_tendsto⟩
  use v, hv
  have h_cont : Continuous fun v => ‖u - v‖ := by fun_prop
  have : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 ‖u - v‖) := by
    convert! Tendsto.comp h_cont.continuousAt w_tendsto
  exact tendsto_nhds_unique this norm_tendsto

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
/-
**norm_eq_iInf_iff_real_inner_le_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_eq_iInf_iff_real_inner_le_zero {K : Set F} (h : Convex Real K) {u : F
} {v : F} (hv : v in K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ forall w in K, ⟪u - v, 
w - v⟫_Real <= 0
参数：h : Convex Real K；hv : v in K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_self_le_mul_self`：mul_self_le_mul_self [PosMulMono α] [MulPosMono α]
 (ha : 0 <= a) (hab : a <= b) : a * a <= b * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_sub_sq`：norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
（共 118 条，此处仅展示前 30 条）

--- 原说明 ---
Characterization of minimizers for the projection on a convex set in a real inne
r product
space.
-/
theorem norm_eq_iInf_iff_real_inner_le_zero {K : Set F} (h : Convex ℝ K) {u : F} {v : F}
    (hv : v ∈ K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
  let : Nonempty K := ⟨⟨v, hv⟩⟩
  constructor
  · intro eq w hw
    let δ := ⨅ w : K, ‖u - w‖
    let p := ⟪u - v, w - v⟫_ℝ
    let q := ‖w - v‖ ^ 2
    have δ_le (w : K) : δ ≤ ‖u - w‖ := ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ _
    have δ_le' (w) (hw : w ∈ K) : δ ≤ ‖u - w‖ := δ_le ⟨w, hw⟩
    have (θ : ℝ) (hθ₁ : 0 < θ) (hθ₂ : θ ≤ 1) : 2 * p ≤ θ * q := by
      have : ‖u - v‖ ^ 2 ≤ ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 :=
        calc ‖u - v‖ ^ 2
          _ ≤ ‖u - (θ • w + (1 - θ) • v)‖ ^ 2 := by
            simp only [sq]; apply mul_self_le_mul_self (norm_nonneg _)
            rw [eq]; apply δ_le'
            apply h hw hv
            exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel _ _]
          _ = ‖u - v - θ • (w - v)‖ ^ 2 := by
            have : u - (θ • w + (1 - θ) • v) = u - v - θ • (w - v) := by
              rw [smul_sub, sub_smul, one_smul]
              simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev]
            rw [this]
          _ = ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 := by
            rw [@norm_sub_sq ℝ, inner_smul_right, norm_smul]
            simp only [sq]
            change
              ‖u - v‖ * ‖u - v‖ - 2 * (θ * ⟪u - v, w - v⟫_ℝ) +
                absR θ * ‖w - v‖ * (absR θ * ‖w - v‖) =
              ‖u - v‖ * ‖u - v‖ - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * (‖w - v‖ * ‖w - v‖)
            rw [abs_of_pos hθ₁]; ring
      have eq₁ :
        ‖u - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ‖w - v‖ ^ 2 =
          ‖u - v‖ ^ 2 + (θ * θ * ‖w - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ) := by
        abel
      rw [eq₁, le_add_iff_nonneg_right] at this
      have eq₂ :
        θ * θ * ‖w - v‖ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ =
          θ * (θ * ‖w - v‖ ^ 2 - 2 * ⟪u - v, w - v⟫_ℝ) := by ring
      rw [eq₂] at this
      exact le_of_sub_nonneg (nonneg_of_mul_nonneg_right this hθ₁)
    by_cases hq : q = 0
    · rw [hq] at this
      have : p ≤ 0 := by
        have := this (1 : ℝ) (by simp) (by simp)
        linarith
      exact this
    · have q_pos : 0 < q := lt_of_le_of_ne (sq_nonneg _) fun h ↦ hq h.symm
      by_contra hp
      rw [not_le] at hp
      let θ := min (1 : ℝ) (p / q)
      have eq₁ : θ * q ≤ p :=
        calc
          θ * q ≤ p / q * q := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
          _ = p := div_mul_cancel₀ _ hq
      have : 2 * p ≤ p :=
        calc
          2 * p ≤ θ * q := by
            exact this θ (lt_min (by simp) (div_pos hp q_pos)) (by simp [θ])
          _ ≤ p := eq₁
      linarith
  · intro h
    apply le_antisymm
    · apply le_ciInf
      intro w
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      have := h w w.2
      calc
        ‖u - v‖ * ‖u - v‖ ≤ ‖u - v‖ * ‖u - v‖ - 2 * ⟪u - v, w - v⟫_ℝ := by linarith
        _ ≤ ‖u - v‖ ^ 2 - 2 * ⟪u - v, w - v⟫_ℝ + ‖w - v‖ ^ 2 := by
          rw [sq]
          refine le_add_of_nonneg_right ?_
          exact sq_nonneg _
        _ = ‖u - v - (w - v)‖ ^ 2 := (@norm_sub_sq ℝ _ _ _ _ _ _).symm
        _ = ‖u - w‖ * ‖u - w‖ := by
          have : u - v - (w - v) = u - w := by abel
          rw [this, sq]
    · change ⨅ w : K, ‖u - w‖ ≤ (fun w : K => ‖u - w‖) ⟨v, hv⟩
      apply ciInf_le
      use 0
      rintro y ⟨z, rfl⟩
      exact norm_nonneg _

namespace Submodule

variable (K : Submodule 𝕜 E)

/-- Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
/-
**Submodule.exists_norm_eq_iInf_of_complete_subspace** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule`。
形式化陈述：exists_norm_eq_iInf_of_complete_subspace (h : IsComplete (↑K : Set E)) : f
orall u : E, exists v in K, ‖u - v‖ = ⨅ w : (K : Set E), ‖u - w‖
参数：h : IsComplete (↑K : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `exists_norm_eq_iInf_of_complete_convex`：exists_norm_eq_iInf_of_complete_
convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K) (h₂ : Convex Real K) : 
forall u : F, exists v in K,…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Submodule.convex`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (K :…

--- 原说明 ---
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete
 subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to
 `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_iInf_of_complete_subspace (h : IsComplete (↑K : Set E)) :
    ∀ u : E, ∃ v ∈ K, ‖u - v‖ = ⨅ w : (K : Set E), ‖u - w‖ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule ℝ E := Submodule.restrictScalars ℝ K
  exact exists_norm_eq_iInf_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex

/-- Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superseded by `norm_eq_iInf_iff_inner_eq_zero` that gives the same conclusion over
any `RCLike` field.
-/
/-
**Submodule.norm_eq_iInf_iff_real_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：norm_eq_iInf_iff_real_inner_eq_zero (K : Submodule Real F) {u : F} {v : F}
 (hv : v in K) : (‖u - v‖ = ⨅ w : (↑K : Set F), ‖u - w‖) ↔ forall w in K, ⟪u - v
, w⟫_Real = 0
参数：K : Submodule Real F；hv : v in K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_iInf_iff_real_inner_le_zero`：norm_eq_iInf_iff_real_inner_le_zero
 {K : Set F} (h : Convex Real K) {u : F} {v : F} (hv : v in K) : (‖u - v‖ = ⨅ w 
: K, ‖u - w‖) ↔ forall w …
· 使用定理 `Submodule.convex`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (K :…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Characterization of minimizers in the projection on a subspace, in the real case
.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subs
pace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only i
f
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `
K`).
This is superseded by `norm_eq_iInf_iff_inner_eq_zero` that gives the same concl
usion over
any `RCLike` field.
-/
theorem norm_eq_iInf_iff_real_inner_eq_zero (K : Submodule ℝ F) {u : F} {v : F} (hv : v ∈ K) :
    (‖u - v‖ = ⨅ w : (↑K : Set F), ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
  Iff.intro
    (by
      intro h
      have h : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
        rwa [norm_eq_iInf_iff_real_inner_le_zero] at h
        exacts [K.convex, hv]
      intro w hw
      have le : ⟪u - v, w⟫_ℝ ≤ 0 := by
        let w' := w + v
        have : w' ∈ K := Submodule.add_mem _ hw hv
        have h₁ := h w' this
        have h₂ : w' - v = w := by
          simp only [w', add_neg_cancel_right, sub_eq_add_neg]
        rw [h₂] at h₁
        exact h₁
      have ge : ⟪u - v, w⟫_ℝ ≥ 0 := by
        let w'' := -w + v
        have : w'' ∈ K := Submodule.add_mem _ (Submodule.neg_mem _ hw) hv
        have h₁ := h w'' this
        have h₂ : w'' - v = -w := by
          simp only [w'', add_neg_cancel_right, sub_eq_add_neg]
        rw [h₂, inner_neg_right] at h₁
        linarith
      exact le_antisymm le ge)
    (by
      intro h
      have : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
        intro w hw
        let w' := w - v
        have : w' ∈ K := Submodule.sub_mem _ hw hv
        have h₁ := h w' this
        exact le_of_eq h₁
      rwa [norm_eq_iInf_iff_real_inner_le_zero]
      exacts [Submodule.convex _, hv])

/-- Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
/-
**Submodule.norm_eq_iInf_iff_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：norm_eq_iInf_iff_inner_eq_zero {u : E} {v : E} (hv : v in K) : (‖u - v‖ = 
⨅ w : K, ‖u - w‖) ↔ forall w in K, ⟪u - v, w⟫ = 0
参数：hv : v in K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.norm_eq_iInf_iff_real_inner_eq_zero`：norm_eq_iInf_iff_real_inn
er_eq_zero (K : Submodule Real F) {u : F} {v : F} (hv : v in K) : (‖u - v‖ = ⨅ w
 : (↑K : Set F), ‖u - w‖) ↔ forall …
· 使用定理 `RCLike.ext`：ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = 
w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RCLike.I_im'`：I_im' (z : K) : im (I : K) * im z = im z
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `real_inner_eq_re_inner`：real_inner_eq_re_inner (x y : E) : (Inner.rclike
ToReal 𝕜 E).inner x y = re ⟪x, y⟫
· 使用定理 `RCLike.zero_re`：zero_re : re (0 : K) = (0 : Real)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace
.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only i
f
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `
K`)
-/
theorem norm_eq_iInf_iff_inner_eq_zero {u : E} {v : E} (hv : v ∈ K) :
    (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  let K' : Submodule ℝ E := K.restrictScalars ℝ
  constructor
  · intro H
    have A : ∀ w ∈ K, re ⟪u - v, w⟫ = 0 := (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).1 H
    intro w hw
    apply RCLike.ext
    · simp [A w hw]
    · symm
      calc
        im (0 : 𝕜) = 0 := im.map_zero
        _ = re ⟪u - v, (-I : 𝕜) • w⟫ := (A _ (K.smul_mem (-I) hw)).symm
        _ = re (-I * ⟪u - v, w⟫) := by rw [inner_smul_right]
        _ = im ⟪u - v, w⟫ := by simp
  · intro H
    have : ∀ w ∈ K', ⟪u - v, w⟫_ℝ = 0 := by
      intro w hw
      rw [real_inner_eq_re_inner, H w hw]
      exact zero_re
    exact (K'.norm_eq_iInf_iff_real_inner_eq_zero hv).2 this

end Submodule

