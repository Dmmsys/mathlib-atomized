/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Extending a backward bound on a normed group homomorphism from a dense set

Possible TODO (from the PR's review, https://github.com/leanprover-community/mathlib/pull/8498):
"This feels a lot like the second step in the proof of the Banach open mapping theorem
(`exists_preimage_norm_le`) ... wonder if it would be possible to refactor it using one of [the
lemmas in this file]."
-/

public section


open Filter Finset

open Topology

variable {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
variable {H : Type*} [NormedAddCommGroup H]

/-- Given `f : NormedAddGroupHom G H` for some complete `G` and a subgroup `K` of `H`, if every
element `x` of `K` has a preimage under `f` whose norm is at most `C*‖x‖` then the same holds for
elements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any
positive `ε`.
-/
/-
**controlled_closure_of_complete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：controlled_closure_of_complete {f : NormedAddGroupHom G H} {K : AddSubgrou
p H} {C ε : Real} (hC : 0 < C) (hε : 0 < ε) (hyp : f.SurjectiveOnWith K C) : f.S
urjectiveOnWith K.topologicalClosure (C + ε)
参数：hC : 0 < C；hε : 0 < ε；hyp : f.SurjectiveOnWith K C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `controlled_sum_of_mem_closure`：∀ {E : Type u_4} [inst : SeminormedAddCom
mGroup E] {a : E} {s : AddSubgroup E},   a ∈ closure ↑s →     ∀ {b : ℕ → ℝ},    
   (∀ (n : ℕ), 0 < …
· 使用定理 `NormedAddCommGroup.cauchy_series_of_le_geometric''`：NormedAddCommGroup.c
auchy_series_of_le_geometric'' {C : Real} {u : Nat -> α} {N : Nat} {r : Real} (h
r₀ : 0 < r) (hr₁ : r < 1) (h : forall n …
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
Given `f : NormedAddGroupHom G H` for some complete `G` and a subgroup `K` of `H
`, if every
element `x` of `K` has a preimage under `f` whose norm is at most `C*‖x‖` then t
he same holds for
elements of the (topological) closure of `K` with constant `C+ε` instead of `C`,
 for any
positive `ε`.
-/
theorem controlled_closure_of_complete {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hyp : f.SurjectiveOnWith K C) :
    f.SurjectiveOnWith K.topologicalClosure (C + ε) := by
  rintro (h : H) (h_in : h ∈ K.topologicalClosure)
  -- We first get rid of the easy case where `h = 0`.
  by_cases hyp_h : h = 0
  · rw [hyp_h]
    use 0
    simp
  /- The desired preimage will be constructed as the sum of a series. Convergence of
    the series will be guaranteed by completeness of `G`. We first write `h` as the sum
    of a sequence `v` of elements of `K` which starts close to `h` and then quickly goes to zero.
    The sequence `b` below quantifies this. -/
  set b : ℕ → ℝ := fun i => (1 / 2) ^ i * (ε * ‖h‖ / 2) / C
  have b_pos (i) : 0 < b i := by positivity
  obtain
    ⟨v : ℕ → H, lim_v : Tendsto (fun n : ℕ => ∑ k ∈ range (n + 1), v k) atTop (𝓝 h), v_in :
      ∀ n, v n ∈ K, hv₀ : ‖-v 0 + h‖ < b 0, hv : ∀ n > 0, ‖v n‖ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos
  /- The controlled surjectivity assumption on `f` allows to build preimages `u n` for all
    elements `v n` of the `v` sequence. -/
  have : ∀ n, ∃ m' : G, f m' = v n ∧ ‖m'‖ ≤ C * ‖v n‖ := fun n : ℕ => hyp (v n) (v_in n)
  choose u hu hnorm_u using this
  /- The desired series `s` is then obtained by summing `u`. We then check our choice of
    `b` ensures `s` is Cauchy. -/
  set s : ℕ → G := fun n => ∑ k ∈ range (n + 1), u k
  have : CauchySeq s := by
    apply NormedAddCommGroup.cauchy_series_of_le_geometric'' (by simp) one_half_lt_one
    · rintro n (hn : n ≥ 1)
      calc
        ‖u n‖ ≤ C * ‖v n‖ := hnorm_u n
        _ ≤ C * b n := by gcongr; exact (hv _ <| Nat.succ_le_iff.mp hn).le
        _ = (1 / 2) ^ n * (ε * ‖h‖ / 2) := by simp [b, mul_div_cancel₀ _ hC.ne.symm]
        _ = ε * ‖h‖ / 2 * (1 / 2) ^ n := mul_comm _ _
  -- We now show that the limit `g` of `s` is the desired preimage.
  obtain ⟨g : G, hg⟩ := cauchySeq_tendsto_of_complete this
  refine ⟨g, ?_, ?_⟩
  · -- We indeed get a preimage. First note:
    have : f ∘ s = fun n => ∑ k ∈ range (n + 1), v k := by
      ext n
      simp [s, map_sum, hu]
    /- In the above equality, the left-hand-side converges to `f g` by continuity of `f` and
      definition of `g` while the right-hand-side converges to `h` by construction of `v` so
      `g` is indeed a preimage of `h`. -/
    rw [← this] at lim_v
    exact tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v
  · -- Then we need to estimate the norm of `g`, using our careful choice of `b`.
    suffices ∀ n, ‖s n‖ ≤ (C + ε) * ‖h‖ from
      le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hg) this
    intro n
    have hnorm₀ : ‖u 0‖ ≤ C * b 0 + C * ‖h‖ := by
      have :=
        calc
          ‖v 0‖ ≤ ‖h‖ + ‖v 0 - h‖ := norm_le_insert' _ _
          _ ≤ ‖h‖ + b 0 := by rw [← norm_neg_add]; gcongr
      calc
        ‖u 0‖ ≤ C * ‖v 0‖ := hnorm_u 0
        _ ≤ C * (‖h‖ + b 0) := by gcongr
        _ = C * b 0 + C * ‖h‖ := by rw [add_comm, mul_add]
    have : (∑ k ∈ range (n + 1), C * b k) ≤ ε * ‖h‖ :=
      calc (∑ k ∈ range (n + 1), C * b k)
        _ = (∑ k ∈ range (n + 1), (1 / 2 : ℝ) ^ k) * (ε * ‖h‖ / 2) := by
          simp only [b, mul_div_cancel₀ _ hC.ne.symm, ← sum_mul]
        _ ≤ 2 * (ε * ‖h‖ / 2) := by gcongr; apply sum_geometric_two_le
        _ = ε * ‖h‖ := mul_div_cancel₀ _ two_ne_zero
    calc
      ‖s n‖ ≤ ∑ k ∈ range (n + 1), ‖u k‖ := norm_sum_le _ _
      _ = (∑ k ∈ range n, ‖u (k + 1)‖) + ‖u 0‖ := sum_range_succ' _ _
      _ ≤ (∑ k ∈ range n, C * ‖v (k + 1)‖) + ‖u 0‖ := by gcongr; apply hnorm_u
      _ ≤ (∑ k ∈ range n, C * b (k + 1)) + (C * b 0 + C * ‖h‖) := by
        gcongr with k; exact (hv _ k.succ_pos).le
      _ = (∑ k ∈ range (n + 1), C * b k) + C * ‖h‖ := by rw [← add_assoc, sum_range_succ']
      _ ≤ (C + ε) * ‖h‖ := by
        rw [add_comm, add_mul]
        gcongr

/-- Given `f : NormedAddGroupHom G H` for some complete `G`, if every element `x` of the image of
an isometric immersion `j : NormedAddGroupHom K H` has a preimage under `f` whose norm is at most
`C*‖x‖` then the same holds for elements of the (topological) closure of this image with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its completion
(in this case the closure is the full target group).
-/
/-
**controlled_closure_range_of_complete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：controlled_closure_range_of_complete {f : NormedAddGroupHom G H} {K : Type
*} [SeminormedAddCommGroup K] {j : NormedAddGroupHom K H} (hj : forall x, ‖j x‖ 
= ‖x‖) {C ε : Real} (hC : 0 < C) (hε : 0 < ε) (hyp : forall k, exists g, f g = j
 k ∧ ‖g‖ <= C * ‖k‖) : f.SurjectiveOnWith j.range.topologicalClosure (C + ε)
参数：hj : forall x, ‖j x‖ = ‖x‖；hC : 0 < C；hε : 0 < ε；hyp : forall k, exists g, f 
g = j k ∧ ‖g‖ <= C * ‖k‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedAddGroupHom.mem_range`：mem_range (v : V₂) : v in f.range ↔ exists 
w, f w = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `controlled_closure_of_complete`：controlled_closure_of_complete {f : Norm
edAddGroupHom G H} {K : AddSubgroup H} {C ε : Real} (hC : 0 < C) (hε : 0 < ε) (h
yp : f.SurjectiveOnW…

--- 原说明 ---
Given `f : NormedAddGroupHom G H` for some complete `G`, if every element `x` of
 the image of
an isometric immersion `j : NormedAddGroupHom K H` has a preimage under `f` whos
e norm is at most
`C*‖x‖` then the same holds for elements of the (topological) closure of this im
age with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its 
completion
(in this case the closure is the full target group).
-/
theorem controlled_closure_range_of_complete {f : NormedAddGroupHom G H} {K : Type*}
    [SeminormedAddCommGroup K] {j : NormedAddGroupHom K H} (hj : ∀ x, ‖j x‖ = ‖x‖) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ k, ∃ g, f g = j k ∧ ‖g‖ ≤ C * ‖k‖) :
    f.SurjectiveOnWith j.range.topologicalClosure (C + ε) := by
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ‖g‖ ≤ C * ‖h‖ := by
    intro h h_in
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp
