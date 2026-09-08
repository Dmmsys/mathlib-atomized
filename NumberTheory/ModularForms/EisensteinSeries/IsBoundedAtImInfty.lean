/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.

## Outline of argument

We need to bound the value of the Eisenstein series (acted on by `A : SL(2,ℤ)`)
at a given point `z` in the upper half plane. Since these are modular forms of level `Γ(N)`,
it suffices to prove this for `z ∈ verticalStrip N z.im`.

We can then, first observe that the slash action just changes our `a` to `(a ᵥ* A)` and
we then use our bounds for Eisenstein series in these vertical strips to get the result.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix SlashInvariantForm CongruenceSubgroup

open scoped MatrixGroups

namespace EisensteinSeries

/-
**EisensteinSeries.summable_norm_eisSummand** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstei
nSeries`。
形式化陈述：summable_norm_eisSummand {k : Int} (hk : 3 <= k) (z : ℍ) : Summable fun (x
 : Fin 2 -> Int) => ‖(eisSummand k x z)‖
参数：hk : 3 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `EisensteinSeries.summable_one_div_norm_rpow`：summable_one_div_norm_rpow 
{k : Real} (hk : 2 < k) : Summable fun (x : Fin 2 -> Int) => ‖x‖ ^ (-k)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用引理 `EisensteinSeries.summand_bound`：summand_bound {k : Real} (hk : 0 <= k) (
x : Fin 2 -> Int) : ‖x 0 * (z : Complex) + x 1‖ ^ (-k) <= (r z) ^ (-k) * ‖x‖ ^ (
-k)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
lemma summable_norm_eisSummand {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖ := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : ℝ)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro b
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound z (show 0 ≤ (k : ℝ) by positivity) b

/-- The norm of the restricted sum is less than the full sum of the norms. -/
/-
**EisensteinSeries.norm_le_tsum_norm** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries
`。
形式化陈述：norm_le_tsum_norm (N : Nat) (a : Fin 2 -> ZMod N) (k : Int) (hk : 3 <= k) 
(z : ℍ) : ‖eisensteinSeries a k z‖ <= ∑' (x : Fin 2 -> Int), ‖eisSummand k x z‖
参数：N : Nat；a : Fin 2 -> ZMod N；k : Int；hk : 3 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_tsum_le_tsum_norm`：norm_tsum_le_tsum_norm {f : ι -> E} (hf : Summab
le fun i => ‖f i‖) : ‖∑' i, f i‖ <= ∑' i, ‖f i‖
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用引理 `EisensteinSeries.summable_norm_eisSummand`：summable_norm_eisSummand {k :
 Int} (hk : 3 <= k) (z : ℍ) : Summable fun (x : Fin 2 -> Int) => ‖(eisSummand k 
x z)‖
· 使用定理 `Summable.tsum_subtype_le`：∀ {κ : Type u_4} {γ : Type u_5} [inst : AddCom
mGroup γ] [inst_1 : PartialOrder γ] [IsOrderedAddMonoid γ]   [inst_3 : UniformSp
ace γ] [IsUnif…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
The norm of the restricted sum is less than the full sum of the norms.
-/
lemma norm_le_tsum_norm (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ‖eisensteinSeries a k z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  simp_rw [eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖) _ (fun _ ↦ norm_nonneg _)
      (summable_norm_eisSummand hk z))

/-- Eisenstein series are bounded at infinity. -/
/-
**EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF** 是 Mathlib 中的一个定理，位于命
名空间 `EisensteinSeries`。
形式化陈述：isBoundedAtImInfty_eisensteinSeriesSIF {N : Nat} [NeZero N] (a : Fin 2 -> 
ZMod N) {k : Int} (hk : 3 <= k) (A : SL(2, Int)) : IsBoundedAtImInfty (eisenstei
nSeriesSIF a k ∣[k] A)
参数：a : Fin 2 -> ZMod N；hk : 3 <= k；A : SL(2, Int)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.ofNat_pos`：ofNat_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRin
g α] [Nontrivial α] {n : Nat} [n.AtLeastTwo] : 0 < (ofNat(n) : α)
· 使用定理 `UpperHalfPlane.ModularGroup_T_zpow_mem_verticalStrip`：ModularGroup_T_zpo
w_mem_verticalStrip (z : ℍ) {N : Nat} (hn : 0 < N) : exists n : Int, ModularGrou
p.T ^ (N * n) • z in verticalStrip N z.im
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashInvariantForm.coe_mk`：SlashInvariantForm.coe_mk (f : ℍ -> Complex) 
(hf : forall γ in Γ, f ∣[k] γ = f) : ⇑(mk f hf) = f
· 使用引理 `EisensteinSeries.eisensteinSeries_slash_apply`：eisensteinSeries_slash_ap
ply (k : Int) (γ : SL(2, Int)) : eisensteinSeries a k ∣[k] γ = eisensteinSeries 
(a ᵥ* γ) k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EisensteinSeries.eisensteinSeriesSIF_apply`：eisensteinSeriesSIF_apply (k
 : Int) (z : ℍ) : eisensteinSeriesSIF a k z = eisensteinSeries a k z
· 使用定理 `SlashInvariantForm.T_zpow_width_invariant`：T_zpow_width_invariant (N : N
at) (k n : Int) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) : f (((ModularGroup
.T ^ (N * n))) • z) = f z
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `EisensteinSeries.norm_le_tsum_norm`：norm_le_tsum_norm (N : Nat) (a : Fin
 2 -> ZMod N) (k : Int) (hk : 3 <= k) (z : ℍ) : ‖eisensteinSeries a k z‖ <= ∑' (
x : Fin 2 -> Int), ‖eisS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用引理 `EisensteinSeries.summand_bound_of_mem_verticalStrip`：summand_bound_of_me
m_verticalStrip {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int) {A B : Real} (hB : 0
 < B) (hz : z in verticalStrip A B) : ‖x …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Eisenstein series are bounded at infinity.
-/
theorem isBoundedAtImInfty_eisensteinSeriesSIF {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) {k : ℤ}
    (hk : 3 ≤ k) (A : SL(2, ℤ)) : IsBoundedAtImInfty (eisensteinSeriesSIF a k ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeriesSIF] at *
  refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [SlashInvariantForm.coe_mk, eisensteinSeries_slash_apply, ← eisensteinSeriesSIF_apply,
    ← T_zpow_width_invariant N k n (eisensteinSeriesSIF (a ᵥ* A) k) z]
  apply le_trans (norm_le_tsum_norm N (a ᵥ* A) k hk _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

@[deprecated (since := "2026-02-10")]
alias isBoundedAtImInfty_eisensteinSeries_SIF := isBoundedAtImInfty_eisensteinSeriesSIF

end EisensteinSeries

