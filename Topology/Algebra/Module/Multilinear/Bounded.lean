/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Images of (von Neumann) bounded sets under continuous multilinear maps

In this file we prove that continuous multilinear maps
send von Neumann bounded sets to von Neumann bounded sets.

We prove 2 versions of the theorem:
one assumes that the index type is nonempty,
and the other assumes that the codomain is a topological vector space.

## Implementation notes

We do not assume the index type `ι` to be finite.
While for a nonzero continuous multilinear map
the family `∀ i, E i` has to be essentially finite
(more precisely, all but finitely many `E i` has to be trivial),
proving theorems without a `[Finite ι]` assumption saves us some typeclass searches here and there.
-/

public section

open Bornology Filter Set Function
open scoped Topology

namespace Bornology.IsVonNBounded

variable {ι 𝕜 F : Type*} {E : ι → Type*} [NormedField 𝕜]
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The image of a von Neumann bounded set under a continuous multilinear map
is von Neumann bounded.

This version does not assume that the topologies on the domain and on the codomain
agree with the vector space structure in any way
but it assumes that `ι` is nonempty.
-/
/-
**Bornology.IsVonNBounded.image_multilinear'** 是 Mathlib 中的一个定理，位于命名空间 `Bornolog
y.IsVonNBounded`。
形式化陈述：image_multilinear' [Nonempty ι] {s : Set (forall i, E i)} (hs : IsVonNBoun
ded 𝕜 s) (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s)
参数：forall i, E i；hs : IsVonNBounded 𝕜 s；f : ContinuousMultilinearMap 𝕜 E F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `absorbs_iff_norm`：absorbs_iff_norm : Absorbs 𝕜 A B ↔ exists r, forall c 
: 𝕜, r <= ‖c‖ -> B subseteq c • A
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
The image of a von Neumann bounded set under a continuous multilinear map
is von Neumann bounded.

This version does not assume that the topologies on the domain and on the codoma
in
agree with the vector space structure in any way
but it assumes that `ι` is nonempty.
-/
theorem image_multilinear' [Nonempty ι] {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s)
    (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s) := fun V hV ↦ by
  classical
  if h₁ : ∀ c : 𝕜, ‖c‖ ≤ 1 then
    exact absorbs_iff_norm.2 ⟨2, fun c hc ↦ by linarith [h₁ c]⟩
  else
    let _ : NontriviallyNormedField 𝕜 := ⟨by simpa using h₁⟩
    obtain ⟨I, t, ht₀, hft⟩ :
        ∃ (I : Finset ι) (t : ∀ i, Set (E i)), (∀ i, t i ∈ 𝓝 0) ∧ Set.pi I t ⊆ f ⁻¹' V := by
      have hfV : f ⁻¹' V ∈ 𝓝 0 := (map_continuous f).tendsto' _ _ f.map_zero hV
      rwa [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hfV
    have : ∀ i, ∃ c : 𝕜, c ≠ 0 ∧ ∀ c' : 𝕜, ‖c'‖ ≤ ‖c‖ → ∀ x ∈ s, c' • x i ∈ t i := fun i ↦ by
      rw [isVonNBounded_pi_iff] at hs
      have := (hs i).tendsto_smallSets_nhds.eventually (mem_lift' (ht₀ i))
      rcases NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff.1 this with ⟨r, hr₀, hr⟩
      rcases NormedField.exists_norm_lt 𝕜 hr₀ with ⟨c, hc₀, hc⟩
      refine ⟨c, norm_pos_iff.1 hc₀, fun c' hle x hx ↦ ?_⟩
      exact hr (hle.trans_lt hc) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    choose c hc₀ hc using this
    rw [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV),
      NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    have hc₀' : ∏ i ∈ I, c i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hc₀ i
    refine ⟨‖∏ i ∈ I, c i‖, norm_pos_iff.2 hc₀', fun a ha ↦ mapsTo_image_iff.2 fun x hx ↦ ?_⟩
    let ⟨i₀⟩ := ‹Nonempty ι›
    set y := I.piecewise (fun i ↦ c i • x i) x
    calc
      f (update y i₀ ((a / ∏ i ∈ I, c i) • y i₀)) ∈ V := hft fun i hi => by
        rcases eq_or_ne i i₀ with rfl | hne
        · simp_rw [update_self, y, I.piecewise_eq_of_mem _ _ hi, smul_smul]
          refine hc _ _ ?_ _ hx
          calc
            ‖(a / ∏ i ∈ I, c i) * c i‖ ≤ (‖∏ i ∈ I, c i‖ / ‖∏ i ∈ I, c i‖) * ‖c i‖ := by
              rw [norm_mul, norm_div]; gcongr; exact ha.out.le
            _ ≤ 1 * ‖c i‖ := by gcongr; apply div_self_le_one
            _ = ‖c i‖ := one_mul _
        · simp_rw [update_of_ne hne, y, I.piecewise_eq_of_mem _ _ hi]
          exact hc _ _ le_rfl _ hx
      _ = a • f x := by
        rw [f.map_update_smul, update_eq_self, f.map_piecewise_smul, div_eq_mul_inv, mul_smul,
          inv_smul_smul₀ hc₀']

/-- The image of a von Neumann bounded set under a continuous multilinear map
is von Neumann bounded.

This version assumes that the codomain is a topological vector space.
-/
/-
**Bornology.IsVonNBounded.image_multilinear** 是 Mathlib 中的一个定理，位于命名空间 `Bornology
.IsVonNBounded`。
形式化陈述：image_multilinear [ContinuousSMul 𝕜 F] {s : Set (forall i, E i)} (hs : IsV
onNBounded 𝕜 s) (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s)
参数：forall i, E i；hs : IsVonNBounded 𝕜 s；f : ContinuousMultilinearMap 𝕜 E F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bornology.isBounded_iff_isVonNBounded`：isBounded_iff_isVonNBounded {s : 
Set E} : @IsBounded _ (vonNBornology 𝕜 E) s ↔ IsVonNBounded 𝕜 s
· 使用定理 `Set.Finite.isBounded`：Set.Finite.isBounded [Bornology α] {s : Set α} (hs
 : s.Finite) : IsBounded s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Bornology.IsVonNBounded.image_multilinear'`：image_multilinear' [Nonempty
 ι] {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s) (f : ContinuousMultilinea
rMap 𝕜 E F) : IsVonNBounded 𝕜 (f…

--- 原说明 ---
The image of a von Neumann bounded set under a continuous multilinear map
is von Neumann bounded.

This version assumes that the codomain is a topological vector space.
-/
theorem image_multilinear [ContinuousSMul 𝕜 F] {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s)
    (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    exact (isBounded_iff_isVonNBounded _).1 <|
      @Set.Finite.isBounded _ (vonNBornology 𝕜 F) _ (s.toFinite.image _)
  | inr h => exact hs.image_multilinear' f

end IsVonNBounded

end Bornology

