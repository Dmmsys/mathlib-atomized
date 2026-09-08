/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.UrysohnsLemma

/-!
# Perfectly normal topological spaces.

This file proves some properties of a perfectly normal space.

## TODO

Prove that the product of a perfectly normal space and a metric space is perfectly normal.

-/

@[expose] public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A topological space is perfectly normal iff every closed set is the zero set of a continuous
function taking values in the unit interval. -/
/-
**perfectlyNormalSpace_iff_forall_isClosed_preimage_zero** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：perfectlyNormalSpace_iff_forall_isClosed_preimage_zero : PerfectlyNormalSp
ace X ↔ forall s, IsClosed s -> exists f : C(X, Real), s = f ⁻¹' {0} ∧ forall x,
 f x in Icc (0 : Real) 1 where mp h s hs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isGδ_iff_eq_iInter_nat`：isGδ_iff_eq_iInter_nat {s : Set X} : IsGδ s ↔ ex
ists (f : Nat -> Set X), (forall n, IsOpen (f n)) ∧ s = ⋂ n, f n
· 使用定理 `IsClosed.isGδ`：IsClosed.isGδ [PerfectlyNormalSpace X] {s : Set X} (hs : 
IsClosed s) : IsGδ s
· 使用定理 `LE.le.disjoint_compl_right`：LE.le.disjoint_compl_right (h : a <= b) : Di
sjoint a bᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 127 条，此处仅展示前 30 条）

--- 原说明 ---
A topological space is perfectly normal iff every closed set is the zero set of 
a continuous
function taking values in the unit interval.
-/
theorem perfectlyNormalSpace_iff_forall_isClosed_preimage_zero :
    PerfectlyNormalSpace X ↔ ∀ s, IsClosed s → ∃ f : C(X, ℝ), s = f ⁻¹' {0} ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 where
  mp h s hs := by
    -- write `s` as the intersection of a sequence of open sets `U n`
    obtain ⟨U, ho, hu⟩ := isGδ_iff_eq_iInter_nat.1 hs.isGδ
    have (n : ℕ) : Disjoint s (U n)ᶜ := by
      apply LE.le.disjoint_compl_right
      grw [hu, iInter_subset]
    -- for each `n`, construct a continuous function `f n` that separates `s` from `(U n)ᶜ`
    choose f hfs hfu hfr using fun n =>
      exists_continuous_zero_one_of_isClosed hs (ho n).isClosed_compl (this n)
    have hsb (x : X) (n : ℕ) : ‖(f n) x * (1 / 2 / 2 ^ n)‖ ≤ 1 / 2 / 2 ^ n := by
      simp [abs_of_nonneg (hfr n x).1, (hfr n x).2]
    have hsx (x : X) : Summable fun n => f n x * (1 / 2 / 2 ^ n) :=
      (summable_geometric_two' 1).of_norm_bounded fun n => hsb x n
    -- consider the infinite sum of `f n x * (1 / 2 / 2 ^ n)`, which is uniformly convergent and
    -- thus continuous because it is dominated by a geometric series
    let h : C(X, ℝ) :=
      { toFun x := ∑' n, f n x * (1 / 2 / 2 ^ n)
        continuous_toFun :=
          continuous_tsum (fun n => by fun_prop) (summable_geometric_two' 1) fun n x => hsb x n }
    refine ⟨h, ?_, fun x => ⟨?_, ?_⟩⟩
    · ext x
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · suffices ∀ n, f n x = 0 from by simp [h, this]
        exact fun n => hfs n hp
      · contrapose h
        simp only [preimage, notMem_ofPred_iff, ContinuousMap.coe_mk, mem_singleton_iff]
        apply ne_of_gt
        obtain ⟨i, hi⟩ := mem_iUnion.1 <| compl_iInter _ ▸ mem_compl (hu ▸ h)
        calc
        _ < 1 / 2 / 2 ^ i := by positivity
        _ = f i x * (1 / 2 / 2 ^ i) := by simp [hfu i hi]
        _ ≤ _ := (hsx x).le_tsum i fun j hj => by positivity [(hfr j x).1]
    · exact tsum_nonneg fun n => by simp [(hfr n x).1]
    · calc
      _ = ∑' n, f n x * (1 / 2 / 2 ^ n) := by simp [h]
      _ ≤ ∑' n, 1 / 2 / 2 ^ n :=
        (hsx x).tsum_le_tsum (fun n => by simp [(hfr n x).2]) (summable_geometric_two' 1)
      _ = _ := tsum_geometric_two' 1
  mpr h :=
    { normal s t hs ht hst := by
        -- pick `f, g` such that `s = f ⁻¹' {0}` and `t = g ⁻¹' {0}`, and then the function
        -- `f / (f  + g)` separates `s` and `t`.
        obtain ⟨f, hf, hfr⟩ := h s hs
        obtain ⟨g, hg, hgr⟩ := h t ht
        have hsn : SeparatedNhds {(0 : ℝ)} {1} :=
          SeparatedNhds.of_finite (finite_singleton _) (finite_singleton _)
          (disjoint_singleton.2 zero_ne_one)
        have hfg (x : X) : f x + g x ≠ 0 := by
          simp_all only [preimage, mem_singleton_iff]
          by_cases! hfx : f x = 0
          · simpa [hfx] using hst.notMem_of_mem_left hfx
          · positivity [(hgr x).1, (hfr x).1]
        have hp : s = (fun a => f a / (f a + g a)) ⁻¹' {0} := by simp_all [preimage]
        have : t = (fun a => f a / (f a + g a)) ⁻¹' {1} := by simp_all [preimage, div_eq_one_iff_eq]
        rw [hp, this]
        exact hsn.preimage (f.continuous.div₀ (f.continuous.add g.continuous) hfg)
      closed_gdelta s hs := by
        by_cases! hse : s = ∅
        · simp_all
        -- pick `f` such that `s = f ⁻¹' {0} = ⋂ n, f ⁻¹' (Iio (1 / (n + 1)))`
        obtain ⟨f, hf, hfr⟩ := h s hs
        refine isGδ_iff_eq_iInter_nat.2 ⟨fun n => f ⁻¹' (Iio (1 / (n + 1))),
          fun n => ?_, ?_⟩
        · exact f.continuous.isOpen_preimage _ isOpen_Iio
        · simp only [hf, ← preimage_iInter,
            ← preimage_range_inter (s := ⋂ (n : ℕ), Iio (1 / (n + 1) : ℝ)), inter_iInter]
          congr
          rw [eq_comm, eq_singleton_iff_unique_mem]
          refine ⟨mem_iInter_of_mem fun n => ?_, fun x h => ?_⟩
          · exact ⟨(hf ▸ hse : (f ⁻¹' {0}).Nonempty), show 0 < (1 / (n + 1) : ℝ) by positivity⟩
          · apply le_antisymm
            · simp only [mem_iInter, mem_inter_iff, mem_Iio] at h
              exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (h n).2.le)
            · rcases (mem_iInter.1 h 0).1 with ⟨x, rfl⟩
              exact (hfr x).1 }

@[deprecated (since := "2026-06-03")]
alias Topology.IsEmbedding.perfectlyNormalSpace := Topology.IsInducing.perfectlyNormalSpace
