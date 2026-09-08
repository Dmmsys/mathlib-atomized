/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!

# Connection between adic properties and topological properties

## Main results
- `IsAdic.isPrecomplete_iff`:
  `IsPrecomplete I R` is equivalent to `CompleteSpace R` in the adic topology.
- `IsAdic.isAdicComplete_iff`:
  `IsAdicComplete I R` is equivalent to `CompleteSpace R` and `T2Space R` in the adic topology.

-/

public section

section TopologicalSpace

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R} (hI : IsAdic I)

include hI in
/-- `IsHausdorff I R` is equivalent to being Hausdorff in the adic topology. -/
/-
**IsAdic.isHausdorff_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAdic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : TopologicalSpace R] {I : Id
eal R},   IsAdic I → (IsHausdorff I R ↔ T2Space R)
参数：IsHausdorff I R ↔ T2Space R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddGroupFilterBasis.t2Space_iff_sInter_subset`：∀ {G : Type u} [inst : Ad
dGroup G] [t : TopologicalSpace G] (F : AddGroupFilterBasis G),   F.topology = t
 → (T2Space G ↔ ⋂₀ F.sets ⊆ {0})
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isHausdorff_iff`：isHausdorff_iff : IsHausdorff I M ↔ forall x : M, (fora
ll n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FilterBasis.mk.congr_simp`：∀ {α : Type u_6} (sets sets_1 : Set (Set α)) 
(e_sets : sets = sets_1) (nonempty : sets.Nonempty)   (inter_sets : ∀ {x y : Set
 α}, x ∈ sets →…
· 使用定理 `AddGroupFilterBasis.mk.congr_simp`：∀ {A : Type u} [inst : AddGroup A] (t
oFilterBasis toFilterBasis_1 : FilterBasis A)   (e_toFilterBasis : toFilterBasis
 = toFilterBasis_1) (ze…
· 使用定理 `RingFilterBasis.mk.congr_simp`：∀ {R : Type u} [inst : Ring R] [toAddGrou
pFilterBasis : AddGroupFilterBasis R]   [toAddGroupFilterBasis_1 : AddGroupFilte
rBasis R]   (e_toAd…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`IsHausdorff I R` is equivalent to being Hausdorff in the adic topology.
-/
protected lemma IsAdic.isHausdorff_iff : IsHausdorff I R ↔ T2Space R := by
  rw [I.ringFilterBasis.t2Space_iff_sInter_subset hI.symm, isHausdorff_iff]
  simp +instances [SModEq.zero, Ideal.ringFilterBasis, RingSubgroupsBasis.toRingFilterBasis]

end TopologicalSpace

section UniformSpace

open Topology Uniformity

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  {I : Ideal R} (hI : IsAdic I)

include hI in
/-- `IsPrecomplete I R` is equivalent to being complete in the adic topology. -/
/-
**IsAdic.isPrecomplete_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAdic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : UniformSpace R] [IsUniformA
ddGroup R] {I : Ideal R},   IsAdic I → (IsPrecomplete I R ↔ CompleteSpace R)
参数：IsPrecomplete I R ↔ CompleteSpace R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.isCountablyGenerated`：∀ {α : Type u_1} {ι : Type u_4} [C
ountable ι] {f : Filter α} {p : ι → Prop} {s : ι → Set α},   f.HasBasis p s → f.
IsCountablyGenerated
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `IsAdic.hasBasis_nhds_zero`：IsAdic.hasBasis_nhds_zero {I : Ideal R} (hI :
 IsAdic I) : (𝓝 (0 : R)).HasBasis (fun _ => True) fun n => ↑(I ^ n)
· 使用定理 `IsUniformAddGroup.uniformity_countably_generated`：∀ {α : Type u_1} [inst
 : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] [(nhds 0).IsCount
ablyGenerated],   (uniformity α).IsCou…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformSpace.complete_of_cauchySeq_tendsto`：complete_of_cauchySeq_tendst
o (H' : forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) : C
ompleteSpace α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.cauchySeq_iff`：Filter.HasBasis.cauchySeq_iff {γ} [Nonemp
ty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (h :
 (𝓤 α).HasBasis p s…
· 使用定理 `Filter.HasBasis.uniformity_of_nhds_zero`：∀ {α : Type u_1} [inst : Unifor
mSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {ι : Sort u_3} {p : ι → Pr
op}   {U : ι → Set α}, (nhds …
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `IsAdic.hasBasis_nhds`：IsAdic.hasBasis_nhds {I : Ideal R} (hI : IsAdic I)
 (x : R) : (𝓝 x).HasBasis (fun _ => True) fun n => (x + ·) '' ↑(I ^ n)
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
`IsPrecomplete I R` is equivalent to being complete in the adic topology.
-/
protected lemma IsAdic.isPrecomplete_iff : IsPrecomplete I R ↔ CompleteSpace R := by
  have := hI.hasBasis_nhds_zero.isCountablyGenerated
  have : (𝓤 R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  simp only [isPrecomplete_iff, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  constructor
  · intro H
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    have : ∀ i, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → u n - u m ∈ I ^ i := by
      simpa using hI.hasBasis_nhds_zero.uniformity_of_nhds_zero.cauchySeq_iff.mp hu
    choose N hN using this
    obtain ⟨L, hL⟩ := H (fun i ↦ u ((Finset.Iic i).sup N))
      fun _ ↦ hN _ _ (Finset.le_sup (by simpa)) _ (Finset.le_sup (by simp))
    use L
    suffices ∀ i, ∃ N, ∀ n, N ≤ n → u n - L ∈ I ^ i by
      simpa [(hI.hasBasis_nhds L).tendsto_right_iff, sub_eq_neg_add]
    refine fun i ↦ ⟨(Finset.Iic i).sup N, fun n hn ↦ ?_⟩
    have := Ideal.add_mem _ (hN i ((Finset.Iic i).sup N) (Finset.le_sup (by simp))
      n (.trans (Finset.le_sup (by simp)) hn)) (hL i)
    rwa [sub_add_sub_cancel] at this
  · intro H f hf
    obtain ⟨L, hL⟩ := CompleteSpace.complete (f := Filter.atTop.map f)
      (hI.hasBasis_nhds_zero.uniformity_of_nhds_zero.cauchySeq_iff.mpr fun i _ ↦
        ⟨i, fun m hm n hn ↦ by simpa using Ideal.sub_mem _ (hf hm) (hf hn)⟩)
    refine ⟨L, fun i ↦ ?_⟩
    obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → f n - L ∈ I ^ i := by
      simpa [sub_eq_neg_add] using (hI.hasBasis_nhds L).tendsto_right_iff.mp hL i
    simpa using Ideal.add_mem _ (hN (max i N) le_sup_right) (hf (le_max_left i N))

include hI in
/-- `IsAdicComplete I R` is equivalent to being complete and hausdorff in the adic topology. -/
/-
**IsAdic.isAdicComplete_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAdic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : UniformSpace R] [IsUniformA
ddGroup R] {I : Ideal R},   IsAdic I → (IsAdicComplete I R ↔ CompleteSpace R ∧ T
2Space R)
参数：IsAdicComplete I R ↔ CompleteSpace R ∧ T2Space R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAdicComplete_iff`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) (
M : Type u_4) [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M], IsAdicCo
mplete I…
· 使用定理 `IsAdic.isHausdorff_iff`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : T
opologicalSpace R] {I : Ideal R},   IsAdic I → (IsHausdorff I R ↔ T2Space R)
· 使用定理 `IsAdic.isPrecomplete_iff`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 :
 UniformSpace R] [IsUniformAddGroup R] {I : Ideal R},   IsAdic I → (IsPrecomplet
e I R ↔ Comple…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`IsAdicComplete I R` is equivalent to being complete and hausdorff in the adic t
opology.
-/
protected lemma IsAdic.isAdicComplete_iff : IsAdicComplete I R ↔ CompleteSpace R ∧ T2Space R := by
  rw [isAdicComplete_iff, hI.isHausdorff_iff, hI.isPrecomplete_iff, and_comm]

end UniformSpace

section congrRingEquiv

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S)

/-
**IsPrecomplete.congr_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrecomplete.congr_ringEquiv : IsPrecomplete (I.map e) S ↔ IsPrecomplete 
I R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `IsAdic.isPrecomplete_iff`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 :
 UniformSpace R] [IsUniformAddGroup R] {I : Ideal R},   IsAdic I → (IsPrecomplet
e I R ↔ Comple…
· 使用定理 `WithIdeal.instIsUniformAddGroup`：∀ (R : Type u_1) [inst : CommRing R] [i
nst_1 : WithIdeal R], IsUniformAddGroup R
· 使用定理 `completeSpace_congr`：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbe
dding e) : CompleteSpace α ↔ CompleteSpace β
· 使用引理 `UniformEquiv.isUniformEmbedding`：isUniformEmbedding (h : α ≃ᵤ β) : IsUni
formEmbedding h
-/
theorem IsPrecomplete.congr_ringEquiv : IsPrecomplete (I.map e) S ↔ IsPrecomplete I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm, IsAdic.isPrecomplete_iff (by rfl), IsAdic.isPrecomplete_iff (by rfl)]
  exact completeSpace_congr (e := WithIdeal.uniformEquiv e rfl) (by
    simpa using UniformEquiv.isUniformEmbedding ..)
/-
**IsHausdorff.congr_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.congr_ringEquiv : IsHausdorff (I.map e) S ↔ IsHausdorff I R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `IsAdic.isHausdorff_iff`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : T
opologicalSpace R] {I : Ideal R},   IsAdic I → (IsHausdorff I R ↔ T2Space R)
· 使用定理 `Homeomorph.t2Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
-/
theorem IsHausdorff.congr_ringEquiv : IsHausdorff (I.map e) S ↔ IsHausdorff I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm, IsAdic.isHausdorff_iff rfl, IsAdic.isHausdorff_iff rfl]
  exact ⟨fun _ ↦ (WithIdeal.uniformEquiv e rfl).toHomeomorph.t2Space, fun _ ↦
    (WithIdeal.uniformEquiv e rfl).toHomeomorph.symm.t2Space⟩
/-
**IsAdicComplete.congr_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAdicComplete.congr_ringEquiv : IsAdicComplete (I.map e) S ↔ IsAdicComple
te I R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsAdicComplete.congr_ringEquiv : IsAdicComplete (I.map e) S ↔ IsAdicComplete I R := by
  simp [isAdicComplete_iff, IsHausdorff.congr_ringEquiv, IsPrecomplete.congr_ringEquiv]

end congrRingEquiv

