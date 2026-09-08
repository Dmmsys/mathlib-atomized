/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

* `Ideal.IsHomogeneous.isPrime_iff`: for any `I : Ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
  homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `Ideal.IsPrime.homogeneousCore`: for any `I : Ideal A`, if `I` is prime, then
  `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `Ideal.IsHomogeneous.radical`: for any `I : Ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `HomogeneousIdeal.radical`: for any `I : HomogeneousIdeal 𝒜`, `I.radical` is the
  radical of `I` as a `HomogeneousIdeal 𝒜`.

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
linearly ordered cancellative monoid. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `Ideal.IsHomogeneous.isPrime_iff`
fails for a non-cancellative set see `Counterexamples/HomogeneousPrimeNotPrime.lean`.

## Tags

homogeneous, radical
-/

@[expose] public section


open GradedRing DirectSum SetLike Finset

variable {ι σ A : Type*}
variable [CommRing A]
variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

/-
**Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : 
I.IsHomogeneous 𝒜) (I_ne_top : I != ⊤) (homogeneous_mem_or_mem : forall {x y : A
}, IsHomogeneousElem 𝒜 x -> IsHomogeneousElem 𝒜 y -> x * y in I -> x in I ∨ y in
 I) : Ideal.IsPrime I
参数：hI : I.IsHomogeneous 𝒜；I_ne_top : I != ⊤；homogeneous_mem_or_mem : forall {x y
 : A}, IsHomogeneousElem 𝒜 x -> IsHomogeneousElem 𝒜 y -> x * y in I -> x in I ∨ 
y in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_nonempty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (Finset.filter p s).Nonempty ↔ ∃ a ∈ s, p a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
· 使用定理 `trivial`：True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DirectSum.coe_mul_apply`：coe_mul_apply [AddMonoid ι] [SetLike.GradedMono
id A] [forall (i : ι) (x : A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) :
 ((r * r') n …
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 56 条，此处仅展示前 30 条）
-/
theorem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (I_ne_top : I ≠ ⊤)
    (homogeneous_mem_or_mem :
      ∀ {x y : A}, IsHomogeneousElem 𝒜 x → IsHomogeneousElem 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I) :
    Ideal.IsPrime I :=
  ⟨I_ne_top, by
    intro x y hxy
    by_contra! ⟨rid₁, rid₂⟩
    classical
      /-
        The idea of the proof is the following :
        since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
        Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support | yⱼ ∉ J}`;
        let `max₁, max₂` be the maximum of the two sets, then `proj (max₁ + max₂) (x * y) ∈ I`.
        Then, `proj max₁ x ∉ I` and `proj max₂ j ∉ I`
        but `proj i x ∈ I` for all `max₁ < i` and `proj j y ∈ I` for all `max₂ < j`.
        `  proj (max₁ + max₂) (x * y)`
        `= ∑ {(i, j) ∈ supports | i + j = max₁ + max₂}, xᵢ * yⱼ`
        `= proj max₁ x * proj max₂ y`
        `  + ∑ {(i, j) ∈ supports \ {(max₁, max₂)} | i + j = max₁ + max₂}, xᵢ * yⱼ`.
        This is a contradiction, because both `proj (max₁ + max₂) (x * y) ∈ I` and the sum on the
        right-hand side is in `I` however `proj max₁ x * proj max₂ y` is not in `I`.
        -/
      set set₁ := {i ∈ (decompose 𝒜 x).support | proj 𝒜 i x ∉ I} with set₁_eq
      set set₂ := {i ∈ (decompose 𝒜 y).support | proj 𝒜 i y ∉ I} with set₂_eq
      have nonempty :
        ∀ x : A, x ∉ I → {i ∈ (decompose 𝒜 x).support | proj 𝒜 i x ∉ I}.Nonempty := by
        intro x hx
        rw [filter_nonempty_iff]
        contrapose! hx
        simp_rw [proj_apply] at hx
        rw [← sum_support_decompose 𝒜 x]
        exact Ideal.sum_mem _ hx
      set max₁ := set₁.max' (nonempty x rid₁)
      set max₂ := set₂.max' (nonempty y rid₂)
      have mem_max₁ : max₁ ∈ set₁ := max'_mem set₁ (nonempty x rid₁)
      have mem_max₂ : max₂ ∈ set₂ := max'_mem set₂ (nonempty y rid₂)
      replace hxy : proj 𝒜 (max₁ + max₂) (x * y) ∈ I := hI _ hxy
      have mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∈ I := by
        set antidiag :=
          {z ∈ (decompose 𝒜 x).support ×ˢ (decompose 𝒜 y).support | z.1 + z.2 = max₁ + max₂}
           with ha
        have mem_antidiag : (max₁, max₂) ∈ antidiag := by
          simp only [antidiag, mem_filter, mem_product]
          exact ⟨⟨mem_of_mem_filter _ mem_max₁, mem_of_mem_filter _ mem_max₂⟩, trivial⟩
        have eq_add_sum :=
          calc
            proj 𝒜 (max₁ + max₂) (x * y) = ∑ ij ∈ antidiag, proj 𝒜 ij.1 x * proj 𝒜 ij.2 y := by
              simp_rw [ha, proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply 𝒜]
            _ =
                proj 𝒜 max₁ x * proj 𝒜 max₂ y +
                  ∑ ij ∈ antidiag.erase (max₁, max₂), proj 𝒜 ij.1 x * proj 𝒜 ij.2 y :=
              (add_sum_erase _ _ mem_antidiag).symm
        rw [eq_sub_of_add_eq eq_add_sum.symm]
        refine Ideal.sub_mem _ hxy (Ideal.sum_mem _ fun z H => ?_)
        rcases z with ⟨i, j⟩
        simp only [antidiag, mem_erase, Prod.mk_inj, Ne, mem_filter, mem_product] at H
        rcases H with ⟨H₁, ⟨H₂, H₃⟩, H₄⟩
        have max_lt : max₁ < i ∨ max₂ < j := by
          convert! le_or_lt_of_add_le_add H₄.ge using 1
          rw [Ne.le_iff_lt]
          rintro rfl
          cases H₁ ⟨rfl, add_left_cancel H₄⟩
        rcases max_lt with max_lt | max_lt
        · -- in this case `max₁ < i`, then `xᵢ ∈ I`; for otherwise `i ∈ set₁` then `i ≤ max₁`.
          have notMem : i ∉ set₁ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₁ (nonempty x rid₁)).mp max_lt i h)
          rw [set₁_eq] at notMem
          simp only [not_and, Classical.not_not, mem_filter] at notMem
          exact Ideal.mul_mem_right _ I (notMem H₂)
        · -- in this case `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
          have notMem : j ∉ set₂ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₂ (nonempty y rid₂)).mp max_lt j h)
          rw [set₂_eq] at notMem
          simp only [not_and, Classical.not_not, mem_filter] at notMem
          exact Ideal.mul_mem_left I _ (notMem H₃)
      have notMem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∉ I := by
        have neither_mem : proj 𝒜 max₁ x ∉ I ∧ proj 𝒜 max₂ y ∉ I := by
          rw [mem_filter] at mem_max₁ mem_max₂
          exact ⟨mem_max₁.2, mem_max₂.2⟩
        intro _rid
        rcases homogeneous_mem_or_mem ⟨max₁, SetLike.coe_mem _⟩ ⟨max₂, SetLike.coe_mem _⟩ mem_I
          with h | h
        · apply neither_mem.1 h
        · apply neither_mem.2 h
      exact notMem_I mem_I⟩
/-
**Ideal.IsHomogeneous.isPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.isPrime_iff {I : Ideal A} (h : I.IsHomogeneous 𝒜) : I.
IsPrime ↔ I != ⊤ ∧ forall {x y : A}, IsHomogeneousElem 𝒜 x -> IsHomogeneousElem 
𝒜 y -> x * y in I -> x in I ∨ y in I
参数：h : I.IsHomogeneous 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`：Ideal.IsHomogeneo
us.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (I_n
e_top : I != ⊤) (homogeneous_mem_or_mem : f…
-/
theorem Ideal.IsHomogeneous.isPrime_iff {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.IsPrime ↔
      I ≠ ⊤ ∧
        ∀ {x y : A},
          IsHomogeneousElem 𝒜 x → IsHomogeneousElem 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun HI => ⟨HI.ne_top, fun _ _ hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩
/-
**Ideal.IsPrime.homogeneousCore** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsPrime.homogeneousCore {I : Ideal A} (h : I.IsPrime) : (I.homogeneo
usCore 𝒜).toIdeal.IsPrime
参数：h : I.IsPrime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`：Ideal.IsHomogeneo
us.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (I_n
e_top : I != ⊤) (homogeneous_mem_or_mem : f…
· 使用定理 `HomogeneousIdeal.isHomogeneous`：HomogeneousIdeal.isHomogeneous (I : Homo
geneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.toIdeal_homogeneousCore_le`：Ideal.toIdeal_homogeneousCore_le : (I.
homogeneousCore 𝒜).toIdeal <= I
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Ideal.mem_homogeneousCore_of_homogeneous_of_mem`：Ideal.mem_homogeneousCo
re_of_homogeneous_of_mem {x : A} (h : SetLike.IsHomogeneousElem 𝒜 x) (hmem : x i
n I) : x in I.homogeneousCore 𝒜
-/
theorem Ideal.IsPrime.homogeneousCore {I : Ideal A} (h : I.IsPrime) :
    (I.homogeneousCore 𝒜).toIdeal.IsPrime := by
  apply (Ideal.homogeneousCore 𝒜 I).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine H.imp ?_ ?_
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hx
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hy
/-
**Ideal.IsHomogeneous.radical_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.IsHomogeneous 𝒜) : I.
radical = InfSet.sInf { J | Ideal.IsHomogeneous 𝒜 J ∧ I <= J ∧ J.IsPrime }
参数：hI : I.IsHomogeneous 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sInf_le_sInf_of_isCoinitialFor`：∀ {α : Type u_1} [inst : CompleteSemilat
ticeInf α] {s t : Set α}, IsCoinitialFor s t → sInf t ≤ sInf s
· 使用定理 `HomogeneousIdeal.isHomogeneous`：HomogeneousIdeal.isHomogeneous (I : Homo
geneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self`：Ideal.IsHomogeneous
.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) : (I.homogeneousCore 𝒜)
.toIdeal = I
· 使用定理 `Ideal.homogeneousCore_mono`：Ideal.homogeneousCore_mono : Monotone (Ideal
.homogeneousCore 𝒜)
· 使用定理 `Ideal.IsPrime.homogeneousCore`：Ideal.IsPrime.homogeneousCore {I : Ideal 
A} (h : I.IsPrime) : (I.homogeneousCore 𝒜).toIdeal.IsPrime
· 使用定理 `Ideal.toIdeal_homogeneousCore_le`：Ideal.toIdeal_homogeneousCore_le : (I.
homogeneousCore 𝒜).toIdeal <= I
-/
theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    I.radical = InfSet.sInf { J | Ideal.IsHomogeneous 𝒜 J ∧ I ≤ J ∧ J.IsPrime } := by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    rintro J ⟨HJ₁, HJ₂⟩
    refine ⟨(J.homogeneousCore 𝒜).toIdeal, ?_, J.toIdeal_homogeneousCore_le _⟩
    refine ⟨HomogeneousIdeal.isHomogeneous _, ?_, HJ₂.homogeneousCore⟩
    exact hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ HJ₁)
/-
**Ideal.IsHomogeneous.radical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous 𝒜) : I.radi
cal.IsHomogeneous 𝒜
参数：h : I.IsHomogeneous 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsHomogeneous.radical_eq`：Ideal.IsHomogeneous.radical_eq {I : Idea
l A} (hI : I.IsHomogeneous 𝒜) : I.radical = InfSet.sInf { J | Ideal.IsHomogeneou
s 𝒜 J ∧ I <= J ∧ J.I…
· 使用定理 `Ideal.IsHomogeneous.sInf`：sInf {ℐ : Set (Ideal A)} (h : forall I in ℐ, I
deal.IsHomogeneous 𝒜 I) : (sInf ℐ).IsHomogeneous 𝒜
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.radical.IsHomogeneous 𝒜 := by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left

/-- The radical of a homogeneous ideal, as another homogeneous ideal. -/
/-
**HomogeneousIdeal.radical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.radical (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜
参数：I : HomogeneousIdeal 𝒜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radical of a homogeneous ideal, as another homogeneous ideal.
-/
def HomogeneousIdeal.radical (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  ⟨I.toIdeal.radical, I.isHomogeneous.radical⟩

@[simp]
/-
**HomogeneousIdeal.coe_radical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) : I.radical.toIdeal 
= I.toIdeal.radical
参数：I : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) :
    I.radical.toIdeal = I.toIdeal.radical := rfl
