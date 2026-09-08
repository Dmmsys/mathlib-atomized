/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Rolle's Theorem for polynomials

In this file we use Rolle's Theorem
to relate the number of real roots of a real polynomial and its derivative.
Namely, we prove the following facts.

* `Polynomial.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ`:
  the number of roots of a real polynomial `p` is at most the number of roots of its derivative
  that are not roots of `p` plus one.
* `Polynomial.card_roots_toFinset_le_derivative`, `Polynomial.card_rootSet_le_derivative`:
  the number of roots of a real polynomial
  is at most the number of roots of its derivative plus one.
* `Polynomial.card_roots_le_derivative`: same, but the roots are counted with multiplicities.

## Keywords

polynomial, Rolle's Theorem, root
-/

public section

namespace Polynomial

/-- The number of roots of a real polynomial `p` is at most the number of roots of its derivative
that are not roots of `p` plus one. -/
/-
**Polynomial.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ** 是 M
athlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ (p : Real[X]
) : p.roots.toFinset.card <= (p.derivative.roots.toFinset \ p.roots.toFinset).ca
rd + 1
参数：p : Real[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.eq_C_of_derivative_eq_zero`：eq_C_of_derivative_eq_zero (h : d
erivative p = 0) : p = C (p.coeff 0)
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Polynomial.derivative_zero`：derivative_zero : derivative (0 : R[X]) = 0
· 使用定理 `Finset.card_le_sdiff_of_interleaved`：card_le_sdiff_of_interleaved {s t :
 Finset α} (h : forallᵉ (x in s) (y in s), x < y -> (forall z in s, z ∉ Set.Ioo 
x y) -> exists z in t, x …
· 使用定理 `exists_deriv_eq_zero`：exists_deriv_eq_zero (hab : a < b) (hfc : Continuo
usOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, deriv f c = 0
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The number of roots of a real polynomial `p` is at most the number of roots of i
ts derivative
that are not roots of `p` plus one.
-/
theorem card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ (p : ℝ[X]) :
    p.roots.toFinset.card ≤ (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp']
    simp
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy hxy' => ?_
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  refine ⟨z, ?_, hz1⟩
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]

@[deprecated (since := "2026-06-03")]
alias card_roots_toFinset_le_card_roots_derivative_diff_roots_succ :=
  card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ

/-- The number of roots of a real polynomial is at most the number of roots of its derivative plus
one. -/
/-
**Polynomial.card_roots_toFinset_le_derivative** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：card_roots_toFinset_le_derivative (p : Real[X]) : p.roots.toFinset.card <=
 p.derivative.roots.toFinset.card + 1
参数：p : Real[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Polynomial.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
`：card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ (p : Real[X]) : 
p.roots.toFinset.card <= (p.derivative.roots.toFinset \ p.root…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The number of roots of a real polynomial is at most the number of roots of its d
erivative plus
one.
-/
theorem card_roots_toFinset_le_derivative (p : ℝ[X]) :
    p.roots.toFinset.card ≤ p.derivative.roots.toFinset.card + 1 :=
  p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ.trans <| by
    grw [Finset.sdiff_subset]

/-- The number of roots of a real polynomial (counted with multiplicities) is at most the number of
roots of its derivative (counted with multiplicities) plus one. -/
/-
**Polynomial.card_roots_le_derivative** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_roots_le_derivative (p : Real[X]) : Multiset.card p.roots <= Multiset
.card (derivative p).roots + 1
参数：p : Real[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_sum_count_eq`：toFinset_sum_count_eq (s : Multiset ι) :
 ∑ a in s.toFinset, s.count a = card s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity`：root
Multiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t :
 R) : p.rootMultiplicity t - 1 <= p.derivative.rootMulti…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Polynomial.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
`：card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ (p : Real[X]) : 
p.roots.toFinset.card <= (p.derivative.roots.toFinset \ p.root…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The number of roots of a real polynomial (counted with multiplicities) is at mos
t the number of
roots of its derivative (counted with multiplicities) plus one.
-/
theorem card_roots_le_derivative (p : ℝ[X]) :
    Multiset.card p.roots ≤ Multiset.card (derivative p).roots + 1 :=
  calc
    Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun _ _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ)
    _ ≤ (∑ x ∈ p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x ∈ p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union, ←
        Multiset.toFinset_sum_count_eq, ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-- The number of real roots of a polynomial is at most the number of roots of its derivative plus
one. -/
/-
**Polynomial.card_rootSet_le_derivative** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_rootSet_le_derivative {F : Type*} [CommRing F] [Algebra F Real] (p : 
F[X]) : Fintype.card (p.rootSet Real) <= Fintype.card (p.derivative.rootSet Real
) + 1
参数：p : F[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `Polynomial.card_roots_toFinset_le_derivative`：card_roots_toFinset_le_der
ivative (p : Real[X]) : p.roots.toFinset.card <= p.derivative.roots.toFinset.car
d + 1

--- 原说明 ---
The number of real roots of a polynomial is at most the number of roots of its d
erivative plus
one.
-/
theorem card_rootSet_le_derivative {F : Type*} [CommRing F] [Algebra F ℝ] (p : F[X]) :
    Fintype.card (p.rootSet ℝ) ≤ Fintype.card (p.derivative.rootSet ℝ) + 1 := by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F ℝ))

end Polynomial

