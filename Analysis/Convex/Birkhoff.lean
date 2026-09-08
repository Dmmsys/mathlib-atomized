/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Birkhoff's theorem

## Main statements

* `doublyStochastic_eq_sum_perm`: If `M` is a doubly stochastic matrix, then it is a convex
  combination of permutation matrices.
* `doublyStochastic_eq_convexHull_perm`: The set of doubly stochastic matrices is the convex hull
  of the permutation matrices.
* `extremePoints_doublyStochastic`: The set of extreme points of the doubly stochastic matrices is
  the set of permutation matrices.

## TODO

* Show that for `x y : n → R`, `x` is majorized by `y` if and only if there is a doubly stochastic
  matrix `M` such that `M *ᵥ y = x`.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

public section

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] {M : Matrix n n R}

set_option backward.isDefEq.respectTransparency.types false in
/--
If M is a positive scalar multiple of a doubly stochastic matrix, then there is a permutation matrix
whose support is contained in the support of M.
-/
/-
**exists_perm_eq_zero_implies_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If M is a positive scalar multiple of a doubly stochastic matrix, then there is 
a permutation matrix
whose support is contained in the support of M.
-/
private lemma exists_perm_eq_zero_implies_eq_zero {s : R} (hs : 0 < s)
    (hM : ∃ M' ∈ doublyStochastic R n, M = s • M') :
    ∃ σ : Equiv.Perm n, ∀ i j, M i j = 0 → σ.permMatrix R i j = 0 := by
  rw [exists_mem_doublyStochastic_eq_smul_iff hs.le] at hM
  let f (i : n) : Finset n := {j | M i j ≠ 0}
  have hf (A : Finset n) : #A ≤ #(A.biUnion f) := by
    have (i : _) : ∑ j ∈ f i, M i j = s := by simp [f, sum_subset (filter_subset _ _), hM.2.1]
    have h₁ : ∑ i ∈ A, ∑ j ∈ f i, M i j = #A * s := by simp [this]
    have h₂ : ∑ i, ∑ j ∈ A.biUnion f, M i j = #(A.biUnion f) * s := by
      simp [sum_comm (t := A.biUnion f), hM.2.2]
    suffices #A * s ≤ #(A.biUnion f) * s by exact_mod_cast le_of_mul_le_mul_right this hs
    rw [← h₁, ← h₂]
    trans ∑ i ∈ A, ∑ j ∈ A.biUnion f, M i j
    · refine sum_le_sum fun i hi => ?_
      exact sum_le_sum_of_subset_of_nonneg (subset_biUnion_of_mem f hi) (by simp [*])
    · exact sum_le_sum_of_subset_of_nonneg (by simp) fun _ _ _ => sum_nonneg fun j _ => hM.1 _ _
  obtain ⟨g, hg, hg'⟩ := (all_card_le_biUnion_card_iff_exists_injective f).1 hf
  rw [Finite.injective_iff_bijective] at hg
  refine ⟨Equiv.ofBijective g hg, fun i j hij => ?_⟩
  simp only [PEquiv.toMatrix_apply, Option.mem_def, ite_eq_right_iff, one_ne_zero, imp_false,
    Equiv.toPEquiv_apply, Equiv.ofBijective_apply, Option.some.injEq]
  rintro rfl
  simpa [f, hij] using hg' i

end LinearOrderedSemifield

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] {M : Matrix n n R}

/--
If M is a scalar multiple of a doubly stochastic matrix, then it is a conical combination of
permutation matrices. This is most useful when M is a doubly stochastic matrix, in which case
the combination is convex.

This particular formulation is chosen to make the inductive step easier: we no longer need to
rescale each time a permutation matrix is subtracted.
-/
/-
**doublyStochastic_sum_perm_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If M is a scalar multiple of a doubly stochastic matrix, then it is a conical co
mbination of
permutation matrices. This is most useful when M is a doubly stochastic matrix, 
in which case
the combination is convex.

This particular formulation is chosen to make the inductive step easier: we no l
onger need to
rescale each time a permutation matrix is subtracted.
-/
private lemma doublyStochastic_sum_perm_aux (M : Matrix n n R)
    (s : R) (hs : 0 ≤ s)
    (hM : ∃ M' ∈ doublyStochastic R n, M = s • M') :
    ∃ w : Equiv.Perm n → R, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ • σ.permMatrix R = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨1, by simp, Subsingleton.elim _ _⟩
  set d : ℕ := #{i : n × n | M i.1 i.2 ≠ 0} with ← hd
  clear_value d
  induction d using Nat.strongRecOn generalizing M s
  case ind d ih =>
  rcases eq_or_lt_of_le hs with rfl | hs'
  case inl =>
    use 0
    simp only [zero_smul, exists_and_right] at hM
    simp [hM]
  obtain ⟨σ, hσ⟩ := exists_perm_eq_zero_implies_eq_zero hs' hM
  obtain ⟨i, hi, hi'⟩ := exists_min_image _ (fun i => M i (σ i)) univ_nonempty
  rw [exists_mem_doublyStochastic_eq_smul_iff hs] at hM
  let N : Matrix n n R := M - M i (σ i) • σ.permMatrix R
  have hMi' : 0 < M i (σ i) := (hM.1 _ _).lt_of_ne' fun h => by
    simpa [Equiv.toPEquiv_apply] using hσ _ _ h
  let s' : R := s - M i (σ i)
  have hs' : 0 ≤ s' := by
    simp only [s', sub_nonneg, ← hM.2.1 i]
    exact single_le_sum (fun j _ => hM.1 i j) (by simp)
  have : ∃ M' ∈ doublyStochastic R n, N = s' • M' := by
    rw [exists_mem_doublyStochastic_eq_smul_iff hs']
    simp only [Matrix.sub_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_nonneg,
      sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, N]
    refine ⟨fun i' j => ?_, by simp [s', hM.2.1], by simp [s', ← σ.eq_symm_apply, hM]⟩
    split
    case isTrue h => exact (hi' i' (by simp)).trans_eq (by rw [h])
    case isFalse h => exact hM.1 _ _
  have hd' : #{i : n × n | N i.1 i.2 ≠ 0} < d := by
    rw [← hd]
    gcongr
    rw [ssubset_iff_of_subset (monotone_filter_right _ _)]
    · simp_rw [mem_filter_univ, not_not, Prod.exists]
      exact ⟨i, σ i, hMi'.ne', by simp [N, Equiv.toPEquiv_apply]⟩
    · rintro ⟨i', j'⟩ _ hN' hM'
      have hσ' : σ i' ≠ j' := by
        simpa [Equiv.toPEquiv_apply] using hσ i' j' hM'
      exact hN' <| by simp [N, hM', hσ', Equiv.toPEquiv_apply]
  obtain ⟨w, hw, hw'⟩ := ih _ hd' _ s' hs' this rfl
  refine ⟨w + fun σ' => if σ' = σ then M i (σ i) else 0, ?_⟩
  simp only [Pi.add_apply, add_smul, sum_add_distrib, hw', ite_smul, zero_smul,
    sum_ite_eq', mem_univ, ↓reduceIte, N, sub_add_cancel, and_true]
  intro σ'
  split <;> simp [add_nonneg, hw, hM.1]

set_option backward.isDefEq.respectTransparency false in
/--
If M is a doubly stochastic matrix, then it is a convex combination of permutation matrices. Note
`doublyStochastic_eq_convexHull_permMatrix` shows `doublyStochastic n` is exactly the convex hull of
the permutation matrices, and this lemma is instead most useful for accessing the coefficients of
each permutation matrices directly.
-/
/-
**exists_eq_sum_perm_of_mem_doublyStochastic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_eq_sum_perm_of_mem_doublyStochastic (hM : M in doublyStochastic R n
) : exists w : Equiv.Perm n -> R, (forall σ, 0 <= w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ
 • σ.permMatrix R = M
参数：hM : M in doublyStochastic R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `_private.Mathlib.Analysis.Convex.Birkhoff.0.doublyStochastic_sum_perm_au
x`：∀ {R : Type u_1} {n : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [
inst_2 : Field R] [inst_3 : LinearOrder R]   [inst_4 : IsStrict…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.smul_apply`：smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i :
 m) (j : n) : (r • A) i j = r • (A i j)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `sum_row_of_mem_doublyStochastic`：sum_row_of_mem_doublyStochastic (hM : M
 in doublyStochastic R n) (i : n) : ∑ j, M i j = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a

--- 原说明 ---
If M is a doubly stochastic matrix, then it is a convex combination of permutati
on matrices. Note
`doublyStochastic_eq_convexHull_permMatrix` shows `doublyStochastic n` is exactl
y the convex hull of
the permutation matrices, and this lemma is instead most useful for accessing th
e coefficients of
each permutation matrices directly.
-/
lemma exists_eq_sum_perm_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) :
    ∃ w : Equiv.Perm n → R, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix R = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨fun _ => 1, by simp, by simp, Subsingleton.elim _ _⟩
  obtain ⟨w, hw1, hw3⟩ := doublyStochastic_sum_perm_aux M 1 (by simp) ⟨M, hM, by simp⟩
  refine ⟨w, hw1, ?_, hw3⟩
  inhabit n
  have : ∑ j, ∑ σ : Equiv.Perm n, w σ • σ.permMatrix R default j = 1 := by
    simp only [← smul_apply (m := n), ← Finset.sum_apply, hw3]
    rw [sum_row_of_mem_doublyStochastic hM]
  simpa [sum_comm (γ := n), Equiv.toPEquiv_apply] using this

/--
**Birkhoff's theorem**
The set of doubly stochastic matrices is the convex hull of the permutation matrices.  Note
`exists_eq_sum_perm_of_mem_doublyStochastic` gives a convex weighting of each permutation matrix
directly.  To show `doublyStochastic n` is convex, use `convex_doublyStochastic`.
-/
/-
**doublyStochastic_eq_convexHull_permMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：doublyStochastic_eq_convexHull_permMatrix : doublyStochastic R n = convexH
ull R {σ.permMatrix R | σ : Equiv.Perm n}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用引理 `permMatrix_mem_doublyStochastic`：permMatrix_mem_doublyStochastic {σ : Eq
uiv.Perm n} : σ.permMatrix R in doublyStochastic R n
· 使用引理 `convex_doublyStochastic`：convex_doublyStochastic : Convex R (doublyStoch
astic R n : Set (Matrix n n R))
· 使用引理 `exists_eq_sum_perm_of_mem_doublyStochastic`：exists_eq_sum_perm_of_mem_do
ublyStochastic (hM : M in doublyStochastic R n) : exists w : Equiv.Perm n -> R, 
(forall σ, 0 <= w σ) ∧ ∑ σ, w σ …
· 使用引理 `mem_convexHull_of_exists_fintype`：mem_convexHull_of_exists_fintype {s : 
Set E} {x : E} [Fintype ι] (w : ι -> R) (z : ι -> E) (hw₀ : forall i, 0 <= w i) 
(hw₁ : ∑ i, w i = 1) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
**Birkhoff's theorem**
The set of doubly stochastic matrices is the convex hull of the permutation matr
ices.  Note
`exists_eq_sum_perm_of_mem_doublyStochastic` gives a convex weighting of each pe
rmutation matrix
directly.  To show `doublyStochastic n` is convex, use `convex_doublyStochastic`
.
-/
theorem doublyStochastic_eq_convexHull_permMatrix :
    doublyStochastic R n = convexHull R {σ.permMatrix R | σ : Equiv.Perm n} := by
  refine (convexHull_min ?g1 convex_doublyStochastic).antisymm' fun M hM => ?g2
  case g1 =>
    rintro x ⟨h, rfl⟩
    exact permMatrix_mem_doublyStochastic
  case g2 =>
    obtain ⟨w, hw1, hw2, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
    exact mem_convexHull_of_exists_fintype w (·.permMatrix R) hw1 hw2 (by simp) hw3

/--
The set of extreme points of the doubly stochastic matrices is the set of permutation matrices.
-/
/-
**extremePoints_doublyStochastic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_doublyStochastic : Set.extremePoints R (doublyStochastic R n
) = {σ.permMatrix R | σ : Equiv.Perm n}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `doublyStochastic_eq_convexHull_permMatrix`：doublyStochastic_eq_convexHul
l_permMatrix : doublyStochastic R n = convexHull R {σ.permMatrix R | σ : Equiv.P
erm n}
· 使用定理 `extremePoints_convexHull_subset`：extremePoints_convexHull_subset : (conv
exHull 𝕜 A).extremePoints 𝕜 subseteq A
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
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `permMatrix_mem_doublyStochastic`：permMatrix_mem_doublyStochastic {σ : Eq
uiv.Perm n} : σ.permMatrix R in doublyStochastic R n
· 使用定理 `image_openSegment`：image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' o
penSegment 𝕜 a b = openSegment 𝕜 (f a) (f b)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `openSegment_eq_Ioo'`：openSegment_eq_Ioo' (hxy : x != y) : openSegment 𝕜 
x y = Ioo (min x y) (max x y)
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `openSegment_same`：openSegment_same (x : E) : openSegment 𝕜 x x = {x}
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The set of extreme points of the doubly stochastic matrices is the set of permut
ation matrices.
-/
theorem extremePoints_doublyStochastic :
    Set.extremePoints R (doublyStochastic R n) = {σ.permMatrix R | σ : Equiv.Perm n} := by
  refine subset_antisymm ?_ ?_
  · rw [doublyStochastic_eq_convexHull_permMatrix]
    exact extremePoints_convexHull_subset
  rintro _ ⟨σ, rfl⟩
  refine ⟨permMatrix_mem_doublyStochastic, fun x₁ hx₁ x₂ hx₂ hσ ↦ ?_⟩
  suffices ∀ i j : n, x₁ i j = x₂ i j by
    obtain rfl : x₁ = x₂ := by simpa [← Matrix.ext_iff]
    simp_all
  intro i j
  have h₁ : σ.permMatrix R i j ∈ openSegment R (x₁ i j) (x₂ i j) :=
    image_openSegment _ (entryLinearMap R R i j).toAffineMap x₁ x₂ ▸ ⟨_, hσ, rfl⟩
  by_contra! h
  have h₂ : openSegment R (x₁ i j) (x₂ i j) ⊆ Set.Ioo 0 1 := by
    rw [openSegment_eq_Ioo' h]
    apply Set.Ioo_subset_Ioo <;>
    simp_all [nonneg_of_mem_doublyStochastic, le_one_of_mem_doublyStochastic]
  specialize h₂ h₁
  aesop

end LinearOrderedField

open scoped Matrix.Norms.L2Operator

/-
**Matrix.l2_opNorm_le_one_of_mem_doublyStochastic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.l2_opNorm_le_one_of_mem_doublyStochastic {M : Matrix n n Real} (hM 
: M in doublyStochastic Real n) : ‖M‖ <= 1
参数：hM : M in doublyStochastic Real n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.exists_ge_of_mem_convexHull`：ConvexOn.exists_ge_of_mem_convexHu
ll {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s) (hx : x in convexHull 
𝕜 t) : exists y in t, f x …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `convexOn_univ_norm`：convexOn_univ_norm : ConvexOn Real univ (norm : E ->
 Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `doublyStochastic_eq_convexHull_permMatrix`：doublyStochastic_eq_convexHul
l_permMatrix : doublyStochastic R n = convexHull R {σ.permMatrix R | σ : Equiv.P
erm n}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matrix.permMatrix_l2_opNorm_le`：permMatrix_l2_opNorm_le : ‖σ.permMatrix 
𝕜‖ <= 1
-/
theorem Matrix.l2_opNorm_le_one_of_mem_doublyStochastic {M : Matrix n n ℝ}
    (hM : M ∈ doublyStochastic ℝ n) :
    ‖M‖ ≤ 1 := by
  rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hM
  have ⟨_, ⟨σ, rfl⟩, hσ⟩ := convexOn_univ_norm.exists_ge_of_mem_convexHull (by simp) hM
  exact hσ.trans (permMatrix_l2_opNorm_le _)
