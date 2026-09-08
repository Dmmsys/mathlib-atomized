/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Normed.Field.Krasner

/-!
# Transfer algebraic properties from dense subfields

In this file, we prove that algebraically closedness of a complete normed field of characteristic
zero can be inherited from its dense subfields. Let `K` be a dense subfield of a complete normed
field `L`.

## Main results
- `IsAlgClosed.of_denseRange` : If `K` is an algebraically closed dense subfield of a complete
nonarchimedean normed field `L` of characteristic zero, then `L` is also algebraically closed.

## TODO
Show that
1. if `K` is perfect, then `L` is perfect;
2. if `L` is separably closed, then `K` is separably closed;
3. upgrade `IsAlgClosed.of_denseRange` to:  If `K` is separably closed, then `L` is
algebraically closed.

2 and 3 will be easy to implement once we establish the result that every polynomial can be
approximated by a *separable* polynomial.

## Reference
[Notes](https://math.stanford.edu/%7Econrad/248APage/handouts/algclosurecomp.pdf) by Brian Conrad.

## Tags
Normed field, algebraically closedness
-/

public section

open Polynomial

/-- If `K` is an algebraically closed dense subfield of a complete nonarchimedean normed field `L`
of characteristic zero, then `L` is also algebraically closed. -/
/-
**IsAlgClosed.of_denseRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgClosed.of_denseRange {K L : Type*} [Field K] [NontriviallyNormedField
 L] [CompleteSpace L] [CharZero L] [IsUltrametricDist L] [Algebra K L] (hi : Den
seRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L
参数：hi : DenseRange (algebraMap K L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> exists x, p.eval x = 0) : IsAlgClosed k
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.IsSplittingField.instFiniteDimensionalSplittingField`：∀ {K : 
Type v} [inst : Field K] (f : Polynomial K), FiniteDimensional K f.SplittingFiel
d
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Polynomial.degree_ne_of_natDegree_ne`：degree_ne_of_natDegree_ne {n : Nat
} : p.natDegree != n -> degree p != n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.eval_rootOfSplits`：eval_rootOfSplits (hf : f.Splits) (hfd : f
.degree != 0) : f.eval (rootOfSplits hf hfd) = 0
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 117 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is an algebraically closed dense subfield of a complete nonarchimedean no
rmed field `L`
of characteristic zero, then `L` is also algebraically closed.
-/
theorem IsAlgClosed.of_denseRange {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [CharZero L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L := by
  -- Fix any monic irreducible polynomial `f` in `L`.
  -- Let `F` be the splitting field of `f`. Let `a` be a root of `f` in `F`.
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  let : NormedField F := spectralNorm.normedField L F
  let : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  -- Let `δ` be a positive real number such that `δ ≤ ‖a - a'‖` for
  -- every Galois conjugates `a'` of `a`
  classical
    let S : Finset F := {x ∈ (f.rootSet F).toFinset | x ≠ a}
  let δ : ℝ := if hS : S.Nonempty then Finset.min' (S.image fun x => ‖a - x‖)
      (Finset.image_nonempty.mpr hS) else 1
  have norm_sub_le : ∀ a' : F, IsConjRoot L a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · apply Finset.min'_le (S.image fun x => ‖a - x‖) (‖a - a'‖)
      apply Finset.mem_image_of_mem
      simp only [minpoly.eq_of_irreducible_of_monic firr fa0 fmon, Finset.mem_filter,
        Set.mem_toFinset, S]
      rw [← (isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩)]
      exact ⟨conj, ne.symm⟩
    · simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
      Set.mem_toFinset, not_not, S] at hS
      rw [isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩,
          ← minpoly.eq_of_irreducible_of_monic firr fa0 fmon] at conj
      exact (ne (hS conj).symm).elim
  have δpos : δ > 0 := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [gt_iff_lt, Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro a' ha'
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at ha'
      rw [norm_pos_iff, sub_ne_zero]
      exact ha'.2.symm
    · linarith
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  -- We can find a `g ∈ K[X]` whose coefficients sufficiently close to coefficients of `f`.
  -- By continuity of roots, there exists a root `b` of `g` in `K` such that `‖a - b‖ ≤ δ`.
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  let ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
      (by simpa [Polynomial.map_map] using (IsAlgClosed.splits g).map ((algebraMap L F).comp _))
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have bbot : b ∈ (⊥ : IntermediateField L F) := by
    rw [Polynomial.aroots_def, Splits.roots_map ((IsAlgClosed.splits g).map _),
        Multiset.mem_map] at hb
    obtain ⟨bCp, _, hbCp⟩ := hb
    rw [IntermediateField.mem_bot]
    exact ⟨bCp, hbCp⟩
  simp only [Polynomial.mem_roots', ne_eq, Polynomial.map_eq_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map_algebraMap] at hb
  -- By Krasner's lemma, `a ∈ L(b) = L`. Thus `f` has a root in `L`.
  have abot : a ∈ (⊥ : IntermediateField L F) := by
    have masp : ((minpoly L a).map (algebraMap L F)).Splits := by
      simpa [minpoly.eq_of_irreducible_of_monic firr fa0 fmon] using
        (Polynomial.SplittingField.splits f)
    simpa [IntermediateField.adjoin_simple_eq_bot_iff.mpr bbot] using
      IsKrasner.krasner (minpoly.irreducible ⟨f, fmon, fa0⟩).separable
        masp ⟨(g.map _), gmon.map _, hb.2⟩ fun a' h1 h2 ↦ lt_of_lt_of_le hab (norm_sub_le a' h1 h2)
  obtain ⟨aCp, haCp⟩ := IntermediateField.mem_bot.mp abot
  use aCp
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, haCp, map_zero]
  · exact RingHom.injective _
