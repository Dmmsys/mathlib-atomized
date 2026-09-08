/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations

/-!
# An additional lemma about coprime ideals

This lemma generalises `exists_sum_eq_one_iff_pairwise_coprime` to the case of non-principal ideals.
It is on a separate file due to import requirements.
-/

public section


namespace Ideal

variable {ι R : Type*} [CommSemiring R]

/-- A finite family of ideals is pairwise coprime (that is, any two of them generate the whole ring)
iff when taking all the possible intersections of all but one of these ideals, the resulting family
of ideals still generate the whole ring.

For example with three ideals : `I ⊔ J = I ⊔ K = J ⊔ K = ⊤ ↔ (I ⊓ J) ⊔ (I ⊓ K) ⊔ (J ⊓ K) = ⊤`.

When ideals are all of the form `I i = R ∙ s i`, this is equivalent to the
`exists_sum_eq_one_iff_pairwise_coprime` lemma. -/
/-
**Ideal.iSup_iInf_eq_top_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：iSup_iInf_eq_top_iff_pairwise {t : Finset ι} (h : t.Nonempty) (I : ι -> Id
eal R) : (⨆ i in t, ⨅ (j) (_ : j in t) (_ : j != i), I j) = ⊤ ↔ (t : Set ι).Pair
wise fun i j => I i ⊔ I j = ⊤
参数：h : t.Nonempty；I : ι -> Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Submodule.mem_iSup_finset_iff_exists_sum`：mem_iSup_finset_iff_exists_sum
 {s : Finset ι} (p : ι -> Submodule R N) (a : N) : (a in ⨆ i in s, p i) ↔ exists
 μ : forall i, p i, (∑ i in s,…
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_iInf_eq_left`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] {b : β} {f : (x : β) → x = b → α},   ⨅ x, ⨅ (h : x = b), f x h = f b ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Ideal.mem_iInf`：mem_iInf {ι : Sort*} {I : ι -> Ideal R} {x : R} : x in i
Inf I ↔ forall i, x in I i
· 使用定理 `Finset.subset_cons`：subset_cons (h : a ∉ s) : s subseteq s.cons a h
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
A finite family of ideals is pairwise coprime (that is, any two of them generate
 the whole ring)
iff when taking all the possible intersections of all but one of these ideals, t
he resulting family
of ideals still generate the whole ring.

For example with three ideals : `I ⊔ J = I ⊔ K = J ⊔ K = ⊤ ↔ (I ⊓ J) ⊔ (I ⊓ K) ⊔
 (J ⊓ K) = ⊤`.

When ideals are all of the form `I i = R ∙ s i`, this is equivalent to the
`exists_sum_eq_one_iff_pairwise_coprime` lemma.
-/
theorem iSup_iInf_eq_top_iff_pairwise {t : Finset ι} (h : t.Nonempty) (I : ι → Ideal R) :
    (⨆ i ∈ t, ⨅ (j) (_ : j ∈ t) (_ : j ≠ i), I j) = ⊤ ↔
      (t : Set ι).Pairwise fun i j => I i ⊔ I j = ⊤ := by
  have : DecidableEq ι := Classical.decEq ι
  rw [eq_top_iff_one, Submodule.mem_iSup_finset_iff_exists_sum]
  refine h.cons_induction ?_ ?_ <;> clear t h
  · simp only [Finset.sum_singleton, Finset.coe_singleton, Set.pairwise_singleton, iff_true]
    refine fun a => ⟨fun i => if h : i = a then ⟨1, ?_⟩ else 0, ?_⟩
    · simp [h]
    · simp only [dif_pos, Submodule.coe_mk]
  intro a t hat h ih
  have : Std.Symm (I · ⊔ I · = ⊤) := { symm i j := sup_comm .. |>.trans }
  rw [Finset.coe_cons, Set.pairwise_insert_of_symm]
  constructor
  · rintro ⟨μ, hμ⟩
    rw [Finset.sum_cons] at hμ
    refine ⟨ih.mp ⟨Pi.single h.choose ⟨μ a, ?a1⟩ + fun i => ⟨μ i, ?a2⟩, ?a3⟩, fun b hb ab => ?a4⟩
    case a1 =>
      have := Submodule.coe_mem (μ a)
      rw [mem_iInf] at this ⊢
      --for some reason `simp only [mem_iInf]` times out
      intro i
      specialize this i
      rw [mem_iInf, mem_iInf] at this ⊢
      intro hi _
      apply this (Finset.subset_cons _ hi)
      rintro rfl
      exact hat hi
    case a2 =>
      have := Submodule.coe_mem (μ i)
      simp only [mem_iInf] at this ⊢
      intro j hj ij
      exact this _ (Finset.subset_cons _ hj) ij
    case a3 =>
      rw [← @if_pos _ _ h.choose_spec R (μ a) 0, ← Finset.sum_pi_single', ← Finset.sum_add_distrib]
        at hμ
      convert! hμ
      rename_i i _
      rw [Pi.add_apply, Submodule.coe_add, Submodule.coe_mk]
      by_cases hi : i = h.choose
      · rw [hi, Pi.single_eq_same, Pi.single_eq_same, Submodule.coe_mk]
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Submodule.coe_zero]
    case a4 =>
      rw [eq_top_iff_one, Submodule.mem_sup]
      rw [add_comm] at hμ
      refine ⟨_, ?_, _, ?_, hμ⟩
      · refine sum_mem _ fun x hx => ?_
        have := Submodule.coe_mem (μ x)
        simp only [mem_iInf] at this
        apply this _ (Finset.mem_cons_self _ _)
        rintro rfl
        exact hat hx
      · have := Submodule.coe_mem (μ a)
        simp only [mem_iInf] at this
        exact this _ (Finset.subset_cons _ hb) ab.symm
  · rintro ⟨hs, Hb⟩
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    have := sup_iInf_eq_top fun b hb => Hb b hb (ne_of_mem_of_not_mem hb hat).symm
    rw [eq_top_iff_one, Submodule.mem_sup] at this
    obtain ⟨u, hu, v, hv, huv⟩ := this
    refine ⟨fun i => if hi : i = a then ⟨v, ?_⟩ else ⟨u * μ i, ?_⟩, ?_⟩
    · simp only [mem_iInf] at hv ⊢
      intro j hj ij
      rw [Finset.mem_cons, ← hi] at hj
      exact hv _ (hj.resolve_left ij)
    · have := Submodule.coe_mem (μ i)
      simp only [mem_iInf] at this ⊢
      intro j hj ij
      rcases Finset.mem_cons.mp hj with (rfl | hj)
      · exact mul_mem_right _ _ hu
      · exact mul_mem_left _ _ (this _ hj ij)
    · dsimp only
      rw [Finset.sum_cons, dif_pos rfl, add_comm]
      rw [← mul_one u] at huv
      rw [← huv, ← hμ, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [dif_neg]
      rintro rfl
      exact hat hj

end Ideal

