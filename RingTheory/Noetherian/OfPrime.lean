/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
module

public import Mathlib.RingTheory.Ideal.Oka
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Noetherian rings and prime ideals

## Main results

- `IsNoetherianRing.of_prime`: a ring where all prime ideals are finitely generated is a noetherian
  ring

## References

- [cohen1950]: *Commutative rings with restricted minimum condition*, I. S. Cohen, Theorem 2
-/

public section

variable {R : Type*} [CommRing R]

namespace Ideal

open Set Finset

/-- `Ideal.FG` is an Oka predicate. -/
/-
**Ideal.isOka_fg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isOka_fg : IsOka (FG (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_exists_fin_generating_family`：fg_iff_exists_fin_generat
ing_family {N : Submodule R M} : N.FG ↔ exists (n : Nat) (s : Fin n -> M), span 
R (range s) = N
· 使用定理 `Ideal.mem_span_singleton_sup`：mem_span_singleton_sup {x y : α} {I : Idea
l α} : x in Ideal.span {y} ⊔ I ↔ exists a : α, exists b in I, a * y + b = x
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.mem_span_range_self`：mem_span_range_self {β : Type*} {f : β -> α} 
{x : β} : f x in span (range f)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Ideal.span_union`：span_union (s t : Set α) : span (s union t) = span s ⊔
 span t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.mem_colon_span_singleton`：∀ {R : Type u_1} [inst : CommSemiring R]
 {I : Ideal R} {x r : R}, r ∈ Submodule.colon I ↑(Ideal.span {x}) ↔ r * x ∈ I
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Ideal.mem_span_range_iff_exists_fun`：Ideal.mem_span_range_iff_exists_fun
 [Fintype α] {x : R} {v : α -> R} : x in Ideal.span (Set.range v) ↔ exists c : α
 -> R, ∑ i, c i * v i = x
· 使用定理 `Ideal.mem_sup_left`：mem_sup_left {S T : Ideal R} : forall {x : R}, x in 
S -> x in S ⊔ T
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
`Ideal.FG` is an Oka predicate.
-/
theorem isOka_fg : IsOka (FG (R := R)) where
  top := ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    classical
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H k : ∃ r : R, ∃ p ∈ I, r * a + p = f k := by
      apply mem_span_singleton_sup.1
      rw [sup_comm, ← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ ∪ image (a • i) univ, le_antisymm ?_ (fun y hy ↦ ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun _ ↦ mul_comm a _ ▸ mem_colon_span_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 (hf ▸ Ideal.mem_sup_left hy)
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib, ← sum_mul, add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ ↦ mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm, ← smul_eq_mul, range_smul, ← submodule_span_eq, Submodule.span_smul, hi]
      exact smul_mem_smul_set <| mem_colon_span_singleton.2 <|
        (I.add_mem_iff_right <| I.sum_mem (fun _ _ ↦ mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)

end Ideal

open Ideal

/-- If all prime ideals in a commutative ring are finitely generated, so are all other ideals. -/
/-
**IsNoetherianRing.of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherianRing.of_prime (H : forall I : Ideal R, I.IsPrime -> I.FG) : Is
NoetherianRing R
参数：H : forall I : Ideal R, I.IsPrime -> I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsOka.forall_of_forall_prime'`：forall_of_forall_prime' (hchain : f
orall C subseteq {I | ¬P I}, IsChain (· <= ·) C -> forall _ in C, P (sSup C) -> 
exists I in C, P I) (hpri…
· 使用定理 `Ideal.isOka_fg`：isOka_fg : IsOka (FG (R
· 使用定理 `DirectedOn.exists_mem_subset_of_finset_subset_biUnion`：DirectedOn.exists
_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι -> Set α} {c : Set ι} 
(hn : c.Nonempty) (hc : DirectedOn (fun i j…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sSup_of_directed`：mem_sSup_of_directed {s : Set (Submodule
 R M)} {z} (hs : s.Nonempty) (hdir : DirectedOn (· <= ·) s) : z in sSup s ↔ exis
ts y in s, z in y
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I

--- 原说明 ---
If all prime ideals in a commutative ring are finitely generated, so are all oth
er ideals.
-/
theorem IsNoetherianRing.of_prime (H : ∀ I : Ideal R, I.IsPrime → I.FG) :
    IsNoetherianRing R := by
  refine ⟨isOka_fg.forall_of_forall_prime' (fun C hC₁ hC₂ I hI h ↦ ⟨sSup C, ?_, h⟩) H⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨J, J_mem_C, G_subset_J⟩ : ∃ J ∈ C, (G : Set R) ⊆ J := by
    refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ⟨I, hI⟩ (fun _ hx ↦ ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    exact (Submodule.mem_sSup_of_directed ⟨I, hI⟩ hC₂.directedOn).1 <| hG ▸ subset_span hx
  suffices J_eq_sSup : J = sSup C from J_eq_sSup ▸ J_mem_C
  exact le_antisymm (le_sSup J_mem_C) (hG ▸ Ideal.span_le.2 G_subset_J)

/-- If all non-zero prime ideals in a commutative ring are finitely generated,
so are all other ideals. -/
/-
**IsNoetherianRing.of_prime_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherianRing.of_prime_ne_bot (H : forall I : Ideal R, I.IsPrime -> I !
= ⊥ -> I.FG) : IsNoetherianRing R
参数：H : forall I : Ideal R, I.IsPrime -> I != ⊥ -> I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherianRing.of_prime`：IsNoetherianRing.of_prime (H : forall I : Ide
al R, I.IsPrime -> I.FG) : IsNoetherianRing R
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If all non-zero prime ideals in a commutative ring are finitely generated,
so are all other ideals.
-/
theorem IsNoetherianRing.of_prime_ne_bot (H : ∀ I : Ideal R, I.IsPrime → I ≠ ⊥ → I.FG) :
    IsNoetherianRing R :=
  .of_prime fun I hi ↦ (eq_or_ne I ⊥).elim (· ▸ Submodule.fg_bot) <| H _ hi
