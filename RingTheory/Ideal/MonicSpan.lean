/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic

/-!

# Lemmas for ideal in polynomial span by monic polynomial

-/

@[expose] public section

variable (R : Type*) [CommRing R]

open Ideal

namespace Polynomial

/-
**Polynomial.exists_monic_span** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：exists_monic_span {k : Type*} [Field k] (I : Ideal k[X]) (ne : I != ⊥) : e
xists f, f.Monic ∧ I = Ideal.span {f}
参数：I : Ideal k[X]；ne : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `Ideal.exists_normalized_span_of_isPrincipal`：Ideal.exists_normalized_spa
n_of_isPrincipal {R : Type*} [CommSemiring R] [NormalizationMonoid R] (I : Ideal
 R) [I.IsPrincipal] : exists x, n…
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.normalize_eq_self_iff_monic`：normalize_eq_self_iff_monic [Dec
idableEq R] {p : R[X]} (hp : p != 0) : normalize p = p ↔ p.Monic
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma exists_monic_span {k : Type*} [Field k] (I : Ideal k[X]) (ne : I ≠ ⊥) :
    ∃ f, f.Monic ∧ I = Ideal.span {f} := by
  classical
  obtain ⟨x, h, spanx⟩ := Ideal.exists_normalized_span_of_isPrincipal I
  refine ⟨x, (Polynomial.normalize_eq_self_iff_monic ?_).mp h, spanx⟩
  by_contra eq0
  simp [eq0, spanx] at ne
/-
**Polynomial.exists_monic_span_sup_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：exists_monic_span_sup_map_eq (p : Ideal R[X]) (ism : (p.comap C).IsMaximal
) (ne : p != (p.comap C).map C) : exists f : R[X], f.Monic ∧ p = (p.comap C).map
 C ⊔ Ideal.span {f}
参数：p : Ideal R[X]；ism : (p.comap C).IsMaximal；ne : p != (p.comap C).map C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.ker_mapRingHom`：∀ {R : Type u} {S : Type u_1} [inst : CommSem
iring R] [inst_1 : Semiring S] (f : R →+* S),   RingHom.ker (Polynomial.mapRingH
om f) = Ideal.m…
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Polynomial.exists_monic_span`：exists_monic_span {k : Type*} [Field k] (I
 : Ideal k[X]) (ne : I != ⊥) : exists f, f.Monic ∧ I = Ideal.span {f}
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Polynomial.lifts_and_natDegree_eq_and_monic`：lifts_and_natDegree_eq_and_
monic {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[X], map f
 q = p ∧ q.natDegree = p.natDegre…
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
lemma exists_monic_span_sup_map_eq (p : Ideal R[X])
    (ism : (p.comap C).IsMaximal) (ne : p ≠ (p.comap C).map C) :
    ∃ f : R[X], f.Monic ∧ p = (p.comap C).map C ⊔ Ideal.span {f} := by
  let q := p.comap C
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  have ne' : Ideal.map (mapRingHom (Ideal.Quotient.mk q)) p ≠ ⊥ := by
    simp only [ne_eq, map_eq_bot_iff_le_ker, Polynomial.ker_mapRingHom, q, mk_ker]
    exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le ne.symm)
  rcases Polynomial.exists_monic_span _ ne' with ⟨y, mony, hy⟩
  have : y ∈ lifts (Ideal.Quotient.mk q) := map_surjective _ Ideal.Quotient.mk_surjective _
  rcases Polynomial.lifts_and_natDegree_eq_and_monic this mony with ⟨f, hf, deg, monf⟩
  use f, monf
  trans comap (mapRingHom (Ideal.Quotient.mk q)) ((span {f}).map (mapRingHom (Ideal.Quotient.mk q)))
  · rw [Ideal.map_span, coe_mapRingHom, Set.image_singleton, hf, ← hy,
      Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective)]
    simpa [Polynomial.ker_mapRingHom, q] using Ideal.map_comap_le
  · rw [Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective),
      sup_comm, Polynomial.ker_mapRingHom, mk_ker]

end Polynomial

