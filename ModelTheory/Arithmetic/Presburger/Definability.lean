/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic
public import Mathlib.ModelTheory.Definability

import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Presburger definability and semilinear sets

This file formalizes the classical result that Presburger definable sets are the same as semilinear
sets. As an application of this result, we show that the graph of multiplication is not Presburger
definable.

## Main Results

- `presburger.definable_iff_isSemilinearSet`: a set is Presburger definable in `ℕ` if and only if it
  is semilinear.
- `presburger.definable₁_iff_ultimately_periodic`: in the 1-dimensional case, a set is Presburger
  arithmetic definable in `ℕ` if and only if it is ultimately periodic, i.e. periodic after some
  number `k`.
- `presburger.mul_not_definable`: the graph of multiplication is not Presburger definable in `ℕ`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger Formulas, and
  Languages*][ginsburg1966]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

public section

variable {α : Type*} {s : Set (α → ℕ)} {A : Set ℕ}

open Set FirstOrder Language

/-
**IsLinearSet.definable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.definable [Finite α] (hs : IsLinearSet s) : A.Definable presbu
rger s
参数：hs : IsLinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLinearSet_iff`：isLinearSet_iff : IsLinearSet s ↔ exists (a : M) (t : F
inset M), s = a +ᵥ (closure (t : Set M) : Set M)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `FirstOrder.Language.Term.realize_varsToConstants`：realize_varsToConstant
s [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {t : L.Term (α 
oplus β)} {v : β -> M} : t.varsToConst…
· 使用定理 `FirstOrder.Language.presburger.realize_natCast`：∀ {α : Type u_1} {M : Ty
pe u_2} {v : α → M} [inst : AddMonoidWithOne M] {n : ℕ},   FirstOrder.Language.T
erm.realize v ↑n = ↑n
· 使用定理 `FirstOrder.Language.presburger.realize_sum`：∀ {α : Type u_1} {M : Type u
_2} {v : α → M} [inst : AddCommMonoidWithOne M] {β : Type u_3} {s : Finset β}   
{f : β → FirstOrder.Language.pre…
· 使用定理 `FirstOrder.Language.presburger.realize_nsmul`：∀ {α : Type u_1} {t : Firs
tOrder.Language.presburger.Term α} {M : Type u_2} {v : α → M} [inst : AddMonoidW
ithOne M]   {n : ℕ}, FirstOrder.La…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsLinearSet.definable [Finite α] (hs : IsLinearSet s) : A.Definable presburger s := by
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨v, t, rfl⟩
  refine ⟨Formula.iExs t (Formula.iInf fun i : α =>
    (Term.var (Sum.inl i)).equal
      (Term.varsToConstants
        ((v i : presburger.Term _) + presburger.sum Finset.univ fun x : t =>
          x.1 i • Term.var (Sum.inr (Sum.inr x))))), ?_⟩
  ext x
  simp only [mem_vadd_set, SetLike.mem_coe, AddSubmonoid.mem_closure_finset', Finset.univ_eq_attach,
    nsmul_eq_mul, vadd_eq_add, ↓existsAndEq, true_and, mem_ofPred_eq, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var, Sum.elim_inl,
    Term.realize_varsToConstants, coe_con, presburger.realize_add, presburger.realize_natCast,
    Nat.cast_id, presburger.realize_sum, presburger.realize_nsmul, Sum.elim_inr, smul_eq_mul]
  congr! with a
  simp_rw [Eq.comm (b := x), fun x : t => mul_comm (a x : α → ℕ) x, funext_iff]
  congr! 1 with i
  simp
/-
**IsSemilinearSet.definable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.definable [Finite α] (hs : IsSemilinearSet s) : A.Definabl
e presburger s
参数：hs : IsSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSemilinearSet_iff`：isSemilinearSet_iff : IsSemilinearSet s ↔ exists (S
 : Finset (Set M)), (forall t in S, IsLinearSet t) ∧ s = ⋃₀ S
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsLinearSet.definable`：IsLinearSet.definable [Finite α] (hs : IsLinearSe
t s) : A.Definable presburger s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsSemilinearSet.definable [Finite α] (hs : IsSemilinearSet s) :
    A.Definable presburger s := by
  rw [isSemilinearSet_iff] at hs
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_ofPred_eq] at this
  simp [this]

namespace FirstOrder.Language.presburger

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.presburger.term_realize_eq_add_dotProduct** 是 Mathlib 中的一个
引理，位于命名空间 `FirstOrder.Language.presburger`。
形式化陈述：term_realize_eq_add_dotProduct [Fintype α] (t : presburger[[A]].Term α) : 
exists (k : Nat) (u : α -> Nat), forall (v : α -> Nat), t.realize v = k + u ⬝ᵥ v
参数：t : presburger[[A]].Term α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FirstOrder.Language.withConstants_funMap_sumInl`：withConstants_funMap_su
mInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {n} {f : L.F
unctions n} {x : Fin n -> M} : @funMa…
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_dotProduct`：add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `FirstOrder.Language.withConstants_funMap_sumInr`：withConstants_funMap_su
mInr {a : α} {x : Fin 0 -> M} : @funMap L[[α]] M _ 0 (Sum.inr a : L[[α]].Functio
ns 0) x = L.con a
-/
lemma term_realize_eq_add_dotProduct [Fintype α] (t : presburger[[A]].Term α) :
    ∃ (k : ℕ) (u : α → ℕ), ∀ (v : α → ℕ), t.realize v = k + u ⬝ᵥ v := by
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp [ih]
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl, add_dotProduct, add_left_comm, add_assoc, add_left_comm,
          ← add_assoc]
        simp [ih]
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInr, zero_dotProduct, add_zero]
        rfl
      | succ => nomatch f

variable [Finite α]

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.presburger.isSemilinearSet_boundedFormula_realize** 是 Math
lib 中的一个引理，位于命名空间 `FirstOrder.Language.presburger`。
形式化陈述：isSemilinearSet_boundedFormula_realize {n} (φ : presburger[[A]].BoundedFor
mula α n) : IsSemilinearSet {v : α oplus Fin n -> Nat | φ.Realize (v ∘ Sum.inl) 
(v ∘ Sum.inr)}
参数：φ : presburger[[A]].BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemilinearSet.empty`：IsSemilinearSet.empty : IsSemilinearSet (∅ : Set 
M)
· 使用引理 `FirstOrder.Language.presburger.term_realize_eq_add_dotProduct`：term_real
ize_eq_add_dotProduct [Fintype α] (t : presburger[[A]].Term α) : exists (k : Nat
) (u : α -> Nat), forall (v : α -> Nat), t.realize …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sum.elim_comp_inl_inr`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f
 : α ⊕ β → γ), Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) = f
· 使用定理 `Matrix.cons_mulVec`：cons_mulVec [Fintype n'] (v : n' -> α) (A : Fin m ->
 n' -> α) (w : n' -> α) : (of <| vecCons v A) *ᵥ w = vecCons (v ⬝ᵥ w) (of A *ᵥ w
)
· 使用定理 `Matrix.empty_mulVec`：empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α)
 (v : n' -> α) : A *ᵥ v = ![]
· 使用定理 `Matrix.add_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (v : Fin n.succ
 → α) (y : α) (w : Fin n → α),   v + Matrix.vecCons y w = Matrix.vecCons (Matrix
.vecH…
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `Matrix.empty_add_empty`：∀ {α : Type u_1} [inst : Add α] (v w : Fin 0 → α
), v + w = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.isSemilinearSet_setOfPred_mulVec_eq`：∀ {ι : Type u_3} {κ : Type u_4}
 [inst : Fintype κ] (u v : ι → ℕ) (A B : Matrix ι κ ℕ),   IsSemilinearSet {x | u
 + A.mulVec x = v + B.mulVec …
· 使用定理 `Set.ofPred_inter_eq_sep`：ofPred_inter_eq_sep (p : α -> Prop) (s : Set α)
 : {a | p a} inter s = {a in s | p a}
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsSemilinearSet.compl`：∀ {M : Type u_1} [inst : AddCommMonoid M] {s : Se
t M} [AddMonoid.FG M], IsSemilinearSet s → IsSemilinearSet sᶜ
· 使用定理 `Pi.instAddMonoidFG`：∀ {ι : Type u_5} [Finite ι] {M : ι → Type u_6} [inst
 : (i : ι) → AddMonoid (M i)] [∀ (i : ι), AddMonoid.FG (M i)],   AddMonoid.FG ((
i : ι) →…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AddMonoid.instFGNat`：AddMonoid.FG ℕ
· 使用定理 `IsSemilinearSet.inter`：∀ {M : Type u_1} [inst : AddCommMonoid M] {s₁ s₂ 
: Set M},   IsSemilinearSet s₁ → IsSemilinearSet s₂ → IsSemilinearSet (s₁ ∩ s₂)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 46 条，此处仅展示前 30 条）
-/
lemma isSemilinearSet_boundedFormula_realize {n} (φ : presburger[[A]].BoundedFormula α n) :
    IsSemilinearSet {v : α ⊕ Fin n → ℕ | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
  have := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct t₂ with ⟨k₂, u₂, ht₂⟩
    convert! Nat.isSemilinearSet_setOfPred_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel f => nomatch f
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert! (ih₂.compl.inter ih₁).compl using 1
    simp [ofPred_inter_eq_sep, imp_iff_not_or, compl_ofPred]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft ℕ ℕ e)] at ih
    convert! ih.compl.proj.compl using 1
    simp_rw [compl_ofPred, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_ofPred, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]
/-
**FirstOrder.Language.presburger.isSemilinearSet_formula_realize_semilinear** 是 
Mathlib 中的一个引理，位于命名空间 `FirstOrder.Language.presburger`。
形式化陈述：isSemilinearSet_formula_realize_semilinear (φ : presburger[[A]].Formula α)
 : IsSemilinearSet (Set.ofPred φ.Realize : Set (α -> Nat))
参数：φ : presburger[[A]].Formula α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.arrowCongr_apply`：∀ {α₁ : Sort u_1} {β₁ : Sort u_2} {α₂ : Sort u_3
} {β₂ : Sort u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (f : α₁ → β₁) (a : α₂),   (e₁.ar
rowCongr e₂)…
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.sumEmpty_symm_apply`：∀ (α : Type u_9) (β : Type u_10) [inst : IsEm
pty β] (val : α), (Equiv.sumEmpty α β).symm val = Sum.inl val
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsSemilinearSet.image`：IsSemilinearSet.image (hs : IsSemilinearSet s) (f
 : F) : IsSemilinearSet (f '' s)
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `FirstOrder.Language.presburger.isSemilinearSet_boundedFormula_realize`：i
sSemilinearSet_boundedFormula_realize {n} (φ : presburger[[A]].BoundedFormula α 
n) : IsSemilinearSet {v : α oplus Fin n -> Nat | φ.Realize …
-/
lemma isSemilinearSet_formula_realize_semilinear (φ : presburger[[A]].Formula α) :
    IsSemilinearSet (Set.ofPred φ.Realize : Set (α → ℕ)) := by
  let e := Equiv.sumEmpty α (Fin 0)
  convert! (isSemilinearSet_boundedFormula_realize φ).image (LinearMap.funLeft ℕ ℕ e.symm)
  ext x
  simp only [mem_ofPred_eq, mem_image]
  rw [(e.arrowCongr (.refl ℕ)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

/-- A set is Presburger definable in `ℕ` if and only if it is semilinear. -/
/-
**FirstOrder.Language.presburger.definable_iff_isSemilinearSet** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.presburger`。
形式化陈述：definable_iff_isSemilinearSet {s : Set (α -> Nat)} : A.Definable presburge
r s ↔ IsSemilinearSet s
参数：α -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FirstOrder.Language.presburger.isSemilinearSet_formula_realize_semilinea
r`：isSemilinearSet_formula_realize_semilinear (φ : presburger[[A]].Formula α) : 
IsSemilinearSet (Set.ofPred φ.Realize : Set (α -> Nat))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSemilinearSet.definable`：IsSemilinearSet.definable [Finite α] (hs : Is
SemilinearSet s) : A.Definable presburger s

--- 原说明 ---
A set is Presburger definable in `ℕ` if and only if it is semilinear.
-/
theorem definable_iff_isSemilinearSet {s : Set (α → ℕ)} :
    A.Definable presburger s ↔ IsSemilinearSet s :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ isSemilinearSet_formula_realize_semilinear φ, IsSemilinearSet.definable⟩

/-- In the 1-dimensional case, a set is Presburger arithmetic definable in `ℕ` if and only if it
  is ultimately periodic, i.e. periodic after some number `k`. -/
/-
**FirstOrder.Language.presburger.definable** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the 1-dimensional case, a set is Presburger arithmetic definable in `ℕ` if an
d only if it
  is ultimately periodic, i.e. periodic after some number `k`.
-/
theorem definable₁_iff_ultimately_periodic {s : Set ℕ} :
    A.Definable₁ presburger s ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ s ↔ x + p ∈ s := by
  rw [Definable₁, definable_iff_isSemilinearSet,
    ← isSemilinearSet_image_iff (LinearEquiv.funUnique (Fin 1) ℕ ℕ), ← preimage_ofPred_eq]
  simp only [LinearEquiv.funUnique_apply, Function.eval, Fin.default_eq_zero, ofPred_mem_eq]
  rw [image_preimage_eq s fun x => ⟨![x], rfl⟩, Nat.isSemilinearSet_iff_ultimately_periodic]

/-- The graph of multiplication is not Presburger definable in `ℕ`. -/
/-
**FirstOrder.Language.presburger.mul_not_definable** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.presburger`。
形式化陈述：mul_not_definable : ¬ A.Definable presburger {v : Fin 3 -> Nat | v 0 = v 1
 * v 2}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Definable₁.eq_1`：∀ {M : Type w} (A : Set M) (L : FirstOrder.Language
) [inst : L.Structure M] (s : Set M),   A.Definable₁ L s = A.Definable L {x | x 
0 ∈ s}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.Definable.image_comp`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Lan
guage} [inst : L.Structure M] {α : Type u₁} {β : Type u_1}   {s : Set (β → M)}, 
A.Definable L …
· 使用定理 `Set.Definable.preimage_comp`：∀ {M : Type w} {A : Set M} {L : FirstOrder.
Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1} (f : α → β)   {s :
 Set (α → M)}, A.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic`：defin
able₁_iff_ultimately_periodic {s : Set Nat} : A.Definable₁ presburger s ↔ exists
 k, exists p > 0, forall x >= k, x in s ↔ x + p in s
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Nat.mul_self_le_mul_self`：∀ {m n : ℕ}, m ≤ n → m * m ≤ n * n

--- 原说明 ---
The graph of multiplication is not Presburger definable in `ℕ`.
-/
theorem mul_not_definable : ¬ A.Definable presburger {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : ℕ} := by
    rw [Definable₁]
    convert! (hmul.preimage_comp (β := Fin 2) ![0, 1, 1]).image_comp ![0]
    ext
    simpa [funext_iff, Fin.exists_fin_succ_pi] using exists_congr fun _ => Eq.comm
  rw [definable₁_iff_ultimately_periodic] at hsqr
  rcases hsqr with ⟨k, p, hp, h⟩
  specialize h ((max k p) * (max k p)) ((Nat.le_mul_self _).trans' (le_max_left _ _))
  simp only [mem_ofPred_eq, exists_apply_eq_apply, true_iff] at h
  rcases h with ⟨x, h₁⟩
  by_cases h₂ : x ≤ max k p
  · apply Nat.mul_self_le_mul_self at h₂
    grind
  · simp only [not_le, Nat.lt_iff_add_one_le] at h₂
    apply Nat.mul_self_le_mul_self at h₂
    grind

end FirstOrder.Language.presburger

