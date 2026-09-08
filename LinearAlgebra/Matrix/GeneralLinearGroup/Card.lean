/-
Copyright (c) 2024 Thomas Lanard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Inna Capdeboscq, Johan Commelin, Thomas Lanard, Peiran Wu
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
/-!
# Cardinal of the general linear group over finite rings

This file computes the cardinal of the general linear group over finite rings.

## Main statements

* `card_linearIndependent` gives the cardinal of the set of linearly independent vectors over a
  finite-dimensional vector space over a finite field.
* `Matrix.card_GL_field` gives the cardinal of the general linear group over a finite field.
-/

@[expose] public section

open LinearMap Module

section LinearIndependent

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Finite V]

local notation "q" => Fintype.card K
local notation "n" => Module.finrank K V

attribute [local instance] Fintype.ofFinite in
open Fintype in
/-- The cardinal of the set of linearly independent vectors over a finite-dimensional vector space
over a finite field. -/
/-
**card_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_linearIndependent {k : Nat} (hk : k <= n) : Nat.card { s : Fin k -> V
 // LinearIndependent K s } = ∏ i : Fin k, (q ^ n - q ^ i.val)
参数：hk : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.linearCombination_fin_zero`：linearCombination_fin_zero (f : Fin 
0 -> M) : linearCombination R f = 0
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.card_compl_set`：Fintype.card_compl_set [Fintype α] (s : Set α) [
Fintype s] [Fintype (↥sᶜ : Sort _)] : Fintype.card (↥sᶜ : Sort _) = Fintype.card
 α - Fintype…
· 使用定理 `Module.card_eq_pow_finrank`：∀ {K : Type u} {V : Type v} [inst : Division
Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : Finty
pe K] [inst_4 : …
· 使用定理 `finrank_span_eq_card`：finrank_span_eq_card [Nontrivial R] {ι : Type*} [F
intype ι] {b : ι -> M} (hb : LinearIndependent R b) : finrank R (span R (Set.ran
ge b)) = F…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The cardinal of the set of linearly independent vectors over a finite-dimensiona
l vector space
over a finite field.
-/
theorem card_linearIndependent {k : ℕ} (hk : k ≤ n) :
    Nat.card { s : Fin k → V // LinearIndependent K s } =
      ∏ i : Fin k, (q ^ n - q ^ i.val) := by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero =>
      have : Unique { s : Fin 0 → V // (⊤ : Submodule K (Fin 0 →₀ K)) = ⊥ } :=
        uniqueOfSubsingleton ⟨0, Subsingleton.elim ..⟩
      simp_rw [linearIndependent_iff_ker, Finsupp.linearCombination_fin_zero, ker_zero,
        Finset.univ_eq_empty, Finset.prod_empty, card_unique]
  | succ k ih =>
      have (s : { s : Fin k → V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k → V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set, Module.card_eq_pow_finrank (K := K)
            (V := ((Submodule.span K (Set.range (s : Fin k → V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [Module.card_eq_pow_finrank (K := K)]
      simp [card_congr (equiv_linearIndependent k), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ (Fin.last k), -Set.fintypeCard_eq_ncard]

end LinearIndependent

namespace Matrix

section field

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

variable (n : ℕ)

/-- Equivalence between `GL n F` and `n` vectors of length `n` that are linearly independent. Given
by sending a matrix to its columns. -/
/-
**Matrix.equiv_GL_linearindependent** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：equiv_GL_linearindependent : GL (Fin n) 𝔽 ≃ { s : Fin n -> Fin n -> 𝔽 // L
inearIndependent 𝔽 s } where toFun M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `GL n F` and `n` vectors of length `n` that are linearly ind
ependent. Given
by sending a matrix to its columns.
-/
noncomputable def equiv_GL_linearindependent :
    GL (Fin n) 𝔽 ≃ { s : Fin n → Fin n → 𝔽 // LinearIndependent 𝔽 s } where
  toFun M := ⟨M.1.col, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank, ← rank_eq_finrank_span_cols, rank_unit]⟩
  invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) <| by
    classical
    let b := basisOfPiSpaceOfLinearIndependent M.2
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose,
      ← coe_basisOfPiSpaceOfLinearIndependent M.2]
    exact isUnit_det_of_invertible _
  right_inv := by exact congrFun rfl

/-- The cardinal of the general linear group over a finite field. -/
/-
**Matrix.card_GL_field** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：card_GL_field : Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ n - q ^ (i :
 Nat))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `card_linearIndependent`：card_linearIndependent {k : Nat} (hk : k <= n) :
 Nat.card { s : Fin k -> V // LinearIndependent K s } = ∏ i : Fin k, (q ^ n - q 
^ i.val)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n

--- 原说明 ---
The cardinal of the general linear group over a finite field.
-/
theorem card_GL_field :
    Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ n - q ^ (i : ℕ)) := by
  rw [Nat.card_congr (equiv_GL_linearindependent n), card_linearIndependent,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

end field

end Matrix

