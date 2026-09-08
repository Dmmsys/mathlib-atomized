/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! # Some lemmas about the degree lexicographic monomial order on multivariate polynomials -/

public section

namespace MvPolynomial

open MonomialOrder Finsupp

open scoped MonomialOrder

variable {σ : Type*} {R : Type*}

section CommSemiring

variable [CommSemiring R] {f g : MvPolynomial σ R}

section LinearOrder

variable [LinearOrder σ] [WellFoundedGT σ]

/-
**MvPolynomial.degree_degLexDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degree_degLexDegree : (degLex.degree f).degree = f.totalDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MvPolynomial.le_totalDegree`：le_totalDegree {p : MvPolynomial σ R} {s : 
σ ->₀ Nat} (h : s in p.support) : (s.sum fun _ e => e) <= totalDegree p
· 使用引理 `MonomialOrder.degree_mem_support`：degree_mem_support {p : MvPolynomial σ
 R} (hp : p != 0) : m.degree p in p.support
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Finsupp.DegLex.monotone_degree`：monotone_degree : Monotone (fun (x : Deg
Lex (α ->₀ Nat)) => (ofDegLex x).degree)
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
-/
theorem degree_degLexDegree : (degLex.degree f).degree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf]
  apply le_antisymm
  · exact le_totalDegree (degLex.degree_mem_support hf)
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro b hb
    exact DegLex.monotone_degree (degLex.le_degree hb)
/-
**MvPolynomial.degLex_totalDegree_monotone** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：degLex_totalDegree_monotone (h : degLex.degree f ≼[degLex] degLex.degree g
) : f.totalDegree <= g.totalDegree
参数：h : degLex.degree f ≼[degLex] degLex.degree g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.DegLex.monotone_degree`：monotone_degree : Monotone (fun (x : Deg
Lex (α ->₀ Nat)) => (ofDegLex x).degree)
-/
theorem degLex_totalDegree_monotone (h : degLex.degree f ≼[degLex] degLex.degree g) :
    f.totalDegree ≤ g.totalDegree := by
  simp only [← MvPolynomial.degree_degLexDegree]
  exact DegLex.monotone_degree h

end LinearOrder

end CommSemiring

end MvPolynomial

