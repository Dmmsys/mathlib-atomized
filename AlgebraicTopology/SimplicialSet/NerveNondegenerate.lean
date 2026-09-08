/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The nondegenerate simplices in the nerve of a partially ordered type

In this file, we show that if `X` is a partially ordered type,
then an `n`-simplex `s` of the nerve is nondegenerate iff
the monotone map `s.obj : Fin (n + 1) → X` is strictly monotone.

-/

public section

universe u

open CategoryTheory Simplicial

namespace PartialOrder

variable {X : Type*} [PartialOrder X] {n : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
/-
**PartialOrder.mem_range_nerve_** 是 Mathlib 中的一个引理，位于命名空间 `PartialOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_range_nerve_σ_iff (s : (nerve X) _⦋n + 1⦌) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve X).σ i) ↔
      s.obj i.castSucc = s.obj i.succ := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [-nerve_obj, nerve.σ_obj]
  · intro h
    refine ⟨(nerve X).δ i.castSucc s, ?_⟩
    ext j
    rw [nerve.σ_obj, nerve.δ_obj]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.pred_succ,
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
    · simp only [not_lt] at h₁
      grind [→ Fin.succAbove_of_castSucc_lt,
        → Fin.predAbove_of_le_castSucc, Fin.castSucc_castPred, Fin.castPred_castSucc,
        Fin.succAbove_castSucc_self, → LE.le.lt_or_eq]
/-
**PartialOrder.mem_nerve_degenerate_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `PartialOrde
r`。
形式化陈述：mem_nerve_degenerate_of_eq (s : (nerve X) _⦋n + 1⦌) {i : Fin (n + 1)} (hi 
: s.obj i.castSucc = s.obj i.succ) : s in (nerve X).degenerate (n + 1)
参数：s : (nerve X) _⦋n + 1⦌；n + 1；hi : s.obj i.castSucc = s.obj i.succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.degenerate_eq_iUnion_range_σ`：degenerate_eq_iUnion_range_σ : X.dege
nerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PartialOrder.mem_range_nerve_σ_iff`：mem_range_nerve_σ_iff (s : (nerve X)
 _⦋n + 1⦌) (i : Fin (n + 1)) : s in Set.range ((nerve X).σ i) ↔ s.obj i.castSucc
 = s.obj i.succ
-/
lemma mem_nerve_degenerate_of_eq (s : (nerve X) _⦋n + 1⦌) {i : Fin (n + 1)}
    (hi : s.obj i.castSucc = s.obj i.succ) :
    s ∈ (nerve X).degenerate (n + 1) := by
  simp only [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  exact ⟨i, by rwa [← mem_range_nerve_σ_iff] at hi⟩
/-
**PartialOrder.mem_nerve_nonDegenerate_iff_strictMono** 是 Mathlib 中的一个引理，位于命名空间 
`PartialOrder`。
形式化陈述：mem_nerve_nonDegenerate_iff_strictMono (s : (nerve X) _⦋n⦌) : s in (nerve 
X).nonDegenerate n ↔ StrictMono s.obj
参数：s : (nerve X) _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.nondegenerate_zero`：nondegenerate_zero : X.nonDegenerate 0 = Set.un
iv
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Subsingleton.strictMono`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] [Subsingleton α] (f : α → β), StrictMono f
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `SSet.mem_degenerate_iff_notMem_nonDegenerate`：mem_degenerate_iff_notMem_
nonDegenerate (x : X _⦋n⦌) : x in X.degenerate n ↔ x ∉ X.nonDegenerate n
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用引理 `SSet.degenerate_eq_iUnion_range_σ`：degenerate_eq_iUnion_range_σ : X.dege
nerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i)
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
-/
lemma mem_nerve_nonDegenerate_iff_strictMono (s : (nerve X) _⦋n⦌) :
    s ∈ (nerve X).nonDegenerate n ↔ StrictMono s.obj := by
  obtain _ | n := n
  · simpa using Subsingleton.strictMono _
  · rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
      Fin.strictMono_iff_lt_succ, SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    simp only [mem_range_nerve_σ_iff, not_forall]
    apply exists_congr
    intro i
    have := s.monotone i.castSucc_le_succ
    grind [lt_self_iff_false, LE.le.lt_or_eq]
/-
**PartialOrder.mem_nerve_nonDegenerate_iff_injective** 是 Mathlib 中的一个引理，位于命名空间 `
PartialOrder`。
形式化陈述：mem_nerve_nonDegenerate_iff_injective (s : (nerve X) _⦋n⦌) : s in (nerve X
).nonDegenerate n ↔ Function.Injective s.obj
参数：s : (nerve X) _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PartialOrder.mem_nerve_nonDegenerate_iff_strictMono`：mem_nerve_nonDegene
rate_iff_strictMono (s : (nerve X) _⦋n⦌) : s in (nerve X).nonDegenerate n ↔ Stri
ctMono s.obj
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
-/
lemma mem_nerve_nonDegenerate_iff_injective (s : (nerve X) _⦋n⦌) :
    s ∈ (nerve X).nonDegenerate n ↔ Function.Injective s.obj := by
  rw [mem_nerve_nonDegenerate_iff_strictMono]
  refine ⟨fun h ↦ h.injective, fun h i j hij ↦ ?_⟩
  obtain h' | h' := (s.monotone hij.le).lt_or_eq
  · exact h'
  · exact ((h h').not_lt hij).elim

end PartialOrder

