/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.Projectivization.Independence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!

# Collinearity in Projective Space

This file defines collinearity of points in projective space and proves
the uniqueness of the line through two distinct points.

## Main Results

* `Projectivization.IsCollinear`: A family of points in projective space is collinear if there
  exists a submodule of dimension at most 2 containing all points in the family.
* `Projectivization.line_unique`: Given two distinct points in projective space, there is a unique
  line (submodule of dimension 2) containing both points.

## Tags
Projective space, collinearity, projective geometry

-/

@[expose] public section

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  (M : Submodule K V) (S : Set (Projectivization K V))

namespace Projectivization

/-- If there exists a submodule of dimension at most `2` containing all points in
  `S`, then `S` is collinear. The finite-dimensionality is required so that this notion is
  meaningful even when `V` is infinite-dimensional. -/
/-
**Projectivization.IsCollinear** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：IsCollinear : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there exists a submodule of dimension at most `2` containing all points in
  `S`, then `S` is collinear. The finite-dimensionality is required so that this
 notion is
  meaningful even when `V` is infinite-dimensional.
-/
def IsCollinear : Prop := ∃ (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule ≤ 2 ∧ S ⊆ M
/-
**Projectivization.IsCollinear_iff** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：IsCollinear_iff : IsCollinear S ↔ exists (M : Subspace K V), Module.Finite
 K M.submodule ∧ Module.finrank K M.submodule <= 2 ∧ S subseteq M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsCollinear_iff : IsCollinear S ↔ ∃ (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule ≤ 2 ∧ S ⊆ M := Iff.rfl
/-
**Projectivization.IsCollinear_iff_rank** 是 Mathlib 中的一个引理，位于命名空间 `Projectivizat
ion`。
形式化陈述：IsCollinear_iff_rank : IsCollinear S ↔ exists (M : Subspace K V), Module.r
ank K M.submodule <= 2 ∧ S subseteq M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.IsCollinear_iff`：IsCollinear_iff : IsCollinear S ↔ exis
ts (M : Subspace K V), Module.Finite K M.submodule ∧ Module.finrank K M.submodul
e <= 2 ∧ S subseteq M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteDimensional.finrank_le_iff_rank_le`：finrank_le_iff_rank_le [Finite
Dimensional K V] {n : Nat} : finrank K V <= n ↔ Module.rank K V <= n
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Module.finrank_le_of_rank_le`：finrank_le_of_rank_le {n : Nat} (h : Modul
e.rank R M <= ↑n) : finrank R M <= n
-/
lemma IsCollinear_iff_rank :
    IsCollinear S ↔
      ∃ (M : Subspace K V), Module.rank K M.submodule ≤ 2 ∧ S ⊆ M := by
  rw [IsCollinear_iff]
  refine ⟨fun ⟨M, hM1, hM2, hM3⟩ ↦ ⟨M, ?_, hM3⟩, fun ⟨M, hM1, hM2⟩ ↦ ⟨M, ?_, ?_, hM2⟩⟩
  · exact FiniteDimensional.finrank_le_iff_rank_le (K := K) (V := M.submodule) (n := 2)|>.1 hM2
  · exact Module.rank_lt_aleph0_iff.1 (hM1.trans_lt (by norm_num))
  · exact Module.finrank_le_of_rank_le hM1

@[simp]
/-
**Projectivization.isCollinear_empty** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization
`。
形式化陈述：isCollinear_empty : IsCollinear (∅ : Set (Projectivization K V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.IsCollinear_iff_rank`：IsCollinear_iff_rank : IsCollinea
r S ↔ exists (M : Subspace K V), Module.rank K M.submodule <= 2 ∧ S subseteq M
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
· 使用定理 `SupBotHomClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Max α] [inst_2 : Max β] [inst_3 : Bot α]  
 [inst_4 : Bot β] …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `OrderIsoClass.toCompleteLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : EquivLike F α β] [inst_1 : CompleteLattice α]   [inst_2 
: CompleteLattice β] [OrderIs…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Projectivization.Subspace.bot_coe`：bot_coe : ((⊥ : Subspace K V) : Set (
Projectivization K V)) = ∅
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma isCollinear_empty : IsCollinear (∅ : Set (Projectivization K V)) := by
  rw [IsCollinear_iff_rank]
  use ⊥
  rw [map_bot]
  simp

open scoped LinearAlgebra.Projectivization
/-
**Projectivization.isCollinear_subset** 是 Mathlib 中的一个引理，位于命名空间 `Projectivizatio
n`。
形式化陈述：isCollinear_subset (s t : Set (ℙ K V)) (hst : s subseteq t) (h : IsColline
ar t) : IsCollinear s
参数：s t : Set (ℙ K V)；hst : s subseteq t；h : IsCollinear t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma isCollinear_subset (s t : Set (ℙ K V)) (hst : s ⊆ t) (h : IsCollinear t) : IsCollinear s := by
  obtain ⟨M, hMfin, hM1, hM2⟩ := h
  exact ⟨M, hMfin, hM1, hst.trans hM2⟩

@[simp]
/-
**Projectivization.isCollinear_singleton'** 是 Mathlib 中的一个引理，位于命名空间 `Projectiviz
ation`。
形式化陈述：isCollinear_singleton' (a : ℙ K V) : IsCollinear {a}
参数：a : ℙ K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Module.Finite.span_of_finite`：span_of_finite {A : Set M} (hA : Set.Finit
e A) : Module.Finite R (span R A)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isCollinear_singleton' (a : ℙ K V) : IsCollinear {a} := by
  induction a using ind with | h v hv =>
  refine ⟨(Submodule.span K {v}).projectivization, ?_, ?_, ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, finrank_span_singleton hv]
    omega
  · simp [Submodule.mem_span_of_mem]
/-
**Projectivization.isCollinear_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Projectiv
ization`。
形式化陈述：isCollinear_subsingleton (hS : S.Subsingleton) : IsCollinear S
参数：hS : S.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isCollinear_subsingleton (hS : S.Subsingleton) :
    IsCollinear S := by
  obtain hS' | ⟨x, hx⟩ := hS.eq_empty_or_singleton <;> simp_all
/-
**Projectivization.isCollinear_pair** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`
。
形式化陈述：isCollinear_pair (a b : ℙ K V) : IsCollinear {a, b}
参数：a b : ℙ K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Module.Finite.span_of_finite`：span_of_finite {A : Set M} (hA : Set.Finit
e A) : Module.Finite R (span R A)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.range_cons_cons_empty`：range_cons_cons_empty (x y : α) (u : Fin 0
 -> α) : Set.range (vecCons x <| vecCons y u) = {x, y}
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
· 使用引理 `Projectivization.independent_mk_iff_LinearIndependent`：independent_mk_if
f_LinearIndependent {u v : V} (hu : u != 0) (hv : v != 0) : Independent ![mk K u
 hu, mk K v hv] ↔ LinearIndependent K ![u, …
· 使用定理 `Projectivization.independent_pair_iff_ne`：independent_pair_iff_ne (u v :
 ℙ K V) : Independent ![u, v] ↔ u != v
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma isCollinear_pair (a b : ℙ K V) : IsCollinear {a, b} := by
  if h : a = b then simp [h] else
  induction a using Projectivization.ind with | h v hv =>
  induction b using Projectivization.ind with | h w hw =>
  rw [← ne_eq, ← independent_pair_iff_ne, independent_mk_iff_LinearIndependent] at h
  refine ⟨(Submodule.span K {v, w}).projectivization, ?_, ?_, fun s hs ↦ hs.casesOn ?_ ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, ← Matrix.range_cons_cons_empty v w ![]]
    simp [finrank_span_eq_card h]
  all_goals rintro rfl; simp [Submodule.mem_span_of_mem]
/-
**Projectivization.isCollinear_of_card_eq_two** 是 Mathlib 中的一个引理，位于命名空间 `Project
ivization`。
形式化陈述：isCollinear_of_card_eq_two (hS : S.ncard = 2) : IsCollinear S
参数：hS : S.ncard = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ncard_eq_two`：ncard_eq_two : s.ncard = 2 ↔ exists x y, x != y ∧ s = 
{x, y}
· 使用引理 `Projectivization.isCollinear_pair`：isCollinear_pair (a b : ℙ K V) : IsCo
llinear {a, b}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isCollinear_of_card_eq_two (hS : S.ncard = 2) : IsCollinear S := by
  obtain ⟨x, y, _, rfl⟩ := Set.ncard_eq_two.1 hS
  exact isCollinear_pair x y
/-
**Projectivization.line_unique'** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：line_unique' {u v : V} (hu : u != 0) (hv : v != 0) (huv : LinearIndependen
t K ![u, v]) (p : Submodule K V) (hp1 : Module.finrank K p = 2) (hp2 : mk K u hu
 in p.projectivization) (hp3 : mk K v hv in p.projectivization) : p = Submodule.
span K {u, v}
参数：hu : u != 0；hv : v != 0；huv : LinearIndependent K ![u, v]；p : Submodule K V；h
p1 : Module.finrank K p = 2；hp2 : mk K u hu in p.projectivization；hp3 : mk K v h
v in p.projectivization。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Module.finite_of_finrank_eq_succ`：finite_of_finrank_eq_succ {n : Nat} (h
n : finrank R M = n.succ) : Module.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `Matrix.range_cons_cons_empty`：range_cons_cons_empty (x y : α) (u : Fin 0
 -> α) : Set.range (vecCons x <| vecCons y u) = {x, y}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finrank_span_eq_card`：finrank_span_eq_card [Nontrivial R] {ι : Type*} [F
intype ι] {b : ι -> M} (hb : LinearIndependent R b) : finrank R (span R (Set.ran
ge b)) = F…
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma line_unique' {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : LinearIndependent K ![u, v])
    (p : Submodule K V) (hp1 : Module.finrank K p = 2)
    (hp2 : mk K u hu ∈ p.projectivization) (hp3 : mk K v hv ∈ p.projectivization) :
    p = Submodule.span K {u, v} := by
  have h1 : Submodule.span K {u, v} ≤ p := by
    refine Submodule.span_le.2 fun x hx ↦ ?_
    simp only [Submodule.mk_mem_projectivization_iff] at hp2 hp3
    refine hx.casesOn ?_ ?_ <;> simp_all
  have : Module.Finite K p := Module.finite_of_finrank_eq_succ hp1
  refine Submodule.eq_of_le_of_finrank_eq h1 ?_ |>.symm
  rw [hp1, ← Matrix.range_cons_cons_empty _ _ ![]]
  simp [finrank_span_eq_card huv]
/-
**Projectivization.line_unique** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：line_unique {x y : ℙ K V} (hxy : x != y) (p q : Submodule K V) (hp1 : Modu
le.finrank K p = 2) (hq1 : Module.finrank K q = 2) (hp2 : x in p.projectivizatio
n) (hp3 : y in p.projectivization) (hq2 : x in q.projectivization) (hq3 : y in q
.projectivization) : p = q
参数：hxy : x != y；p q : Submodule K V；hp1 : Module.finrank K p = 2；hq1 : Module.fi
nrank K q = 2；hp2 : x in p.projectivization；hp3 : y in p.projectivization；hq2 : 
x in q.projectivization；hq3 : y in q.projectivization。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.line_unique'`：line_unique' {u v : V} (hu : u != 0) (hv 
: v != 0) (huv : LinearIndependent K ![u, v]) (p : Submodule K V) (hp1 : Module.
finrank K p = 2) (h…
· 使用引理 `Projectivization.independent_mk_iff_LinearIndependent`：independent_mk_if
f_LinearIndependent {u v : V} (hu : u != 0) (hv : v != 0) : Independent ![mk K u
 hu, mk K v hv] ↔ LinearIndependent K ![u, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.independent_pair_iff_ne`：independent_pair_iff_ne (u v :
 ℙ K V) : Independent ![u, v] ↔ u != v
-/
lemma line_unique {x y : ℙ K V} (hxy : x ≠ y) (p q : Submodule K V) (hp1 : Module.finrank K p = 2)
    (hq1 : Module.finrank K q = 2) (hp2 : x ∈ p.projectivization) (hp3 : y ∈ p.projectivization)
    (hq2 : x ∈ q.projectivization) (hq3 : y ∈ q.projectivization) : p = q := by
  induction x using ind with | h v hv =>
  induction y using ind with | h w hw =>
  rw [← independent_pair_iff_ne, independent_mk_iff_LinearIndependent] at hxy
  rw [line_unique' hv hw hxy p hp1 hp2 hp3, line_unique' hv hw hxy q hq1 hq2 hq3]

end Projectivization

