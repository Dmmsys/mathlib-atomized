/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Behrend
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to at most one triangle.

The lower bound comes from turning the big 3AP-free set from Behrend's construction into a graph
that has the property that every triangle gives a (possibly trivial) arithmetic progression on the
original set.

## Main declarations

* `ruzsaSzemerediNumberNat n`: Maximum number of edges a graph on `n` vertices can have such that
  each edge belongs to exactly one triangle.
* `ruzsaSzemerediNumberNat_asymptotic_lower_bound`: There exists a graph with `n` vertices and
  `Ω((n ^ 2 * exp (-4 * √(log n))))` edges such that each edge belongs to exactly one triangle.
-/

@[expose] public section

open Finset Nat Real SimpleGraph Sum3 SimpleGraph.TripartiteFromTriangles
open Fintype (card)
open scoped Pointwise

variable {α β : Type*}

/-! ### The Ruzsa-Szemerédi number -/

section ruzsaSzemerediNumber
variable [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {G H : SimpleGraph α}

variable (α) in
/-- The **Ruzsa-Szemerédi number** of a fintype is the maximum number of edges a locally linear
graph on that type can have.

In other words, `ruzsaSzemerediNumber α` is the maximum number of edges a graph on `α` can have such
that each edge belongs to exactly one triangle. -/
/-
**ruzsaSzemerediNumber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumber : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Ruzsa-Szemerédi number** of a fintype is the maximum number of edges a loc
ally linear
graph on that type can have.

In other words, `ruzsaSzemerediNumber α` is the maximum number of edges a graph 
on `α` can have such
that each edge belongs to exactly one triangle.
-/
noncomputable def ruzsaSzemerediNumber : ℕ := by
  classical
  exact Nat.findGreatest (fun m ↦ ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) ((card α).choose 3)
/-
**ruzsaSzemerediNumber_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumber_le : ruzsaSzemerediNumber α <= (card α).choose 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_le`：findGreatest_le (n : Nat) : Nat.findGreatest P n <=
 n
-/
lemma ruzsaSzemerediNumber_le : ruzsaSzemerediNumber α ≤ (card α).choose 3 := by
  classical
  exact Nat.findGreatest_le _
/-
**ruzsaSzemerediNumber_spec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumber_spec : exists (G : SimpleGraph α) (_ : DecidableRel G
.Adj), #(G.cliqueFinset 3) = ruzsaSzemerediNumber α ∧ G.LocallyLinear
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `SimpleGraph.locallyLinear_bot`：∀ {α : Type u_1}, ⊥.LocallyLinear
-/
lemma ruzsaSzemerediNumber_spec :
    ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = ruzsaSzemerediNumber α ∧ G.LocallyLinear := by
  classical
  exact @Nat.findGreatest_spec _
    (fun m ↦ ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) _ _ (Nat.zero_le _)
    ⟨⊥, inferInstance, by simp, locallyLinear_bot⟩

variable {m n : ℕ}
/-
**SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber [DecidableRel G.Adj] (hG
 : G.LocallyLinear) : #(G.cliqueFinset 3) <= ruzsaSzemerediNumber α
参数：hG : G.LocallyLinear。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_findGreatest`：le_findGreatest (hmb : m <= n) (hm : P m) : m <= Na
t.findGreatest P n
· 使用定理 `SimpleGraph.card_cliqueFinset_le`：card_cliqueFinset_le : #(G.cliqueFinse
t n) <= (card α).choose n
-/
lemma SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : #(G.cliqueFinset 3) ≤ ruzsaSzemerediNumber α := by
  classical
  exact le_findGreatest card_cliqueFinset_le ⟨G, inferInstance, by congr, hG⟩
/-
**ruzsaSzemerediNumber_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsaSzemerediNumber α <= ruzsaSze
merediNumber β
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_mono`：findGreatest_mono [DecidablePred Q] (hPQ : forall
 n, P n -> Q n) (hmn : m <= n) : Nat.findGreatest P m <= Nat.findGreatest Q n
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `SimpleGraph.cliqueFinset_map`：cliqueFinset_map (f : α ↪ β) (hn : n != 1)
 : (G.map f).cliqueFinset n = (G.cliqueFinset n).map ⟨map f, Finset.map_injectiv
e _⟩
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `SimpleGraph.LocallyLinear.map`：∀ {α : Type u_1} {β : Type u_2} {G : Simp
leGraph α} (f : α ↪ β),   G.LocallyLinear → (SimpleGraph.map (⇑f) G).LocallyLine
ar
· 使用定理 `Nat.choose_mono`：choose_mono (b : Nat) : Monotone fun a => choose a b
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
-/
lemma ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsaSzemerediNumber α ≤ ruzsaSzemerediNumber β := by
  classical
  refine findGreatest_mono ?_ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, _, rfl, hG⟩
  refine ⟨G.map f, inferInstance, ?_, hG.map _⟩
  rw [← card_map ⟨map f, Finset.map_injective _⟩, ← cliqueFinset_map G f]
  decide
/-
**ruzsaSzemerediNumber_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumber_congr (e : α ≃ β) : ruzsaSzemerediNumber α = ruzsaSze
merediNumber β
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `ruzsaSzemerediNumber_mono`：ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsa
SzemerediNumber α <= ruzsaSzemerediNumber β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ruzsaSzemerediNumber_congr (e : α ≃ β) : ruzsaSzemerediNumber α = ruzsaSzemerediNumber β :=
  (ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm <| ruzsaSzemerediNumber_mono e.symm

/-- The `n`-th **Ruzsa-Szemerédi number** is the maximum number of edges a locally linear graph on
`n` vertices can have.

In other words, `ruzsaSzemerediNumberNat n` is the maximum number of edges a graph on `n` vertices
can have such that each edge belongs to exactly one triangle. -/
/-
**ruzsaSzemerediNumberNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th **Ruzsa-Szemerédi number** is the maximum number of edges a locally l
inear graph on
`n` vertices can have.

In other words, `ruzsaSzemerediNumberNat n` is the maximum number of edges a gra
ph on `n` vertices
can have such that each edge belongs to exactly one triangle.
-/
noncomputable def ruzsaSzemerediNumberNat (n : ℕ) : ℕ := ruzsaSzemerediNumber (Fin n)

@[simp]
/-
**ruzsaSzemerediNumberNat_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat_card : ruzsaSzemerediNumberNat (card α) = ruzsaSze
merediNumber α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ruzsaSzemerediNumber_congr`：ruzsaSzemerediNumber_congr (e : α ≃ β) : ruz
saSzemerediNumber α = ruzsaSzemerediNumber β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ruzsaSzemerediNumberNat_card : ruzsaSzemerediNumberNat (card α) = ruzsaSzemerediNumber α :=
  ruzsaSzemerediNumber_congr (Fintype.equivFin _).symm

@[gcongr]
/-
**ruzsaSzemerediNumberNat_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat_mono : Monotone ruzsaSzemerediNumberNat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ruzsaSzemerediNumber_mono`：ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsa
SzemerediNumber α <= ruzsaSzemerediNumber β
-/
lemma ruzsaSzemerediNumberNat_mono : Monotone ruzsaSzemerediNumberNat := fun _m _n h =>
  ruzsaSzemerediNumber_mono (Fin.castLEEmb h)
/-
**ruzsaSzemerediNumberNat_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat_le : ruzsaSzemerediNumberNat n <= n.choose 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ruzsaSzemerediNumber_le`：ruzsaSzemerediNumber_le : ruzsaSzemerediNumber 
α <= (card α).choose 3
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
lemma ruzsaSzemerediNumberNat_le : ruzsaSzemerediNumberNat n ≤ n.choose 3 :=
  ruzsaSzemerediNumber_le.trans_eq <| by rw [Fintype.card_fin]
/-
**ruzsaSzemerediNumberNat_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `ruzsaSzemerediNumberNat_le`：ruzsaSzemerediNumberNat_le : ruzsaSzemerediN
umberNat n <= n.choose 3
-/
@[simp] lemma ruzsaSzemerediNumberNat_zero : ruzsaSzemerediNumberNat 0 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le
/-
**ruzsaSzemerediNumberNat_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `ruzsaSzemerediNumberNat_le`：ruzsaSzemerediNumberNat_le : ruzsaSzemerediN
umberNat n <= n.choose 3
-/
@[simp] lemma ruzsaSzemerediNumberNat_one : ruzsaSzemerediNumberNat 1 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le
/-
**ruzsaSzemerediNumberNat_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat 2 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `ruzsaSzemerediNumberNat_le`：ruzsaSzemerediNumberNat_le : ruzsaSzemerediN
umberNat n <= n.choose 3
-/
@[simp] lemma ruzsaSzemerediNumberNat_two : ruzsaSzemerediNumberNat 2 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

end ruzsaSzemerediNumber

/-! ### The Ruzsa-Szemerédi construction -/

section RuzsaSzemeredi
variable [Fintype α] [CommRing α] {s : Finset α} {x : α × α × α}

/-- The triangle indices for the Ruzsa-Szemerédi construction. -/
/-
**triangleIndices** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle indices for the Ruzsa-Szemerédi construction.
-/
private def triangleIndices (s : Finset α) : Finset (α × α × α) :=
  (univ ×ˢ s).map
    ⟨fun xa ↦ (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      simp only [Prod.ext_iff] at h
      obtain rfl := h.1
      obtain rfl := add_right_injective _ h.2.1
      rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**mem_triangleIndices** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_triangleIndices :
    x ∈ triangleIndices s ↔ ∃ y, ∃ a ∈ s, (y, y + a, y + 2 * a) = x := by simp [triangleIndices]

@[simp]
/-
**card_triangleIndices** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_triangleIndices : #(triangleIndices s) = card α * #s := by
  simp [triangleIndices]
/-
**noAccidental** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma noAccidental (hs : ThreeAPFree (s : Set α)) :
    NoAccidental (triangleIndices s : Finset (α × α × α)) where
  eq_or_eq_or_eq := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl
    have : a + c = b + b := by linear_combination h₁.symm - h₂.symm
    obtain rfl := hs ha hb hc this
    simp_all

variable [Fact <| IsUnit (2 : α)]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : ExplicitDisjoint (triangleIndices s : Finset (α × α × α)) where
  inj₀ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂
    linear_combination 2 * h₁.symm - h₂.symm
  inj₁ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl rfl h
    simpa [(Fact.out (p := IsUnit (2 : α))).mul_right_inj, eq_comm] using h
  inj₂ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h rfl
    simpa [(Fact.out (p := IsUnit (2 : α))).mul_right_inj, eq_comm] using h
/-
**locallyLinear** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma locallyLinear (hs : ThreeAPFree (s : Set α)) :
    (graph <| triangleIndices s).LocallyLinear :=
  haveI := noAccidental hs; TripartiteFromTriangles.locallyLinear _
/-
**card_edgeFinset** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_edgeFinset (hs : ThreeAPFree (s : Set α)) [DecidableEq α] :
    #(graph <| triangleIndices s).edgeFinset = 3 * card α * #s := by
  have := noAccidental hs
  rw [(locallyLinear hs).card_edgeFinset, card_triangles, card_triangleIndices, mul_assoc]

end RuzsaSzemeredi

variable (α) [Fintype α] [DecidableEq α] [CommRing α] [Fact <| IsUnit (2 : α)]

/-
**addRothNumber_le_ruzsaSzemerediNumber** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：addRothNumber_le_ruzsaSzemerediNumber : card α * addRothNumber (univ : Fin
set α) <= ruzsaSzemerediNumber (Sum α (Sum α α))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `addRothNumber_spec`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Ad
dMonoid α] (s : Finset α),   ∃ t ⊆ s, t.card = addRothNumber s ∧ ThreeAPFree ↑t
· 使用定理 `_private.Mathlib.Combinatorics.Extremal.RuzsaSzemeredi.0.noAccidental`：∀
 {α : Type u_1} [inst : Fintype α] [inst_1 : CommRing α] {s : Finset α},   Three
APFree ↑s → SimpleGraph.TripartiteFromTriangles.NoAccidenta…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Combinatorics.Extremal.RuzsaSzemeredi.0.card_triangleIn
dices`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : CommRing α] {s : Finset α},
   (triangleIndices✝ s).card = Fintype.card α * s.card
· 使用定理 `SimpleGraph.TripartiteFromTriangles.card_triangles`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} (t : Finset (α × β × γ)) [inst : DecidableEq α] [inst
_1 : DecidableEq β]   [inst_2 : Decidabl…
· 使用引理 `SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber`：SimpleGraph.LocallyLi
near.le_ruzsaSzemerediNumber [DecidableRel G.Adj] (hG : G.LocallyLinear) : #(G.c
liqueFinset 3) <= ruzsaSzemerediNumber …
· 使用定理 `_private.Mathlib.Combinatorics.Extremal.RuzsaSzemeredi.0.locallyLinear`：
∀ {α : Type u_1} [inst : Fintype α] [inst_1 : CommRing α] {s : Finset α} [Fact (
IsUnit 2)],   ThreeAPFree ↑s → (SimpleGraph.TripartiteFromTr…
-/
lemma addRothNumber_le_ruzsaSzemerediNumber :
    card α * addRothNumber (univ : Finset α) ≤ ruzsaSzemerediNumber (Sum α (Sum α α)) := by
  obtain ⟨s, -, hscard, hs⟩ := addRothNumber_spec (univ : Finset α)
  have := noAccidental hs
  rw [← hscard, ← card_triangleIndices, ← card_triangles]
  exact (locallyLinear hs).le_ruzsaSzemerediNumber
/-
**rothNumberNat_le_ruzsaSzemerediNumberNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rothNumberNat_le_ruzsaSzemerediNumberNat (n : Nat) : (2 * n + 1) * rothNum
berNat n <= ruzsaSzemerediNumberNat (6 * n + 3)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.coprime_one_right_eq_true`：∀ (n : ℕ), n.Coprime 1 = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.addRothNumber_eq_rothNumberNat`：Fin.addRothNumber_eq_rothNumberNat {
k : Fin (n + 1)} (hkn : 2 * k <= n) : addRothNumber (Iio k : Finset (Fin n.succ)
) = rothNumberNat k
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用引理 `addRothNumber_le_ruzsaSzemerediNumber`：addRothNumber_le_ruzsaSzemerediNu
mber : card α * addRothNumber (univ : Finset α) <= ruzsaSzemerediNumber (Sum α (
Sum α α))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 44 条，此处仅展示前 30 条）
-/
lemma rothNumberNat_le_ruzsaSzemerediNumberNat (n : ℕ) :
    (2 * n + 1) * rothNumberNat n ≤ ruzsaSzemerediNumberNat (6 * n + 3) := by
  let α := Fin (2 * n + 1)
  have : Nat.Coprime 2 (2 * n + 1) := by simp
  have : Fact (IsUnit (2 : Fin (2 * n + 1))) := ⟨by simpa
    using! (ZMod.unitOfCoprime 2 this).isUnit⟩
  open scoped Fin.CommRing in
  calc
    (2 * n + 1) * rothNumberNat n
    _ = Fintype.card α * addRothNumber (Iio (⟨n, by lia⟩ : α)) := by
      rw [Fin.addRothNumber_eq_rothNumberNat (by simp), Fintype.card_fin]
    _ ≤ Fintype.card α * addRothNumber (univ : Finset α) := by
      gcongr; exact subset_univ _
    _ ≤ ruzsaSzemerediNumber (Sum α (Sum α α)) := addRothNumber_le_ruzsaSzemerediNumber _
    _ = ruzsaSzemerediNumberNat (6 * n + 3) := by
      simp_rw [← ruzsaSzemerediNumberNat_card, Fintype.card_sum, α, Fintype.card_fin]
      ring_nf

/-- Lower bound on the **Ruzsa-Szemerédi problem** in terms of 3AP-free sets.

If there exists a 3AP-free subset of `[1, ..., (n - 3) / 6]` of size `m`, then there exists a graph
with `n` vertices and `(n / 3 - 2) * m` edges such that each edge belongs to exactly one triangle.
-/
/-
**rothNumberNat_le_ruzsaSzemerediNumberNat'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_le_ruzsaSzemerediNumberNat' : forall n : Nat, (n / 3 - 2 : R
eal) * rothNumberNat ((n - 3) / 6) <= ruzsaSzemerediNumberNat n | 0 => by simp |
 1 => by simp | 2 => by simp | n + 3 => by calc _ <= (↑(2 * (n / 6) + 1) : Real)
 * rothNumberNat (n / 6)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ruzsaSzemerediNumberNat_zero`：ruzsaSzemerediNumberNat 0 = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ruzsaSzemerediNumberNat_one`：ruzsaSzemerediNumberNat 1 = 0
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `ruzsaSzemerediNumberNat_two`：ruzsaSzemerediNumberNat 2 = 0
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_add_one`：div_add_one (h : b != 0) : a / b + 1 = (a + b) / b
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Lower bound on the **Ruzsa-Szemerédi problem** in terms of 3AP-free sets.

If there exists a 3AP-free subset of `[1, ..., (n - 3) / 6]` of size `m`, then t
here exists a graph
with `n` vertices and `(n / 3 - 2) * m` edges such that each edge belongs to exa
ctly one triangle.
-/
theorem rothNumberNat_le_ruzsaSzemerediNumberNat' :
    ∀ n : ℕ, (n / 3 - 2 : ℝ) * rothNumberNat ((n - 3) / 6) ≤ ruzsaSzemerediNumberNat n
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    calc
      _ ≤ (↑(2 * (n / 6) + 1) : ℝ) * rothNumberNat (n / 6) :=
        mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      _ ≤ (ruzsaSzemerediNumberNat (6 * (n / 6) + 3) : ℝ) := ?_
      _ ≤ _ := by grw [Nat.mul_div_le]
    · simp only [cast_add, cast_ofNat, cast_mul, cast_one, tsub_le_iff_right]
      rw [← div_add_one (three_ne_zero' ℝ), ← le_sub_iff_add_le, div_le_iff₀ (zero_lt_three' ℝ),
        add_assoc, add_sub_assoc, add_mul, mul_right_comm, add_sub_cancel_left]
      norm_cast
      rw [← mul_add_one]
      exact (Nat.lt_mul_div_succ _ <| by simp).le
    · norm_cast
      exact rothNumberNat_le_ruzsaSzemerediNumberNat _

/-- Explicit lower bound on the **Ruzsa-Szemerédi problem**.

There exists a graph with `n` vertices and
`(n / 3 - 2) * (n - 3) / 6 * exp (-4 * √(log ((n - 3) / 6)))` edges such that each edge belongs
to exactly one triangle. -/
/-
**ruzsaSzemerediNumberNat_lower_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat_lower_bound (n : Nat) : (n / 3 - 2 : Real) * ↑((n 
- 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6))) <= ruzsaSzemerediNumberNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Behrend.roth_lower_bound`：roth_lower_bound : (N : Real) * exp (-4 * √(lo
g N)) <= rothNumberNat N
· 使用定理 `rothNumberNat_le_ruzsaSzemerediNumberNat'`：rothNumberNat_le_ruzsaSzemere
diNumberNat' : forall n : Nat, (n / 3 - 2 : Real) * rothNumberNat ((n - 3) / 6) 
<= ruzsaSzemerediNumberNat n | …

--- 原说明 ---
Explicit lower bound on the **Ruzsa-Szemerédi problem**.

There exists a graph with `n` vertices and
`(n / 3 - 2) * (n - 3) / 6 * exp (-4 * √(log ((n - 3) / 6)))` edges such that ea
ch edge belongs
to exactly one triangle.
-/
theorem ruzsaSzemerediNumberNat_lower_bound (n : ℕ) :
    (n / 3 - 2 : ℝ) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6))) ≤
      ruzsaSzemerediNumberNat n := by
  rw [mul_assoc]
  obtain hn | hn := le_total (n / 3 - 2 : ℝ) 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hn <| by positivity).trans (Nat.cast_nonneg _)
  exact
    (mul_le_mul_of_nonneg_left Behrend.roth_lower_bound hn).trans
      (rothNumberNat_le_ruzsaSzemerediNumberNat' _)

open Asymptotics Filter

/-- Asymptotic lower bound on the **Ruzsa-Szemerédi problem**.

There exists a graph with `n` vertices and `Ω((n ^ 2 * exp (-4 * √(log n))))` edges such that
each edge belongs to exactly one triangle. -/
/-
**ruzsaSzemerediNumberNat_asymptotic_lower_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ruzsaSzemerediNumberNat_asymptotic_lower_bound : (fun n => n ^ 2 * exp (-4
 * √(log n)) : Nat -> Real) =O[atTop] fun n => (ruzsaSzemerediNumberNat n : Real
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Asymptotics.IsBigO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [ins
t : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α → E}
   {l : Filter α} {g : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.right_isBigO_sub`：∀ {α : Type u_1} {E' : Type u_6}
 [inst : SeminormedAddCommGroup E'] {l : Filter α} {f₁ f₂ : α → E'},   f₁ =o[l] 
f₂ → f₂ =O[l] fun x => f₂ x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Filter.Tendsto.atTop_of_const_mul₀`：∀ {α : Type u_1} {β : Type u_2} [ins
t : Semiring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {c : α}, 0…
· 使用定理 `zero_lt_three`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Pa
rtialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 3
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用引理 `Real.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Real)‖ = n
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
Asymptotic lower bound on the **Ruzsa-Szemerédi problem**.

There exists a graph with `n` vertices and `Ω((n ^ 2 * exp (-4 * √(log n))))` ed
ges such that
each edge belongs to exactly one triangle.
-/
theorem ruzsaSzemerediNumberNat_asymptotic_lower_bound :
    (fun n ↦ n ^ 2 * exp (-4 * √(log n)) : ℕ → ℝ) =O[atTop]
     fun n ↦ (ruzsaSzemerediNumberNat n : ℝ) := by
  trans fun n ↦ (n / 3 - 2) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6)))
  · simp_rw [sq]
    refine (IsBigO.mul ?_ ?_).mul ?_
    · trans fun n ↦ n / 3
      · simp_rw [div_eq_inv_mul]
        exact (isBigO_refl ..).const_mul_right (by simp)
      refine IsLittleO.right_isBigO_sub ?_
      simpa [div_eq_inv_mul, Function.comp_def] using
        .atTop_of_const_mul₀ zero_lt_three (by simp [tendsto_natCast_atTop_atTop])
    · rw [IsBigO_def]
      refine ⟨12, ?_⟩
      simp only [IsBigOWith, norm_natCast, eventually_atTop]
      exact ⟨15, fun x hx ↦ by norm_cast; lia⟩
    · rw [isBigO_exp_comp_exp_comp]
      refine ⟨0, ?_⟩
      simp only [neg_mul, eventually_map, Pi.sub_apply, sub_neg_eq_add, neg_add_le_iff_le_add,
        add_zero, eventually_atTop]
      refine ⟨9, fun x hx ↦ ?_⟩
      gcongr
      · simp
        lia
      · lia
  · refine .of_norm_eventuallyLE ?_
    filter_upwards [eventually_ge_atTop 6] with n hn
    have : (0 : ℝ) ≤ n / 3 - 2 := by rify at hn; linarith
    simpa [neg_mul, abs_mul, abs_of_nonneg this] using ruzsaSzemerediNumberNat_lower_bound n
