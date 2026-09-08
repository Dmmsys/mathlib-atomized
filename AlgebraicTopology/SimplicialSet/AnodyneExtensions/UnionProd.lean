/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# A pairing for the pushout-product of a horn inclusion and a boundary inclusion

Let `l : Fin (m + 2)` and `n : ℕ`. In this file, we construct a regular pairing
for the subcomplex `unionProd Λ[m + 1, l] ∂Δ[n]` of `Δ[m + 1] ⊗ Δ[n]`. It follows
immediately that the inclusion of the union of `Λ[m + 1, l] ⊗ Δ[n]` and
`Δ[m + 1] ⊗ ∂Δ[n]` in `Δ[m + 1] ⊗ Δ[n]` is a (strong) anodyne extension
(which is inner when `l ≠ 0` and `l ≠ Fin.last _`).

The main construction works only when `l ≠ Fin.last _`, i.e. `l = k.castSucc`
for `k : Fin (m + 1)`: the remaining case is obtained using symmetries and
the case `k = 0`.

In order to do the case of `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]` for `k : Fin (m + 1)`,
we follow the proof by Sean Moss. Let us consider a nondegenerate `d`-simplex `x` of
`Δ[m + 1] ⊗ Δ[n]` which does not belong to `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`.
`x` can be thought as a "walk" on the vertices `{0, ..., m + 1} × {0, ..., n}`
of `Δ[m + 1] ⊗ Δ[n]` (this is actually a strictly monotone map
`Fin (d + 1) → Fin (m + 2) × Fin (n + 1)`).
The condition that `x` does not belong to `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
translates by saying that `x` reaches all the rows
(see the lemma `prodStdSimplex.pairingCore.mem_range_right`)
and all the columns expect the `k.castSucc`-th
(see the lemma `prodStdSimplex.pairingCore.mem_range_left`). This puts
constraints for each `i` on the vector from `x i` to `x (i + 1)`:
it has to be `(0, 1)`, `(1,0)`, `(1,1)`, `(2, 0)` or `(2, 1)` (the last two
cases may appear only if the `k.castSucc`-th column is skipped).
We introduce a predicate `IsIndex` taking `x` and `l : Fin (d + 1)` as arguments
and which is satisfied if `l` is the smallest `i` such that `x l` is
in the `k.succ` column, `l ≠ 0`, and the vector from `x (l.pred _)` to `x l`
is exactly `(1, 0)`.

The type (I) simplices for the pairing are those `x` such that there exists `l`
such that the predicate `IsIndex` hold. The corresponding type (II) simplex
is obtained by removing `x (l.pred _)` from the walk.


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

namespace prodStdSimplex

variable {m : ℕ} {k : Fin (m + 1)} {n : ℕ}
  (x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N) {d : ℕ}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.prodStdSimplex.objEquiv_apply_fst'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodSt
dSimplex`。
形式化陈述：objEquiv_apply_fst' (hd : x.dim = d) (i : Fin (d + 1)) : dsimp% ((objEquiv
 (x.cast hd).simplex) i).1 = (x.cast hd).simplex.1 i
参数：hd : x.dim = d；i : Fin (d + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma objEquiv_apply_fst' (hd : x.dim = d) (i : Fin (d + 1)) :
    dsimp% ((objEquiv (x.cast hd).simplex) i).1 = (x.cast hd).simplex.1 i := rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.prodStdSimplex.objEquiv_apply_snd'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodSt
dSimplex`。
形式化陈述：objEquiv_apply_snd' (hd : x.dim = d) (i : Fin (d + 1)) : dsimp% ((objEquiv
 (x.cast hd).simplex) i).2 = (x.cast hd).simplex.2 i
参数：hd : x.dim = d；i : Fin (d + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma objEquiv_apply_snd' (hd : x.dim = d) (i : Fin (d + 1)) :
    dsimp% ((objEquiv (x.cast hd).simplex) i).2 = (x.cast hd).simplex.2 i := rfl

namespace pairingCore

section

variable (hd : x.dim = d)

/-- Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. In particular,
`x` induces a strictly monotone map from `Fin (d + 1)` to
`{0, ..., m + 1} × {0, ..., n}`. We introduce a predicate on elements in
`Fin (d + 1)` which shall be satisfied for `l.succ` (`l : Fin d`)
if `x l.castSucc = (k.castSucc, t)` and `x l.succ = (k.succ, t)`
for some `t`. The nondegenerate simplices `x` such that there exists
such a `l` shall be the type (I) simplices of a pairing, and the
corresponding type (II) simplex shall be obtained by deleting `x l.castSucc`. -/
/-
**SSet.prodStdSimplex.pairingCore.IsIndex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodSt
dSimplex.pairingCore`。
形式化陈述：IsIndex : Fin (d + 1) -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. In particular,
`x` induces a strictly monotone map from `Fin (d + 1)` to
`{0, ..., m + 1} × {0, ..., n}`. We introduce a predicate on elements in
`Fin (d + 1)` which shall be satisfied for `l.succ` (`l : Fin d`)
if `x l.castSucc = (k.castSucc, t)` and `x l.succ = (k.succ, t)`
for some `t`. The nondegenerate simplices `x` such that there exists
such a `l` shall be the type (I) simplices of a pairing, and the
corresponding type (II) simplex shall be obtained by deleting `x l.castSucc`.
-/
def IsIndex : Fin (d + 1) → Prop :=
  Fin.cases False (fun l ↦
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
    (x.cast hd).simplex.1 l.succ = k.succ ∧
    (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc)

@[simp]
/-
**SSet.prodStdSimplex.pairingCore.isIndex_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet.p
rodStdSimplex.pairingCore`。
形式化陈述：isIndex_zero : IsIndex x hd 0 ↔ False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma isIndex_zero : IsIndex x hd 0 ↔ False := Iff.rfl
/-
**SSet.prodStdSimplex.pairingCore.isIndex_succ** 是 Mathlib 中的一个引理，位于命名空间 `SSet.p
rodStdSimplex.pairingCore`。
形式化陈述：isIndex_succ (l : Fin d) : IsIndex x hd l.succ ↔ (x.cast hd).simplex.1 l.c
astSucc = k.castSucc ∧ (x.cast hd).simplex.1 l.succ = k.succ ∧ (x.cast hd).simpl
ex.2 l.succ = (x.cast hd).simplex.2 l.castSucc
参数：l : Fin d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isIndex_succ (l : Fin d) :
    IsIndex x hd l.succ ↔
      (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
      (x.cast hd).simplex.1 l.succ = k.succ ∧
      (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc := Iff.rfl
/-
**SSet.prodStdSimplex.pairingCore.mem_range_left** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.prodStdSimplex.pairingCore`。
形式化陈述：mem_range_left (i : Fin (m + 2)) (hi : i != k.castSucc) : i in Set.range (
x.cast hd).simplex.1
参数：i : Fin (m + 2)；hi : i != k.castSucc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma mem_range_left (i : Fin (m + 2)) (hi : i ≠ k.castSucc) :
    i ∈ Set.range (x.cast hd).simplex.1 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range] at this
  tauto
/-
**SSet.prodStdSimplex.pairingCore.mem_range_right** 是 Mathlib 中的一个引理，位于命名空间 `SSe
t.prodStdSimplex.pairingCore`。
形式化陈述：mem_range_right (i : Fin (n + 1)) : i in Set.range (x.cast hd).simplex.2
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma mem_range_right (i : Fin (n + 1)) :
    i ∈ Set.range (x.cast hd).simplex.2 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range] at this
  tauto

/-- Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the finite subset of `Fin (d + 1)` consisting of those `l` such
that `x l` is of the form `(k.succ, _)`. -/
/-
**SSet.prodStdSimplex.pairingCore.finset** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStd
Simplex.pairingCore`。
形式化陈述：finset : Finset (Fin (d + 1))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the finite subset of `Fin (d + 1)` consisting of those `l` such
that `x l` is of the form `(k.succ, _)`.
-/
noncomputable def finset : Finset (Fin (d + 1)) :=
  { l : Fin (d + 1) | (x.cast hd).simplex.1 l = k.succ }

@[simp]
/-
**SSet.prodStdSimplex.pairingCore.mem_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.prodStdSimplex.pairingCore`。
形式化陈述：mem_finset_iff (l : Fin (d + 1)) : dsimp% l in finset x hd ↔ (x.cast hd).s
implex.1 l = k.succ
参数：l : Fin (d + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_finset_iff (l : Fin (d + 1)) :
    dsimp% l ∈ finset x hd ↔ (x.cast hd).simplex.1 l = k.succ := by
  simp [finset]
/-
**SSet.prodStdSimplex.pairingCore.nonempty_finset** 是 Mathlib 中的一个引理，位于命名空间 `SSe
t.prodStdSimplex.pairingCore`。
形式化陈述：nonempty_finset : (finset x hd).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.prodStdSimplex.pairingCore.mem_range_left`：mem_range_left (i : Fin 
(m + 2)) (hi : i != k.castSucc) : i in Set.range (x.cast hd).simplex.1
-/
lemma nonempty_finset : (finset x hd).Nonempty := by
  obtain ⟨i, hi⟩ := mem_range_left x hd k.succ (by grind)
  exact ⟨i, by simpa using hi⟩

/-- Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the smallest `l : Fin (d + 1)` such that `x l` is of the form `(k.succ, _)`. -/
/-
**SSet.prodStdSimplex.pairingCore.min** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdSim
plex.pairingCore`。
形式化陈述：min : Fin (d + 1)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `SSet.prodStdSimplex.pairingCore.nonempty_finset`：nonempty_finset : (fins
et x hd).Nonempty

--- 原说明 ---
Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the smallest `l : Fin (d + 1)` such that `x l` is of the form `(k.succ, _)`.
-/
noncomputable def min : Fin (d + 1) := (finset x hd).min' (nonempty_finset x hd)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.prodStdSimplex.pairingCore.simplex_fst_min** 是 Mathlib 中的一个引理，位于命名空间 `SSe
t.prodStdSimplex.pairingCore`。
形式化陈述：simplex_fst_min : dsimp% (x.cast hd).simplex.1 (min x hd) = k.succ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.prodStdSimplex.pairingCore.mem_finset_iff`：mem_finset_iff (l : Fin 
(d + 1)) : dsimp% l in finset x hd ↔ (x.cast hd).simplex.1 l = k.succ
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用引理 `SSet.prodStdSimplex.pairingCore.nonempty_finset`：nonempty_finset : (fins
et x hd).Nonempty
-/
lemma simplex_fst_min : dsimp% (x.cast hd).simplex.1 (min x hd) = k.succ := by
  rw [← mem_finset_iff]
  apply Finset.min'_mem

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.prodStdSimplex.pairingCore.simplex_fst_le_castSucc_iff** 是 Mathlib 中的一个引理
，位于命名空间 `SSet.prodStdSimplex.pairingCore`。
形式化陈述：simplex_fst_le_castSucc_iff (i : Fin (d + 1)) : dsimp% (x.cast hd).simplex
.1 i <= k.castSucc ↔ i < min x hd
参数：i : Fin (d + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `SSet.stdSimplex.monotone_apply`：monotone_apply {n i : Nat} (x : Δ[n] _⦋i
⦌) : Monotone (fun (j : Fin (i + 1)) => x j)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `SSet.prodStdSimplex.pairingCore.simplex_fst_min`：simplex_fst_min : dsimp
% (x.cast hd).simplex.1 (min x hd) = k.succ
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
-/
lemma simplex_fst_le_castSucc_iff (i : Fin (d + 1)) :
    dsimp% (x.cast hd).simplex.1 i ≤ k.castSucc ↔ i < min x hd := by
  contrapose!
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | h := h.lt_or_eq
    · by_contra! h'
      have := stdSimplex.monotone_apply (x.cast hd).simplex.1 h'.le
      dsimp at this
      rw [simplex_fst_min, ← not_lt] at this
      tauto
    · exact Finset.min'_le _ _ (by simpa using h.symm)
  · rw [Fin.castSucc_lt_iff_succ_le, ← simplex_fst_min x hd]
    exact stdSimplex.monotone_apply _ h

end

namespace IsIndex

section

variable {x} {hd : x.dim = d} {l : Fin d} (hl : IsIndex x hd l.succ)

include hl

/-
**SSet.prodStdSimplex.pairingCore.IsIndex.simplex_fst_castSucc** 是 Mathlib 中的一个引
理，位于命名空间 `SSet.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：simplex_fst_castSucc : dsimp% (x.cast hd).simplex.1 l.castSucc = k.castSuc
c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
lemma simplex_fst_castSucc :
    dsimp% (x.cast hd).simplex.1 l.castSucc = k.castSucc := hl.1
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.simplex_fst_succ** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：simplex_fst_succ : dsimp% (x.cast hd).simplex.1 l.succ = k.succ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma simplex_fst_succ :
    dsimp% (x.cast hd).simplex.1 l.succ = k.succ := hl.2.1
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.simplex_snd_succ** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：simplex_snd_succ : dsimp% (x.cast hd).simplex.2 l.succ = (x.cast hd).simpl
ex.2 l.castSucc
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
lemma simplex_snd_succ :
    dsimp% (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc := hl.2.2
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.succ_le_simplex_fst_iff** 是 Mathlib 中的
一个引理，位于命名空间 `SSet.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：succ_le_simplex_fst_iff (i : Fin (d + 1)) : dsimp% k.succ <= (x.cast hd).s
implex.1 i ↔ l.succ <= i
参数：i : Fin (d + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.simplex_fst_castSucc`：simplex_fs
t_castSucc : dsimp% (x.cast hd).simplex.1 l.castSucc = k.castSucc
· 使用引理 `SSet.stdSimplex.monotone_apply`：monotone_apply {n i : Nat} (x : Δ[n] _⦋i
⦌) : Monotone (fun (j : Fin (i + 1)) => x j)
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.simplex_fst_succ`：simplex_fst_su
cc : dsimp% (x.cast hd).simplex.1 l.succ = k.succ
-/
lemma succ_le_simplex_fst_iff (i : Fin (d + 1)) :
    dsimp% k.succ ≤ (x.cast hd).simplex.1 i ↔ l.succ ≤ i := by
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · by_contra!
    rw [← not_lt] at hi
    apply hi
    rw [← Fin.le_castSucc_iff] at this ⊢
    conv_rhs => rw [← hl.simplex_fst_castSucc]
    exact stdSimplex.monotone_apply _ this
  · rw [← hl.simplex_fst_succ]
    exact stdSimplex.monotone_apply _ hi
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.simplex_fst_le_castSucc_iff** 是 Mathli
b 中的一个引理，位于命名空间 `SSet.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：simplex_fst_le_castSucc_iff (i : Fin (d + 1)) : dsimp% (x.cast hd).simplex
.1 i <= k.castSucc ↔ i < l.succ
参数：i : Fin (d + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.succ_le_simplex_fst_iff`：succ_le
_simplex_fst_iff (i : Fin (d + 1)) : dsimp% k.succ <= (x.cast hd).simplex.1 i ↔ 
l.succ <= i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma simplex_fst_le_castSucc_iff (i : Fin (d + 1)) :
    dsimp% (x.cast hd).simplex.1 i ≤ k.castSucc ↔ i < l.succ := by
  rw [Fin.le_castSucc_iff, ← not_le, hl.succ_le_simplex_fst_iff, not_le]
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.min_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：min_eq : min x hd = l.succ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.simplex_fst_succ`：simplex_fst_su
cc : dsimp% (x.cast hd).simplex.1 l.succ = k.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `SSet.prodStdSimplex.pairingCore.nonempty_finset`：nonempty_finset : (fins
et x hd).Nonempty
· 使用定理 `Finset.le_min'_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.succ_le_simplex_fst_iff`：succ_le
_simplex_fst_iff (i : Fin (d + 1)) : dsimp% k.succ <= (x.cast hd).simplex.1 i ↔ 
l.succ <= i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.prodStdSimplex.pairingCore.mem_finset_iff`：mem_finset_iff (l : Fin 
(d + 1)) : dsimp% l in finset x hd ↔ (x.cast hd).simplex.1 l = k.succ
-/
lemma min_eq : min x hd = l.succ :=
  le_antisymm (Finset.min'_le _ _ (by simpa using hl.simplex_fst_succ))
    ((Finset.le_min'_iff _ _ ).2 (fun i hi ↦ by
      rw [mem_finset_iff] at hi
      simp [← hl.succ_le_simplex_fst_iff, ← hi]))
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.unique** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.prodStdSimplex.pairingCore.IsIndex`。
形式化陈述：unique {l' : Fin d} (hl' : IsIndex x hd l'.succ) : l = l'
参数：hl' : IsIndex x hd l'.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_inj`：∀ {n : ℕ} {a b : Fin n}, a.succ = b.succ ↔ a = b
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.min_eq`：min_eq : min x hd = l.su
cc
-/
lemma unique {l' : Fin d} (hl' : IsIndex x hd l'.succ) : l = l' := by
  rw [← Fin.succ_inj, ← hl.min_eq, hl'.min_eq]

end

section

variable {x} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

set_option backward.isDefEq.respectTransparency.types false in
/-- The type (II) simplex obtained as a face of a type (I) simplex. -/
@[simps -isSimp]
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.pro
dStdSimplex.pairingCore.IsIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (II) simplex obtained as a face of a type (I) simplex.
-/
noncomputable abbrev δ :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N where
  dim := d
  simplex := (Δ[m + 1] ⊗ Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ (x.cast hd).nonDegenerate _
  notMem := by
    dsimp
    -- `simp? [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range,
    --   mem_horn_iff_notMem_range,stdSimplex.δ_apply]` says:
    simp only [Subcomplex.mem_unionProd_iff, prod_δ_snd, mem_boundary_iff_notMem_range,
      Set.mem_range, stdSimplex.δ_apply, not_exists, prod_δ_fst, mem_horn_iff_notMem_range,
      ne_eq, exists_prop, not_or, not_forall, Decidable.not_not, not_and]
    refine ⟨fun j ↦ ?_, fun j hj ↦ ?_⟩
    · obtain ⟨i, hi⟩ := mem_range_right x hd j
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · refine ⟨l, ?_⟩
        rw [Fin.succAbove_castSucc_self, ← hi, ← hl.simplex_snd_succ]
        rfl
      · exact ⟨_, hi⟩
    · obtain ⟨i, hi⟩ := mem_range_left x hd j hj
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · exact (hj (by rw [← hi, hl.simplex_fst_castSucc])).elim
      · exact ⟨_, hi⟩

end

end IsIndex

variable (k n) in
/-- The type of type (I) simplices for the pairing -/
/-
**SSet.prodStdSimplex.pairingCore.Type** 是 Mathlib 中的一个结构，位于命名空间 `SSet.prodStdSi
mplex.pairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of type (I) simplices for the pairing
-/
structure Type₁ where
  /-- the nondegenerate simplex -/
  x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N
  /-- the dimension of the 1-codimensional face -/
  d : ℕ
  hd : x.dim = d + 1
  /-- the index attached to the corresponding type (II) simplex -/
  index : Fin (d + 1)
  isIndex : IsIndex x hd index.succ

variable {x} in
/-- Constructor for `Type₁ k n`. -/
@[simps]
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.type** 是 Mathlib 中的一个定义，位于命名空间 `SSet.p
rodStdSimplex.pairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Type₁ k n`.
-/
def IsIndex.type₁ {hd : x.dim = d + 1} {i : Fin (d + 1)}
    (h : IsIndex x hd i.succ) : Type₁.{u} k n where
  x := x
  d := d
  hd := hd
  index := i
  isIndex := h

namespace Type₁

/-
**SSet.prodStdSimplex.pairingCore.Type₁.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
prodStdSimplex.pairingCore.Type₁`。
形式化陈述：ext_iff {s t : Type₁.{u} k n} : s = t ↔ s.x = t.x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.prodStdSimplex.pairingCore.Type₁.hd`：∀ {m : ℕ} {k : Fin (m + 1)} {n
 : ℕ} (self : SSet.prodStdSimplex.pairingCore.Type₁ k n), self.x.dim = self.d + 
1
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsIndex.min_eq`：min_eq : min x hd = l.su
cc
· 使用定理 `SSet.prodStdSimplex.pairingCore.Type₁.isIndex`：∀ {m : ℕ} {k : Fin (m + 1
)} {n : ℕ} (self : SSet.prodStdSimplex.pairingCore.Type₁ k n),   SSet.prodStdSim
plex.pairingCore.IsIndex self.x ⋯ s…
-/
lemma ext_iff {s t : Type₁.{u} k n} :
    s = t ↔ s.x = t.x := by
  refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
  have hs := s.isIndex.min_eq
  have ht := t.isIndex.min_eq
  obtain ⟨x, d, hd, l, isIndex⟩ := s
  obtain ⟨y, d', hd', l', isIndex'⟩ := t
  subst h
  obtain rfl : d = d' := by grind
  obtain rfl : l = l' := by grind
  dsimp

/-- The type (II) simplex obtained as a face of a type (I) simplex. -/
/-
**SSet.prodStdSimplex.pairingCore.Type₁.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.Type₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (II) simplex obtained as a face of a type (I) simplex.
-/
noncomputable abbrev δ (s : Type₁.{u} k n) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N :=
  s.isIndex.δ

end Type₁

/-- Let `x` be a nondegenerate simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the property that `x` is a type (II) simplex for the pairing
`prodStdSimplex.pairingCore` that is constructed below. -/
/-
**SSet.prodStdSimplex.pairingCore.IsType** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStd
Simplex.pairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x` be a nondegenerate simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the property that `x` is a type (II) simplex for the pairing
`prodStdSimplex.pairingCore` that is constructed below.
-/
def IsType₂ : Prop :=
  ∀ (d : ℕ) (hd : x.dim = d) (l : Fin (d + 1)), ¬ IsIndex x hd l

namespace IsType₂

variable (hx : IsType₂ x) {d : ℕ} (hd : x.dim = d)

/-- Auxiliary definition for `IsType₂.simplex`. This gives the underlying
data of the type (I) simplex reconstructed from a type (II) simplex. -/
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `IsType₂.simplex`. This gives the underlying
data of the type (I) simplex reconstructed from a type (II) simplex.
-/
noncomputable def φ (i : Fin (d + 2)) : Fin (m + 2) × Fin (n + 1) :=
  if i = (min x hd).castSucc
  then ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩
  else objEquiv (x.cast hd).simplex ((min x hd).predAbove i)

@[simp]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_castSucc :
    φ x hd (min x hd).castSucc = ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩ := by
  simp [φ]

@[simp]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_succAbove (i : Fin (d + 1)) :
    φ x hd ((min x hd).castSucc.succAbove i) =
      objEquiv (x.cast hd).simplex i := by
  simp [φ]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_of_ne (i : Fin (d + 2)) (hi : i ≠ (min x hd).castSucc) :
    φ x hd i = objEquiv (x.cast hd).simplex ((min x hd).predAbove i) :=
  if_neg hi
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_of_lt (i : Fin (d + 2)) (hi : i < (min x hd).castSucc) :
    φ x hd i = objEquiv (x.cast hd).simplex (i.castPred (by grind)) := by
  rw [φ_of_ne _ _ _ hi.ne, Fin.predAbove_of_le_castSucc _ _ hi.le]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_of_gt (i : Fin (d + 2)) (hi : (min x hd).castSucc < i) :
    φ x hd i = objEquiv (x.cast hd).simplex (i.pred (by aesop)) := by
  rw [φ_of_ne _ _ _ hi.ne', Fin.predAbove_of_castSucc_lt _ _ hi]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_succ_snd : (φ x hd (min x hd).succ).2 = (φ x hd (min x hd).castSucc).2 := by
  have := φ_succAbove x hd (min x hd)
  simp_all [φ_castSucc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_succ_fst : (φ x hd (min x hd).succ).1 = k.succ := by
  have := φ_succAbove x hd (min x hd)
  simp_all [simplex_fst_min x hd]

variable {x}

include hx in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.strictMono_** 是 Mathlib 中的一个引理，位于命名空间 
`SSet.prodStdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strictMono_φ : StrictMono (φ x hd) := by
  have hx' := (prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain hi | rfl | hi := lt_trichotomy i (min x hd)
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
    rw [φ_of_lt _ _ _ (by grind), Fin.castPred_castSucc]
    rw [Fin.castSucc_lt_iff_succ_le] at hi
    obtain hi | hi :=  hi.lt_or_eq
    · rw [φ_of_lt _ _ _ (by grind)]
      exact hx' (Fin.lt_def.2 (by dsimp; grind))
    · rw [← Fin.castSucc_succ, hi, φ_castSucc]
      refine lt_of_le_of_ne ⟨?_, ?_⟩ ?_
      · dsimp
        rw [simplex_fst_le_castSucc_iff]
        grind
      · exact stdSimplex.monotone_apply _
          (by dsimp; rw [← hi]; exact Fin.castSucc_le_succ i)
      · intro h
        rw [Prod.ext_iff] at h
        dsimp at h
        obtain ⟨h₁, h₂⟩ := h
        apply hx _ hd i.succ
        rw [isIndex_succ]
        refine ⟨h₁, ?_, by aesop⟩
        have := φ_succAbove x hd (min x hd)
        rw [Fin.succAbove_castSucc_self] at this
        rw [← φ_succ_fst x hd, this, hi]
        dsimp
  · exact Prod.lt_of_lt_of_le (by simp) (by simp)
  · rw [φ_of_gt _ _ _ (by grind), φ_of_gt _ _ _ (by grind)]
    exact hx' (by grind)

/-- The type (I) simplex reconstructed from a type (II) simplex. -/
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.simplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `S
Set.prodStdSimplex.pairingCore.IsType₂`。
形式化陈述：simplex : (Δ[m + 1] otimes Δ[n]) _⦋d + 1⦌
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The type (I) simplex reconstructed from a type (II) simplex.
-/
noncomputable abbrev simplex : (Δ[m + 1] ⊗ Δ[n]) _⦋d + 1⦌ :=
  (objEquiv.{u}.symm ⟨φ x hd, (hx.strictMono_φ hd).monotone⟩)

@[simp]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.simplex_fst_apply** 是 Mathlib 中的一个引理，位
于命名空间 `SSet.prodStdSimplex.pairingCore.IsType₂`。
形式化陈述：simplex_fst_apply (i : Fin (d + 2)) : (hx.simplex hd).1 i = (φ x hd i).1
参数：i : Fin (d + 2)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma simplex_fst_apply (i : Fin (d + 2)) :
    (hx.simplex hd).1 i = (φ x hd i).1 := rfl

@[simp]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.simplex_snd_apply** 是 Mathlib 中的一个引理，位
于命名空间 `SSet.prodStdSimplex.pairingCore.IsType₂`。
形式化陈述：simplex_snd_apply (i : Fin (d + 2)) : (hx.simplex hd).2 i = (φ x hd i).2
参数：i : Fin (d + 2)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma simplex_snd_apply (i : Fin (d + 2)) :
    (hx.simplex hd).2 i = (φ x hd i).2 := rfl
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.simplex_mem_nonDegenerate** 是 Mathlib 
中的一个引理，位于命名空间 `SSet.prodStdSimplex.pairingCore.IsType₂`。
形式化陈述：simplex_mem_nonDegenerate : hx.simplex hd in (Δ[m + 1] otimes Δ[n]).nonDeg
enerate (d + 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv`：nonDegenerate
_iff_strictMono_objEquiv {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) : z 
in (Δ[p] otimes Δ[q]).nonDegenerate n ↔ StrictM…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsType₂.strictMono_φ`：strictMono_φ : Str
ictMono (φ x hd)
-/
lemma simplex_mem_nonDegenerate :
    hx.simplex hd ∈ (Δ[m + 1] ⊗ Δ[n]).nonDegenerate (d + 1) := by
  rw [nonDegenerate_iff_strictMono_objEquiv, Equiv.apply_symm_apply]
  exact hx.strictMono_φ hd
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_simplex :
    (Δ[m + 1] ⊗ Δ[n]).δ (min x hd).castSucc (hx.simplex hd) = (x.cast hd).simplex := by
  apply objEquiv.injective
  ext i : 2
  dsimp only [simplex]
  rw [objEquiv_δ_apply, Equiv.apply_symm_apply, OrderHom.coe_mk, φ_succAbove]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.notMem_simplex** 是 Mathlib 中的一个引理，位于命名
空间 `SSet.prodStdSimplex.pairingCore.IsType₂`。
形式化陈述：notMem_simplex : hx.simplex hd ∉ (Subcomplex.unionProd.{u} Λ[m + 1, k.cast
Succ] ∂Δ[n]).obj _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.N.notMem`：∀ {X : _root_.SSet} {A : X.Subcomplex} (self :
 A.N), self.simplex ∉ A.obj (Opposite.op { len := self.dim })
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.prodStdSimplex.pairingCore.IsType₂.δ_simplex`：δ_simplex : (Δ[m + 1]
 otimes Δ[n]).δ (min x hd).castSucc (hx.simplex hd) = (x.cast hd).simplex
· 使用定理 `CategoryTheory.Subfunctor.map`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (self : CategoryTheory
.Subfunctor F) {U V…
-/
lemma notMem_simplex :
    hx.simplex hd ∉ (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).obj _ := by
  refine fun h ↦ (x.cast hd).notMem ?_
  rw [← hx.δ_simplex hd]
  exact (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).map
    (SimplexCategory.δ (min x hd).castSucc).op h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The type (I) simplex reconstructed from a type (II) simplex. -/
@[simps]
/-
**SSet.prodStdSimplex.pairingCore.IsType₂.type** 是 Mathlib 中的一个定义，位于命名空间 `SSet.p
rodStdSimplex.pairingCore.IsType₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type (I) simplex reconstructed from a type (II) simplex.
-/
noncomputable def type₁ : Type₁ k n where
  x :=
    Subcomplex.N.mk (hx.simplex hd) (hx.simplex_mem_nonDegenerate hd)
      (hx.notMem_simplex hd)
  d := d
  hd := rfl
  index := min x hd
  isIndex := by simp [isIndex_succ]

end IsType₂

namespace IsIndex

variable {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.min_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.p
rodStdSimplex.pairingCore.IsIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_δ : min (d := d) hl.δ rfl = l := by
  refine le_antisymm (Finset.min'_le _ _ ?_)
    (Finset.le_min' _ _ _ (fun y hy ↦ ?_))
  · simp only [mem_finset_iff]
    simp only [Monoidal.tensorObj_obj, S.cast_dim, S.cast_simplex_rfl, prod_δ_fst,
      stdSimplex.δ_apply, Fin.succAbove_castSucc_self]
    exact hl.simplex_fst_succ
  · simp only [mem_finset_iff, Monoidal.tensorObj_obj, S.cast_dim,
      S.cast_simplex_rfl, prod_δ_fst, stdSimplex.δ_apply] at hy
    by_contra!
    rw [Fin.succAbove_of_castSucc_lt _ _ (by grind)] at hy
    grind [(hl.succ_le_simplex_fst_iff y.castSucc).1 hy.symm.le]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.isType** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.prodStdSimplex.pairingCore.IsIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isType₂_δ : IsType₂ hl.δ := by
  intro _ rfl t ht
  dsimp at t ht
  obtain ⟨t, rfl⟩ := Fin.eq_succ_of_ne_zero (i := t) (fun h ↦ by simp [h] at ht)
  obtain rfl : l = t.succ := by rw [← ht.min_eq, hl.min_δ]
  refine ((prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate t.castSucc.castSucc_lt_succ).ne ?_
  simp only [isIndex_succ] at hl ht
  dsimp [stdSimplex.δ_apply] at hl ht ⊢
  aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {x} in
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.eq_of_isType** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.prodStdSimplex.pairingCore.IsIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_of_isType₂_δ {u : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (hu : IsType₂ u) (i : Fin (d + 2))
    (hu' : S.mk u.simplex = S.mk (((Δ[m + 1] ⊗ Δ[n])).δ i (x.cast hd).simplex)) :
    i = l.castSucc ∨ i = l.succ := by
  obtain rfl : u.dim = d := congr_arg S.dim hu'
  rw [S.ext_iff] at hu'
  obtain hi | rfl | hi := lt_trichotomy i l.castSucc
  · obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := l) (by grind)
    refine (hu _ rfl l.succ ?_).elim
    simp [isIndex_succ, S.cast_simplex_rfl, hu', stdSimplex.δ_apply,
      Fin.succAbove_of_lt_succ i l.castSucc hi,
      Fin.succAbove_of_lt_succ i l.succ (by grind), dsimp% hl.simplex_fst_succ,
      dsimp% hl.simplex_snd_succ, dsimp% hl.simplex_fst_castSucc]
  · exact Or.inl rfl
  · obtain rfl | hi := (Fin.castSucc_lt_iff_succ_le.1 hi).eq_or_lt
    · exact Or.inr rfl
    · obtain ⟨l, rfl⟩ := Fin.eq_castSucc_of_ne_last (x := l) (by grind)
      refine (hu _ rfl l.succ ?_).elim
      simp [isIndex_succ, hu', stdSimplex.δ_apply,
        Fin.succAbove_of_castSucc_lt i l.castSucc (by grind),
        Fin.succAbove_of_castSucc_lt i l.succ (by grind),
        dsimp% hl.simplex_fst_castSucc, dsimp% hl.simplex_snd_succ,
        dsimp% hl.simplex_fst_succ]

end IsIndex

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.prodStdSimplex.pairingCore.IsType** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStd
Simplex.pairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsType₂.type₁_eq_of_δ_eq
    {t : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (ht : IsType₂ t) (s : Type₁.{u} k n) (hst : s.δ = t) {d : ℕ} (hd : t.dim = d) :
    ht.type₁ hd = s := by
  subst hst hd
  rw [Type₁.ext_iff, Subcomplex.N.ext_iff, N.ext_iff]
  rw [← s.x.toS.cast_eq_self s.hd, S.ext_iff']
  refine ⟨rfl, objEquiv.injective ?_⟩
  ext i : 2
  change φ s.δ rfl i = _
  by_cases! hi : i = s.index.castSucc
  · subst hi
    conv_lhs => rw [← s.isIndex.min_δ]
    dsimp
    rw [φ_castSucc]
    ext : 1
    · simp [← s.isIndex.simplex_fst_castSucc]
      rfl
    · change (s.x.cast s.hd).simplex.2
        (s.index.castSucc.succAbove (min s.δ rfl)) = _
      rw [s.isIndex.min_δ, Fin.succAbove_castSucc_self]
      exact s.isIndex.simplex_snd_succ -- defeq abuse
  · rw [← s.isIndex.min_δ] at hi
    rw [φ_of_ne _ rfl _ hi]
    change objEquiv (s.x.cast s.hd).simplex
      (s.index.castSucc.succAbove ((min s.δ rfl).predAbove i)) = _
    congr 1
    rw [← s.isIndex.min_δ]
    exact Fin.succAbove_predAbove hi -- `simp [hi]` should work but doesn't
/-
**SSet.prodStdSimplex.pairingCore.Type** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStdSi
mplex.pairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Type₁.isType₂_δ (s : Type₁.{u} k n) : IsType₂ s.δ :=
  s.isIndex.isType₂_δ

variable {x} in
/-
**SSet.prodStdSimplex.pairingCore.IsIndex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex.pairingCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsIndex.δ_injective
    {d : ℕ} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)
    {y : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    {d' : ℕ} {hd' : y.dim = d' + 1} {l' : Fin (d' + 1)} (hl' : IsIndex y hd' l'.succ)
    (h : hl.δ = hl'.δ) :
    x = y := by
  have h₁ := hl.isType₂_δ.type₁_eq_of_δ_eq hl'.type₁ h.symm rfl
  have h₂ := hl.isType₂_δ.type₁_eq_of_δ_eq hl.type₁ rfl rfl
  exact congr_arg Type₁.x (h₂.symm.trans h₁)

end pairingCore

open pairingCore

/-- The underlying structure which gives a pairing for
`Subcomplex.unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`. -/
@[simps]
/-
**SSet.prodStdSimplex.pairingCore** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdSimplex
`。
形式化陈述：pairingCore {m : Nat} (k : Fin (m + 1)) (n : Nat) : (Subcomplex.unionProd.
{u} Λ[m + 1, k.castSucc] ∂Δ[n]).PairingCore where ι
参数：k : Fin (m + 1)；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.prodStdSimplex.pairingCore.Type₁.hd`：∀ {m : ℕ} {k : Fin (m + 1)} {n
 : ℕ} (self : SSet.prodStdSimplex.pairingCore.Type₁ k n), self.x.dim = self.d + 
1

--- 原说明 ---
The underlying structure which gives a pairing for
`Subcomplex.unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`.
-/
noncomputable def pairingCore {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).PairingCore where
  ι := Type₁.{u} k n
  dim s := s.d
  simplex s := (s.x.cast s.hd).simplex
  index s := s.index.castSucc
  nonDegenerate₁ s := (s.x.cast s.hd).nonDegenerate
  nonDegenerate₂ s := s.isIndex.δ.nonDegenerate
  notMem₁ s := (s.x.cast s.hd).notMem
  notMem₂ s := s.isIndex.δ.notMem
  injective_type₁' {s t} h := by
    rw [Type₁.ext_iff, Subcomplex.N.ext_iff, N.ext_iff]
    rwa [← s.x.toS.cast_eq_self s.hd, ← t.x.toS.cast_eq_self t.hd]
  injective_type₂' {s t} h := by
    replace h : s.δ = t.δ := by rwa [Subcomplex.N.ext_iff, N.ext_iff]
    generalize hs : s.δ = u
    have hu' : IsType₂ u := by simpa only [hs] using s.isType₂_δ
    rw [← hu'.type₁_eq_of_δ_eq _ hs rfl,
      hu'.type₁_eq_of_δ_eq _ (h.symm.trans hs) rfl]
  type₁_ne_type₂' s t hst := by
    replace hst : s.x = t.isIndex.δ := by
      rwa [Subcomplex.N.ext_iff, N.ext_iff, ← s.x.cast_eq_self s.hd]
    have := t.isIndex.isType₂_δ
    rw [← hst] at this
    exact this _ _ _ s.isIndex
  surjective' x := by
    by_cases hx : IsType₂ x
    · generalize hd : x.dim = d
      refine ⟨hx.type₁ hd, Or.inr ?_⟩
      rw [S.ext_iff']
      exact ⟨hd, (hx.δ_simplex hd).symm⟩
    · simp only [IsType₂, not_forall, not_not] at hx
      obtain ⟨_ | d, hd, i, hx⟩ := hx
      · fin_cases i
        simp at hx
      · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by rintro rfl; simp at hx)
        refine ⟨{ x := x, d := d, hd := hd, index := i, isIndex := hx }, Or.inl ?_⟩
        dsimp
        rw [S.ext_iff']
        exact ⟨hd, rfl⟩

@[simp]
/-
**SSet.prodStdSimplex.type** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma type₁_pairingCore {m : ℕ} (k : Fin (m + 1)) {n : ℕ}
    (s : Type₁.{u} k n) :
    (pairingCore k n).type₁ s = s.x :=
  Subcomplex.N.cast_eq_self _ s.hd

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A weak rank function for `pairingCore k n`. -/
/-
**SSet.prodStdSimplex.weakRankFunction** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdSi
mplex`。
形式化陈述：weakRankFunction {m : Nat} (k : Fin (m + 1)) (n : Nat) : (pairingCore.{u} 
k n).WeakRankFunction Nat where rank s
参数：k : Fin (m + 1)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak rank function for `pairingCore k n`.
-/
noncomputable def weakRankFunction {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairingCore.{u} k n).WeakRankFunction ℕ where
  rank s := (finset s.x rfl).card
  lt := by
    intro ⟨s, d, hds, is, hs⟩ ⟨t, d', hdt, it, ht⟩ ⟨h₁, h₂⟩ h₃
    obtain ⟨ds, s, hs₁, hs₂, rfl⟩ := Subcomplex.N.mk_surjective s
    obtain ⟨dt, t, ht₁, ht₂, rfl⟩ := Subcomplex.N.mk_surjective t
    obtain rfl : d = d' := h₃
    obtain rfl : ds = d + 1 := hds
    obtain rfl : dt = d + 1 := hdt
    simp only [ne_eq, pairingCore_ι, Type₁.ext_iff] at h₁
    obtain ⟨f, hf, hδ⟩ := N.le_iff_exists_mono.1 h₂.le
    dsimp at f hf
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl | rfl := ht.eq_of_isType₂_δ hs.isType₂_δ i (by
      rw [S.ext_iff']
      exact ⟨rfl, hδ.symm⟩)
    · refine (h₁ (hs.δ_injective ht ?_)).elim
      rw [Subcomplex.N.ext_iff, N.ext_iff, S.ext_iff']
      exact ⟨rfl, hδ.symm⟩
    · let Ss := finset (Subcomplex.N.mk s hs₁ hs₂) rfl
      let St := finset (Subcomplex.N.mk t ht₁ ht₂) rfl
      let Sδ := finset hs.δ rfl
      replace hδ (i : Fin (d + 1)) :
          s.1 (is.castSucc.succAbove i) = t.1 (it.succ.succAbove i) :=
        DFunLike.congr_fun (congr_arg Prod.fst hδ.symm) i
      have hSs (i : Fin (d + 1)) : i ∈ Sδ ↔ is.castSucc.succAbove i ∈ Ss := by
        simp [Sδ, Ss, stdSimplex.δ_apply]
      have hSt (i : Fin (d + 1)) : i ∈ Sδ ↔ it.succ.succAbove i ∈ St := by
        simp [Sδ, St, stdSimplex.δ_apply, hδ]
      suffices Ss.card = Sδ.card ∧ St.card = Sδ.card + 1 by grind
      constructor
      · suffices Ss = Finset.image is.castSucc.succAbove Sδ by
          rw [this]
          exact Finset.card_image_of_injective _ Fin.succAbove_right_injective
        ext i
        obtain rfl | ⟨i, rfl⟩ := is.castSucc.eq_self_or_eq_succAbove i
        · have : is.castSucc ∉ Ss := fun h ↦ by
            have : s.1 is.castSucc ≤ k.castSucc := by
              simpa using (hs.simplex_fst_le_castSucc_iff is.castSucc).2 (by simp)
            simp_all [Ss]
          simpa
        · simp [hSs]
      · suffices St = Finset.image it.succ.succAbove Sδ ∪ {it.succ} by
          rw [this, Finset.card_union_of_disjoint (by simp),
            Finset.card_image_of_injective _ Fin.succAbove_right_injective,
            Finset.card_singleton]
        ext i
        obtain rfl | ⟨i, rfl⟩ := it.succ.eq_self_or_eq_succAbove i
        · have : it.succ ∈ St := by
            simpa [St, mem_finset_iff] using ht.simplex_fst_succ
          simp [hSt, this]
        · simp [hSt]
/-
**SSet.prodStdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairingCore.{u} k n).IsRegular :=
  (weakRankFunction.{u} k n).isRegular
/-
**SSet.prodStdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {m : ℕ} (k : Fin m) (n : ℕ) :
    (pairingCore.{u} k.succ n).IsInner where
  ne_zero (s : Type₁ k.succ n) h := by
    have : s.index = 0 := by rwa [← Fin.castSucc_eq_zero_iff]
    have hs : IsIndex s.x s.hd (Fin.succ 0) := by simpa [this] using s.isIndex
    obtain ⟨i, hi⟩ := mem_range_left s.x s.hd 0 (fun h ↦ by simp [Fin.ext_iff] at h)
    have := stdSimplex.monotone_apply (s.x.cast s.hd).simplex.1 i.zero_le
    have h₁ := hs.simplex_fst_castSucc
    dsimp only [Fin.castSucc_zero] at h₁
    simp [h₁, hi] at this
  ne_last x := by
    dsimp [pairingCore]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- A regular pairing for `Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`. -/
/-
**SSet.prodStdSimplex.pairing** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdSimplex`。
形式化陈述：pairing {m : Nat} (k : Fin (m + 2)) (n : Nat) : (Subcomplex.unionProd.{u} 
Λ[m + 1, k] ∂Δ[n]).Pairing
参数：k : Fin (m + 2)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular pairing for `Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`.
-/
noncomputable def pairing {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).Pairing :=
  if hk : k = Fin.last (m + 1) then
    (pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso
      (((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
        Functor.Monoidal.μIso opFunctor _ _) (by
          dsimp
          rw [hk, Subcomplex.preimage_comp,
            Subcomplex.preimage_op_unionProd,
            Subcomplex.preimage_unionProd,
            op_boundary, op_horn, Fin.rev_zero])
  else
    (pairingCore.{u} (k.castPred hk) n).pairing
/-
**SSet.prodStdSimplex.pairing_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStdSi
mplex`。
形式化陈述：pairing_castSucc {m : Nat} (k : Fin (m + 1)) (n : Nat) : pairing.{u} k.cas
tSucc n = (pairingCore.{u} k n).pairing
参数：k : Fin (m + 1)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma pairing_castSucc {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    pairing.{u} k.castSucc n = (pairingCore.{u} k n).pairing :=
  dif_neg (by grind)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.prodStdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (pairing.{u} k n).IsRegular := by
  by_cases! hk : k = Fin.last (m + 1)
  · subst hk
    dsimp only [pairing]
    rw [dif_pos rfl]
    infer_instance
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    rw [pairing_castSucc]
    infer_instance
/-
**SSet.prodStdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {m : ℕ} (k : Fin m) (n : ℕ) :
    (pairing.{u} k.castSucc.succ n).IsInner := by
  simp only [← Fin.castSucc_succ, pairing_castSucc]
  infer_instance

end prodStdSimplex

end SSet

