/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Parity

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs.

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

/-- Bicoloring of a path graph -/
/-
**SimpleGraph.pathGraph.bicoloring** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.pathGr
aph`。
形式化陈述：(n : ℕ) → (SimpleGraph.pathGraph n).Coloring Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bicoloring of a path graph
-/
def pathGraph.bicoloring (n : ℕ) :
    Coloring (pathGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

/-- Embedding of `pathGraph 2` into the first two elements of `pathGraph n` for `2 ≤ n` -/
/-
**SimpleGraph.pathGraph_two_embedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph_two_embedding (n : Nat) (h : 2 <= n) : pathGraph 2 ↪g pathGraph 
n where toFun v
参数：n : Nat；h : 2 <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of `pathGraph 2` into the first two elements of `pathGraph n` for `2 ≤
 n`
-/
def pathGraph_two_embedding (n : ℕ) (h : 2 ≤ n) : pathGraph 2 ↪g pathGraph n where
  toFun v := ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by simp [pathGraph]
/-
**SimpleGraph.chromaticNumber_pathGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_pathGraph (n : Nat) (h : 2 <= n) : (pathGraph n).chromatic
Number = 2
参数：n : Nat；h : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `SimpleGraph.two_le_chromaticNumber_of_adj`：two_le_chromaticNumber_of_adj
 {u v : V} (hadj : G.Adj u v) : 2 <= G.chromaticNumber
-/
theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj
/-
**SimpleGraph.Coloring.even_length_iff_congr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Coloring`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} (c : G.Coloring Bool) {u v : α} (p : 
G.Walk u v),   Even p.length ↔ (c u = true ↔ c v = true)
参数：c : G.Coloring Bool；p : G.Walk u v；c u = true ↔ c v = true。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff`：not_iff : ¬(a ↔ b) ↔ (¬a ↔ b)
· 使用定理 `Bool.eq_iff_iff`：∀ {a b : Bool}, a = b ↔ (a = true ↔ b = true)
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
-/
theorem Coloring.even_length_iff_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Even p.length ↔ (c u ↔ c v) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff, ← Bool.eq_iff_iff]
      exact c.valid h
    tauto
/-
**SimpleGraph.Coloring.odd_length_iff_not_congr** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Coloring`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} (c : G.Coloring Bool) {u v : α} (p : 
G.Walk u v),   Odd p.length ↔ (¬c u = true ↔ c v = true)
参数：c : G.Coloring Bool；p : G.Walk u v；¬c u = true ↔ c v = true。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `SimpleGraph.Coloring.even_length_iff_congr`：∀ {α : Type u_1} {G : Simple
Graph α} (c : G.Coloring Bool) {u v : α} (p : G.Walk u v),   Even p.length ↔ (c 
u = true ↔ c v = true)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem Coloring.odd_length_iff_not_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Odd p.length ↔ (¬c u ↔ c v) := by
  rw [← Nat.not_even_iff_odd, c.even_length_iff_congr p]
  tauto
/-
**SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Walk`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {u : α} (p : G.Walk u u), Odd p.lengt
h → 3 ≤ G.chromaticNumber
参数：p : G.Walk u u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.by_contradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Order.le_of_lt_add_one`：le_of_lt_add_one (h : x < y + 1) : x <= y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `SimpleGraph.Coloring.odd_length_iff_not_congr`：∀ {α : Type u_1} {G : Sim
pleGraph α} (c : G.Coloring Bool) {u v : α} (p : G.Walk u v),   Odd p.length ↔ (
¬c u = true ↔ c v = true)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
-/
theorem Walk.three_le_chromaticNumber_of_odd_loop {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hOdd : Odd p.length) : 3 ≤ G.chromaticNumber := Classical.by_contradiction <| by
  intro h
  have h' : G.chromaticNumber ≤ 2 := Order.le_of_lt_add_one <| not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_congr p).mp hOdd
  simp_all

/-- Bicoloring of a cycle graph of even size -/
/-
**SimpleGraph.cycleGraph.bicoloring_of_even** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGra
ph.cycleGraph`。
形式化陈述：(n : ℕ) → Even n → (SimpleGraph.cycleGraph n).Coloring Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bicoloring of a cycle graph of even size
-/
def cycleGraph.bicoloring_of_even (n : ℕ) (h : Even n) : Coloring (cycleGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hadj
      cases hadj with
      | inl huv | inr huv =>
        rw [← add_eq_of_eq_sub' huv.symm, ← Fin.even_iff_mod_of_even h,
          ← Fin.even_iff_mod_of_even h, Fin.even_add_one_iff_odd]
        apply Classical.not_iff.mpr
        simp [Fin.not_odd_iff_even_of_even h, Fin.not_even_iff_odd_of_even h]
/-
**SimpleGraph.chromaticNumber_cycleGraph_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：chromaticNumber_cycleGraph_of_even (n : Nat) (h : 2 <= n) (hEven : Even n)
 : (cycleGraph n).chromaticNumber = 2
参数：n : Nat；h : 2 <= n；hEven : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `SimpleGraph.two_le_chromaticNumber_of_adj`：two_le_chromaticNumber_of_adj
 {u v : V} (hadj : G.Adj u v) : 2 <= G.chromaticNumber
-/
theorem chromaticNumber_cycleGraph_of_even (n : ℕ) (h : 2 ≤ n) (hEven : Even n) :
    (cycleGraph n).chromaticNumber = 2 := by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

/-- Tricoloring of a cycle graph -/
/-
**SimpleGraph.cycleGraph.tricoloring** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.cycl
eGraph`。
形式化陈述：(n : ℕ) → 2 ≤ n → (SimpleGraph.cycleGraph n).Coloring (Fin 3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tricoloring of a cycle graph
-/
def cycleGraph.tricoloring (n : ℕ) (h : 2 ≤ n) : Coloring (cycleGraph n)
    (Fin 3) := Coloring.mk (fun u ↦ if u.val = n - 1 then 2 else ⟨u.val % 2, by lia⟩) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hadj
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val (?_))).symm
        exact v.val.mod_lt Nat.zero_lt_two
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val ?_))
        exact u.val.mod_lt Nat.zero_lt_two
      · simp only [ne_eq, Fin.ext_iff]
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        cases hadj with
        | inl huv | inr huv =>
          rw [← add_eq_of_eq_sub' huv.symm]
          simp only [Fin.val_add_eq_of_add_lt hv', Fin.val_add_eq_of_add_lt hu', Fin.val_one]
          rw [show ∀ x y : ℕ, x % 2 = y % 2 ↔ (Even x ↔ Even y) by simp [Nat.even_iff]; lia,
            Nat.even_add]
          simp only [Nat.not_even_one, iff_false, not_iff_self, iff_not_self]
          exact id
/-
**SimpleGraph.chromaticNumber_cycleGraph_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：chromaticNumber_cycleGraph_of_odd (n : Nat) (h : 2 <= n) (hOdd : Odd n) : 
(cycleGraph n).chromaticNumber = 3
参数：n : Nat；h : 2 <= n；hOdd : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.lt_of_le_of_ne`：∀ {n m : ℕ}, n ≤ m → ¬n = m → n < m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.not_odd_iff`：not_odd_iff : ¬Odd n ↔ n % 2 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `SimpleGraph.cycleGraph.length_cycle`：∀ {n : ℕ}, (SimpleGraph.cycleGraph.
cycle n).length = n + 3
· 使用定理 `SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop`：∀ {α : Type u_1} 
{G : SimpleGraph α} {u : α} (p : G.Walk u u), Odd p.length → 3 ≤ G.chromaticNumb
er
-/
theorem chromaticNumber_cycleGraph_of_odd (n : ℕ) (h : 2 ≤ n) (hOdd : Odd n) :
    (cycleGraph n).chromaticNumber = 3 := by
  have hc := (cycleGraph.tricoloring n h).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hn3 : n - 3 + 3 = n := by
      refine Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h ?_))
      intro h2
      rw [← h2] at hOdd
      exact (Nat.not_odd_iff.mpr rfl) hOdd
    let w : (cycleGraph (n - 3 + 3)).Walk 0 0 := cycleGraph.cycle (n - 3)
    have hOdd' : Odd w.length := by
      rw [cycleGraph.length_cycle, hn3]
      exact hOdd
    rw [← hn3]
    exact Walk.three_le_chromaticNumber_of_odd_loop w hOdd'

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The injection `(x₁, x₂) ↦ x₁` is always an `r`-coloring of a `completeEquipartiteGraph r ·`. -/
/-
**SimpleGraph.Coloring.completeEquipartiteGraph** 是 Mathlib 中的一个定义，位于命名空间 `Simpl
eGraph.Coloring`。
形式化陈述：{r t : ℕ} → (SimpleGraph.completeEquipartiteGraph r t).Coloring (Fin r)
参数：SimpleGraph.completeEquipartiteGraph r t；Fin r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection `(x₁, x₂) ↦ x₁` is always an `r`-coloring of a `completeEquipartit
eGraph r ·`.
-/
def Coloring.completeEquipartiteGraph :
  (completeEquipartiteGraph r t).Coloring (Fin r) := ⟨Prod.fst, id⟩

/-- The `completeEquipartiteGraph r t` is always `r`-colorable. -/
/-
**SimpleGraph.completeEquipartiteGraph_colorable** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：completeEquipartiteGraph_colorable : (completeEquipartiteGraph r t).Colora
ble r
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `completeEquipartiteGraph r t` is always `r`-colorable.
-/
theorem completeEquipartiteGraph_colorable :
  (completeEquipartiteGraph r t).Colorable r := ⟨Coloring.completeEquipartiteGraph⟩

end CompleteEquipartiteGraph

open Walk
/-
**SimpleGraph.two_colorable_iff_forall_loop_even** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph`。
形式化陈述：two_colorable_iff_forall_loop_even {α : Type*} {G : SimpleGraph α} : G.Col
orable 2 ↔ forall u, forall (w : G.Walk u u), Even w.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop`：∀ {α : Type u_1} 
{G : SimpleGraph α} {u : α} (p : G.Walk u u), Odd p.length → 3 ≤ G.chromaticNumb
er
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.colorable_iff_forall_connectedComponent`：colorable_iff_foral
l_connectedComponent {n : Nat} : G.Colorable n ↔ forall c : G.ConnectedComponent
, (c.toSimpleGraph).Colorable n
· 使用定理 `SimpleGraph.ConnectedComponent.nonempty_supp`：nonempty_supp (C : G.Conne
ctedComponent) : C.supp.Nonempty
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`：connected_toSimp
leGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where preconnec
ted
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `SimpleGraph.Walk.length_concat`：length_concat {u v w : V} (p : G.Walk u 
v) (h : G.Adj v w) : (p.concat h).length = p.length + 1
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Even.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd
 (a + 1)
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
-/
lemma two_colorable_iff_forall_loop_even {α : Type*} {G : SimpleGraph α} :
    G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), Even w.length := by
  simp_rw [← Nat.not_odd_iff_even]
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponent.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a ↦ Fin.ofNat 2 (c.connected_toSimpleGraph ⟨_, hv⟩ a).some.length
    intro a b hab he
    apply h _ <| (((c.connected_toSimpleGraph ⟨_, hv⟩ a).some.concat hab).append
                 (c.connected_toSimpleGraph ⟨_, hv⟩ b).some.reverse).map c.toSimpleGraph_hom
    rw [length_map, length_append, length_concat, length_reverse, add_right_comm]
    have : ((Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ a)).length) % 2 =
        (Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ b)).length % 2 := by
      simp_rw [← Fin.val_natCast, ← Fin.ofNat_eq_cast, he]
    exact (Nat.even_iff.mpr (by lia)).add_one

end SimpleGraph

