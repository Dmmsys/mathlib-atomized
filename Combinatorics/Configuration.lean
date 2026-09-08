/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projectivization.Constructions

/-!
# Configurations of Points and lines

This file introduces abstract configurations of points and lines, and proves some basic properties.

## Main definitions
* `Configuration.Nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `Configuration.HasPoints`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `Configuration.HasLines`:  A nondegenerate configuration in which
  every pair of points has a line through them.
* `Configuration.lineCount`: The number of lines through a given point.
* `Configuration.pointCount`: The number of lines through a given line.

## Main statements
* `Configuration.HasLines.card_le`: `HasLines` implies `|P| ≤ |L|`.
* `Configuration.HasPoints.card_le`: `HasPoints` implies `|L| ≤ |P|`.
* `Configuration.HasLines.hasPoints`: `HasLines` and `|P| = |L|` implies `HasPoints`.
* `Configuration.HasPoints.hasLines`: `HasPoints` and `|P| = |L|` implies `HasLines`.

Together, these four statements say that any two of the following properties imply the third:
(a) `HasLines`, (b) `HasPoints`, (c) `|P| = |L|`.

-/

@[expose] public section


open Finset

namespace Configuration

variable (P L : Type*) [Membership P L]

/-- A type synonym. -/
/-
**Configuration.Dual** 是 Mathlib 中的一个定义，位于命名空间 `Configuration`。
形式化陈述：Dual
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym.
-/
def Dual :=
  P
/-
**Configuration.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Inhabited P] : Inhabited (Dual P) :=
  h
/-
**Configuration.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite P] : Finite (Dual P) :=
  ‹Finite P›
/-
**Configuration.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Fintype P] : Fintype (Dual P) :=
  h

set_option synthInstance.checkSynthOrder false in
/-
**Configuration.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (Dual L) (Dual P) :=
  ⟨Function.swap (Membership.mem : L → P → Prop)⟩

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.

  Conditions 3 and 4 are equivalent. -/
/-
**Configuration.Nondegenerate** 是 Mathlib 中的一个归纳类型，位于命名空间 `Configuration`。
形式化陈述：(P : Type u_1) → (L : Type u_2) → [Membership P L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.

  Conditions 3 and 4 are equivalent.
-/
class Nondegenerate : Prop where
  exists_point : ∀ l : L, ∃ p, p ∉ l
  exists_line : ∀ p, ∃ l : L, p ∉ l
  eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
/-
**Configuration.HasPoints** 是 Mathlib 中的一个归纳类型，位于命名空间 `Configuration`。
形式化陈述：(P : Type u_1) → (L : Type u_2) → [Membership P L] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nondegenerate configuration in which every pair of lines has an intersection p
oint.
-/
class HasPoints extends Nondegenerate P L where
  /-- Intersection of two lines -/
  mkPoint : ∀ {l₁ l₂ : L}, l₁ ≠ l₂ → P
  mkPoint_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mkPoint h ∈ l₁ ∧ mkPoint h ∈ l₂

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
/-
**Configuration.HasLines** 是 Mathlib 中的一个归纳类型，位于命名空间 `Configuration`。
形式化陈述：(P : Type u_1) → (L : Type u_2) → [Membership P L] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nondegenerate configuration in which every pair of points has a line through t
hem.
-/
class HasLines extends Nondegenerate P L where
  /-- Line through two points -/
  mkLine : ∀ {p₁ p₂ : P}, p₁ ≠ p₂ → L
  mkLine_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mkLine h ∧ p₂ ∈ mkLine h

open Nondegenerate

open HasPoints (mkPoint mkPoint_ax)

open HasLines (mkLine mkLine_ax)
/-
**Configuration.Dual.Nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `Configuration.Dual
`。
形式化陈述：∀ (P : Type u_1) (L : Type u_2) [inst : Membership P L] [Configuration.Non
degenerate P L],   Configuration.Nondegenerate (Configuration.Dual L) (Configura
tion.Dual P)
参数：P : Type u_1；L : Type u_2；Configuration.Dual L；Configuration.Dual P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.Nondegenerate.exists_line`：∀ {P : Type u_1} {L : Type u_2}
 {inst : Membership P L} [self : Configuration.Nondegenerate P L] (p : P), ∃ l, 
p ∉ l
· 使用定理 `Configuration.Nondegenerate.exists_point`：∀ {P : Type u_1} {L : Type u_2
} {inst : Membership P L} [self : Configuration.Nondegenerate P L] (l : L), ∃ p,
 p ∉ l
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Configuration.Nondegenerate.eq_or_eq`：∀ {P : Type u_1} {L : Type u_2} {i
nst : Membership P L} [self : Configuration.Nondegenerate P L] {p₁ p₂ : P}   {l₁
 l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l…
-/
instance Dual.Nondegenerate [Nondegenerate P L] : Nondegenerate (Dual L) (Dual P) where
  exists_point := @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq := @fun l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ => (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm
/-
**Configuration.Dual.hasLines** 是 Mathlib 中的一个定义，位于命名空间 `Configuration.Dual`。
形式化陈述：(P : Type u_1) →   (L : Type u_2) →     [inst : Membership P L] →       [C
onfiguration.HasPoints P L] → Configuration.HasLines (Configuration.Dual L) (Con
figuration.Dual P)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasPoints.mkPoint_ax`：∀ {P : Type u_1} {L : Type u_2} {ins
t : Membership P L} [self : Configuration.HasPoints P L] {l₁ l₂ : L} (h : l₁ ≠ l
₂),   Configuration.HasP…
-/
instance Dual.hasLines [HasPoints P L] : HasLines (Dual L) (Dual P) :=
  { Dual.Nondegenerate _ _ with
    mkLine := @mkPoint P L _ _
    mkLine_ax := @mkPoint_ax P L _ _ }
/-
**Configuration.Dual.hasPoints** 是 Mathlib 中的一个定义，位于命名空间 `Configuration.Dual`。
形式化陈述：(P : Type u_1) →   (L : Type u_2) →     [inst : Membership P L] →       [C
onfiguration.HasLines P L] → Configuration.HasPoints (Configuration.Dual L) (Con
figuration.Dual P)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasLines.mkLine_ax`：∀ {P : Type u_1} {L : Type u_2} {inst 
: Membership P L} [self : Configuration.HasLines P L] {p₁ p₂ : P} (h : p₁ ≠ p₂),
   p₁ ∈ Configuration.…
-/
instance Dual.hasPoints [HasLines P L] : HasPoints (Dual L) (Dual P) :=
  { Dual.Nondegenerate _ _ with
    mkPoint := @mkLine P L _ _
    mkPoint_ax := @mkLine_ax P L _ _ }
/-
**Configuration.HasPoints.existsUnique_point** 是 Mathlib 中的一个定理，位于命名空间 `Configur
ation.HasPoints`。
形式化陈述：∀ (P : Type u_1) (L : Type u_2) [inst : Membership P L] [Configuration.Has
Points P L] (l₁ l₂ : L),   l₁ ≠ l₂ → ∃! p, p ∈ l₁ ∧ p ∈ l₂
参数：P : Type u_1；L : Type u_2；l₁ l₂ : L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasPoints.mkPoint_ax`：∀ {P : Type u_1} {L : Type u_2} {ins
t : Membership P L} [self : Configuration.HasPoints P L] {l₁ l₂ : L} (h : l₁ ≠ l
₂),   Configuration.HasP…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Configuration.Nondegenerate.eq_or_eq`：∀ {P : Type u_1} {L : Type u_2} {i
nst : Membership P L} [self : Configuration.Nondegenerate P L] {p₁ p₂ : P}   {l₁
 l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l…
· 使用定理 `Configuration.HasPoints.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2}
 {inst : Membership P L} [self : Configuration.HasPoints P L],   Configuration.N
ondegenerate P L
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasPoints.existsUnique_point [HasPoints P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
    ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
  ⟨mkPoint hl, mkPoint_ax hl, fun _ hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩
/-
**Configuration.HasLines.existsUnique_line** 是 Mathlib 中的一个定理，位于命名空间 `Configurat
ion.HasLines`。
形式化陈述：∀ (P : Type u_1) (L : Type u_2) [inst : Membership P L] [Configuration.Has
Lines P L] (p₁ p₂ : P),   p₁ ≠ p₂ → ∃! l, p₁ ∈ l ∧ p₂ ∈ l
参数：P : Type u_1；L : Type u_2；p₁ p₂ : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasPoints.existsUnique_point`：∀ (P : Type u_1) (L : Type u
_2) [inst : Membership P L] [Configuration.HasPoints P L] (l₁ l₂ : L),   l₁ ≠ l₂
 → ∃! p, p ∈ l₁ ∧ p ∈ l₂
-/
theorem HasLines.existsUnique_line [HasLines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
    ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
  HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp

variable {P L}

/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
/-
**Configuration.Nondegenerate.exists_injective_of_card_le** 是 Mathlib 中的一个定理，位于命
名空间 `Configuration.Nondegenerate`。
形式化陈述：∀ {P : Type u_1} {L : Type u_2} [inst : Membership P L] [Configuration.Non
degenerate P L] [inst_2 : Fintype P]   [inst_3 : Fintype L], Fintype.card L ≤ Fi
ntype.card P → ∃ f, Function.Injective f ∧ ∀ (l : L), f l ∉ l
参数：l : L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `Configuration.Nondegenerate.exists_point`：∀ {P : Type u_1} {L : Type u_2
} {inst : Membership P L} [self : Configuration.Nondegenerate P L] (l : L), ∃ p,
 p ∉ l
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `Finset.singleton_biUnion`：singleton_biUnion {a : α} : Finset.biUnion {a}
 t = t a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Finset.card_ne_zero_of_mem`：card_ne_zero_of_mem (h : a in s) : #s != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_le_one_iff`：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s
 -> b in s -> a = b
· 使用定理 `Finset.one_lt_card_iff`：one_lt_card_iff : 1 < #s ↔ exists a b, a in s ∧ 
b in s ∧ a != b
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Configuration.Nondegenerate.eq_or_eq`：∀ {P : Type u_1} {L : Type u_2} {i
nst : Membership P L} [self : Configuration.Nondegenerate P L] {p₁ p₂ : P}   {l₁
 l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.card_eq_iff_eq_univ`：Finset.card_eq_iff_eq_univ [Fintype α] (s : 
Finset α) : #s = Fintype.card α ↔ s = univ
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If a nondegenerate configuration has at least as many points as lines, then ther
e exists
  an injective function `f` from lines to points, such that `f l` does not lie o
n `l`.
-/
theorem Nondegenerate.exists_injective_of_card_le [Nondegenerate P L] [Fintype P] [Fintype L]
    (h : Fintype.card L ≤ Fintype.card P) : ∃ f : L → P, Function.Injective f ∧ ∀ l, f l ∉ l := by
  classical
    let t : L → Finset P := fun l => Set.toFinset { p | p ∉ l }
    suffices ∀ s : Finset L, #s ≤ (s.biUnion t).card by
      -- Hall's marriage theorem
      obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp this
      exact ⟨f, hf1, fun l => Set.mem_toFinset.mp (hf2 l)⟩
    intro s
    by_cases hs₀ : #s = 0
    -- If `s = ∅`, then `#s = 0 ≤ #(s.bUnion t)`
    · simp_rw [hs₀, zero_le]
    by_cases hs₁ : #s = 1
    -- If `s = {l}`, then pick a point `p ∉ l`
    · obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp hs₁
      obtain ⟨p, hl⟩ := exists_point (P := P) l
      rw [Finset.card_singleton, Finset.singleton_biUnion, Nat.one_le_iff_ne_zero]
      exact Finset.card_ne_zero_of_mem (Set.mem_toFinset.mpr hl)
    suffices #(s.biUnion t)ᶜ ≤ #sᶜ by
      -- Rephrase in terms of complements (uses `h`)
      rw [Finset.card_compl, Finset.card_compl, tsub_le_iff_left] at this
      replace := h.trans this
      rwa [← add_tsub_assoc_of_le s.card_le_univ, le_tsub_iff_left (le_add_left s.card_le_univ),
        add_le_add_iff_right] at this
    have hs₂ : #(s.biUnion t)ᶜ ≤ 1 := by
      -- At most one line through two points of `s`
      refine Finset.card_le_one_iff.mpr @fun p₁ p₂ hp₁ hp₂ => ?_
      simp_rw [t, Finset.mem_compl, Finset.mem_biUnion, not_exists, not_and,
        Set.mem_toFinset, Set.mem_ofPred_eq, Classical.not_not] at hp₁ hp₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ :=
        Finset.one_lt_card_iff.mp (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩)
      exact (eq_or_eq (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃
    by_cases hs₃ : #sᶜ = 0
    · rw [hs₃, Nat.le_zero]
      rw [Finset.card_compl, tsub_eq_zero_iff_le, (Finset.card_le_univ _).ge_iff_eq', eq_comm,
        Finset.card_eq_iff_eq_univ] at hs₃ ⊢
      rw [hs₃]
      rw [Finset.eq_univ_iff_forall] at hs₃ ⊢
      exact fun p =>
        Exists.elim (exists_line p) -- If `s = univ`, then show `s.bUnion t = univ`
        fun l hl => Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Set.mem_toFinset.mpr hl⟩
    · exact hs₂.trans (Nat.one_le_iff_ne_zero.mpr hs₃)

-- If `s < univ`, then consequence of `hs₂`
variable (L)

/-- Number of points on a given line. -/
/-
**Configuration.lineCount** 是 Mathlib 中的一个定义，位于命名空间 `Configuration`。
形式化陈述：lineCount (p : P) : Nat
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Number of points on a given line.
-/
noncomputable def lineCount (p : P) : ℕ :=
  Nat.card { l : L // p ∈ l }

variable (P) {L}

/-- Number of lines through a given point. -/
/-
**Configuration.pointCount** 是 Mathlib 中的一个定义，位于命名空间 `Configuration`。
形式化陈述：pointCount (l : L) : Nat
参数：l : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Number of lines through a given point.
-/
noncomputable def pointCount (l : L) : ℕ :=
  Nat.card { p : P // p ∈ l }

variable (L)
/-
**Configuration.sum_lineCount_eq_sum_pointCount** 是 Mathlib 中的一个定理，位于命名空间 `Confi
guration`。
形式化陈述：sum_lineCount_eq_sum_pointCount [Fintype P] [Fintype L] : ∑ p : P, lineCou
nt L p = ∑ l : L, pointCount P l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sum_lineCount_eq_sum_pointCount [Fintype P] [Fintype L] :
    ∑ p : P, lineCount L p = ∑ l : L, pointCount P l := by
  classical
    simp only [lineCount, pointCount, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    apply Fintype.card_congr
    calc
      (Σ p, { l : L // p ∈ l }) ≃ { x : P × L // x.1 ∈ x.2 } :=
        (Equiv.subtypeProdEquivSigmaSubtype (· ∈ ·)).symm
      _ ≃ { x : L × P // x.2 ∈ x.1 } := (Equiv.prodComm P L).subtypeEquiv fun x => Iff.rfl
      _ ≃ Σ l, { p // p ∈ l } := Equiv.subtypeProdEquivSigmaSubtype fun (l : L) (p : P) => p ∈ l

variable {P L}
/-
**Configuration.HasLines.pointCount_le_lineCount** 是 Mathlib 中的一个定理，位于命名空间 `Conf
iguration.HasLines`。
形式化陈述：∀ {P : Type u_1} {L : Type u_2} [inst : Membership P L] [Configuration.Has
Lines P L] {p : P} {l : L},   p ∉ l → ∀ [Finite { l // p ∈ l }], Configuration.p
ointCount P l ≤ Configuration.lineCount L p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Configuration.lineCount.eq_1`：∀ {P : Type u_1} (L : Type u_2) [inst : Me
mbership P L] (p : P), Configuration.lineCount L p = Nat.card { l // p ∈ l }
· 使用定理 `Configuration.pointCount.eq_1`：∀ (P : Type u_1) {L : Type u_2} [inst : M
embership P L] (l : L), Configuration.pointCount P l = Nat.card { p // p ∈ l }
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Configuration.HasLines.mkLine_ax`：∀ {P : Type u_1} {L : Type u_2} {inst 
: Membership P L} [self : Configuration.HasLines P L] {p₁ p₂ : P} (h : p₁ ≠ p₂),
   p₁ ∈ Configuration.…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Configuration.Nondegenerate.eq_or_eq`：∀ {P : Type u_1} {L : Type u_2} {i
nst : Membership P L} [self : Configuration.Nondegenerate P L] {p₁ p₂ : P}   {l₁
 l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l…
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem HasLines.pointCount_le_lineCount [HasLines P L] {p : P} {l : L} (h : p ∉ l)
    [Finite { l : L // p ∈ l }] : pointCount P l ≤ lineCount L p := by
  by_cases hf : Infinite { p : P // p ∈ l }
  · simp [pointCount]
  have := fintypeOfNotInfinite hf
  cases nonempty_fintype { l : L // p ∈ l }
  rw [lineCount, pointCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have : ∀ p' : { p // p ∈ l }, p ≠ p' := fun p' hp' => h ((congr_arg (· ∈ l) hp').mpr p'.2)
  exact
    Fintype.card_le_of_injective (fun p' => ⟨mkLine (this p'), (mkLine_ax (this p')).1⟩)
      fun p₁ p₂ hp =>
      Subtype.ext ((eq_or_eq p₁.2 p₂.2 (mkLine_ax (this p₁)).2
            ((congr_arg (_ ∈ ·) (Subtype.ext_iff.mp hp)).mpr (mkLine_ax (this p₂)).2)).resolve_right
          fun h' => (congr_arg (p ∉ ·) h').mp h (mkLine_ax (this p₁)).1)
/-
**Configuration.HasPoints.lineCount_le_pointCount** 是 Mathlib 中的一个定理，位于命名空间 `Con
figuration.HasPoints`。
形式化陈述：∀ {P : Type u_1} {L : Type u_2} [inst : Membership P L] [Configuration.Has
Points P L] {p : P} {l : L},   p ∉ l → ∀ [hf : Finite { p // p ∈ l }], Configura
tion.lineCount L p ≤ Configuration.pointCount P l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasLines.pointCount_le_lineCount`：∀ {P : Type u_1} {L : Ty
pe u_2} [inst : Membership P L] [Configuration.HasLines P L] {p : P} {l : L},   
p ∉ l → ∀ [Finite { l // p ∈ l }], C…
-/
theorem HasPoints.lineCount_le_pointCount [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
    [hf : Finite { p : P // p ∈ l }] : lineCount L p ≤ pointCount P l :=
  @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf

variable (P L)

/-- If a nondegenerate configuration has a unique line through any two points, then `|P| ≤ |L|`. -/
/-
**Configuration.HasLines.card_le** 是 Mathlib 中的一个定理，位于命名空间 `Configuration.HasLin
es`。
形式化陈述：∀ (P : Type u_1) (L : Type u_2) [inst : Membership P L] [Configuration.Has
Lines P L] [inst : Fintype P]   [inst_1 : Fintype L], Fintype.card P ≤ Fintype.c
ard L
参数：P : Type u_1；L : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Configuration.Nondegenerate.exists_injective_of_card_le`：∀ {P : Type u_1
} {L : Type u_2} [inst : Membership P L] [Configuration.Nondegenerate P L] [inst
_2 : Fintype P]   [inst_3 : Fintype L], Finty…
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Configuration.sum_lineCount_eq_sum_pointCount`：sum_lineCount_eq_sum_poin
tCount [Fintype P] [Fintype L] : ∑ p : P, lineCount L p = ∑ l : L, pointCount P 
l
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Configuration.HasLines.pointCount_le_lineCount`：∀ {P : Type u_1} {L : Ty
pe u_2} [inst : Membership P L] [Configuration.HasLines P L] {p : P} {l : L},   
p ∉ l → ∀ [Finite { l // p ∈ l }], C…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用定理 `Finset.sum_lt_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {
s t : Finset ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Configuration.lineCount.eq_1`：∀ {P : Type u_1} (L : Type u_2) [inst : Me
mbership P L] (p : P), Configuration.lineCount L p = Nat.card { l // p ∈ l }
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Configuration.Nondegenerate.exists_line`：∀ {P : Type u_1} {L : Type u_2}
 {inst : Membership P L} [self : Configuration.Nondegenerate P L] (p : P), ∃ l, 
p ∉ l
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If a nondegenerate configuration has a unique line through any two points, then 
`|P| ≤ |L|`.
-/
theorem HasLines.card_le [HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P ≤ Fintype.card L := by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := Nondegenerate.exists_injective_of_card_le (le_of_not_ge hc₂)
  have :=
    calc
      ∑ p, lineCount L p = ∑ l, pointCount P l := sum_lineCount_eq_sum_pointCount P L
      _ ≤ ∑ l, lineCount L (f l) :=
        (Finset.sum_le_sum fun l _ => HasLines.pointCount_le_lineCount (hf₂ l))
      _ = ∑ p ∈ univ.map ⟨f, hf₁⟩, lineCount L p := by rw [sum_map]; dsimp
      _ < ∑ p, lineCount L p := by
        obtain ⟨p, hp⟩ := not_forall.mp (mt (Fintype.card_le_of_surjective f) hc₂)
        refine sum_lt_sum_of_subset (subset_univ _) (mem_univ p) ?_ ?_ fun p _ _ ↦ zero_le
        · simpa only [Finset.mem_map, exists_prop, Finset.mem_univ, true_and]
        · rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_pos_iff]
          obtain ⟨l, _⟩ := @exists_line P L _ _ p
          exact
            let := not_exists.mp hp l
            ⟨⟨mkLine this, (mkLine_ax this).2⟩⟩
  exact lt_irrefl _ this

/-- If a nondegenerate configuration has a unique point on any two lines, then `|L| ≤ |P|`. -/
/-
**Configuration.HasPoints.card_le** 是 Mathlib 中的一个定理，位于命名空间 `Configuration.HasPo
ints`。
形式化陈述：∀ (P : Type u_1) (L : Type u_2) [inst : Membership P L] [Configuration.Has
Points P L] [inst : Fintype P]   [inst_1 : Fintype L], Fintype.card L ≤ Fintype.
card P
参数：P : Type u_1；L : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasLines.card_le`：∀ (P : Type u_1) (L : Type u_2) [inst : 
Membership P L] [Configuration.HasLines P L] [inst : Fintype P]   [inst_1 : Fint
ype L], Fintype.card…

--- 原说明 ---
If a nondegenerate configuration has a unique point on any two lines, then `|L| 
≤ |P|`.
-/
theorem HasPoints.card_le [HasPoints P L] [Fintype P] [Fintype L] :
    Fintype.card L ≤ Fintype.card P :=
  @HasLines.card_le (Dual L) (Dual P) _ _ _ _

variable {P L}
/-
**Configuration.HasLines.exists_bijective_of_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `
Configuration.HasLines`。
形式化陈述：∀ {P : Type u_1} {L : Type u_2} [inst : Membership P L] [Configuration.Has
Lines P L] [inst_2 : Fintype P]   [inst_3 : Fintype L],   Fintype.card P = Finty
pe.card L →     ∃ f, Function.Bijective f ∧ ∀ (l : L), Configuration.pointCount 
P l = Configuration.lineCount L (f l)
参数：l : L；f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.Nondegenerate.exists_injective_of_card_le`：∀ {P : Type u_1
} {L : Type u_2} [inst : Membership P L] [Configuration.Nondegenerate P L] [inst
_2 : Fintype P]   [inst_3 : Fintype L], Finty…
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_eq_sum_iff_of_le`：∀ {ι : Type u_9} {M : Type u_10} [inst : Ad
dCommMonoid M] [inst_1 : PartialOrder M] [IsOrderedCancelAddMonoid M]   {s : Fin
set ι} {f g : ι →…
· 使用定理 `Configuration.HasLines.pointCount_le_lineCount`：∀ {P : Type u_1} {L : Ty
pe u_2} [inst : Membership P L] [Configuration.HasLines P L] {p : P} {l : L},   
p ∉ l → ∀ [Finite { l // p ∈ l }], C…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Configuration.sum_lineCount_eq_sum_pointCount`：sum_lineCount_eq_sum_poin
tCount [Fintype P] [Fintype L] : ∑ p : P, lineCount L p = ∑ l : L, pointCount P 
l
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem HasLines.exists_bijective_of_card_eq [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) :
    ∃ f : L → P, Function.Bijective f ∧ ∀ l, pointCount P l = lineCount L (f l) := by
  obtain ⟨f, hf1, hf2⟩ := Nondegenerate.exists_injective_of_card_le (ge_of_eq h)
  have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
  exact ⟨f, hf3, fun l ↦ (sum_eq_sum_iff_of_le fun l _ ↦ pointCount_le_lineCount (hf2 l)).1
        ((hf3.sum_comp _).trans (sum_lineCount_eq_sum_pointCount P L)).symm _ <| mem_univ _⟩
/-
**Configuration.HasLines.lineCount_eq_pointCount** 是 Mathlib 中的一个定理，位于命名空间 `Conf
iguration.HasLines`。
形式化陈述：∀ {P : Type u_1} {L : Type u_2} [inst : Membership P L] [Configuration.Has
Lines P L] [inst_2 : Fintype P]   [inst_3 : Fintype L],   Fintype.card P = Finty
pe.card L →     ∀ {p : P} {l : L}, p ∉ l → Configuration.lineCount L p = Configu
ration.pointCount P l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasLines.exists_bijective_of_card_eq`：∀ {P : Type u_1} {L 
: Type u_2} [inst : Membership P L] [Configuration.HasLines P L] [inst_2 : Finty
pe P]   [inst_3 : Fintype L],   Fintype.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_product_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintyp
e α] [inst_1 : Fintype β], Finset.univ ×ˢ Finset.univ = Finset.univ
· 使用定理 `Finset.sum_product_right`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5}
 [inst : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈
 s ×ˢ t, f x =…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Configuration.sum_lineCount_eq_sum_pointCount`：sum_lineCount_eq_sum_poin
tCount [Fintype P] [Fintype L] : ∑ p : P, lineCount L p = ∑ l : L, pointCount P 
l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_finset_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5
} [inst : AddCommMonoid β] (r : Finset (γ × α)) (s : Finset γ)   (t : γ → Finset
 α),   (∀ (p : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Finset.sum_finset_product_right`：∀ {α : Type u_3} {β : Type u_4} {γ : Ty
pe u_5} [inst : AddCommMonoid β] (r : Finset (α × γ)) (s : Finset γ)   (t : γ → 
Finset α),   (∀ (p : …
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [in
st : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e
 : ι → κ),…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.sum_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_eq_sum_iff_of_le`：∀ {ι : Type u_9} {M : Type u_10} [inst : Ad
dCommMonoid M] [inst_1 : PartialOrder M] [IsOrderedCancelAddMonoid M]   {s : Fin
set ι} {f g : ι →…
（共 35 条，此处仅展示前 30 条）
-/
theorem HasLines.lineCount_eq_pointCount [HasLines P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l := by
  classical
    obtain ⟨f, hf1, hf2⟩ := HasLines.exists_bijective_of_card_eq hPL
    let s : Finset (P × L) := Set.toFinset { i | i.1 ∈ i.2 }
    have step1 : ∑ i : P × L, lineCount L i.1 = ∑ i : P × L, pointCount P i.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product_right, Finset.sum_product]
      simp_rw [Finset.sum_const, Finset.card_univ, hPL, sum_lineCount_eq_sum_pointCount]
    have step2 : ∑ i ∈ s, lineCount L i.1 = ∑ i ∈ s, pointCount P i.2 := by
      rw [s.sum_finset_product Finset.univ fun p => Set.toFinset { l | p ∈ l }]
      on_goal 1 =>
        rw [s.sum_finset_product_right Finset.univ fun l => Set.toFinset { p | p ∈ l }, eq_comm]
        · refine sum_bijective _ hf1 (by simp) fun l _ ↦ ?_
          simp_rw [hf2, sum_const, Set.toFinset_card, ← Nat.card_eq_fintype_card]
          change pointCount P l • _ = lineCount L (f l) • _
          rw [hf2]
      all_goals simp_rw [s, Finset.mem_univ, true_and, Set.mem_toFinset]; exact fun p => Iff.rfl
    have step3 : ∑ i ∈ sᶜ, lineCount L i.1 = ∑ i ∈ sᶜ, pointCount P i.2 := by
      rwa [← s.sum_add_sum_compl, ← s.sum_add_sum_compl, step2, add_left_cancel_iff] at step1
    rw [← Set.toFinset_compl] at step3
    exact
      ((Finset.sum_eq_sum_iff_of_le fun i hi =>
              HasLines.pointCount_le_lineCount (by exact Set.mem_toFinset.mp hi)).mp
          step3.symm (p, l) (Set.mem_toFinset.mpr hpl)).symm
/-
**Configuration.HasPoints.lineCount_eq_pointCount** 是 Mathlib 中的一个定理，位于命名空间 `Con
figuration.HasPoints`。
形式化陈述：∀ {P : Type u_1} {L : Type u_2} [inst : Membership P L] [Configuration.Has
Points P L] [inst_2 : Fintype P]   [inst_3 : Fintype L],   Fintype.card P = Fint
ype.card L →     ∀ {p : P} {l : L}, p ∉ l → Configuration.lineCount L p = Config
uration.pointCount P l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Configuration.HasLines.lineCount_eq_pointCount`：∀ {P : Type u_1} {L : Ty
pe u_2} [inst : Membership P L] [Configuration.HasLines P L] [inst_2 : Fintype P
]   [inst_3 : Fintype L],   Fintype.…
-/
theorem HasPoints.lineCount_eq_pointCount [HasPoints P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l :=
  (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm

/-- If a nondegenerate configuration has a unique line through any two points, and if `|P| = |L|`,
  then there is a unique point on any two lines. -/
@[instance_reducible]
/-
**Configuration.HasLines.hasPoints** 是 Mathlib 中的一个定义，位于命名空间 `Configuration.HasL
ines`。
形式化陈述：{P : Type u_1} →   {L : Type u_2} →     [inst : Membership P L] →       [C
onfiguration.HasLines P L] →         [inst_2 : Fintype P] → [inst_3 : Fintype L]
 → Fintype.card P = Fintype.card L → Configuration.HasPoints P L
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L

--- 原说明 ---
If a nondegenerate configuration has a unique line through any two points, and i
f `|P| = |L|`,
  then there is a unique point on any two lines.
-/
noncomputable def HasLines.hasPoints [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasPoints P L :=
  let : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂ := fun l₁ l₂ hl => by
    classical
      obtain ⟨f, _, hf2⟩ := HasLines.exists_bijective_of_card_eq h
      have : Nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩
      have := Fintype.one_lt_card_iff_nontrivial.mp ((congr_arg _ h).mpr Fintype.one_lt_card)
      have h₁ : ∀ p : P, 0 < lineCount L p := fun p =>
        Exists.elim (exists_ne p) fun q hq =>
          (congr_arg _ Nat.card_eq_fintype_card).mpr
            (Fintype.card_pos_iff.mpr ⟨⟨mkLine hq, (mkLine_ax hq).2⟩⟩)
      have h₂ : ∀ l : L, 0 < pointCount P l := fun l => (congr_arg _ (hf2 l)).mpr (h₁ (f l))
      obtain ⟨p, hl₁⟩ := Fintype.card_pos_iff.mp ((congr_arg _ Nat.card_eq_fintype_card).mp (h₂ l₁))
      by_cases hl₂ : p ∈ l₂
      · exact ⟨p, hl₁, hl₂⟩
      have key' : Fintype.card { q : P // q ∈ l₂ } = Fintype.card { l : L // p ∈ l } :=
        ((HasLines.lineCount_eq_pointCount h hl₂).trans Nat.card_eq_fintype_card).symm.trans
          Nat.card_eq_fintype_card
      have : ∀ q : { q // q ∈ l₂ }, p ≠ q := fun q hq => hl₂ ((congr_arg (· ∈ l₂) hq).mpr q.2)
      let f : { q : P // q ∈ l₂ } → { l : L // p ∈ l } := fun q =>
        ⟨mkLine (this q), (mkLine_ax (this q)).1⟩
      have hf : Function.Injective f := fun q₁ q₂ hq =>
        Subtype.ext ((eq_or_eq q₁.2 q₂.2 (mkLine_ax (this q₁)).2
            ((congr_arg (_ ∈ ·) (Subtype.ext_iff.mp hq)).mpr (mkLine_ax (this q₂)).2)).resolve_right
            fun h => (congr_arg (p ∉ ·) h).mp hl₂ (mkLine_ax (this q₁)).1)
      have key' := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, key'⟩).2
      obtain ⟨q, hq⟩ := key' ⟨l₁, hl₁⟩
      exact ⟨q, (congr_arg (_ ∈ ·) (Subtype.ext_iff.mp hq)).mp (mkLine_ax (this q)).2, q.2⟩
  { ‹HasLines P L› with
    mkPoint := fun {l₁ l₂} hl => Classical.choose (this l₁ l₂ hl)
    mkPoint_ax := fun {l₁ l₂} hl => Classical.choose_spec (this l₁ l₂ hl) }

/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
@[instance_reducible]
/-
**Configuration.HasPoints.hasLines** 是 Mathlib 中的一个定义，位于命名空间 `Configuration.HasP
oints`。
形式化陈述：{P : Type u_1} →   {L : Type u_2} →     [inst : Membership P L] →       [C
onfiguration.HasPoints P L] →         [inst_2 : Fintype P] → [inst_3 : Fintype L
] → Fintype.card P = Fintype.card L → Configuration.HasLines P L
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.HasPoints.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2}
 {inst : Membership P L} [self : Configuration.HasPoints P L],   Configuration.N
ondegenerate P L

--- 原说明 ---
If a nondegenerate configuration has a unique point on any two lines, and if `|P
| = |L|`,
  then there is a unique line through any two points.
-/
noncomputable def HasPoints.hasLines [HasPoints P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasLines P L :=
  let := @HasLines.hasPoints (Dual L) (Dual P) _ _ _ _ h.symm
  { ‹HasPoints P L› with
    mkLine := @fun _ _ => this.mkPoint
    mkLine_ax := @fun _ _ => this.mkPoint_ax }

variable (P L)

/-- A projective plane is a nondegenerate configuration in which every pair of lines has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position. -/
/-
**Configuration.ProjectivePlane** 是 Mathlib 中的一个归纳类型，位于命名空间 `Configuration`。
形式化陈述：(P : Type u_1) → (L : Type u_2) → [Membership P L] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A projective plane is a nondegenerate configuration in which every pair of lines
 has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position.
-/
class ProjectivePlane extends HasPoints P L, HasLines P L where
  exists_config :
    ∃ (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L),
      p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧ p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃

namespace ProjectivePlane

variable [ProjectivePlane P L]

/-
**Configuration.ProjectivePlane.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration.Projec
tivePlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProjectivePlane (Dual L) (Dual P) :=
  { Dual.hasPoints _ _, Dual.hasLines _ _ with
    exists_config :=
      let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

/-- The order of a projective plane is one less than the number of lines through an arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line. -/
/-
**Configuration.ProjectivePlane.order** 是 Mathlib 中的一个定义，位于命名空间 `Configuration.P
rojectivePlane`。
形式化陈述：order : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.ProjectivePlane.exists_config`：∀ {P : Type u_1} {L : Type 
u_2} {inst : Membership P L} [self : Configuration.ProjectivePlane P L],   ∃ p₁ 
p₂ p₃ l₁ l₂ l₃, p₁ ∉ l₂ ∧ p₁ ∉ l₃…

--- 原说明 ---
The order of a projective plane is one less than the number of lines through an 
arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line.
-/
noncomputable def order : ℕ :=
  lineCount L (Classical.choose (@exists_config P L _ _)) - 1
/-
**Configuration.ProjectivePlane.card_points_eq_card_lines** 是 Mathlib 中的一个定理，位于命
名空间 `Configuration.ProjectivePlane`。
形式化陈述：card_points_eq_card_lines [Fintype P] [Fintype L] : Fintype.card P = Finty
pe.card L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Configuration.HasLines.card_le`：∀ (P : Type u_1) (L : Type u_2) [inst : 
Membership P L] [Configuration.HasLines P L] [inst : Fintype P]   [inst_1 : Fint
ype L], Fintype.card…
· 使用定理 `Configuration.HasPoints.card_le`：∀ (P : Type u_1) (L : Type u_2) [inst :
 Membership P L] [Configuration.HasPoints P L] [inst : Fintype P]   [inst_1 : Fi
ntype L], Fintype.car…
-/
theorem card_points_eq_card_lines [Fintype P] [Fintype L] : Fintype.card P = Fintype.card L :=
  le_antisymm (HasLines.card_le P L) (HasPoints.card_le P L)

variable {P}
/-
**Configuration.ProjectivePlane.lineCount_eq_lineCount** 是 Mathlib 中的一个定理，位于命名空间
 `Configuration.ProjectivePlane`。
形式化陈述：lineCount_eq_lineCount [Finite P] [Finite L] (p q : P) : lineCount L p = l
ineCount L q
参数：p q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Configuration.ProjectivePlane.exists_config`：∀ {P : Type u_1} {L : Type 
u_2} {inst : Membership P L} [self : Configuration.ProjectivePlane P L],   ∃ p₁ 
p₂ p₃ l₁ l₂ l₃, p₁ ∉ l₂ ∧ p₁ ∉ l₃…
· 使用定理 `Configuration.ProjectivePlane.card_points_eq_card_lines`：card_points_eq_
card_lines [Fintype P] [Fintype L] : Fintype.card P = Fintype.card L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Configuration.HasLines.lineCount_eq_pointCount`：∀ {P : Type u_1} {L : Ty
pe u_2} [inst : Membership P L] [Configuration.HasLines P L] [inst_2 : Fintype P
]   [inst_3 : Fintype L],   Fintype.…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `or_not`：or_not {p : Prop} : p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Configuration.Nondegenerate.eq_or_eq`：∀ {P : Type u_1} {L : Type u_2} {i
nst : Membership P L} [self : Configuration.Nondegenerate P L] {p₁ p₂ : P}   {l₁
 l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l…
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem lineCount_eq_lineCount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q := by
  cases nonempty_fintype P
  cases nonempty_fintype L
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  have h := card_points_eq_card_lines P L
  let n := lineCount L p₂
  have hp₂ : lineCount L p₂ = n := rfl
  have hl₁ : pointCount P l₁ = n := (HasLines.lineCount_eq_pointCount h h₂₁).symm.trans hp₂
  have hp₃ : lineCount L p₃ = n := (HasLines.lineCount_eq_pointCount h h₃₁).trans hl₁
  have hl₃ : pointCount P l₃ = n := (HasLines.lineCount_eq_pointCount h h₃₃).symm.trans hp₃
  have hp₁ : lineCount L p₁ = n := (HasLines.lineCount_eq_pointCount h h₁₃).trans hl₃
  have hl₂ : pointCount P l₂ = n := (HasLines.lineCount_eq_pointCount h h₁₂).symm.trans hp₁
  suffices ∀ p : P, lineCount L p = n by exact (this p).trans (this q).symm
  refine fun p =>
    or_not.elim (fun h₂ => ?_) fun h₂ => (HasLines.lineCount_eq_pointCount h h₂).trans hl₂
  refine or_not.elim (fun h₃ => ?_) fun h₃ => (HasLines.lineCount_eq_pointCount h h₃).trans hl₃
  rw [(eq_or_eq h₂ h₂₂ h₃ h₂₃).resolve_right fun h =>
      h₃₃ ((congr_arg (p₃ ∈ ·) h).mp h₃₂)]

variable (P) {L}
/-
**Configuration.ProjectivePlane.pointCount_eq_pointCount** 是 Mathlib 中的一个定理，位于命名
空间 `Configuration.ProjectivePlane`。
形式化陈述：pointCount_eq_pointCount [Finite P] [Finite L] (l m : L) : pointCount P l 
= pointCount P m
参数：l m : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.ProjectivePlane.lineCount_eq_lineCount`：lineCount_eq_lineC
ount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q
· 使用定理 `Configuration.instFiniteDual`：∀ (P : Type u_1) [Finite P], Finite (Confi
guration.Dual P)
-/
theorem pointCount_eq_pointCount [Finite P] [Finite L] (l m : L) :
    pointCount P l = pointCount P m := by
  apply lineCount_eq_lineCount (Dual P)

variable {P}
/-
**Configuration.ProjectivePlane.lineCount_eq_pointCount** 是 Mathlib 中的一个定理，位于命名空
间 `Configuration.ProjectivePlane`。
形式化陈述：lineCount_eq_pointCount [Finite P] [Finite L] (p : P) (l : L) : lineCount 
L p = pointCount P l
参数：p : P；l : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Configuration.Nondegenerate.exists_point`：∀ {P : Type u_1} {L : Type u_2
} {inst : Membership P L} [self : Configuration.Nondegenerate P L] (l : L), ∃ p,
 p ∉ l
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Configuration.ProjectivePlane.lineCount_eq_lineCount`：lineCount_eq_lineC
ount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Configuration.HasLines.lineCount_eq_pointCount`：∀ {P : Type u_1} {L : Ty
pe u_2} [inst : Membership P L] [Configuration.HasLines P L] [inst_2 : Fintype P
]   [inst_3 : Fintype L],   Fintype.…
· 使用定理 `Configuration.ProjectivePlane.card_points_eq_card_lines`：card_points_eq_
card_lines [Fintype P] [Fintype L] : Fintype.card P = Fintype.card L
-/
theorem lineCount_eq_pointCount [Finite P] [Finite L] (p : P) (l : L) :
    lineCount L p = pointCount P l :=
  Exists.elim (exists_point l) fun q hq =>
    (lineCount_eq_lineCount L p q).trans <| by
      cases nonempty_fintype P
      cases nonempty_fintype L
      exact HasLines.lineCount_eq_pointCount (card_points_eq_card_lines P L) hq

variable (P L)
/-
**Configuration.ProjectivePlane.Dual.order** 是 Mathlib 中的一个定理，位于命名空间 `Configurat
ion.ProjectivePlane.Dual`。
形式化陈述：∀ (P : Type u_1) (L : Type u_2) [inst : Membership P L] [inst_1 : Configur
ation.ProjectivePlane P L] [Finite P]   [Finite L],   Configuration.ProjectivePl
ane.order (Configuration.Dual L) (Configuration.Dual P) =     Configuration.Proj
ectivePlane.order P L
参数：P : Type u_1；L : Type u_2；Configuration.Dual L；Configuration.Dual P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Configuration.ProjectivePlane.exists_config`：∀ {P : Type u_1} {L : Type 
u_2} {inst : Membership P L} [self : Configuration.ProjectivePlane P L],   ∃ p₁ 
p₂ p₃ l₁ l₂ l₃, p₁ ∉ l₂ ∧ p₁ ∉ l₃…
· 使用定理 `Configuration.ProjectivePlane.lineCount_eq_pointCount`：lineCount_eq_poin
tCount [Finite P] [Finite L] (p : P) (l : L) : lineCount L p = pointCount P l
· 使用定理 `Configuration.instFiniteDual`：∀ (P : Type u_1) [Finite P], Finite (Confi
guration.Dual P)
-/
theorem Dual.order [Finite P] [Finite L] : order (Dual L) (Dual P) = order P L :=
  congr_arg (fun n => n - 1) (lineCount_eq_pointCount _ _)

variable {P}
/-
**Configuration.ProjectivePlane.lineCount_eq** 是 Mathlib 中的一个定理，位于命名空间 `Configur
ation.ProjectivePlane`。
形式化陈述：lineCount_eq [Finite P] [Finite L] (p : P) : lineCount L p = order P L + 1
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.ProjectivePlane.exists_config`：∀ {P : Type u_1} {L : Type 
u_2} {inst : Membership P L} [self : Configuration.ProjectivePlane P L],   ∃ p₁ 
p₂ p₃ l₁ l₂ l₃, p₁ ∉ l₂ ∧ p₁ ∉ l₃…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Configuration.ProjectivePlane.order.eq_1`：∀ (P : Type u_1) (L : Type u_2
) [inst : Membership P L] [inst_1 : Configuration.ProjectivePlane P L],   Config
uration.ProjectivePlane.order …
· 使用定理 `Configuration.ProjectivePlane.lineCount_eq_lineCount`：lineCount_eq_lineC
ount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q
· 使用定理 `Configuration.lineCount.eq_1`：∀ {P : Type u_1} (L : Type u_2) [inst : Me
mbership P L] (p : P), Configuration.lineCount L p = Nat.card { l // p ∈ l }
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
-/
theorem lineCount_eq [Finite P] [Finite L] (p : P) : lineCount L p = order P L + 1 := by
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := Classical.choose_spec (@exists_config P L _ _)
  cases nonempty_fintype { l : L // q ∈ l }
  rw [order, lineCount_eq_lineCount L p q, lineCount_eq_lineCount L (Classical.choose _) q,
    lineCount, Nat.card_eq_fintype_card, Nat.sub_add_cancel]
  exact Fintype.card_pos_iff.mpr ⟨⟨l, h⟩⟩

variable (P) {L}
/-
**Configuration.ProjectivePlane.pointCount_eq** 是 Mathlib 中的一个定理，位于命名空间 `Configu
ration.ProjectivePlane`。
形式化陈述：pointCount_eq [Finite P] [Finite L] (l : L) : pointCount P l = order P L +
 1
参数：l : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Configuration.ProjectivePlane.lineCount_eq`：lineCount_eq [Finite P] [Fin
ite L] (p : P) : lineCount L p = order P L + 1
· 使用定理 `Configuration.instFiniteDual`：∀ (P : Type u_1) [Finite P], Finite (Confi
guration.Dual P)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Configuration.ProjectivePlane.Dual.order`：∀ (P : Type u_1) (L : Type u_2
) [inst : Membership P L] [inst_1 : Configuration.ProjectivePlane P L] [Finite P
]   [Finite L],   Configuratio…
-/
theorem pointCount_eq [Finite P] [Finite L] (l : L) : pointCount P l = order P L + 1 :=
  (lineCount_eq (Dual P) _).trans (congr_arg (fun n => n + 1) (Dual.order P L))

variable (L)
/-
**Configuration.ProjectivePlane.one_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `Configur
ation.ProjectivePlane`。
形式化陈述：one_lt_order [Finite P] [Finite L] : 1 < order P L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Configuration.ProjectivePlane.exists_config`：∀ {P : Type u_1} {L : Type 
u_2} {inst : Membership P L} [self : Configuration.ProjectivePlane P L],   ∃ p₁ 
p₂ p₃ l₁ l₂ l₃, p₁ ∉ l₂ ∧ p₁ ∉ l₃…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Configuration.ProjectivePlane.pointCount_eq`：pointCount_eq [Finite P] [F
inite L] (l : L) : pointCount P l = order P L + 1
· 使用定理 `Configuration.pointCount.eq_1`：∀ (P : Type u_1) {L : Type u_2} [inst : M
embership P L] (l : L), Configuration.pointCount P l = Nat.card { p // p ∈ l }
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.two_lt_card_iff`：∀ {α : Type u_1} [inst : Fintype α], 2 < Fintyp
e.card α ↔ ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Configuration.HasPoints.mkPoint_ax`：∀ {P : Type u_1} {L : Type u_2} {ins
t : Membership P L} [self : Configuration.HasPoints P L] {l₁ l₂ : L} (h : l₁ ≠ l
₂),   Configuration.HasP…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem one_lt_order [Finite P] [Finite L] : 1 < order P L := by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  cases nonempty_fintype { p : P // p ∈ l₂ }
  rw [← add_lt_add_iff_right 1, ← pointCount_eq _ l₂, pointCount, Nat.card_eq_fintype_card,
    Fintype.two_lt_card_iff]
  simp_rw [Ne, Subtype.ext_iff]
  have h := mkPoint_ax (P := P) (L := L) fun h => h₂₁ ((congr_arg (p₂ ∈ ·) h).mpr h₂₂)
  exact
    ⟨⟨mkPoint _, h.2⟩, ⟨p₂, h₂₂⟩, ⟨p₃, h₃₂⟩, ne_of_mem_of_not_mem h.1 h₂₁,
      ne_of_mem_of_not_mem h.1 h₃₁, ne_of_mem_of_not_mem h₂₃ h₃₃⟩

variable {P}
/-
**Configuration.ProjectivePlane.two_lt_lineCount** 是 Mathlib 中的一个定理，位于命名空间 `Conf
iguration.ProjectivePlane`。
形式化陈述：two_lt_lineCount [Finite P] [Finite L] (p : P) : 2 < lineCount L p
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Configuration.ProjectivePlane.lineCount_eq`：lineCount_eq [Finite P] [Fin
ite L] (p : P) : lineCount L p = order P L + 1
· 使用定理 `Configuration.ProjectivePlane.one_lt_order`：one_lt_order [Finite P] [Fin
ite L] : 1 < order P L
-/
theorem two_lt_lineCount [Finite P] [Finite L] (p : P) : 2 < lineCount L p := by
  simpa only [lineCount_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L

variable (P) {L}
/-
**Configuration.ProjectivePlane.two_lt_pointCount** 是 Mathlib 中的一个定理，位于命名空间 `Con
figuration.ProjectivePlane`。
形式化陈述：two_lt_pointCount [Finite P] [Finite L] (l : L) : 2 < pointCount P l
参数：l : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Configuration.ProjectivePlane.pointCount_eq`：pointCount_eq [Finite P] [F
inite L] (l : L) : pointCount P l = order P L + 1
· 使用定理 `Configuration.ProjectivePlane.one_lt_order`：one_lt_order [Finite P] [Fin
ite L] : 1 < order P L
-/
theorem two_lt_pointCount [Finite P] [Finite L] (l : L) : 2 < pointCount P l := by
  simpa only [pointCount_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L

variable (L)
/-
**Configuration.ProjectivePlane.card_points** 是 Mathlib 中的一个定理，位于命名空间 `Configura
tion.ProjectivePlane`。
形式化陈述：card_points [Fintype P] [Finite L] : Fintype.card P = order P L ^ 2 + orde
r P L + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Configuration.ProjectivePlane.exists_config`：∀ {P : Type u_1} {L : Type 
u_2} {inst : Membership P L} [self : Configuration.ProjectivePlane P L],   ∃ p₁ 
p₂ p₃ l₁ l₂ l₃, p₁ ∉ l₂ ∧ p₁ ∉ l₃…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Configuration.ProjectivePlane.mkLine_ax`：∀ {P : Type u_1} {L : Type u_2}
 {inst : Membership P L} [self : Configuration.ProjectivePlane P L] {p₁ p₂ : P} 
  (h : p₁ ≠ p₂), p₁ ∈ Configu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Sigma.subtype_ext`：∀ {α : Type u_1} {β : Type u_7} {p : α → β → Prop} {x
₀ x₁ : (a : α) × Subtype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = x₁
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Configuration.Nondegenerate.eq_or_eq`：∀ {P : Type u_1} {L : Type u_2} {i
nst : Membership P L} [self : Configuration.Nondegenerate P L] {p₁ p₂ : P}   {l₁
 l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l…
· 使用定理 `Configuration.HasLines.toNondegenerate`：∀ {P : Type u_1} {L : Type u_2} 
{inst : Membership P L} [self : Configuration.HasLines P L],   Configuration.Non
degenerate P L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_tsub_iff_add_eq_of_le`：eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b 
- c ↔ a + c = b
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fintype.card_subtype_eq`：Fintype.card_subtype_eq (y : α) [Fintype { x //
 x = y }] : Fintype.card { x // x = y } = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `tsub_eq_of_eq_add`：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
· 使用定理 `Configuration.ProjectivePlane.pointCount_eq`：pointCount_eq [Finite P] [F
inite L] (l : L) : pointCount P l = order P L + 1
（共 44 条，此处仅展示前 30 条）
-/
theorem card_points [Fintype P] [Finite L] : Fintype.card P = order P L ^ 2 + order P L + 1 := by
  cases nonempty_fintype L
  obtain ⟨p, -⟩ := @exists_config P L _ _
  let ϕ : { q // q ≠ p } ≃ Σ l : { l : L // p ∈ l }, { q // q ∈ l.1 ∧ q ≠ p } :=
    { toFun := fun q => ⟨⟨mkLine q.2, (mkLine_ax q.2).2⟩, q, (mkLine_ax q.2).1, q.2⟩
      invFun := fun lq => ⟨lq.2, lq.2.2.2⟩
      right_inv := fun lq =>
        Sigma.subtype_ext
          (Subtype.ext
            ((eq_or_eq (mkLine_ax lq.2.2.2).1 (mkLine_ax lq.2.2.2).2 lq.2.2.1 lq.1.2).resolve_left
              lq.2.2.2))
          rfl }
  classical
    have h1 : Fintype.card { q // q ≠ p } + 1 = Fintype.card P := by
      apply (eq_tsub_iff_add_eq_of_le (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨p⟩))).mp
      convert! (Fintype.card_subtype_compl _).trans (congr_arg _ (Fintype.card_subtype_eq p))
    have h2 : ∀ l : { l : L // p ∈ l }, Fintype.card { q // q ∈ l.1 ∧ q ≠ p } = order P L := by
      intro l
      rw [← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ l.val) (· ≠ p)),
        Fintype.card_subtype_compl fun x : Subtype (· ∈ l.val) => x.val = p, ←
        Nat.card_eq_fintype_card]
      refine tsub_eq_of_eq_add ((pointCount_eq P l.1).trans ?_)
      rw [← Fintype.card_subtype_eq (⟨p, l.2⟩ : { q : P // q ∈ l.1 })]
      simp_rw [Subtype.ext_iff]
    simp_rw [← h1, Fintype.card_congr ϕ, Fintype.card_sigma, h2, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← lineCount, lineCount_eq, smul_eq_mul, Nat.succ_mul, sq]
/-
**Configuration.ProjectivePlane.card_lines** 是 Mathlib 中的一个定理，位于命名空间 `Configurat
ion.ProjectivePlane`。
形式化陈述：card_lines [Finite P] [Fintype L] : Fintype.card L = order P L ^ 2 + order
 P L + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Configuration.ProjectivePlane.card_points`：card_points [Fintype P] [Fini
te L] : Fintype.card P = order P L ^ 2 + order P L + 1
· 使用定理 `Configuration.instFiniteDual`：∀ (P : Type u_1) [Finite P], Finite (Confi
guration.Dual P)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Configuration.ProjectivePlane.Dual.order`：∀ (P : Type u_1) (L : Type u_2
) [inst : Membership P L] [inst_1 : Configuration.ProjectivePlane P L] [Finite P
]   [Finite L],   Configuratio…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem card_lines [Finite P] [Fintype L] : Fintype.card L = order P L ^ 2 + order P L + 1 :=
  (card_points (Dual L) (Dual P)).trans (congr_arg (fun n => n ^ 2 + n + 1) (Dual.order P L))

end ProjectivePlane

namespace ofField

variable {K : Type*} [Field K]

open scoped LinearAlgebra.Projectivization

open Matrix Projectivization

/-
**Configuration.ofField.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration.ofField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) :=
  ⟨Function.swap orthogonal⟩
/-
**Configuration.ofField.mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `Configuration.ofField
`。
形式化陈述：mem_iff (v w : ℙ K (Fin 3 -> K)) : v in w ↔ orthogonal v w
参数：v w : ℙ K (Fin 3 -> K)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_iff (v w : ℙ K (Fin 3 → K)) : v ∈ w ↔ orthogonal v w :=
  Iff.rfl

-- This lemma can't be moved to the crossProduct file due to heavy imports
/-
**Configuration.ofField.crossProduct_eq_zero_of_dotProduct_eq_zero** 是 Mathlib 中
的一个引理，位于命名空间 `Configuration.ofField`。
形式化陈述：crossProduct_eq_zero_of_dotProduct_eq_zero {a b c d : Fin 3 -> K} (hac : a
 ⬝ᵥ c = 0) (hbc : b ⬝ᵥ c = 0) (had : a ⬝ᵥ d = 0) (hbd : b ⬝ᵥ d = 0) : crossProdu
ct a b = 0 ∨ crossProduct c d = 0
参数：hac : a ⬝ᵥ c = 0；hbc : b ⬝ᵥ c = 0；had : a ⬝ᵥ d = 0；hbd : b ⬝ᵥ d = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Matrix.rank_add_rank_le_card_of_mul_eq_zero`：rank_add_rank_le_card_of_mu
l_eq_zero [Field R] [Finite l] [Fintype m] {A : Matrix l m R} {B : Matrix m n R}
 (hAB : A * B = 0) : A.rank + B.r…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `LinearIndependent.rank_matrix`：∀ {m : Type um} {n : Type un} {R : Type u
R} [inst : Fintype n] [inst_1 : Field R] [inst_2 : Fintype m]   {M : Matrix m n 
R}, LinearIndepende…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.of_row`：of_row (f : m -> n -> α) : (Matrix.of f).row = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matrix.rank_transpose`：rank_transpose [Field R] [Fintype m] (A : Matrix 
m n R) : Aᵀ.rank = A.rank
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
lemma crossProduct_eq_zero_of_dotProduct_eq_zero {a b c d : Fin 3 → K} (hac : a ⬝ᵥ c = 0)
    (hbc : b ⬝ᵥ c = 0) (had : a ⬝ᵥ d = 0) (hbd : b ⬝ᵥ d = 0) :
    crossProduct a b = 0 ∨ crossProduct c d = 0 := by
  by_contra h
  simp_rw [not_or, ← ne_eq, crossProduct_ne_zero_iff_linearIndependent] at h
  rw [← Matrix.of_row (![a, b]), ← Matrix.of_row (![c, d])] at h
  let A : Matrix (Fin 2) (Fin 3) K := .of ![a, b]
  let B : Matrix (Fin 2) (Fin 3) K := .of ![c, d]
  have hAB : A * B.transpose = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  replace hAB := rank_add_rank_le_card_of_mul_eq_zero hAB
  rw [rank_transpose, h.1.rank_matrix, h.2.rank_matrix, Fintype.card_fin, Fintype.card_fin] at hAB
  contradiction
/-
**Configuration.ofField.eq_or_eq_of_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Config
uration.ofField`。
形式化陈述：eq_or_eq_of_orthogonal {a b c d : ℙ K (Fin 3 -> K)} (hac : a.orthogonal c)
 (hbc : b.orthogonal c) (had : a.orthogonal d) (hbd : b.orthogonal d) : a = b ∨ 
c = d
参数：Fin 3 -> K；hac : a.orthogonal c；hbc : b.orthogonal c；had : a.orthogonal d；hbd
 : b.orthogonal d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`：mk_eq_mk_iff_crossPr
oduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) : mk F v hv = mk F 
w hw ↔ crossProduct v w = 0
· 使用引理 `Configuration.ofField.crossProduct_eq_zero_of_dotProduct_eq_zero`：crossP
roduct_eq_zero_of_dotProduct_eq_zero {a b c d : Fin 3 -> K} (hac : a ⬝ᵥ c = 0) (
hbc : b ⬝ᵥ c = 0) (had : a ⬝ᵥ d = 0) (hbd : b ⬝ᵥ d = 0…
-/
lemma eq_or_eq_of_orthogonal {a b c d : ℙ K (Fin 3 → K)} (hac : a.orthogonal c)
    (hbc : b.orthogonal c) (had : a.orthogonal d) (hbd : b.orthogonal d) :
    a = b ∨ c = d := by
  induction a with | h a ha =>
  induction b with | h b hb =>
  induction c with | h c hc =>
  induction d with | h d hd =>
  rw [mk_eq_mk_iff_crossProduct_eq_zero, mk_eq_mk_iff_crossProduct_eq_zero]
  exact crossProduct_eq_zero_of_dotProduct_eq_zero hac hbc had hbd
/-
**Configuration.ofField.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration.ofField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nondegenerate (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) :=
  { exists_point := exists_not_orthogonal_self
    exists_line := exists_not_self_orthogonal
    eq_or_eq := eq_or_eq_of_orthogonal }
/-
**Configuration.ofField.** 是 Mathlib 中的一个实例，位于命名空间 `Configuration.ofField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [DecidableEq K] : ProjectivePlane (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) :=
  { mkPoint := by
      intro v w _
      exact cross v w
    mkPoint_ax := fun h ↦ ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩
    mkLine := by
      intro v w _
      exact cross v w
    mkLine_ax := fun h ↦ ⟨orthogonal_cross_left h, orthogonal_cross_right h⟩
    exists_config := by
      refine ⟨mk K ![0, 1, 1] ?_, mk K ![1, 0, 0] ?_, mk K ![1, 0, 1] ?_, mk K ![1, 0, 0] ?_,
        mk K ![0, 1, 0] ?_, mk K ![0, 0, 1] ?_, ?_⟩ <;> simp [mem_iff, orthogonal_mk] }

end ofField

end Configuration

