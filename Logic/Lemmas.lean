/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto

/-!
# More basic logic properties

A few more logic lemmas. These are in their own file, rather than `Logic.Basic`, because it is
convenient to be able to use the `tauto` or `split_ifs` tactics.

## Implementation notes
We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/

public section

/--
theorem `iff_assoc` / 定理 `iff_assoc`

English:
theorem iff_assoc
  given: {a b c : Prop}
  statement: ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c))
  proof: by tauto

中文:
定理 iff_assoc
  条件: {a b c : 命题}
  结论: ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c))
  证明: by tauto
-/
theorem iff_assoc {a b c : Prop} : ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c)) := by tauto
/--
theorem `iff_left_comm` / 定理 `iff_left_comm`

English:
theorem iff_left_comm
  given: {a b c : Prop}
  statement: (a ↔ (b ↔ c)) ↔ (b ↔ (a ↔ c))
  proof: by tauto

中文:
定理 iff_left_comm
  条件: {a b c : 命题}
  结论: (a ↔ (b ↔ c)) ↔ (b ↔ (a ↔ c))
  证明: by tauto
-/
theorem iff_left_comm {a b c : Prop} : (a ↔ (b ↔ c)) ↔ (b ↔ (a ↔ c)) := by tauto
/--
theorem `iff_right_comm` / 定理 `iff_right_comm`

English:
theorem iff_right_comm
  given: {a b c : Prop}
  statement: ((a ↔ b) ↔ c) ↔ ((a ↔ c) ↔ b)
  proof: by tauto

protected alias ⟨HEq.eq, Eq.heq⟩ := heq_iff_eq

中文:
定理 iff_right_comm
  条件: {a b c : 命题}
  结论: ((a ↔ b) ↔ c) ↔ ((a ↔ c) ↔ b)
  证明: by tauto

protected alias ⟨HEq.eq, Eq.heq⟩ := heq_iff_eq
-/
theorem iff_right_comm {a b c : Prop} : ((a ↔ b) ↔ c) ↔ ((a ↔ c) ↔ b) := by tauto

protected alias ⟨HEq.eq, Eq.heq⟩ := heq_iff_eq

variable {α : Sort*} {p q : Prop} [Decidable p] [Decidable q] {a b c : α}

/--
theorem `dite_dite_distrib_left` / 定理 `dite_dite_distrib_left`

English:
theorem dite_dite_distrib_left
  given: {a : p -> α} {b : ¬p -> q -> α} {c : ¬p -> ¬q -> α}
  proof: by
  split_ifs <;> rfl

中文:
定理 dite_dite_distrib_left
  条件: {a : p -> α} {b : ¬p -> q -> α} {c : ¬p -> ¬q -> α}
  证明: by
  split_ifs <;> rfl

Depends on / 依赖: split_ifs
-/
theorem dite_dite_distrib_left {a : p -> α} {b : ¬p -> q -> α} {c : ¬p -> ¬q -> α} :
    (dite p a fun hp => dite q (b hp) (c hp)) =
      dite q (fun hq => (dite p a) fun hp => b hp hq) fun hq => (dite p a) fun hp => c hp hq := by
  split_ifs <;> rfl

/--
theorem `dite_dite_distrib_right` / 定理 `dite_dite_distrib_right`

English:
theorem dite_dite_distrib_right
  given: {a : p -> q -> α} {b : p -> ¬q -> α} {c : ¬p -> α}
  proof: by
  split_ifs <;> rfl

中文:
定理 dite_dite_distrib_right
  条件: {a : p -> q -> α} {b : p -> ¬q -> α} {c : ¬p -> α}
  证明: by
  split_ifs <;> rfl

Depends on / 依赖: split_ifs
-/
theorem dite_dite_distrib_right {a : p -> q -> α} {b : p -> ¬q -> α} {c : ¬p -> α} :
    dite p (fun hp => dite q (a hp) (b hp)) c =
      dite q (fun hq => dite p (fun hp => a hp hq) c) fun hq => dite p (fun hp => b hp hq) c := by
  split_ifs <;> rfl

/--
theorem `ite_dite_distrib_left` / 定理 `ite_dite_distrib_left`

English:
theorem ite_dite_distrib_left
  given: {a : α} {b : q -> α} {c : ¬q -> α}
  proof: dite_dite_distrib_left

中文:
定理 ite_dite_distrib_left
  条件: {a : α} {b : q -> α} {c : ¬q -> α}
  证明: dite_dite_distrib_left

Depends on / 依赖: dite_dite_distrib_left
-/
theorem ite_dite_distrib_left {a : α} {b : q -> α} {c : ¬q -> α} :
ite p a (dite q b c) = dite q (fun hq => ite p a <| b hq) fun hq => ite p a c hq :=
  dite_dite_distrib_left

/--
theorem `ite_dite_distrib_right` / 定理 `ite_dite_distrib_right`

English:
theorem ite_dite_distrib_right
  given: {a : q -> α} {b : ¬q -> α} {c : α}
  proof: dite_dite_distrib_right

中文:
定理 ite_dite_distrib_right
  条件: {a : q -> α} {b : ¬q -> α} {c : α}
  证明: dite_dite_distrib_right

Depends on / 依赖: dite_dite_distrib_right
-/
theorem ite_dite_distrib_right {a : q -> α} {b : ¬q -> α} {c : α} :
    ite p (dite q a b) c = dite q (fun hq => ite p (a hq) c) fun hq => ite p (b hq) c :=
  dite_dite_distrib_right

/--
theorem `dite_ite_distrib_left` / 定理 `dite_ite_distrib_left`

English:
theorem dite_ite_distrib_left
  given: {a : p -> α} {b : ¬p -> α} {c : ¬p -> α}
  proof: dite_dite_distrib_left

中文:
定理 dite_ite_distrib_left
  条件: {a : p -> α} {b : ¬p -> α} {c : ¬p -> α}
  证明: dite_dite_distrib_left

Depends on / 依赖: dite_dite_distrib_left
-/
theorem dite_ite_distrib_left {a : p -> α} {b : ¬p -> α} {c : ¬p -> α} :
    (dite p a fun hp => ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
  dite_dite_distrib_left

/--
theorem `dite_ite_distrib_right` / 定理 `dite_ite_distrib_right`

English:
theorem dite_ite_distrib_right
  given: {a : p -> α} {b : p -> α} {c : ¬p -> α}
  proof: dite_dite_distrib_right

中文:
定理 dite_ite_distrib_right
  条件: {a : p -> α} {b : p -> α} {c : ¬p -> α}
  证明: dite_dite_distrib_right

Depends on / 依赖: dite_dite_distrib_right
-/
theorem dite_ite_distrib_right {a : p -> α} {b : p -> α} {c : ¬p -> α} :
    dite p (fun hp => ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
  dite_dite_distrib_right

/--
theorem `ite_ite_distrib_left` / 定理 `ite_ite_distrib_left`

English:
theorem ite_ite_distrib_left
  statement: ite p a (ite q b c) = ite q (ite p a b) (ite p a c)
  proof: dite_dite_distrib_left

中文:
定理 ite_ite_distrib_left
  结论: ite p a (ite q b c) = ite q (ite p a b) (ite p a c)
  证明: dite_dite_distrib_left

Depends on / 依赖: dite_dite_distrib_left
-/
theorem ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
  dite_dite_distrib_left

/--
theorem `ite_ite_distrib_right` / 定理 `ite_ite_distrib_right`

English:
theorem ite_ite_distrib_right
  statement: ite p (ite q a b) c = ite q (ite p a c) (ite p b c)
  proof: dite_dite_distrib_right

中文:
定理 ite_ite_distrib_right
  结论: ite p (ite q a b) c = ite q (ite p a c) (ite p b c)
  证明: dite_dite_distrib_right

Depends on / 依赖: dite_dite_distrib_right
-/
theorem ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
  dite_dite_distrib_right

/--
lemma `Prop.forall` / 引理 `Prop.forall`

English:
lemma Prop.forall
  given: {f : Prop -> Prop}
  statement: (forall p, f p) ↔ f True ∧ f False
  proof: ⟨fun h => ⟨h _, h _⟩, by rintro ⟨h₁, h₀⟩ p; by_cases hp : p <;> simp only [hp] <;> assumption⟩

中文:
引理 命题.对任意
  条件: {f : 命题 -> 命题}
  结论: (对任意 p, f p) ↔ f 真 ∧ f 假
  证明: ⟨fun h => ⟨h _, h _⟩, by rintro ⟨h₁, h₀⟩ p; by_cases hp : p <;> simp only [hp] <;> assumption⟩
-/
lemma Prop.forall {f : Prop -> Prop} : (forall p, f p) ↔ f True ∧ f False :=
  ⟨fun h => ⟨h _, h _⟩, by rintro ⟨h₁, h₀⟩ p; by_cases hp : p <;> simp only [hp] <;> assumption⟩

/--
lemma `Prop.exists` / 引理 `Prop.exists`

English:
lemma Prop.exists
  given: {f : Prop -> Prop}
  statement: (exists p, f p) ↔ f True ∨ f False
  proof: ⟨fun ⟨p, h⟩ => by refine (em p).imp ?_ ?_ <;> intro H <;> convert! h <;> simp [H],
    by rintro (h | h) <;> exact ⟨_, h⟩⟩

中文:
引理 命题.存在
  条件: {f : 命题 -> 命题}
  结论: (存在 p, f p) ↔ f 真 ∨ f 假
  证明: ⟨fun ⟨p, h⟩ => by refine (em p).imp ?_ ?_ <;> intro H <;> convert! h <;> simp [H],
    by rintro (h | h) <;> exact ⟨_, h⟩⟩

Depends on / 依赖: convert
-/
lemma Prop.exists {f : Prop -> Prop} : (exists p, f p) ↔ f True ∨ f False :=
  ⟨fun ⟨p, h⟩ => by refine (em p).imp ?_ ?_ <;> intro H <;> convert! h <;> simp [H],
    by rintro (h | h) <;> exact ⟨_, h⟩⟩
