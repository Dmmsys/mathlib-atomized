/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Sublists
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The maximal reduction of a word in a free group

## Main declarations

* `FreeGroup.reduce`: the maximal reduction of a word in a free group
* `FreeGroup.norm`: the length of the maximal reduction of a word in a free group

-/

@[expose] public section


namespace FreeGroup

variable {α : Type*}
variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

section Reduce

variable [DecidableEq α]

/-- The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
@[to_additive
/-- The maximal reduction of a word. It is computable iff `α` has decidable equality. -/]
/-
**FreeGroup.reduce** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：reduce : (L : List (α × Bool)) -> List (α × Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def reduce : (L : List (α × Bool)) → List (α × Bool) :=
  List.rec [] fun hd1 _tl1 ih =>
    List.casesOn ih [hd1] fun hd2 tl2 =>
      if hd1.1 = hd2.1 ∧ hd1.2 = not hd2.2 then tl2 else hd1 :: hd2 :: tl2
/-
**FreeGroup.reduce_nil** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α], FreeGroup.reduce [] = []
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma reduce_nil : reduce ([] : List (α × Bool)) = [] := rfl
/-
**FreeGroup.reduce_singleton** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : α × Bool), FreeGroup.reduce [
s] = [s]
参数：s : α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma reduce_singleton (s : α × Bool) : reduce [s] = [s] := rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.reduce.cons** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L : List (α × Bool)} [inst : DecidableEq α] (x : α × Boo
l),   FreeGroup.reduce (x :: L) =     List.casesOn (FreeGroup.reduce L) [x] fun 
hd tl => if x.1 = hd.1 ∧ x.2 = !hd.2 then tl else x :: hd :: tl
参数：α × Bool；x : α × Bool；x :: L；FreeGroup.reduce L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reduce.cons (x) :
    reduce (x :: L) =
      List.casesOn (reduce L) [x] fun hd tl =>
        if x.1 = hd.1 ∧ x.2 = not hd.2 then tl else x :: hd :: tl :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.reduce_replicate** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：reduce_replicate (n : Nat) (x : α × Bool) : reduce (.replicate n x) = .rep
licate n x
参数：n : Nat；x : α × Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.replicate_succ`：∀ {α : Type u} {a : α} {n : ℕ}, List.replicate (n +
 1) a = a :: List.replicate n a
· 使用定理 `FreeGroup.reduce.cons`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : De
cidableEq α] (x : α × Bool),   FreeGroup.reduce (x :: L) =     List.casesOn (Fre
eGroup.redu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem reduce_replicate (n : ℕ) (x : α × Bool) :
    reduce (.replicate n x) = .replicate n x := by
  induction n with
  | zero => simp [reduce]
  | succ n ih =>
    rw [List.replicate_succ, reduce.cons, ih]
    cases n with
    | zero => simp
    | succ n => simp [List.replicate_succ]

/-- The first theorem that characterises the function `reduce`: a word reduces to its maximal
  reduction. -/
@[to_additive /-- The first theorem that characterises the function `reduce`: a word reduces to its
  maximal reduction. -/]
/-
**FreeGroup.reduce.red** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L : List (α × Bool)} [inst : DecidableEq α], FreeGroup.R
ed L (FreeGroup.reduce L)
参数：α × Bool；FreeGroup.reduce L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.cons_cons`：cons_cons {p} : Red L₁ L₂ -> Red (p :: L₁) (p :
: L₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `FreeGroup.Red.trans`：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)}, FreeGr
oup.Red L₁ L₂ → FreeGroup.Red L₂ L₃ → FreeGroup.Red L₁ L₃
· 使用定理 `FreeGroup.Red.Step.to_red`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.Red.Step L₁ L₂ → FreeGroup.Red L₁ L₂
· 使用定理 `FreeGroup.Red.Step.cons_not_rev`：∀ {α : Type u} {L : List (α × Bool)} {x
 : α} {b : Bool}, FreeGroup.Red.Step ((x, !b) :: (x, b) :: L) L
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem reduce.red : Red L (reduce L) := by
  induction L with
  | nil => constructor
  | cons hd1 tl1 ih =>
    dsimp
    revert ih
    generalize htl : reduce tl1 = TL
    intro ih
    cases TL with
    | nil => exact Red.cons_cons ih
    | cons hd2 tl2 =>
      dsimp only
      split_ifs with h
      · cases hd1
        cases hd2
        cases h
        dsimp at *
        subst_vars
        apply Red.trans (Red.cons_cons ih)
        exact Red.Step.cons_not_rev.to_red
      · exact Red.cons_cons ih

@[to_additive]
/-
**FreeGroup.reduce.not** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {p : Prop} {L₁ L₂ L₃ : List (α × B
ool)} {x : α} {b : Bool},   FreeGroup.reduce L₁ = L₂ ++ (x, b) :: (x, !b) :: L₃ 
→ p
参数：α × Bool；x, b。
该定理/引理表达了一个蕴含关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reduce.not {p : Prop} :
    ∀ {L₁ L₂ L₃ : List (α × Bool)} {x b}, reduce L₁ = L₂ ++ (x, b) :: (x, !b) :: L₃ → p
  | [], L2, L3, _, _ => fun h => by cases L2 <;> injections
  | (x, b) :: L1, L2, L3, x', b' => by
    dsimp
    cases r : reduce L1 with
    | nil =>
      dsimp; intro h
      exfalso
      have := congr_arg List.length h
      grind
    | cons hd tail =>
      obtain ⟨y, c⟩ := hd
      dsimp only
      split_ifs with h <;> intro H
      · rw [H] at r
        exact @reduce.not _ L1 ((y, c) :: L2) L3 x' b' r
      rcases L2 with (_ | ⟨a, L2⟩)
      · injections; subst_vars
        simp at h
      · refine @reduce.not _ L1 L2 L3 x' b' ?_
        rw [List.cons_append] at H
        injection H with _ H
        rw [r, H]

/-- The second theorem that characterises the function `reduce`: the maximal reduction of a word
only reduces to itself. -/
@[to_additive /-- The second theorem that characterises the function `reduce`: the maximal
  reduction of a word only reduces to itself. -/]
/-
**FreeGroup.reduce.min** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.Red (FreeGroup.reduce L₁) L₂ → FreeGroup.reduce L₁ = L₂
参数：α × Bool；FreeGroup.reduce L₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.not`：∀ {α : Type u_1} [inst : DecidableEq α] {p : Prop}
 {L₁ L₂ L₃ : List (α × Bool)} {x : α} {b : Bool},   FreeGroup.reduce L₁ = L₂ ++ 
(x, b) :: …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reduce.min (H : Red (reduce L₁) L₂) : reduce L₁ = L₂ := by
  induction H with
  | refl => rfl
  | tail _ H1 H2 =>
    obtain ⟨L4, L5, x, b⟩ := H1
    exact reduce.not H2

/-- `reduce` is idempotent, i.e. the maximal reduction of the maximal reduction of a word is the
  maximal reduction of the word. -/
@[to_additive (attr := simp) /-- `reduce` is idempotent, i.e. the maximal reduction of the maximal
  reduction of a word is the maximal reduction of the word. -/]
/-
**FreeGroup.reduce.idem** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L : List (α × Bool)} [inst : DecidableEq α],   FreeGroup
.reduce (FreeGroup.reduce L) = FreeGroup.reduce L
参数：α × Bool；FreeGroup.reduce L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.reduce.min`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst :
 DecidableEq α],   FreeGroup.Red (FreeGroup.reduce L₁) L₂ → FreeGroup.reduce L₁ 
= L₂
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
-/
theorem reduce.idem : reduce (reduce L) = reduce L :=
  Eq.symm <| reduce.min reduce.red

@[to_additive]
/-
**FreeGroup.reduce.Step.eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce.Step`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.Red.Step L₁ L₂ → FreeGroup.reduce L₁ = FreeGroup.reduce L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.church_rosser`：church_rosser : Red L₁ L₂ -> Red L₁ L₃ -> J
oin Red L₂ L₃
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FreeGroup.reduce.min`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst :
 DecidableEq α],   FreeGroup.Red (FreeGroup.reduce L₁) L₂ → FreeGroup.reduce L₁ 
= L₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reduce.Step.eq (H : Red.Step L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (reduce.red.head H)
  (reduce.min HR13).trans (reduce.min HR23).symm

/-- If a word reduces to another word, then they have a common maximal reduction. -/
@[to_additive /-- If a word reduces to another word, then they have a common maximal reduction. -/]
/-
**FreeGroup.reduce.eq_of_red** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.Red L₁ L₂ → FreeGroup.reduce L₁ = FreeGroup.reduce L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.church_rosser`：church_rosser : Red L₁ L₂ -> Red L₁ L₃ -> J
oin Red L₂ L₃
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
· 使用定理 `FreeGroup.Red.trans`：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)}, FreeGr
oup.Red L₁ L₂ → FreeGroup.Red L₂ L₃ → FreeGroup.Red L₁ L₃
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FreeGroup.reduce.min`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst :
 DecidableEq α],   FreeGroup.Red (FreeGroup.reduce L₁) L₂ → FreeGroup.reduce L₁ 
= L₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a word reduces to another word, then they have a common maximal reduction.
-/
theorem reduce.eq_of_red (H : Red L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (Red.trans H reduce.red)
  (reduce.min HR13).trans (reduce.min HR23).symm

alias red.reduce_eq := reduce.eq_of_red

alias freeAddGroup.red.reduce_eq := FreeAddGroup.reduce.eq_of_red

@[to_additive]
/-
**FreeGroup.Red.reduce_right** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.Red L₁ L₂ → FreeGroup.Red L₁ (FreeGroup.reduce L₂)
参数：α × Bool；FreeGroup.reduce L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
· 使用定理 `FreeGroup.reduce.eq_of_red`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [
inst : DecidableEq α],   FreeGroup.Red L₁ L₂ → FreeGroup.reduce L₁ = FreeGroup.r
educe L₂
-/
theorem Red.reduce_right (h : Red L₁ L₂) : Red L₁ (reduce L₂) :=
  reduce.eq_of_red h ▸ reduce.red

@[to_additive]
/-
**FreeGroup.Red.reduce_left** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.Red L₁ L₂ → FreeGroup.Red L₂ (FreeGroup.reduce L₁)
参数：α × Bool；FreeGroup.reduce L₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.reduce.eq_of_red`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [
inst : DecidableEq α],   FreeGroup.Red L₁ L₂ → FreeGroup.reduce L₁ = FreeGroup.r
educe L₂
-/
theorem Red.reduce_left (h : Red L₁ L₂) : Red L₂ (reduce L₁) :=
  (reduce.eq_of_red h).symm ▸ reduce.red

/-- If two words correspond to the same element in the free group, then they
have a common maximal reduction. This is the proof that the function that sends
an element of the free group to its maximal reduction is well-defined. -/
@[to_additive /-- If two words correspond to the same element in the additive free group, then they
  have a common maximal reduction. This is the proof that the function that sends an element of the
  free group to its maximal reduction is well-defined. -/]
/-
**FreeGroup.reduce.sound** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.mk L₁ = FreeGroup.mk L₂ → FreeGroup.reduce L₁ = FreeGroup.reduce L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FreeGroup.Red.exact`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup
.mk L₁ = FreeGroup.mk L₂ ↔ Relation.Join FreeGroup.Red L₁ L₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FreeGroup.reduce.eq_of_red`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [
inst : DecidableEq α],   FreeGroup.Red L₁ L₂ → FreeGroup.reduce L₁ = FreeGroup.r
educe L₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, H13, H23⟩ := Red.exact.1 H
  (reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

/-- If two words have a common maximal reduction, then they correspond to the same element in the
  free group. -/
@[to_additive /-- If two words have a common maximal reduction, then they correspond to the same
  element in the additive free group. -/]
/-
**FreeGroup.reduce.exact** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.reduce L₁ = FreeGroup.reduce L₂ → FreeGroup.mk L₁ = FreeGroup.mk L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FreeGroup.Red.exact`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup
.mk L₁ = FreeGroup.mk L₂ ↔ Relation.Join FreeGroup.Red L₁ L₂
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
-/
theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
  Red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

/-- A word and its maximal reduction correspond to the same element of the free group. -/
@[to_additive /-- A word and its maximal reduction correspond to the same element of the additive
  free group. -/]
/-
**FreeGroup.reduce.self** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L : List (α × Bool)} [inst : DecidableEq α], FreeGroup.m
k (FreeGroup.reduce L) = FreeGroup.mk L
参数：α × Bool；FreeGroup.reduce L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.exact`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst
 : DecidableEq α],   FreeGroup.reduce L₁ = FreeGroup.reduce L₂ → FreeGroup.mk L₁
 = FreeGroup…
· 使用定理 `FreeGroup.reduce.idem`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : De
cidableEq α],   FreeGroup.reduce (FreeGroup.reduce L) = FreeGroup.reduce L
-/
theorem reduce.self : mk (reduce L) = mk L :=
  reduce.exact reduce.idem

/-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`, then `w₂` reduces to the maximal reduction
  of `w₁`. -/
@[to_additive /-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`, then `w₂` reduces to the
  maximal reduction of `w₁`. -/]
/-
**FreeGroup.reduce.rev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduce`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   FreeG
roup.Red L₁ L₂ → FreeGroup.Red L₂ (FreeGroup.reduce L₁)
参数：α × Bool；FreeGroup.reduce L₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.reduce.eq_of_red`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [
inst : DecidableEq α],   FreeGroup.Red L₁ L₂ → FreeGroup.reduce L₁ = FreeGroup.r
educe L₂
-/
theorem reduce.rev (H : Red L₁ L₂) : Red L₂ (reduce L₁) :=
  (reduce.eq_of_red H).symm ▸ reduce.red

/-- The function that sends an element of the free group to its maximal reduction. -/
@[to_additive /-- The function that sends an element of the additive free group to its maximal
  reduction. -/]
/-
**FreeGroup.toWord** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：toWord : FreeGroup α -> List (α × Bool)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.Step.eq`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [in
st : DecidableEq α],   FreeGroup.Red.Step L₁ L₂ → FreeGroup.reduce L₁ = FreeGrou
p.reduce L₂
-/
def toWord : FreeGroup α → List (α × Bool) :=
  Quot.lift reduce fun _L₁ _L₂ H => reduce.Step.eq H

@[to_additive]
/-
**FreeGroup.mk_toWord** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：mk_toWord : forall {x : FreeGroup α}, mk (toWord x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.self`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : De
cidableEq α], FreeGroup.mk (FreeGroup.reduce L) = FreeGroup.mk L
-/
theorem mk_toWord : ∀ {x : FreeGroup α}, mk (toWord x) = x := by rintro ⟨L⟩; exact reduce.self

@[to_additive]
/-
**FreeGroup.toWord_injective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_injective : Function.Injective (toWord : FreeGroup α -> List (α × B
ool))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.exact`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst
 : DecidableEq α],   FreeGroup.reduce L₁ = FreeGroup.reduce L₂ → FreeGroup.mk L₁
 = FreeGroup…
-/
theorem toWord_injective : Function.Injective (toWord : FreeGroup α → List (α × Bool)) := by
  rintro ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_inj** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_inj {x y : FreeGroup α} : toWord x = toWord y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `FreeGroup.toWord_injective`：toWord_injective : Function.Injective (toWor
d : FreeGroup α -> List (α × Bool))
-/
theorem toWord_inj {x y : FreeGroup α} : toWord x = toWord y ↔ x = y :=
  toWord_injective.eq_iff

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_mk : (mk L₁).toWord = reduce L₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toWord_mk : (mk L₁).toWord = reduce L₁ :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_of (a : α) : (of a).toWord = [(a, true)]
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toWord_of (a : α) : (of a).toWord = [(a, true)] :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.reduce_toWord** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：reduce_toWord : forall x : FreeGroup α, reduce (toWord x) = toWord x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.idem`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : De
cidableEq α],   FreeGroup.reduce (FreeGroup.reduce L) = FreeGroup.reduce L
-/
theorem reduce_toWord : ∀ x : FreeGroup α, reduce (toWord x) = toWord x := by
  rintro ⟨L⟩
  exact reduce.idem

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_one : (1 : FreeGroup α).toWord = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toWord_one : (1 : FreeGroup α).toWord = [] :=
  rfl

@[to_additive]
/-
**FreeGroup.toWord_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_mul (x y : FreeGroup α) : toWord (x * y) = reduce (toWord x ++ toWo
rd y)
参数：x y : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.mk_toWord`：mk_toWord : forall {x : FreeGroup α}, mk (toWord x)
 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FreeGroup.reduce_toWord`：reduce_toWord : forall x : FreeGroup α, reduce 
(toWord x) = toWord x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toWord_mul (x y : FreeGroup α) : toWord (x * y) = reduce (toWord x ++ toWord y) := by
  rw [← mk_toWord (x := x), ← mk_toWord (x := y)]
  simp

@[to_additive]
/-
**FreeGroup.toWord_pow** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_pow (x : FreeGroup α) (n : Nat) : toWord (x ^ n) = reduce (List.rep
licate n x.toWord).flatten
参数：x : FreeGroup α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.mk_toWord`：mk_toWord : forall {x : FreeGroup α}, mk (toWord x)
 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FreeGroup.pow_mk`：pow_mk (n : Nat) : mk L ^ n = mk (List.flatten <| List
.replicate n L)
· 使用定理 `FreeGroup.reduce_toWord`：reduce_toWord : forall x : FreeGroup α, reduce 
(toWord x) = toWord x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toWord_pow (x : FreeGroup α) (n : ℕ) :
    toWord (x ^ n) = reduce (List.replicate n x.toWord).flatten := by
  rw [← mk_toWord (x := x)]
  simp

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_of_pow** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_of_pow (a : α) (n : Nat) : (of a ^ n).toWord = List.replicate n (a,
 true)
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.of.eq_1`：∀ {α : Type u} (x : α), FreeGroup.of x = FreeGroup.mk
 [(x, true)]
· 使用定理 `FreeGroup.pow_mk`：pow_mk (n : Nat) : mk L ^ n = mk (List.flatten <| List
.replicate n L)
· 使用定理 `List.flatten_replicate_singleton`：∀ {n : ℕ} {α : Type u_1} {a : α}, (Lis
t.replicate n [a]).flatten = List.replicate n a
· 使用定理 `FreeGroup.reduce.Step.eq`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [in
st : DecidableEq α],   FreeGroup.Red.Step L₁ L₂ → FreeGroup.reduce L₁ = FreeGrou
p.reduce L₂
· 使用定理 `FreeGroup.toWord.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α], FreeGrou
p.toWord = Quot.lift FreeGroup.reduce ⋯
· 使用定理 `FreeGroup.reduce_replicate`：reduce_replicate (n : Nat) (x : α × Bool) : 
reduce (.replicate n x) = .replicate n x
-/
theorem toWord_of_pow (a : α) (n : ℕ) : (of a ^ n).toWord = List.replicate n (a, true) := by
  rw [of, pow_mk, List.flatten_replicate_singleton, toWord]
  exact reduce_replicate _ _

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_eq_nil_iff {x : FreeGroup α} : x.toWord = [] ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `FreeGroup.toWord_injective`：toWord_injective : Function.Injective (toWor
d : FreeGroup α -> List (α × Bool))
· 使用定理 `FreeGroup.toWord_one`：toWord_one : (1 : FreeGroup α).toWord = []
-/
theorem toWord_eq_nil_iff {x : FreeGroup α} : x.toWord = [] ↔ x = 1 :=
  toWord_injective.eq_iff' toWord_one

@[to_additive]
/-
**FreeGroup.reduce_invRev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：reduce_invRev {w : List (α × Bool)} : reduce (invRev w) = invRev (reduce w
)
参数：α × Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.reduce.min`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst :
 DecidableEq α],   FreeGroup.Red (FreeGroup.reduce L₁) L₂ → FreeGroup.reduce L₁ 
= L₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.red_invRev_iff`：red_invRev_iff : Red (invRev L₁) (invRev L₂) ↔
 Red L₁ L₂
· 使用定理 `FreeGroup.invRev_invRev`：invRev_invRev : invRev (invRev L₁) = L₁
· 使用定理 `FreeGroup.Red.reduce_left`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [i
nst : DecidableEq α],   FreeGroup.Red L₁ L₂ → FreeGroup.Red L₂ (FreeGroup.reduce
 L₁)
· 使用定理 `FreeGroup.Red.invRev`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   FreeGr
oup.Red L₁ L₂ → FreeGroup.Red (FreeGroup.invRev L₁) (FreeGroup.invRev L₂)
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
-/
theorem reduce_invRev {w : List (α × Bool)} : reduce (invRev w) = invRev (reduce w) := by
  apply reduce.min
  rw [← red_invRev_iff, invRev_invRev]
  apply Red.reduce_left
  have : Red (invRev (invRev w)) (invRev (reduce (invRev w))) := reduce.red.invRev
  rwa [invRev_invRev] at this

@[to_additive (attr := simp)]
/-
**FreeGroup.toWord_inv** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_inv (x : FreeGroup α) : x⁻¹.toWord = invRev x.toWord
参数：x : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.quot_mk_eq_mk`：quot_mk_eq_mk : Quot.mk Red.Step L = mk L
· 使用定理 `FreeGroup.inv_mk`：inv_mk : (mk L)⁻¹ = mk (invRev L)
· 使用定理 `FreeGroup.toWord_mk`：toWord_mk : (mk L₁).toWord = reduce L₁
· 使用定理 `FreeGroup.reduce_invRev`：reduce_invRev {w : List (α × Bool)} : reduce (i
nvRev w) = invRev (reduce w)
-/
theorem toWord_inv (x : FreeGroup α) : x⁻¹.toWord = invRev x.toWord := by
  rcases x with ⟨L⟩
  rw [quot_mk_eq_mk, inv_mk, toWord_mk, toWord_mk, reduce_invRev]

@[to_additive]
/-
**FreeGroup.reduce_append_reduce_reduce** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：reduce_append_reduce_reduce : reduce (reduce L₁ ++ reduce L₂) = reduce (L₁
 ++ L₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.toWord_mk`：toWord_mk : (mk L₁).toWord = reduce L₁
· 使用定理 `FreeGroup.mul_mk`：mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂)
· 使用定理 `FreeGroup.toWord_mul`：toWord_mul (x y : FreeGroup α) : toWord (x * y) = 
reduce (toWord x ++ toWord y)
-/
theorem reduce_append_reduce_reduce : reduce (reduce L₁ ++ reduce L₂) = reduce (L₁ ++ L₂) := by
  rw [← toWord_mk (L₁ := L₁ ++ L₂), ← mul_mk, toWord_mul, toWord_mk, toWord_mk]

@[to_additive]
/-
**FreeGroup.reduce_cons_reduce** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：reduce_cons_reduce (a : α × Bool) : reduce (a :: reduce L) = reduce (a :: 
L)
参数：a : α × Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.reduce.idem`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : De
cidableEq α],   FreeGroup.reduce (FreeGroup.reduce L) = FreeGroup.reduce L
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reduce_cons_reduce (a : α × Bool) : reduce (a :: reduce L) = reduce (a :: L) := by
  simp

@[to_additive]
/-
**FreeGroup.reduce_invRev_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：reduce_invRev_left_cancel : reduce (invRev L ++ L) = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reduce_invRev_left_cancel : reduce (invRev L ++ L) = [] := by
  simp [← toWord_mk, ← mul_mk, ← inv_mk]

open List -- for <+ notation

@[to_additive]
/-
**FreeGroup.toWord_mul_sublist** 是 Mathlib 中的一个引理，位于命名空间 `FreeGroup`。
形式化陈述：toWord_mul_sublist (x y : FreeGroup α) : (x * y).toWord <+ x.toWord ++ y.t
oWord
参数：x y : FreeGroup α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.sublist`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGro
up.Red L₁ L₂ → L₂.Sublist L₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.mul_mk`：mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂)
· 使用定理 `FreeGroup.mk_toWord`：mk_toWord : forall {x : FreeGroup α}, mk (toWord x)
 = x
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
-/
lemma toWord_mul_sublist (x y : FreeGroup α) : (x * y).toWord <+ x.toWord ++ y.toWord := by
  refine Red.sublist ?_
  have : x * y = FreeGroup.mk (x.toWord ++ y.toWord) := by
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

/-- **Constructive Church-Rosser theorem** (compare `FreeGroup.Red.church_rosser`). -/
@[to_additive
/-- **Constructive Church-Rosser theorem** (compare `FreeAddGroup.Red.church_rosser`). -/]
/-
**FreeGroup.reduce.churchRosser** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup.reduce`。
形式化陈述：{α : Type u_1} →   {L₁ L₂ L₃ : List (α × Bool)} →     [DecidableEq α] → Fr
eeGroup.Red L₁ L₂ → FreeGroup.Red L₁ L₃ → { L₄ // FreeGroup.Red L₂ L₄ ∧ FreeGrou
p.Red L₃ L₄ }
参数：α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def reduce.churchRosser (H12 : Red L₁ L₂) (H13 : Red L₁ L₃) : { L₄ // Red L₂ L₄ ∧ Red L₃ L₄ } :=
  ⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq (FreeGroup α) :=
  toWord_injective.decidableEq

-- TODO @[to_additive] doesn't succeed, possibly due to a bug
--    FreeGroup.Red.decidableRel and FreeAddGroup.Red.decidableRel do not generate the same number
--    of equation lemmas.
/-
**FreeGroup.Red.decidableRel** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup.Red`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → DecidableRel FreeGroup.Red
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Red.decidableRel : DecidableRel (@Red α)
  | [], [] => isTrue Red.refl
  | [], _hd2 :: _tl2 => isFalse fun H => List.noConfusion rfl (heq_of_eq (Red.nil_iff.1 H))
  | (x, b) :: tl, [] =>
    match Red.decidableRel tl [(x, not b)] with
    | isTrue H => isTrue <| Red.trans (Red.cons_cons H) <| (@Red.Step.not _ [] [] _ _).to_red
    | isFalse H => isFalse fun H2 => H <| Red.cons_nil_iff_singleton.1 H2
  | (x1, b1) :: tl1, (x2, b2) :: tl2 =>
    if h : (x1, b1) = (x2, b2) then
      match Red.decidableRel tl1 tl2 with
      | isTrue H => isTrue <| h ▸ Red.cons_cons H
      | isFalse H => isFalse fun H2 => H <| (Red.cons_cons_iff _).1 <| h.symm ▸ H2
    else
      match Red.decidableRel tl1 ((x1, ! b1) :: (x2, b2) :: tl2) with
      | isTrue H => isTrue <| (Red.cons_cons H).tail Red.Step.cons_not
      | isFalse H => isFalse fun H2 => H <| Red.inv_of_red_of_ne h H2

/-- A list containing every word that `w₁` reduces to. -/
/-
**FreeGroup.Red.enum** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup.Red`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → List (α × Bool) → List (List (α × Bool)
)
参数：α × Bool；List (α × Bool)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list containing every word that `w₁` reduces to.
-/
def Red.enum (L₁ : List (α × Bool)) : List (List (α × Bool)) :=
  List.filter (Red L₁) (List.sublists L₁)
/-
**FreeGroup.Red.enum.sound** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.enum`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α],   L₂ ∈ 
List.filter (fun b => decide (FreeGroup.Red L₁ b)) L₁.sublists → FreeGroup.Red L
₁ L₂
参数：α × Bool；fun b => decide (FreeGroup.Red L₁ b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `List.of_mem_filter`：of_mem_filter {a : α} {l} (h : a in filter p l) : p 
a
-/
theorem Red.enum.sound (H : L₂ ∈ List.filter (Red L₁) (List.sublists L₁)) : Red L₁ L₂ :=
  of_decide_eq_true (@List.of_mem_filter _ _ L₂ _ H)
/-
**FreeGroup.Red.enum.complete** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.enum`。
形式化陈述：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst : DecidableEq α], FreeGro
up.Red L₁ L₂ → L₂ ∈ FreeGroup.Red.enum L₁
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_filter_of_mem`：mem_filter_of_mem {a : α} {l} (h₁ : a in l) (h₂ 
: p a) : a in filter p l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_sublists`：mem_sublists {s t : List α} : s in sublists t ↔ s <+ 
t
· 使用定理 `FreeGroup.Red.sublist`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGro
up.Red L₁ L₂ → L₂.Sublist L₁
· 使用定理 `decide_eq_true`：∀ {p : Prop} [inst : Decidable p], p → decide p = true
-/
theorem Red.enum.complete (H : Red L₁ L₂) : L₂ ∈ Red.enum L₁ :=
  List.mem_filter_of_mem (List.mem_sublists.2 <| Red.sublist H) (decide_eq_true H)
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L₁ : List (α × Bool)) : Fintype { L₂ // Red L₁ L₂ } :=
  Fintype.subtype (List.toFinset <| Red.enum L₁) fun _L₂ =>
    ⟨fun H => Red.enum.sound <| List.mem_toFinset.1 H, fun H =>
      List.mem_toFinset.2 <| Red.enum.complete H⟩

@[to_additive]
/-
**FreeGroup.IsReduced.reduce_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduced`。
形式化陈述：∀ {α : Type u_1} {L : List (α × Bool)} [inst : DecidableEq α], FreeGroup.I
sReduced L → FreeGroup.reduce L = L
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.IsReduced.red_iff_eq`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}
, FreeGroup.IsReduced L₁ → (FreeGroup.Red L₁ L₂ ↔ L₂ = L₁)
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
-/
theorem IsReduced.reduce_eq (h : IsReduced L) : reduce L = L := by
  rw [← h.red_iff_eq]
  exact reduce.red

@[to_additive]
/-
**FreeGroup.IsReduced.of_reduce_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduce
d`。
形式化陈述：∀ {α : Type u_1} {L : List (α × Bool)} [inst : DecidableEq α], FreeGroup.r
educe L = L → FreeGroup.IsReduced L
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.IsReduced.eq_1`：∀ {α : Type u} (L : List (α × Bool)), FreeGrou
p.IsReduced L = List.IsChain (fun a b => a.1 = b.1 → a.2 = b.2) L
· 使用定理 `List.isChain_iff_forall_rel_of_append_cons_cons`：isChain_iff_forall_rel_
of_append_cons_cons {l : List α} : IsChain R l ↔ forall ⦃a b l₁ l₂⦄, l = l₁ ++ a
 :: b :: l₂ -> R a b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.ne_not`：ne_not {a b : Bool} : a != !b ↔ a = b
· 使用定理 `FreeGroup.reduce.not`：∀ {α : Type u_1} [inst : DecidableEq α] {p : Prop}
 {L₁ L₂ L₃ : List (α × Bool)} {x : α} {b : Bool},   FreeGroup.reduce L₁ = L₂ ++ 
(x, b) :: …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem IsReduced.of_reduce_eq (h : reduce L = L) : IsReduced L := by
  rw [IsReduced, List.isChain_iff_forall_rel_of_append_cons_cons]
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl rfl
  rw [eq_comm, ← Bool.ne_not]
  rintro rfl
  exact reduce.not (h.trans hl)

@[to_additive]
/-
**FreeGroup.isReduced_iff_reduce_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：isReduced_iff_reduce_eq : IsReduced L ↔ reduce L = L where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.IsReduced.reduce_eq`：∀ {α : Type u_1} {L : List (α × Bool)} [i
nst : DecidableEq α], FreeGroup.IsReduced L → FreeGroup.reduce L = L
· 使用定理 `FreeGroup.IsReduced.of_reduce_eq`：∀ {α : Type u_1} {L : List (α × Bool)}
 [inst : DecidableEq α], FreeGroup.reduce L = L → FreeGroup.IsReduced L
-/
theorem isReduced_iff_reduce_eq : IsReduced L ↔ reduce L = L where
  mp h := h.reduce_eq
  mpr := .of_reduce_eq

@[to_additive]
/-
**FreeGroup.isReduced_toWord** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：isReduced_toWord {x : FreeGroup α} : IsReduced x.toWord
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.reduce_toWord`：reduce_toWord : forall x : FreeGroup α, reduce 
(toWord x) = toWord x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isReduced_toWord {x : FreeGroup α} : IsReduced x.toWord := by
  simp [isReduced_iff_reduce_eq]

end Reduce

@[to_additive (attr := simp)]
/-
**FreeGroup.one_ne_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：one_ne_of (a : α) : 1 != of a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem one_ne_of (a : α) : 1 ≠ of a :=
  letI := Classical.decEq α; ne_of_apply_ne toWord <| by simp

@[to_additive (attr := simp)]
/-
**FreeGroup.of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：∀ {α : Type u_1} (a : α), FreeGroup.of a ≠ 1
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `FreeGroup.one_ne_of`：one_ne_of (a : α) : 1 != of a
-/
theorem of_ne_one (a : α) : of a ≠ 1 := one_ne_of _ |>.symm

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nontrivial (FreeGroup α) where
  exists_pair_ne := let ⟨x⟩ := ‹Nonempty α›; ⟨1, of x, one_ne_of x⟩

section Metric

variable [DecidableEq α]

/-- The length of reduced words provides a norm on a free group. -/
@[to_additive /-- The length of reduced words provides a norm on an additive free group. -/]
/-
**FreeGroup.norm** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：norm (x : FreeGroup α) : Nat
参数：x : FreeGroup α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of reduced words provides a norm on a free group.
-/
def norm (x : FreeGroup α) : ℕ :=
  x.toWord.length

@[to_additive (attr := simp)]
/-
**FreeGroup.norm_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_inv_eq {x : FreeGroup α} : norm x⁻¹ = norm x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.toWord_inv`：toWord_inv (x : FreeGroup α) : x⁻¹.toWord = invRev
 x.toWord
· 使用定理 `FreeGroup.invRev_length`：invRev_length : (invRev L₁).length = L₁.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_inv_eq {x : FreeGroup α} : norm x⁻¹ = norm x := by
  simp only [norm, toWord_inv, invRev_length]

@[to_additive (attr := simp)]
/-
**FreeGroup.norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_eq_zero {x : FreeGroup α} : norm x = 0 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_eq_zero {x : FreeGroup α} : norm x = 0 ↔ x = 1 := by
  simp only [norm, List.length_eq_zero_iff, toWord_eq_nil_iff]

@[to_additive (attr := simp)]
/-
**FreeGroup.norm_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_one : norm (1 : FreeGroup α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_one : norm (1 : FreeGroup α) = 0 :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.norm_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_of (a : α) : norm (of a) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_of (a : α) : norm (of a) = 1 :=
  rfl

@[to_additive]
/-
**FreeGroup.norm_mk_le** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_mk_le : norm (mk L₁) <= L₁.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.length_le`：length_le (h : Red L₁ L₂) : L₂.length <= L₁.len
gth
· 使用定理 `FreeGroup.reduce.red`：∀ {α : Type u_1} {L : List (α × Bool)} [inst : Dec
idableEq α], FreeGroup.Red L (FreeGroup.reduce L)
-/
theorem norm_mk_le : norm (mk L₁) ≤ L₁.length :=
  reduce.red.length_le

@[to_additive]
/-
**FreeGroup.norm_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_mul_le (x y : FreeGroup α) : norm (x * y) <= norm x + norm y
参数：x y : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.mul_mk`：mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂)
· 使用定理 `FreeGroup.mk_toWord`：mk_toWord : forall {x : FreeGroup α}, mk (toWord x)
 = x
· 使用定理 `FreeGroup.norm_mk_le`：norm_mk_le : norm (mk L₁) <= L₁.length
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
-/
theorem norm_mul_le (x y : FreeGroup α) : norm (x * y) ≤ norm x + norm y :=
  calc
    norm (x * y) = norm (mk (x.toWord ++ y.toWord)) := by rw [← mul_mk, mk_toWord, mk_toWord]
    _ ≤ (x.toWord ++ y.toWord).length := norm_mk_le
    _ = norm x + norm y := List.length_append

@[to_additive (attr := simp)]
/-
**FreeGroup.norm_of_pow** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_of_pow (a : α) (n : Nat) : norm (of a ^ n) = n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.norm.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (x : FreeGr
oup α), x.norm = x.toWord.length
· 使用定理 `FreeGroup.toWord_of_pow`：toWord_of_pow (a : α) (n : Nat) : (of a ^ n).to
Word = List.replicate n (a, true)
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
-/
theorem norm_of_pow (a : α) (n : ℕ) : norm (of a ^ n) = n := by
  rw [norm, toWord_of_pow, List.length_replicate]

@[to_additive]
/-
**FreeGroup.norm_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：norm_surjective [Nonempty α] : Function.Surjective (norm (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `FreeGroup.norm_of_pow`：norm_of_pow (a : α) (n : Nat) : norm (of a ^ n) =
 n
-/
theorem norm_surjective [Nonempty α] : Function.Surjective (norm (α := α)) := by
  let ⟨a⟩ := ‹Nonempty α›
  exact Function.RightInverse.surjective <| norm_of_pow a

end Metric

end FreeGroup

