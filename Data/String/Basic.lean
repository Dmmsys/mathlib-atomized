/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.String.Lemmas
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Char
public import Mathlib.Algebra.Order.Group.Nat
import all Init.Data.String.Iterator  -- for unfolding `Iterator.curr`
import all Init.Data.Ord.String  -- for unfolding `String.compare`

/-!
# Strings

Supplementary theorems about the `String` type.
-/

@[expose] public section

namespace String

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
/-
**String.ltb** 是 Mathlib 中的一个定义，位于命名空间 `String`。
形式化陈述：ltb (s₁ s₂ : Legacy.Iterator) : Bool
参数：s₁ s₂ : Legacy.Iterator。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`<` on string iterators. This coincides with `<` on strings as lists.
-/
def ltb (s₁ s₂ : Legacy.Iterator) : Bool :=
  if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false

/-- Induction on `String.ltb`. -/
/-
**String.ltb.inductionOn.** 是 Mathlib 中的一个定义，位于命名空间 `String`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction on `String.ltb`.
-/
@[no_expose] def ltb.inductionOn.{u} {motive : Legacy.Iterator → Legacy.Iterator → Sort u}
    (it₁ it₂ : Legacy.Iterator)
    (ind : ∀ s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → Legacy.Iterator.hasNext ⟨s₁, i₁⟩ →
      i₁.get s₁ = i₂.get s₂ →
        motive (Legacy.Iterator.next ⟨s₁, i₁⟩) (Legacy.Iterator.next ⟨s₂, i₂⟩) →
          motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (eq : ∀ s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → Legacy.Iterator.hasNext ⟨s₁, i₁⟩ →
      ¬ i₁.get s₁ = i₂.get s₂ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₁ : ∀ s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → ¬ Legacy.Iterator.hasNext ⟨s₁, i₁⟩ →
      motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₂ : ∀ s₁ s₂ i₁ i₂, ¬ Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩) :
    motive it₁ it₂ :=
  if h₂ : it₂.hasNext then
    if h₁ : it₁.hasNext then
      if heq : it₁.curr = it₂.curr then
        ind it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq (inductionOn it₁.next it₂.next ind eq base₁ base₂)
      else eq it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq
    else base₁ it₁.s it₂.s it₁.i it₂.i h₂ h₁
  else base₂ it₁.s it₂.s it₁.i it₂.i h₂

set_option backward.isDefEq.respectTransparency false in
/-
**String.ltb_cons_addChar'** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：ltb_cons_addChar' (c : Char) (s₁ s₂ : Legacy.Iterator) : ltb ⟨ofList (c ::
 s₁.s.toList), s₁.i + c⟩ ⟨ofList (c :: s₂.s.toList), s₂.i + c⟩ = ltb s₁ s₂
参数：c : Char；s₁ s₂ : Legacy.Iterator。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `String.ltb.induct_unfolding`：∀ (motive : String.Legacy.Iterator → String
.Legacy.Iterator → Bool → Prop),   (∀ (s₁ s₂ : String.Legacy.Iterator),       s₂
.hasNext = true →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.ltb.eq_1`：∀ (s₁ s₂ : String.Legacy.Iterator),   String.ltb s₁ s₂ 
=     if s₂.hasNext = true then       if s₁.hasNext = true then if s₁.curr = s₂.
curr …
· 使用定理 `String.Legacy.Iterator.hasNext_cons_addChar`：∀ (c : Char) (cs : List Cha
r) (i : String.Pos.Raw),   { s := String.ofList (c :: cs), i := i + c }.hasNext 
= { s := String.ofList cs, i := i…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `String.ofList_toList`：∀ {s : String}, String.ofList s.toList = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `String.get_cons_addChar`：∀ (c : Char) (cs : List Char) (i : String.Pos.R
aw),   String.Pos.Raw.get (String.ofList (c :: cs)) (i + c) = String.Pos.Raw.get
 (String.ofLi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `String.Pos.Raw.add_char_right_comm`：∀ (p : String.Pos.Raw) (c₁ c₂ : Char
), p + c₁ + c₂ = p + c₂ + c₁
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
-/
theorem ltb_cons_addChar' (c : Char) (s₁ s₂ : Legacy.Iterator) :
    ltb ⟨ofList (c :: s₁.s.toList), s₁.i + c⟩ ⟨ofList (c :: s₂.s.toList), s₂.i + c⟩ =
      ltb s₁ s₂ := by
  fun_induction ltb s₁ s₂ with
  | case1 s₁ s₂ h₁ h₂ h ih =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_pos (by simpa using h₂), if_pos, ← ih]
    · simp only [Legacy.Iterator.next, Pos.Raw.next, get_cons_addChar, ofList_toList]
      congr 2 <;> apply Pos.Raw.add_char_right_comm
    · simpa only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList] using h
  | case2 s₁ s₂ h₁ h₂ h =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_pos (by simpa using h₂), if_neg]
    · simp only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList]
    · simpa only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList] using h
  | case3 s₁ s₂ h₁ h₂ =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_neg (by simpa using h₂)]
  | case4 s₁ s₂ h₁ =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, if_neg (by simpa using h₁)]
/-
**String.ltb_cons_addChar** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：ltb_cons_addChar (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos.Raw) : ltb 
⟨ofList (c :: cs₁), i₁ + c⟩ ⟨ofList (c :: cs₂), i₂ + c⟩ = ltb ⟨ofList cs₁, i₁⟩ ⟨
ofList cs₂, i₂⟩
参数：c : Char；cs₁ cs₂ : List Char；i₁ i₂ : Pos.Raw。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `String.ltb_cons_addChar'`：ltb_cons_addChar' (c : Char) (s₁ s₂ : Legacy.I
terator) : ltb ⟨ofList (c :: s₁.s.toList), s₁.i + c⟩ ⟨ofList (c :: s₂.s.toList),
 s₂.i + c⟩ = l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
· 使用定理 `String.ofList_cons`：∀ {c : Char} {l : List Char}, String.ofList (c :: l)
 = String.singleton c ++ String.ofList l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ltb_cons_addChar (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos.Raw) :
    ltb ⟨ofList (c :: cs₁), i₁ + c⟩ ⟨ofList (c :: cs₂), i₂ + c⟩ =
      ltb ⟨ofList cs₁, i₁⟩ ⟨ofList cs₂, i₂⟩ := by
  rw [eq_comm, ← ltb_cons_addChar' c]
  simp
/-
**String.lt_iff_toList_lt** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：lt_iff_toList_lt {s₁ s₂ : String} : s₁ < s₂ ↔ s₁.toList < s₂.toList
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_toList_lt {s₁ s₂ : String} : s₁ < s₂ ↔ s₁.toList < s₂.toList :=
  Iff.rfl

@[simp]
/-
**String.lt_iff_ltb** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：lt_iff_ltb {s₁ s₂ : String} : s₁ < s₂ ↔ ltb (String.Legacy.iter s₁) (Strin
g.Legacy.iter s₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `String.exists_eq_ofList`：∀ (s : String), ∃ l, s = String.ofList l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `String.ltb.eq_def`：∀ (s₁ s₂ : String.Legacy.Iterator),   String.ltb s₁ s
₂ =     if s₂.hasNext = true then       if s₁.hasNext = true then if s₁.curr = s
₂.curr …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `String.ofList_cons`：∀ {c : Char} {l : List Char}, String.ofList (c :: l)
 = String.singleton c ++ String.ofList l
· 使用定理 `String.utf8ByteSize_append`：∀ {s t : String}, (s ++ t).utf8ByteSize = s.
utf8ByteSize + t.utf8ByteSize
· 使用定理 `String.utf8ByteSize_singleton`：∀ {c : Char}, (String.singleton c).utf8By
teSize = c.utf8Size
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `List.nil_lt_cons`：∀ {α : Type u_1} [inst : LT α] (a : α) (l : List α), [
] < a :: l
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `String.rawEndPos_ofList`：∀ (cs : List Char), (String.ofList cs).rawEndPo
s = { byteIdx := String.utf8Len cs }
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
（共 42 条，此处仅展示前 30 条）
-/
theorem lt_iff_ltb {s₁ s₂ : String} :
    s₁ < s₂ ↔ ltb (String.Legacy.iter s₁) (String.Legacy.iter s₂) := by
  rw [Iff.comm]
  obtain ⟨s₁, rfl⟩ := s₁.exists_eq_ofList
  obtain ⟨s₂, rfl⟩ := s₂.exists_eq_ofList
  simp only [lt_iff_toList_lt, String.Legacy.iter, String.Legacy.mkIterator, String.toList_ofList]
  induction s₁ generalizing s₂ <;> cases s₂
  · unfold ltb; decide
  · rename_i c₂ cs₂; apply iff_of_true
    · unfold ltb
      simp [Legacy.Iterator.hasNext, Char.utf8Size_pos]
    · apply List.nil_lt_cons
  · rename_i c₁ cs₁ ih; apply iff_of_false
    · unfold ltb
      simp [Legacy.Iterator.hasNext]
    · apply not_lt_of_gt; apply List.nil_lt_cons
  · rename_i c₁ cs₁ ih c₂ cs₂; unfold ltb
    simp only [Legacy.Iterator.hasNext, Pos.Raw.byteIdx_zero, rawEndPos_ofList, utf8Len_cons,
      add_pos_iff, Char.utf8Size_pos, or_true, decide_true, ↓reduceIte, Legacy.Iterator.curr,
      Pos.Raw.get, String.toList_ofList, Pos.Raw.utf8GetAux, Legacy.Iterator.next, Pos.Raw.next,
      Bool.ite_eq_true_distrib, decide_eq_true_eq]
    split_ifs with h
    · subst c₂
      suffices ltb ⟨ofList (c₁ :: cs₁), (0 : Pos.Raw) + c₁⟩
          ⟨ofList (c₁ :: cs₂), (0 : Pos.Raw) + c₁⟩ =
            ltb ⟨ofList cs₁, 0⟩ ⟨ofList cs₂, 0⟩ by
        rw [this]; exact (ih cs₂).trans List.lex_cons_iff.symm
      apply ltb_cons_addChar
    · refine ⟨List.Lex.rel, fun e ↦ ?_⟩
      cases e <;> rename_i h'
      · assumption
      · contradiction

@[deprecated "Use the new String API" (since := "2026-04-01")]
/-
**String.toList_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：toList_nonempty : forall {s : String}, s != "" -> s.toList = String.Legacy
.front s :: (String.Legacy.drop s 1).toList | s, h => by obtain ⟨l, rfl⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `String.exists_eq_ofList`：∀ (s : String), ∃ l, s = String.ofList l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `String.ofList_cons`：∀ {c : Char} {l : List Char}, String.ofList (c :: l)
 = String.singleton c ++ String.ofList l
· 使用定理 `String.toList_append`：∀ {s t : String}, (s ++ t).toList = s.toList ++ t.
toList
· 使用定理 `String.toList_singleton`：∀ (c : Char), (String.singleton c).toList = [c]
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `String.Pos.Raw.utf8GetAux.eq_2`：∀ (x x_1 : String.Pos.Raw) (c : Char) (c
s : List Char),   String.Pos.Raw.utf8GetAux (c :: cs) x x_1 = if x = x_1 then c 
else String.Pos.Raw.…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `String.toList_drop`：∀ (s : String) (n : ℕ), (String.Legacy.drop s n).toL
ist = List.drop n s.toList
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toList_nonempty :
    ∀ {s : String}, s ≠ "" → s.toList = String.Legacy.front s :: (String.Legacy.drop s 1).toList
  | s, h => by
    obtain ⟨l, rfl⟩ := s.exists_eq_ofList
    match l with
    | [] => simp at h
    | c::cs => simp [Legacy.front, Pos.Raw.get, Pos.Raw.utf8GetAux]

@[simp]
/-
**String.head_empty** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：head_empty : "".toList.head! = default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_empty : "".toList.head! = default :=
  rfl
/-
**String.le_iff_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `String`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_iff_not_lt {s₁ s₂ : String} : s₁ ≤ s₂ ↔ ¬ s₂ < s₁ :=
  Iff.rfl
/-
**String.le_iff_toList_le** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：le_iff_toList_le {s₁ s₂ : String} : s₁ <= s₂ ↔ s₁.toList <= s₂.toList
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.String.Basic.0.String.le_iff_not_lt`：∀ {s₁ s₂ : St
ring}, s₁ ≤ s₂ ↔ ¬s₂ < s₁
· 使用定理 `String.lt_iff_toList_lt`：lt_iff_toList_lt {s₁ s₂ : String} : s₁ < s₂ ↔ s
₁.toList < s₂.toList
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList := by
  rw [String.le_iff_not_lt, lt_iff_toList_lt, not_lt]
/-
**String.** 是 Mathlib 中的一个实例，位于命名空间 `String`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder String where
  le_refl _ := le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_ge a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_ge]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_total a b := by
    simp only [le_iff_toList_le]
    apply le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := String.decidableLT
  compare_eq_compareOfLessAndEq a b := by simp [Ord.compare, String.compare]
/-
**String.ofList_eq** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：ofList_eq {l : List Char} {s : String} : ofList l = s ↔ l = s.toList
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofList_eq {l : List Char} {s : String} : ofList l = s ↔ l = s.toList := by
  simp [← toList_inj]

end String

