/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Decomposing walks

## Main definitions
- `takeUntil`: The path obtained by taking edges of an existing path until a given vertex.
- `dropUntil`: The path obtained by dropping edges of an existing path until a given vertex.
- `rotate`: Rotate a loop walk such that it is centered at the given vertex.
-/

@[expose] public section

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {v w u : V}

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
/-
**SimpleGraph.Walk.takeUntil** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} → [DecidableEq V] → {v w : V} → (p : 
G.Walk v w) → (u : V) → u ∈ p.support → G.Walk v u
参数：p : G.Walk v w；u : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a vertex in the support of a path, give the path up until (and including) 
that vertex.
-/
def takeUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk v u
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then
      hx ▸ Walk.nil
    else
      cons r (takeUntil p u <| by
        cases h
        · exact (hx rfl).elim
        · assumption)
/-
**SimpleGraph.Walk.takeUntil_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u : V} {h : u ∈
 SimpleGraph.Walk.nil.support},   SimpleGraph.Walk.nil.takeUntil u h = SimpleGra
ph.Walk.nil
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem takeUntil_nil {u : V} {h} : takeUntil (nil : G.Walk u u) u h = nil := rfl
/-
**SimpleGraph.Walk.takeUntil_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：takeUntil_cons {v' : V} {p : G.Walk v' v} (hwp : w in p.support) (h : u !=
 w) (hadj : G.Adj u v') : (p.cons hadj).takeUntil w (List.mem_of_mem_tail hwp) =
 (p.takeUntil w hwp).cons hadj
参数：hwp : w in p.support；h : u != w；hadj : G.Adj u v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma takeUntil_cons {v' : V} {p : G.Walk v' v} (hwp : w ∈ p.support) (h : u ≠ w)
    (hadj : G.Adj u v') :
    (p.cons hadj).takeUntil w (List.mem_of_mem_tail hwp) = (p.takeUntil w hwp).cons hadj := by
  simp [Walk.takeUntil, h]

@[simp]
/-
**SimpleGraph.Walk.takeUntil_first** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：takeUntil_first (p : G.Walk u v) : p.takeUntil u p.start_mem_support = .ni
l
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma takeUntil_first (p : G.Walk u v) :
    p.takeUntil u p.start_mem_support = .nil := by cases p <;> simp [Walk.takeUntil]

@[simp]
/-
**SimpleGraph.Walk.nil_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_takeUntil (p : G.Walk u v) (hwp : w in p.support) : (p.takeUntil w hwp
).Nil ↔ u = w
参数：p : G.Walk u v；hwp : w in p.support。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.Nil.eq`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p
 : G.Walk v w}, p.Nil → v = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_first`：takeUntil_first (p : G.Walk u v) : p.t
akeUntil u p.start_mem_support = .nil
-/
lemma nil_takeUntil (p : G.Walk u v) (hwp : w ∈ p.support) :
    (p.takeUntil w hwp).Nil ↔ u = w := ⟨Nil.eq, (by cases ·; simp)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.takeUntil_eq_take** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：takeUntil_eq_take (p : G.Walk u v) (h : w in p.support) : p.takeUntil w h 
= (p.take <| p.support.idxOf w).copy rfl (p.getVert_support_idxOf h)
参数：p : G.Walk u v；h : w in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
-/
lemma takeUntil_eq_take (p : G.Walk u v) (h : w ∈ p.support) :
    p.takeUntil w h = (p.take <| p.support.idxOf w).copy rfl (p.getVert_support_idxOf h) := by
  apply ext_support
  induction p with
  | nil =>
    simp only [takeUntil, eq_mpr_eq_cast, support_nil, getVert_nil, take, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | cons hadj p ih =>
    grind [takeUntil, support, copy_rfl_rfl, support_take]
/-
**SimpleGraph.Walk.length_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：length_takeUntil (p : G.Walk u v) (h : w in p.support) : (p.takeUntil w h)
.length = p.support.idxOf w
参数：p : G.Walk u v；h : w in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用引理 `SimpleGraph.Walk.takeUntil_eq_take`：takeUntil_eq_take (p : G.Walk u v) (
h : w in p.support) : p.takeUntil w h = (p.take <| p.support.idxOf w).copy rfl (
p.getVert_support_idxOf …
· 使用定理 `SimpleGraph.Walk.length_copy`：length_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length
· 使用引理 `SimpleGraph.Walk.take_length`：take_length (p : G.Walk u v) (n : Nat) : (
p.take n).length = n ⊓ p.length
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.idxOf_lt_length_of_mem`：∀ {α : Type u_1} {a : α} [inst : BEq α] [Eq
uivBEq α] {l : List α}, a ∈ l → List.idxOf a l < l.length
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_takeUntil (p : G.Walk u v) (h : w ∈ p.support) :
    (p.takeUntil w h).length = p.support.idxOf w := by
  simp [takeUntil_eq_take, Nat.le_iff_lt_add_one, ← length_support, List.idxOf_lt_length_of_mem h]

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
/-
**SimpleGraph.Walk.dropUntil** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} → [DecidableEq V] → {v w : V} → (p : 
G.Walk v w) → (u : V) → u ∈ p.support → G.Walk u w
参数：p : G.Walk v w；u : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a vertex in the support of a path, give the path from (and including) that
 vertex to
the end. In other words, drop vertices from the front of a path until (and not i
ncluding)
that vertex.
-/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by
      cases h
      · exact (hx rfl).elim
      · assumption

/-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `SimpleGraph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
@[simp]
/-
**SimpleGraph.Walk.take_spec** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：take_spec {u v w : V} (p : G.Walk v w) (h : u in p.support) : (p.takeUntil
 u h).append (p.dropUntil u h) = p
参数：p : G.Walk v w；h : u in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.mem_support_nil_iff`：mem_support_nil_iff {u v : V} : u 
in (nil : G.Walk v v).support ↔ u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…

--- 原说明 ---
The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `SimpleGraph.Walk.count_support_takeUntil_eq_one` specifies where this
 split occurs.
-/
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.dropUntil_first** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：dropUntil_first (p : G.Walk u v) (h : u in p.support) : p.dropUntil u h = 
p
参数：p : G.Walk u v；h : u in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.dropUntil.eq_def`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : DecidableEq V] {v w : V} (x : G.Walk v w) (x_1 : V) (x_2 : x_1 ∈ x.support
),   x.dropUntil x_1 x_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma dropUntil_first (p : G.Walk u v) (h : u ∈ p.support) : p.dropUntil u h = p := by
  unfold dropUntil
  split <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.dropUntil_eq_drop** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：dropUntil_eq_drop (p : G.Walk u v) (h : w in p.support) : p.dropUntil w h 
= (p.drop <| p.support.idxOf w).copy (p.getVert_support_idxOf h) rfl
参数：p : G.Walk u v；h : w in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SimpleGraph.Walk.dropUntil_first`：dropUntil_first (p : G.Walk u v) (h : 
u in p.support) : p.dropUntil u h = p
· 使用引理 `SimpleGraph.Walk.drop_support_eq_support_drop_min`：drop_support_eq_suppo
rt_drop_min {u v} (p : G.Walk u v) (n : Nat) : (p.drop n).support = p.support.dr
op (n ⊓ p.length)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.idxOf_cons_self`：∀ {α : Type u_1} {a : α} [inst : BEq α] [ReflBEq α
] {l : List α}, List.idxOf a (a :: l) = 0
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SimpleGraph.Walk.getVert_cons`：getVert_cons {u v w n} (p : G.Walk v w) (
h : G.Adj u v) (hn : n != 0) : (p.cons h).getVert n = p.getVert (n - 1)
· 使用引理 `SimpleGraph.Walk.drop_cons_eq`：drop_cons_eq (h : G.Adj u v) (p : G.Walk 
v w) (n : Nat) (hn : n != 0) : (cons h p).drop n = (p.drop (n - 1)).copy (p.getV
ert_cons h hn).symm…
· 使用定理 `SimpleGraph.Walk.dropUntil.eq_2`：∀ {V : Type u} {G : SimpleGraph V} [ins
t : DecidableEq V] {v w : V} (x v_1 : V) (r : G.Adj v v_1) (p : G.Walk v_1 w)   
(x_1 : x ∈ (SimpleGra…
-/
lemma dropUntil_eq_drop (p : G.Walk u v) (h : w ∈ p.support) :
    p.dropUntil w h = (p.drop <| p.support.idxOf w).copy (p.getVert_support_idxOf h) rfl := by
  apply ext_support
  induction p with
  | nil =>
    simp only [dropUntil, eq_mpr_eq_cast, support_nil, getVert_nil, drop, support_copy]
    grind [mem_support_nil_iff, support_nil]
  | @cons a _ _ _ p ih =>
    by_cases! h' : w = a
    · subst h'
      simp [dropUntil_first]
    · rw [drop_cons_eq _ _ _ (by grind), support_copy, dropUntil]
      grind
/-
**SimpleGraph.Walk.length_dropUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：length_dropUntil (p : G.Walk u v) (h : w in p.support) : (p.dropUntil w h)
.length = p.length - p.support.idxOf w
参数：p : G.Walk u v；h : w in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用引理 `SimpleGraph.Walk.dropUntil_eq_drop`：dropUntil_eq_drop (p : G.Walk u v) (
h : w in p.support) : p.dropUntil w h = (p.drop <| p.support.idxOf w).copy (p.ge
tVert_support_idxOf h) r…
· 使用定理 `SimpleGraph.Walk.length_copy`：length_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length
· 使用引理 `SimpleGraph.Walk.drop_length`：drop_length (p : G.Walk u v) (n : Nat) : (
p.drop n).length = p.length - n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_dropUntil (p : G.Walk u v) (h : w ∈ p.support) :
    (p.dropUntil w h).length = p.length - p.support.idxOf w := by
  simp [dropUntil_eq_drop]
/-
**SimpleGraph.Walk.isSubwalk_takeUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：isSubwalk_takeUntil (p : G.Walk u v) (h : w in p.support) : (p.takeUntil w
 h).IsSubwalk p
参数：p : G.Walk u v；h : w in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSubwalk_takeUntil (p : G.Walk u v) (h : w ∈ p.support) : (p.takeUntil w h).IsSubwalk p :=
  ⟨nil, p.dropUntil w h, by simp⟩
/-
**SimpleGraph.Walk.isSubwalk_dropUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：isSubwalk_dropUntil (p : G.Walk u v) (h : w in p.support) : (p.dropUntil w
 h).IsSubwalk p
参数：p : G.Walk u v；h : w in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSubwalk_dropUntil (p : G.Walk u v) (h : w ∈ p.support) : (p.dropUntil w h).IsSubwalk p :=
  ⟨p.takeUntil w h, nil, by simp⟩
/-
**SimpleGraph.Walk.mem_support_iff_exists_append** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
 {p : G.Walk u v} : w in p.support ↔ exists (q : G.Walk u w) (r : G.Walk w v), p
 = q.append r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

@[simp]
/-
**SimpleGraph.Walk.count_support_takeUntil_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u in p.su
pport) : (p.takeUntil u h).support.count u = 1
参数：p : G.Walk v w；h : u in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_first`：takeUntil_first (p : G.Walk u v) : p.t
akeUntil u p.start_mem_support = .nil
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.mem_support_nil_iff`：mem_support_nil_iff {u v : V} : u 
in (nil : G.Walk v v).support ↔ u = v
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp
  · cases h
    · simp
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]
/-
**SimpleGraph.Walk.count_edges_takeUntil_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u in p.supp
ort) (x : V) : (p.takeUntil u h).edges.count s(u, x) <= 1
参数：p : G.Walk v w；h : u in p.support；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_first`：takeUntil_first (p : G.Walk u v) : p.t
akeUntil u p.start_mem_support = .nil
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.mem_support_nil_iff`：mem_support_nil_iff {u v : V} : u 
in (nil : G.Walk v v).support ↔ u = v
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `SimpleGraph.Walk.edges_cons`：edges_cons {u v w : V} (h : G.Adj u v) (p :
 G.Walk v w) : (cons h p).edges = s(u, v) :: p.edges
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
    (p.takeUntil u h).edges.count s(u, x) ≤ 1 := by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp
  | cons ha p' ih =>
    cases h
    · simp
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · simp only [beq_iff_eq, Sym2.eq, Sym2.rel_iff'] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih

@[simp]
/-
**SimpleGraph.Walk.takeUntil_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w') 
(h : u in (p.copy hv hw).support) : (p.copy hv hw).takeUntil u h = (p.takeUntil 
u (by subst_vars; exact h)).copy hv rfl
参数：p : G.Walk v w；hv : v = v'；hw : w = w'；h : u in (p.copy hv hw).support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.dropUntil_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w') 
(h : u in (p.copy hv hw).support) : (p.copy hv hw).dropUntil u h = (p.dropUntil 
u (by subst_vars; exact h)).copy rfl hw
参数：p : G.Walk v w；hv : v = v'；hw : w = w'；h : u in (p.copy hv hw).support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.support_takeUntil_prefix_support** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：support_takeUntil_prefix_support (p : G.Walk v w) (h : u in p.support) : (
p.takeUntil u h).support <+: p.support
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_eq_take`：takeUntil_eq_take (p : G.Walk u v) (
h : w in p.support) : p.takeUntil w h = (p.take <| p.support.idxOf w).copy rfl (
p.getVert_support_idxOf …
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用引理 `SimpleGraph.Walk.support_take`：support_take {u v} (p : G.Walk u v) (n : 
Nat) : (p.take n).support = p.support.take (n + 1)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `List.instIsPartialOrderIsPrefix`：∀ {α : Type u_1}, IsPartialOrder (List 
α) fun x1 x2 => x1 <+: x2
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
· 使用定理 `List.prefix_refl`：∀ {α : Type u_1} (l : List α), l <+: l
-/
theorem support_takeUntil_prefix_support (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support <+: p.support := by
  grw [takeUntil_eq_take, support_copy, support_take, List.take_prefix]
/-
**SimpleGraph.Walk.support_takeUntil_subset_support** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：support_takeUntil_subset_support (p : G.Walk v w) (h : u in p.support) : (
p.takeUntil u h).support subseteq p.support
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.support_takeUntil_prefix_support`：support_takeUntil_pre
fix_support (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).support <+
: p.support
-/
theorem support_takeUntil_subset_support (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support :=
  p.support_takeUntil_prefix_support h |>.subset

@[deprecated (since := "2026-05-25")]
alias support_takeUntil_subset := support_takeUntil_subset_support
/-
**SimpleGraph.Walk.support_dropUntil_suffix_support** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：support_dropUntil_suffix_support (p : G.Walk v w) (h : u in p.support) : (
p.dropUntil u h).support <:+ p.support
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.dropUntil_eq_drop`：dropUntil_eq_drop (p : G.Walk u v) (
h : w in p.support) : p.dropUntil w h = (p.drop <| p.support.idxOf w).copy (p.ge
tVert_support_idxOf h) r…
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用引理 `SimpleGraph.Walk.drop_support_eq_support_drop_min`：drop_support_eq_suppo
rt_drop_min {u v} (p : G.Walk u v) (n : Nat) : (p.drop n).support = p.support.dr
op (n ⊓ p.length)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `List.instIsPartialOrderIsSuffix`：∀ {α : Type u_1}, IsPartialOrder (List 
α) fun x1 x2 => x1 <:+ x2
· 使用定理 `List.drop_suffix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.drop i l <
:+ l
· 使用定理 `List.suffix_refl`：∀ {α : Type u_1} (l : List α), l <:+ l
-/
theorem support_dropUntil_suffix_support (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support <:+ p.support := by
  grw [dropUntil_eq_drop, support_copy, drop_support_eq_support_drop_min, List.drop_suffix]
/-
**SimpleGraph.Walk.support_dropUntil_subset_support** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：support_dropUntil_subset_support (p : G.Walk v w) (h : u in p.support) : (
p.dropUntil u h).support subseteq p.support
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.support_dropUntil_suffix_support`：support_dropUntil_suf
fix_support (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).support <:
+ p.support
-/
theorem support_dropUntil_subset_support (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support :=
  p.support_dropUntil_suffix_support h |>.subset

@[deprecated (since := "2026-05-25")]
alias support_dropUntil_subset := support_dropUntil_subset_support
/-
**SimpleGraph.Walk.darts_takeUntil_prefix_darts** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：darts_takeUntil_prefix_darts (p : G.Walk v w) (h : u in p.support) : (p.ta
keUntil u h).darts <+: p.darts
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_eq_take`：takeUntil_eq_take (p : G.Walk u v) (
h : w in p.support) : p.takeUntil w h = (p.take <| p.support.idxOf w).copy rfl (
p.getVert_support_idxOf …
· 使用定理 `SimpleGraph.Walk.darts_copy`：darts_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).darts = p.darts
· 使用引理 `SimpleGraph.Walk.darts_take`：darts_take (p : G.Walk u v) (n : Nat) : (p.
take n).darts = p.darts.take n
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `List.instIsPartialOrderIsPrefix`：∀ {α : Type u_1}, IsPartialOrder (List 
α) fun x1 x2 => x1 <+: x2
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
· 使用定理 `List.prefix_refl`：∀ {α : Type u_1} (l : List α), l <+: l
-/
theorem darts_takeUntil_prefix_darts (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts <+: p.darts := by
  grw [takeUntil_eq_take, darts_copy, darts_take, List.take_prefix]
/-
**SimpleGraph.Walk.darts_takeUntil_subset_darts** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：darts_takeUntil_subset_darts (p : G.Walk v w) (h : u in p.support) : (p.ta
keUntil u h).darts subseteq p.darts
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.darts_takeUntil_prefix_darts`：darts_takeUntil_prefix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).darts <+: p.darts
-/
theorem darts_takeUntil_subset_darts (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts ⊆ p.darts :=
  p.darts_takeUntil_prefix_darts h |>.subset

@[deprecated (since := "2026-05-25")] alias darts_takeUntil_subset := darts_takeUntil_subset_darts
/-
**SimpleGraph.Walk.darts_dropUntil_suffix_darts** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：darts_dropUntil_suffix_darts (p : G.Walk v w) (h : u in p.support) : (p.dr
opUntil u h).darts <:+ p.darts
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.getVert_support_idxOf`：getVert_support_idxOf [Decidable
Eq V] (p : G.Walk u v) (h : w in p.support) : p.getVert (p.support.idxOf w) = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.dropUntil_eq_drop`：dropUntil_eq_drop (p : G.Walk u v) (
h : w in p.support) : p.dropUntil w h = (p.drop <| p.support.idxOf w).copy (p.ge
tVert_support_idxOf h) r…
· 使用定理 `SimpleGraph.Walk.darts_copy`：darts_copy {u v u' v'} (p : G.Walk u v) (hu
 : u = u') (hv : v = v') : (p.copy hu hv).darts = p.darts
· 使用引理 `SimpleGraph.Walk.darts_drop`：darts_drop (p : G.Walk u v) (n : Nat) : (p.
drop n).darts = p.darts.drop n
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `List.instIsPartialOrderIsSuffix`：∀ {α : Type u_1}, IsPartialOrder (List 
α) fun x1 x2 => x1 <:+ x2
· 使用定理 `List.drop_suffix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.drop i l <
:+ l
· 使用定理 `List.suffix_refl`：∀ {α : Type u_1} (l : List α), l <:+ l
-/
theorem darts_dropUntil_suffix_darts (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts <:+ p.darts := by
  grw [dropUntil_eq_drop, darts_copy, darts_drop, List.drop_suffix]
/-
**SimpleGraph.Walk.darts_dropUntil_subset_darts** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：darts_dropUntil_subset_darts (p : G.Walk v w) (h : u in p.support) : (p.dr
opUntil u h).darts subseteq p.darts
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.darts_dropUntil_suffix_darts`：darts_dropUntil_suffix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).darts <:+ p.darts
-/
theorem darts_dropUntil_subset_darts (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts ⊆ p.darts :=
  p.darts_dropUntil_suffix_darts h |>.subset

@[deprecated (since := "2026-05-25")] alias darts_dropUntil_subset := darts_dropUntil_subset_darts
/-
**SimpleGraph.Walk.edges_takeUntil_prefix_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：edges_takeUntil_prefix_edges (p : G.Walk v w) (h : u in p.support) : (p.ta
keUntil u h).edges <+: p.edges
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) ⦃l₁ l₂ : 
List α⦄, l₁ <+: l₂ → List.map f l₁ <+: List.map f l₂
· 使用定理 `SimpleGraph.Walk.darts_takeUntil_prefix_darts`：darts_takeUntil_prefix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).darts <+: p.darts
-/
theorem edges_takeUntil_prefix_edges (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges <+: p.edges :=
  p.darts_takeUntil_prefix_darts h |>.map _
/-
**SimpleGraph.Walk.edges_takeUntil_subset_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：edges_takeUntil_subset_edges (p : G.Walk v w) (h : u in p.support) : (p.ta
keUntil u h).edges subseteq p.edges
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.edges_takeUntil_prefix_edges`：edges_takeUntil_prefix_ed
ges (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).edges <+: p.edges
-/
theorem edges_takeUntil_subset_edges (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges ⊆ p.edges :=
  p.edges_takeUntil_prefix_edges h |>.subset

@[deprecated (since := "2026-05-25")] alias edges_takeUntil_subset := edges_takeUntil_subset_edges
/-
**SimpleGraph.Walk.edges_dropUntil_suffix_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：edges_dropUntil_suffix_edges (p : G.Walk v w) (h : u in p.support) : (p.dr
opUntil u h).edges <:+ p.edges
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) ⦃l₁ l₂ : 
List α⦄, l₁ <:+ l₂ → List.map f l₁ <:+ List.map f l₂
· 使用定理 `SimpleGraph.Walk.darts_dropUntil_suffix_darts`：darts_dropUntil_suffix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).darts <:+ p.darts
-/
theorem edges_dropUntil_suffix_edges (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges <:+ p.edges :=
  p.darts_dropUntil_suffix_darts h |>.map _
/-
**SimpleGraph.Walk.edges_dropUntil_subset_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：edges_dropUntil_subset_edges (p : G.Walk v w) (h : u in p.support) : (p.dr
opUntil u h).edges subseteq p.edges
参数：p : G.Walk v w；h : u in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.edges_dropUntil_suffix_edges`：edges_dropUntil_suffix_ed
ges (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).edges <:+ p.edges
-/
theorem edges_dropUntil_subset_edges (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges ⊆ p.edges :=
  p.edges_dropUntil_suffix_edges h |>.subset

@[deprecated (since := "2026-05-25")] alias edges_dropUntil_subset := edges_dropUntil_subset_edges
/-
**SimpleGraph.Walk.length_takeUntil_le_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：length_takeUntil_le_length {u v w : V} (p : G.Walk v w) (h : u in p.suppor
t) : (p.takeUntil u h).length <= p.length
参数：p : G.Walk v w；h : u in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `List.IsPrefix.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → 
l₁.length ≤ l₂.length
· 使用定理 `SimpleGraph.Walk.darts_takeUntil_prefix_darts`：darts_takeUntil_prefix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).darts <+: p.darts
-/
theorem length_takeUntil_le_length {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length := by
  simpa using p.darts_takeUntil_prefix_darts h |>.length_le

@[deprecated (since := "2026-05-25")] alias length_takeUntil_le := length_takeUntil_le_length
/-
**SimpleGraph.Walk.length_dropUntil_le_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：length_dropUntil_le_length {u v w : V} (p : G.Walk v w) (h : u in p.suppor
t) : (p.dropUntil u h).length <= p.length
参数：p : G.Walk v w；h : u in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `List.IsSuffix.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → 
l₁.length ≤ l₂.length
· 使用定理 `SimpleGraph.Walk.darts_dropUntil_suffix_darts`：darts_dropUntil_suffix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).darts <:+ p.darts
-/
theorem length_dropUntil_le_length {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length := by
  simpa using p.darts_dropUntil_suffix_darts h |>.length_le

@[deprecated (since := "2026-05-25")] alias length_dropUntil_le := length_dropUntil_le_length
/-
**SimpleGraph.Walk.takeUntil_append_of_mem_left** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：takeUntil_append_of_mem_left {x : V} (p : G.Walk u v) (q : G.Walk v w) (hx
 : x in p.support) : (p.append q).takeUntil x (support_subset_support_append_lef
t _ _ hx) = p.takeUntil _ hx
参数：p : G.Walk u v；q : G.Walk v w；hx : x in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.support_subset_support_append_left`：support_subset_supp
ort_append_left {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (q
 : G.Walk v w) : p.support subseteq (p.ap…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_first`：takeUntil_first (p : G.Walk u v) : p.t
akeUntil u p.start_mem_support = .nil
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.mem_support_nil_iff`：mem_support_nil_iff {u v : V} : u 
in (nil : G.Walk v v).support ↔ u = v
-/
lemma takeUntil_append_of_mem_left {x : V} (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ p.support) :
    (p.append q).takeUntil x (support_subset_support_append_left _ _ hx) = p.takeUntil _ hx := by
  induction p with
  | nil => rw [mem_support_nil_iff] at hx; subst_vars; simp
  | cons => grind [cons_append, takeUntil]
/-
**SimpleGraph.Walk.getVert_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：getVert_takeUntil {u v : V} {n : Nat} {p : G.Walk u v} (hw : w in p.suppor
t) (hn : n <= (p.takeUntil w hw).length) : (p.takeUntil w hw).getVert n = p.getV
ert n
参数：hw : w in p.support；hn : n <= (p.takeUntil w hw).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `SimpleGraph.Walk.getVert_append`：getVert_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) (i : Nat) : (p.append q).getVert i = if i < p.length then 
p.getVert i else q.ge…
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
-/
lemma getVert_takeUntil {u v : V} {n : ℕ} {p : G.Walk u v} (hw : w ∈ p.support)
    (hn : n ≤ (p.takeUntil w hw).length) : (p.takeUntil w hw).getVert n = p.getVert n := by
  conv_rhs => rw [← take_spec p hw, getVert_append]
  cases hn.lt_or_eq <;> simp_all
/-
**SimpleGraph.Walk.snd_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：snd_takeUntil (hsu : w != u) (p : G.Walk u v) (h : w in p.support) : (p.ta
keUntil w h).snd = p.snd
参数：hsu : w != u；p : G.Walk u v；h : w in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.getVert_takeUntil`：getVert_takeUntil {u v : V} {n : Nat
} {p : G.Walk u v} (hw : w in p.support) (hn : n <= (p.takeUntil w hw).length) :
 (p.takeUntil w hw).getV…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma snd_takeUntil (hsu : w ≠ u) (p : G.Walk u v) (h : w ∈ p.support) :
    (p.takeUntil w h).snd = p.snd := by
  apply p.getVert_takeUntil h
  contrapose hsu
  symm
  simpa [length_eq_zero_iff] using hsu
/-
**SimpleGraph.Walk.getVert_length_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：getVert_length_takeUntil {p : G.Walk v w} (h : u in p.support) : p.getVert
 (p.takeUntil _ h).length = u
参数：h : u in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
-/
lemma getVert_length_takeUntil {p : G.Walk v w} (h : u ∈ p.support) :
    p.getVert (p.takeUntil _ h).length = u := by
  have := congr_arg₂ (y := (p.takeUntil _ h).length) getVert (p.take_spec h) rfl
  grind [getVert_append, getVert_zero]
/-
**SimpleGraph.Walk.getVert_lt_length_takeUntil_ne** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：getVert_lt_length_takeUntil_ne {n : Nat} {p : G.Walk v w} (h : u in p.supp
ort) (hn : n < (p.takeUntil _ h).length) : p.getVert n != u
参数：h : u in p.support；hn : n < (p.takeUntil _ h).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `Nat.lt_add_one_of_le`：∀ {n m : ℕ}, n ≤ m → n < m + 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.getVert_eq_support_getElem`：getVert_eq_support_getElem 
{u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length) : p.getVert n = p.suppo
rt[n]'(p.length_support ▸ Nat.lt_…
· 使用引理 `SimpleGraph.Walk.getVert_takeUntil`：getVert_takeUntil {u v : V} {n : Nat
} {p : G.Walk u v} (hw : w in p.support) (hn : n <= (p.takeUntil w hw).length) :
 (p.takeUntil w hw).getV…
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `List.getElem_dropLast`：∀ {α : Type u_1} {xs : List α} {i : ℕ} (h : i < x
s.dropLast.length), xs.dropLast[i] = xs[i]
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `SimpleGraph.Walk.count_support_takeUntil_eq_one`：count_support_takeUntil
_eq_one {u v w : V} (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).su
pport.count u = 1
· 使用定理 `SimpleGraph.Walk.dropLast_support_concat`：dropLast_support_concat (p : G
.Walk u v) : p.support.dropLast ++ [v] = p.support
-/
lemma getVert_lt_length_takeUntil_ne {n : ℕ} {p : G.Walk v w} (h : u ∈ p.support)
    (hn : n < (p.takeUntil _ h).length) : p.getVert n ≠ u := by
  rintro rfl
  have h₁ : n < (p.takeUntil _ h).support.dropLast.length := by simpa
  have : p.getVert n ∈ (p.takeUntil _ h).support.dropLast := by
    simp_rw [p.getVert_takeUntil h hn.le ▸ getVert_eq_support_getElem _ hn.le,
      ← List.getElem_dropLast h₁, List.getElem_mem h₁]
  have := dropLast_support_concat _ ▸ p.count_support_takeUntil_eq_one h
  grind [List.not_mem_of_count_eq_zero]
/-
**SimpleGraph.Walk.getVert_le_length_takeUntil_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk`。
形式化陈述：getVert_le_length_takeUntil_eq_iff {n : Nat} {p : G.Walk v w} (h : u in p.
support) (hn : n <= (p.takeUntil _ h).length) : p.getVert n = u ↔ n = (p.takeUnt
il _ h).length
参数：h : u in p.support；hn : n <= (p.takeUntil _ h).length。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getVert_le_length_takeUntil_eq_iff {n : ℕ} {p : G.Walk v w} (h : u ∈ p.support)
    (hn : n ≤ (p.takeUntil _ h).length) : p.getVert n = u ↔ n = (p.takeUntil _ h).length := by
  grind [getVert_length_takeUntil, getVert_lt_length_takeUntil_ne]
/-
**SimpleGraph.Walk.length_takeUntil_lt_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：length_takeUntil_lt_length {u v w : V} {p : G.Walk v w} (h : u in p.suppor
t) (huw : u != w) : (p.takeUntil u h).length < p.length
参数：h : u in p.support；huw : u != w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `SimpleGraph.Walk.length_takeUntil_le_length`：length_takeUntil_le_length 
{u v w : V} (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).length <= 
p.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用引理 `SimpleGraph.Walk.getVert_takeUntil`：getVert_takeUntil {u v : V} {n : Nat
} {p : G.Walk u v} (hw : w in p.support) (hn : n <= (p.takeUntil w hw).length) :
 (p.takeUntil w hw).getV…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma length_takeUntil_lt_length {u v w : V} {p : G.Walk v w} (h : u ∈ p.support) (huw : u ≠ w) :
    (p.takeUntil u h).length < p.length := by
  rw [(p.length_takeUntil_le_length h).lt_iff_ne]
  exact fun hl ↦ huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

@[deprecated (since := "2026-05-25")] alias length_takeUntil_lt := length_takeUntil_lt_length
/-
**SimpleGraph.Walk.length_dropUntil_lt_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：length_dropUntil_lt_length {u v w : V} {p : G.Walk v w} (h : u in p.suppor
t) (huv : u != v) : (p.dropUntil u h).length < p.length
参数：h : u in p.support；huv : u != v。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma length_dropUntil_lt_length {u v w : V} {p : G.Walk v w} (h : u ∈ p.support) (huv : u ≠ v) :
    (p.dropUntil u h).length < p.length := by
  grind [length_dropUntil, cons_tail_support]
/-
**SimpleGraph.Walk.takeUntil_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：takeUntil_takeUntil {w x : V} (p : G.Walk u v) (hw : w in p.support) (hx :
 x in (p.takeUntil w hw).support) : (p.takeUntil w hw).takeUntil x hx = p.takeUn
til x (p.support_takeUntil_subset_support hw hx)
参数：p : G.Walk u v；hw : w in p.support；hx : x in (p.takeUntil w hw).support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.support_takeUntil_subset_support`：support_takeUntil_sub
set_support (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).support su
bseteq p.support
· 使用定理 `SimpleGraph.Walk.support_subset_support_append_left`：support_subset_supp
ort_append_left {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (q
 : G.Walk v w) : p.support subseteq (p.ap…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.takeUntil_append_of_mem_left`：takeUntil_append_of_mem_l
eft {x : V} (p : G.Walk u v) (q : G.Walk v w) (hx : x in p.support) : (p.append 
q).takeUntil x (support_subset_supp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `SimpleGraph.Walk.takeUntil.congr_simp`：∀ {V : Type u} {G : SimpleGraph V
} [inst : DecidableEq V] {v w : V} (p p_1 : G.Walk v w) (e_p : p = p_1) (u : V) 
  (a : u ∈ p.support), p.ta…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma takeUntil_takeUntil {w x : V} (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx =
      p.takeUntil x (p.support_takeUntil_subset_support hw hx) := by
  simp_rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx, take_spec]
/-
**SimpleGraph.Walk.notMem_support_takeUntil_support_takeUntil_subset** 是 Mathlib
 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：notMem_support_takeUntil_support_takeUntil_subset {p : G.Walk u v} {x : V}
 (h : x != w) (hw : w in p.support) (hx : x in (p.takeUntil w hw).support) : w ∉
 (p.takeUntil x (p.support_takeUntil_subset_support hw hx)).support
参数：h : x != w；hw : w in p.support；hx : x in (p.takeUntil w hw).support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.support_takeUntil_subset_support`：support_takeUntil_sub
set_support (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).support su
bseteq p.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.takeUntil_takeUntil`：takeUntil_takeUntil {w x : V} (p :
 G.Walk u v) (hw : w in p.support) (hx : x in (p.takeUntil w hw).support) : (p.t
akeUntil w hw).takeUntil x…
· 使用引理 `SimpleGraph.Walk.length_takeUntil_lt_length`：length_takeUntil_lt_length 
{u v w : V} {p : G.Walk v w} (h : u in p.support) (huw : u != w) : (p.takeUntil 
u h).length < p.length
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.takeUntil.congr_simp`：∀ {V : Type u} {G : SimpleGraph V
} [inst : DecidableEq V] {v w : V} (p p_1 : G.Walk v w) (e_p : p = p_1) (u : V) 
  (a : u ∈ p.support), p.ta…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma notMem_support_takeUntil_support_takeUntil_subset {p : G.Walk u v} {x : V} (h : x ≠ w)
    (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
    w ∉ (p.takeUntil x (p.support_takeUntil_subset_support hw hx)).support := by
  rw [← takeUntil_takeUntil p hw hx]
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt_length _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w hw).length := by
    exact length_takeUntil_lt_length _ h
  simp only [takeUntil_takeUntil] at h1 h2
  lia

/-- Rotate a loop walk such that it is centered at the given vertex. -/
/-
**SimpleGraph.Walk.rotate** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：rotate (c : G.Walk v v) (u : V) (h : u in c.support) : G.Walk u u
参数：c : G.Walk v v；u : V；h : u in c.support。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotate a loop walk such that it is centered at the given vertex.
-/
def rotate (c : G.Walk v v) (u : V) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
/-
**SimpleGraph.Walk.support_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_rotate (c : G.Walk v v) (u : V) (h) : (c.rotate u h).support.tail 
~r c.support.tail
参数：c : G.Walk v v；u : V；h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.tail_support_append`：tail_support_append {u v w : V} (p
 : G.Walk u v) (p' : G.Walk v w) : (p.append p').support.tail = p.support.tail +
+ p'.support.tail
· 使用定理 `List.IsRotated.trans`：∀ {α : Type u} {l l' l'' : List α}, l ~r l' → l' ~
r l'' → l ~r l''
· 使用定理 `List.isRotated_append`：isRotated_append : (l ++ l') ~r (l' ++ l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `List.IsRotated.refl`：∀ {α : Type u} (l : List α), l ~r l
-/
theorem support_rotate (c : G.Walk v v) (u : V) (h) :
    (c.rotate u h).support.tail ~r c.support.tail := by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, take_spec]

@[simp]
/-
**SimpleGraph.Walk.mem_support_rotate_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：mem_support_rotate_iff (c : G.Walk v v) (u : V) (h) : w in (c.rotate u h).
support ↔ w in c.support
参数：c : G.Walk v v；u : V；h。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_support_rotate_iff (c : G.Walk v v) (u : V) (h) :
    w ∈ (c.rotate u h).support ↔ w ∈ c.support := by
  grind [rotate, take_spec, mem_support_append_iff]
/-
**SimpleGraph.Walk.rotate_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：rotate_darts (c : G.Walk v v) (u : V) (h) : (c.rotate u h).darts ~r c.dart
s
参数：c : G.Walk v v；u : V；h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.darts_append`：darts_append {u v w : V} (p : G.Walk u v)
 (p' : G.Walk v w) : (p.append p').darts = p.darts ++ p'.darts
· 使用定理 `List.IsRotated.trans`：∀ {α : Type u} {l l' l'' : List α}, l ~r l' → l' ~
r l'' → l ~r l''
· 使用定理 `List.isRotated_append`：isRotated_append : (l ++ l') ~r (l' ++ l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `List.IsRotated.refl`：∀ {α : Type u} (l : List α), l ~r l
-/
theorem rotate_darts (c : G.Walk v v) (u : V) (h) : (c.rotate u h).darts ~r c.darts := by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, take_spec]
/-
**SimpleGraph.Walk.rotate_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：rotate_edges (c : G.Walk v v) (u : V) (h) : (c.rotate u h).edges ~r c.edge
s
参数：c : G.Walk v v；u : V；h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsRotated.map`：∀ {α : Type u} {β : Type u_1} {l₁ l₂ : List α}, l₁ ~
r l₂ → ∀ (f : α → β), List.map f l₁ ~r List.map f l₂
· 使用定理 `SimpleGraph.Walk.rotate_darts`：rotate_darts (c : G.Walk v v) (u : V) (h)
 : (c.rotate u h).darts ~r c.darts
-/
theorem rotate_edges (c : G.Walk v v) (u : V) (h) : (c.rotate u h).edges ~r c.edges :=
  (rotate_darts c u h).map _
/-
**SimpleGraph.Walk.length_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] (c : G.W
alk v v) (u : V) (h : u ∈ c.support),   (c.rotate u h).length = c.length
参数：c : G.Walk v v；u : V；h : u ∈ c.support；c.rotate u h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_edges`：length_edges {u v : V} (p : G.Walk u v) :
 p.edges.length = p.length
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.IsRotated.perm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
· 使用定理 `SimpleGraph.Walk.rotate_edges`：rotate_edges (c : G.Walk v v) (u : V) (h)
 : (c.rotate u h).edges ~r c.edges
-/
@[simp] lemma length_rotate (c : G.Walk v v) (u : V) (h) : (c.rotate u h).length = c.length := by
  simpa using (rotate_edges c u h).perm.length_eq

@[simp]
/-
**SimpleGraph.Walk.nil_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_rotate {c : G.Walk v v} (h) : (c.rotate u h).Nil ↔ c.Nil
参数：h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_rotate`：∀ {V : Type u} {G : SimpleGraph V} {v : 
V} [inst : DecidableEq V] (c : G.Walk v v) (u : V) (h : u ∈ c.support),   (c.rot
ate u h).length = c.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nil_rotate {c : G.Walk v v} (h) : (c.rotate u h).Nil ↔ c.Nil := by
  simp [← length_eq_zero_iff]

@[deprecated nil_rotate (since := "2026-05-11")]
/-
**SimpleGraph.Walk.rotate_eq_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：rotate_eq_nil {c : G.Walk v v} (h) : c.rotate u h = nil ↔ c = nil
参数：h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rotate_eq_nil {c : G.Walk v v} (h) : c.rotate u h = nil ↔ c = nil := by simp

end WalkDecomp

/-- Given a walk `p` and a node in the support, there exists a natural `n`, such that given node
is the `n`-th node (zero-indexed) in the walk. In addition, `n` is at most the length of the walk.
Due to the definition of `getVert` it would otherwise be legal to return a larger `n` for the last
node. -/
/-
**SimpleGraph.Walk.mem_support_iff_exists_getVert** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} : u in p.suppo
rt ↔ exists n, p.getVert n = u ∧ n <= p.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.getVert_length_takeUntil`：getVert_length_takeUntil {p :
 G.Walk v w} (h : u in p.support) : p.getVert (p.takeUntil _ h).length = u
· 使用定理 `SimpleGraph.Walk.length_takeUntil_le_length`：length_takeUntil_le_length 
{u v w : V} (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).length <= 
p.length
· 使用定理 `SimpleGraph.Walk.getVert_mem_support`：getVert_mem_support {u v : V} (p :
 G.Walk u v) (i : Nat) : p.getVert i in p.support

--- 原说明 ---
Given a walk `p` and a node in the support, there exists a natural `n`, such tha
t given node
is the `n`-th node (zero-indexed) in the walk. In addition, `n` is at most the l
ength of the walk.
Due to the definition of `getVert` it would otherwise be legal to return a large
r `n` for the last
node.
-/
theorem mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} :
    u ∈ p.support ↔ ∃ n, p.getVert n = u ∧ n ≤ p.length := by
  classical
  exact Iff.intro
    (fun h ↦ ⟨_, p.getVert_length_takeUntil h, p.length_takeUntil_le_length h⟩)
    (fun ⟨_, h, _⟩ ↦ h ▸ getVert_mem_support _ _)

end SimpleGraph.Walk

