/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Krause
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
For any `w : α × Bool`, `FreeGroup.startsWith w` is the set of all elements of `FreeGroup α` that
start with `w`.

The main theorem `Orbit.duplicate` proves that applying `w⁻¹` to the orbit of `x` under the action
of `FreeGroup.startsWith w` yields the orbit of `x` under the action of `FreeGroup.startsWith v`
for every `v ≠ w⁻¹` (and the point `x`).
-/

@[expose] public section

variable {α X : Type*} [DecidableEq α]

namespace FreeGroup

/--
All elements of the free Group that start with a certain letter.
-/
/-
**FreeGroup.startsWith** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：startsWith (w : α × Bool)
参数：w : α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All elements of the free Group that start with a certain letter.
-/
def startsWith (w : α × Bool) := {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

/--
The neutral element is not contained in one of the startsWith sets.
-/
/-
**FreeGroup.startsWith.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.startsWith`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {w : α × Bool}, ∀ g ∈ FreeGroup.st
artsWith w, g ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The neutral element is not contained in one of the startsWith sets.
-/
theorem startsWith.ne_one {w : α × Bool} (g : FreeGroup α) (h : g ∈ FreeGroup.startsWith w) :
    g ≠ 1 := fun h1 ↦ by simp [h1, startsWith, FreeGroup.toWord_one] at h

@[simp]
/-
**FreeGroup.startsWith.disjoint_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.star
tsWith`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {w w' : α × Bool},   Disjoint (Fre
eGroup.startsWith w) (FreeGroup.startsWith w') ↔ w ≠ w'
参数：FreeGroup.startsWith w；FreeGroup.startsWith w'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma startsWith.disjoint_iff_ne {w w' : α × Bool} :
    Disjoint (startsWith w) (startsWith w') ↔ w ≠ w' := by
  simp_all only [ne_eq, startsWith, Set.disjoint_iff_inter_eq_empty, Set.ext_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, Option.some.injEq]
  exact Iff.intro (fun h ↦ h (mk [w]) (by simp)) (by grind)
/-
**FreeGroup.startsWith.Injective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.startsWith
`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α], Function.Injective FreeGroup.star
tsWith
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma startsWith.Injective : @startsWith α _ |>.Injective := fun a b h ↦ by
  simp only [startsWith, Set.ext_iff, Set.mem_ofPred_eq] at h
  simpa using h (mk [a])
/-
**FreeGroup.startsWith_mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：startsWith_mk_mul {w : α × Bool} (g : FreeGroup α) (h : ¬ g in startsWith 
(w.1, !w.2)) : mk [w] * g in startsWith w
参数：g : FreeGroup α；h : ¬ g in startsWith (w.1, !w.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FreeGroup.toWord_mul`：toWord_mul (x y : FreeGroup α) : toWord (x * y) = 
reduce (toWord x ++ toWord y)
· 使用定理 `FreeGroup.reduce_toWord`：reduce_toWord : forall x : FreeGroup α, reduce 
(toWord x) = toWord x
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem startsWith_mk_mul {w : α × Bool} (g : FreeGroup α)
    (h : ¬ g ∈ startsWith (w.1, !w.2)) : mk [w] * g ∈ startsWith w := by
  by_cases hC : 0 < g.toWord.length
  · simp only [startsWith, Set.mem_ofPred_eq, getElem?_pos, Option.some.injEq,
      Prod.eq_iff_fst_eq_snd_eq, not_and, Bool.not_eq_not, toWord_mul, toWord_mk, reduce.cons,
      reduce_nil, List.cons_append, List.nil_append, reduce_toWord, hC] at *
    rw [show g.toWord = g.toWord.head (by grind) :: g.toWord.tail by grind]
    grind
  · simp_all [startsWith]

variable [MulAction (FreeGroup α) X]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {w : α × Bool} : SMul (startsWith w) X where
  smul g x := g.val • x

@[simp]
/-
**FreeGroup.startsWith.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.startsWith`
。
形式化陈述：∀ {α : Type u_1} {X : Type u_2} [inst : DecidableEq α] [inst_1 : MulAction
 (FreeGroup α) X] {w : α × Bool}   {g : ↑(FreeGroup.startsWith w)} {x : X}, g • 
x = ↑g • x
参数：FreeGroup α；FreeGroup.startsWith w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma startsWith.smul_def {w : α × Bool} {g : startsWith w} {x : X} : g • x = g.val • x := by
  rfl

/--
Applying `w⁻¹` to the orbit generated by all elements of a free group that start with `w` yields
the orbit generated by all the words that start with every letter except `w⁻¹`
(and the original point).
-/
/-
**FreeGroup.Orbit.duplicate** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Orbit`。
形式化陈述：∀ {α : Type u_1} {X : Type u_2} [inst : DecidableEq α] [inst_1 : MulAction
 (FreeGroup α) X] (x : X) (w : α × Bool),   {x_1 | ∃ y ∈ MulAction.orbit (↑(Free
Group.startsWith w)) x, (FreeGroup.mk [w])⁻¹ • y = x_1} =     (⋃ v ∈ {z | z ≠ (w
.1, !w.2)}, MulAction.orbit (↑(FreeGroup.startsWith v)) x) ∪ {x}
参数：FreeGroup α；x : X；w : α × Bool；↑(FreeGroup.startsWith w)；FreeGroup.mk [w]；⋃ v
 ∈ {z | z ≠ (w.1, !w.2)}, MulAction.orbit (↑(FreeGroup.startsWith v)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.mk_toWord`：mk_toWord : forall {x : FreeGroup α}, mk (toWord x)
 = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `FreeGroup.startsWith.smul_def`：∀ {α : Type u_1} {X : Type u_2} [inst : D
ecidableEq α] [inst_1 : MulAction (FreeGroup α) X] {w : α × Bool}   {g : ↑(FreeG
roup.startsWith w)}…
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FreeGroup.isReduced_cons_cons`：isReduced_cons_cons {a b : (α × Bool)} : 
IsReduced (a :: b :: L) ↔ (a.1 = b.1 -> a.2 = b.2) ∧ IsReduced (b :: L)
· 使用定理 `FreeGroup.isReduced_toWord`：isReduced_toWord {x : FreeGroup α} : IsReduc
ed x.toWord
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `FreeGroup.IsReduced.reduce_eq`：∀ {α : Type u_1} {L : List (α × Bool)} [i
nst : DecidableEq α], FreeGroup.IsReduced L → FreeGroup.reduce L = L
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FreeGroup.startsWith_mk_mul`：startsWith_mk_mul {w : α × Bool} (g : FreeG
roup α) (h : ¬ g in startsWith (w.1, !w.2)) : mk [w] * g in startsWith w
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Applying `w⁻¹` to the orbit generated by all elements of a free group that start
 with `w` yields
the orbit generated by all the words that start with every letter except `w⁻¹`
(and the original point).
-/
theorem Orbit.duplicate (x : X) (w : α × Bool) :
    {(mk [w])⁻¹ • y | y ∈ MulAction.orbit (startsWith w) x} =
      (⋃ v ∈ {z : α × Bool | z ≠ (w.1, !w.2)}, MulAction.orbit (startsWith v) x) ∪ {x} := by
  ext i
  constructor
  · rintro ⟨-, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    set l := g.toWord with hl
    have h : (⟨g, hg⟩ : startsWith w) = ⟨mk g.toWord, by simp [g.mk_toWord, hg]⟩ := by
      simp [g.mk_toWord]
    match l with
    | [] => simp [← hl, startsWith] at hg
    | [a] =>
      simp_rw [h, ← hl, show a = w by simpa [← hl, startsWith] using hg, startsWith.smul_def,
        inv_smul_smul]
      exact Or.inr rfl
    | a :: b :: l =>
      have ha : a = w := by simpa [← hl, startsWith] using hg
      have h1 := isReduced_cons_cons.mp (hl ▸ isReduced_toWord)
      refine Or.inl (Set.mem_biUnion (x := b) (by grind) ?_)
      simp_rw [h, ← hl, ha, ← List.singleton_append (l := b :: l), ← mul_mk, startsWith.smul_def,
        mul_smul, inv_smul_smul]
      exact ⟨⟨mk (b :: l), by simp [startsWith, h1.2.reduce_eq]⟩, rfl⟩
  · rintro (⟨-, ⟨w', rfl⟩, -, ⟨hw, rfl⟩, ⟨g, hg⟩, rfl⟩ | rfl)
    · exact ⟨mk [w] • g • x, ⟨⟨mk [w] * g, startsWith_mk_mul g
        ((startsWith.disjoint_iff_ne.mpr hw).notMem_of_mem_left hg)⟩,
        mul_smul (mk [w]) g x⟩, inv_smul_smul (mk [w]) (g • x)⟩
    · exact ⟨mk [w] • i, ⟨⟨mk [w], rfl⟩, rfl⟩, inv_smul_smul (mk [w]) i⟩

end FreeGroup

