/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.ENat.Lattice

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle, they give `0` or `∞` respectively if the graph is acyclic.

## TODO

- Prove that `G.egirth ≤ 2 * G.ediam + 1` when `G` is not acyclic
- Prove that `G.girth ≤ 2 * G.diam + 1` when the diameter is non-zero

-/

@[expose] public section

namespace SimpleGraph
variable {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}

section egirth


/--
The extended girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is
acyclic.
-/
/-
**SimpleGraph.egirth** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：egirth (G : SimpleGraph α) : Nat∞
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended girth of a simple graph is the length of its smallest cycle, or `∞`
 if the graph is
acyclic.
-/
noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp]
/-
**SimpleGraph.le_egirth** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：le_egirth {n : Nat∞} : n <= G.egirth ↔ forall a (w : G.Walk a a), w.IsCycl
e -> n <= w.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_egirth {n : ℕ∞} : n ≤ G.egirth ↔ ∀ a (w : G.Walk a a), w.IsCycle → n ≤ w.length := by
  simp [egirth]
/-
**SimpleGraph.egirth_le_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：egirth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.egirth <= w.leng
th
参数：h : w.IsCycle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.le_egirth`：le_egirth {n : Nat∞} : n <= G.egirth ↔ forall a (
w : G.Walk a a), w.IsCycle -> n <= w.length
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma egirth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.egirth ≤ w.length :=
  le_egirth.mp le_rfl a w h
/-
**SimpleGraph.Walk.IsCircuit.egirth_le_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {a : α} {w : G.Walk a a}, w.IsCircuit
 → G.egirth ≤ ↑w.length
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.Walk.IsCircuit.isCycle_cycleBypass`：∀ {V : Type u} {G : Simp
leGraph V} {v : V} [inst : DecidableEq V] {w : G.Walk v v}, w.IsCircuit → w.cycl
eBypass.IsCycle
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用引理 `SimpleGraph.Walk.length_cycleBypass_le_length`：length_cycleBypass_le_len
gth (w : G.Walk v v) : w.cycleBypass.length <= w.length
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `SimpleGraph.egirth_le_length`：egirth_le_length {a} {w : G.Walk a a} (h :
 w.IsCycle) : G.egirth <= w.length
-/
lemma Walk.IsCircuit.egirth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.egirth ≤ w.length := by
  classical
  by_contra! hlg
  let w' : G.Walk a a := w.cycleBypass
  have hwc' : w'.IsCycle := hwc.isCycle_cycleBypass
  have hwlg' : w'.length < G.egirth := by
    grw [w.length_cycleBypass_le_length]
    exact hlg
  exact not_le_of_gt hwlg' (SimpleGraph.egirth_le_length hwc')

@[simp]
/-
**SimpleGraph.egirth_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic := by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.egirth_eq_top⟩ := egirth_eq_top

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.egirth_anti** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：egirth_anti : Antitone (egirth : SimpleGraph α -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `iInf₂_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {κ : ι → So
rt u_6} {κ' : ι' → Sort u_7} [inst : CompleteLattice α]   {f : (i : ι) → κ i → α
}…
· 使用定理 `SimpleGraph.Walk.IsCycle.mapLe`：∀ {V : Type u} {G G' : SimpleGraph V} (h
 : G ≤ G') {u : V} {p : G.Walk u u},   p.IsCycle → (SimpleGraph.Walk.mapLe h p).
IsCycle
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
-/
lemma egirth_anti : Antitone (egirth : SimpleGraph α → ℕ∞) :=
  fun G H h ↦ iInf_mono fun a ↦ iInf₂_mono' fun w hw ↦ ⟨w.mapLe h, hw.mapLe _, by simp⟩
/-
**SimpleGraph.exists_egirth_eq_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_egirth_eq_length : (exists (a : α) (w : G.Walk a a), w.IsCycle ∧ G.
egirth = w.length) ↔ ¬ G.IsAcyclic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `iInf_sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{κ : β → Type u_8} (f : (i : β) → κ i → α),   ⨅ i, ⨅ j, f i j = ⨅ x, f x.fst x.s
n…
· 使用定理 `ciInf_mem`：ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
-/
lemma exists_egirth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.egirth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma',
      ENat.iInf_natCast_ne_top, ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _
/-
**SimpleGraph.three_le_egirth** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：three_le_egirth : 3 <= G.egirth
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
-/
lemma three_le_egirth : 3 ≤ G.egirth := by
  simpa using fun _ _ h ↦ h.three_le_length
/-
**SimpleGraph.egirth_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1}, ⊥.egirth = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma egirth_bot : egirth (⊥ : SimpleGraph α) = ⊤ := by simp
/-
**SimpleGraph.egirth_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：egirth_top (h : 3 <= ENat.card α) : egirth (⊤ : SimpleGraph α) = 3
参数：h : 3 <= ENat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.exists_finset_eq_card`：exists_finset_eq_card {α} {n : Nat} (h :
 n <= #α) : exists s : Finset α, n = s.card
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.ofNat_le_toENat`：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeast
Two], OfNat.ofNat n ≤ Cardinal.toENat c ↔ OfNat.ofNat n ≤ c
· 使用定理 `Finset.card_eq_three`：card_eq_three : #s = 3 ↔ exists x y z, x != y ∧ x 
!= z ∧ y != z ∧ s = {x, y, z}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `SimpleGraph.egirth_le_length`：egirth_le_length {a} {w : G.Walk a a} (h :
 w.IsCycle) : G.egirth <= w.length
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 32 条，此处仅展示前 30 条）
-/
theorem egirth_top (h : 3 ≤ ENat.card α) : egirth (⊤ : SimpleGraph α) = 3 := by
  classical
  refine le_antisymm ?_ three_le_egirth
  obtain ⟨s, hcard⟩ := Cardinal.exists_finset_eq_card <| Cardinal.ofNat_le_toENat.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := s.card_eq_three.mp hcard.symm
  set w : Walk ⊤ x x := .cons hxy <| .cons hyz <| .cons hxz.symm .nil with hw
  have : w.IsCycle :=
    { edges_nodup := by aesop
      ne_nil := by aesop
      support_nodup := by aesop }
  grw [egirth_le_length this]
  simp [hw]

@[gcongr only]
/-
**SimpleGraph.IsContained.egirth_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCon
tained`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {G' : SimpleGraph β}, 
G.IsContained G' → G'.egirth ≤ G.egirth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsAcyclic.egirth_eq_top`：∀ {α : Type u_1} {G : SimpleGraph α
}, G.IsAcyclic → G.egirth = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.exists_egirth_eq_length`：exists_egirth_eq_length : (exists (
a : α) (w : G.Walk a a), w.IsCycle ∧ G.egirth = w.length) ↔ ¬ G.IsAcyclic
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用引理 `SimpleGraph.egirth_le_length`：egirth_le_length {a} {w : G.Walk a a} (h :
 w.IsCycle) : G.egirth <= w.length
· 使用定理 `SimpleGraph.Walk.IsCycle.map`：∀ {V : Type u} {V' : Type v} {G : SimpleGr
aph V} {G' : SimpleGraph V'} {f : G →g G'} {u : V} {p : G.Walk u u},   Function.
Injective ⇑f → p.I…
· 使用引理 `SimpleGraph.Copy.injective`：injective (f : Copy A B) : Injective f.toHom
-/
lemma IsContained.egirth_le (h : G ⊑ G') : G'.egirth ≤ G.egirth := by
  by_cases hacyc : G.IsAcyclic
  · simp [hacyc.egirth_eq_top]
  obtain ⟨a, w, hw, hwl⟩ := exists_egirth_eq_length.mpr hacyc
  rw [hwl, ← w.length_map h.some.toHom]
  exact egirth_le_length <| hw.map h.some.injective

@[gcongr only]
/-
**SimpleGraph.Iso.egirth_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {G' : SimpleGraph β} (
f : G ≃g G'), G.egirth = G'.egirth
参数：f : G ≃g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.IsContained.egirth_le`：∀ {α : Type u_1} {β : Type u_2} {G : 
SimpleGraph α} {G' : SimpleGraph β}, G.IsContained G' → G'.egirth ≤ G.egirth
· 使用定理 `SimpleGraph.Iso.isContained'`：∀ {V : Type u_1} {W : Type u_2} {G : Simpl
eGraph V} {H : SimpleGraph W} (e : G ≃g H), H.IsContained G
· 使用定理 `SimpleGraph.Iso.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simple
Graph V} {H : SimpleGraph W} (e : G ≃g H), G.IsContained H
-/
lemma Iso.egirth_eq (f : G ≃g G') : G.egirth = G'.egirth :=
  le_antisymm f.isContained'.egirth_le f.isContained.egirth_le

end egirth

section girth


/--
The girth of a simple graph is the length of its smallest cycle, or junk value `0` if the graph is
acyclic.
-/
/-
**SimpleGraph.girth** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：girth (G : SimpleGraph α) : Nat
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The girth of a simple graph is the length of its smallest cycle, or junk value `
0` if the graph is
acyclic.
-/
noncomputable def girth (G : SimpleGraph α) : ℕ :=
  G.egirth.toNat
/-
**SimpleGraph.girth_le_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：girth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.girth <= w.length
参数：h : w.IsCycle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENat.natCast_toNat_le_self`：natCast_toNat_le_self (n : Nat∞) : ↑(toNat n
) <= n
· 使用引理 `SimpleGraph.egirth_le_length`：egirth_le_length {a} {w : G.Walk a a} (h :
 w.IsCycle) : G.egirth <= w.length
-/
lemma girth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.girth ≤ w.length :=
  ENat.natCast_le_natCast.mp <| G.egirth.natCast_toNat_le_self.trans <| egirth_le_length h
/-
**SimpleGraph.three_le_girth** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：three_le_girth (hG : ¬ G.IsAcyclic) : 3 <= G.girth
参数：hG : ¬ G.IsAcyclic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_toNat`：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n !=
 ⊤) : toNat m <= toNat n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SimpleGraph.three_le_egirth`：three_le_egirth : 3 <= G.egirth
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.egirth_eq_top`：egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic
-/
lemma three_le_girth (hG : ¬ G.IsAcyclic) : 3 ≤ G.girth :=
  ENat.toNat_le_toNat three_le_egirth <| egirth_eq_top.not.mpr hG
/-
**SimpleGraph.girth_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：girth_eq_zero : G.girth = 0 ↔ G.IsAcyclic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `SimpleGraph.three_le_girth`：three_le_girth (hG : ¬ G.IsAcyclic) : 3 <= G
.girth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma girth_eq_zero : G.girth = 0 ↔ G.IsAcyclic :=
  ⟨fun h ↦ not_not.mp <| three_le_girth.mt <| by lia, fun h ↦ by simp [girth, h]⟩

protected alias ⟨_, IsAcyclic.girth_eq_zero⟩ := girth_eq_zero
/-
**SimpleGraph.girth_anti** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：girth_anti {G' : SimpleGraph α} (hab : G <= G') (h : ¬ G.IsAcyclic) : G'.g
irth <= G.girth
参数：hab : G <= G'；h : ¬ G.IsAcyclic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_toNat`：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n !=
 ⊤) : toNat m <= toNat n
· 使用引理 `SimpleGraph.egirth_anti`：egirth_anti : Antitone (egirth : SimpleGraph α 
-> Nat∞)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.egirth_eq_top`：egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic
-/
lemma girth_anti {G' : SimpleGraph α} (hab : G ≤ G') (h : ¬ G.IsAcyclic) : G'.girth ≤ G.girth :=
  ENat.toNat_le_toNat (egirth_anti hab) <| egirth_eq_top.not.mpr h
/-
**SimpleGraph.Walk.IsCircuit.girth_le_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {a : α} {w : G.Walk a a}, w.IsCircuit
 → G.girth ≤ w.length
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENat.natCast_toNat_le_self`：natCast_toNat_le_self (n : Nat∞) : ↑(toNat n
) <= n
· 使用定理 `SimpleGraph.Walk.IsCircuit.egirth_le_length`：∀ {α : Type u_1} {G : Simpl
eGraph α} {a : α} {w : G.Walk a a}, w.IsCircuit → G.egirth ≤ ↑w.length
-/
lemma Walk.IsCircuit.girth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.girth ≤ w.length :=
  ENat.natCast_le_natCast.mp <| G.egirth.natCast_toNat_le_self.trans <| hwc.egirth_le_length
/-
**SimpleGraph.exists_girth_eq_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_girth_eq_length : (exists (a : α) (w : G.Walk a a), w.IsCycle ∧ G.g
irth = w.length) ↔ ¬ G.IsAcyclic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.exists_egirth_eq_length`：exists_egirth_eq_length : (exists (
a : α) (w : G.Walk a a), w.IsCycle ∧ G.egirth = w.length) ↔ ¬ G.IsAcyclic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma exists_girth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.girth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨by tauto, fun h ↦ ?_⟩
  obtain ⟨_, _, _⟩ := exists_egirth_eq_length.mpr h
  simp_all only [girth, ENat.toNat_natCast]
  tauto
/-
**SimpleGraph.girth_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1}, ⊥.girth = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.egirth_bot`：∀ {α : Type u_1}, ⊥.egirth = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma girth_bot : girth (⊥ : SimpleGraph α) = 0 := by
  simp [girth]
/-
**SimpleGraph.girth_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：girth_top (h : 3 <= ENat.card α) : girth (⊤ : SimpleGraph α) = 3
参数：h : 3 <= ENat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.egirth_top`：egirth_top (h : 3 <= ENat.card α) : egirth (⊤ : 
SimpleGraph α) = 3
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem girth_top (h : 3 ≤ ENat.card α) : girth (⊤ : SimpleGraph α) = 3 := by
  simp [girth, egirth_top h]
/-
**SimpleGraph.IsContained.girth_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCont
ained`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {G' : SimpleGraph β}, 
  G.IsContained G' → ¬G.IsAcyclic → G'.girth ≤ G.girth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_toNat`：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n !=
 ⊤) : toNat m <= toNat n
· 使用定理 `SimpleGraph.IsContained.egirth_le`：∀ {α : Type u_1} {β : Type u_2} {G : 
SimpleGraph α} {G' : SimpleGraph β}, G.IsContained G' → G'.egirth ≤ G.egirth
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.egirth_eq_top`：egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic
-/
lemma IsContained.girth_le (h : G ⊑ G') (hG : ¬G.IsAcyclic) : G'.girth ≤ G.girth :=
  ENat.toNat_le_toNat h.egirth_le <| egirth_eq_top.not.mpr hG
/-
**SimpleGraph.Iso.girth_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {G' : SimpleGraph β} (
f : G ≃g G'), G.girth = G'.girth
参数：f : G ≃g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Iso.egirth_eq`：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGr
aph α} {G' : SimpleGraph β} (f : G ≃g G'), G.egirth = G'.egirth
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Iso.girth_eq (f : G ≃g G') : G.girth = G'.girth := by
  simp [girth, f.egirth_eq]

end girth

end SimpleGraph

