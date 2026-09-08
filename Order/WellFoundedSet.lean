/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sigma.Lex
public import Mathlib.Order.RelIso.Set
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Tactic.TFAE

/-!
# Well-founded sets

This file introduces versions of `WellFounded` and `WellQuasiOrdered` for sets.

## Main Definitions

* `Set.WellFoundedOn s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
* `Set.IsWF s` indicates that `<` is well-founded when restricted to `s`.
* `Set.PartiallyWellOrderedOn s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
* `Set.IsPWO s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results

* Higman's Lemma, `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`,
  shows that if `r` is partially well-ordered on `s`, then `List.SublistForall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
* `Set.wellFoundedOn_iff` relates `well_founded_on` to the well-foundedness of a relation on the
  original type, to avoid dealing with subtypes.
* `Set.IsWF.mono` shows that a subset of a well-founded subset is well-founded.
* `Set.IsWF.union` shows that the union of two well-founded subsets is well-founded.
* `Finset.isWF` shows that all `Finset`s are well-founded.

## TODO

* Prove that `s` is partially well-ordered iff it has no infinite descending chain or antichain.
* Rename `Set.PartiallyWellOrderedOn` to `Set.WellQuasiOrderedOn` and `Set.IsPWO` to `Set.IsWQO`.

## References
* [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
* [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/

@[expose] public section

assert_not_exists IsOrderedRing

open scoped Function -- required for scoped `on` notation

variable {ι α β γ : Type*} {π : ι → Type*}

namespace Set

/-! ### Relations well-founded on sets -/

/-- `s.WellFoundedOn r` indicates that the relation `r` is `WellFounded` when restricted to `s`. -/
/-
**Set.WellFoundedOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：WellFoundedOn (s : Set α) (r : α -> α -> Prop) : Prop
参数：s : Set α；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.WellFoundedOn r` indicates that the relation `r` is `WellFounded` when restri
cted to `s`.
-/
def WellFoundedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded (Subrel r (· ∈ s))

@[simp]
/-
**Set.wellFoundedOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_empty (r : α -> α -> Prop) : WellFoundedOn ∅ r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellFounded_of_isEmpty`：wellFounded_of_isEmpty {α} [IsEmpty α] (r : α ->
 α -> Prop) : WellFounded r
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem wellFoundedOn_empty (r : α → α → Prop) : WellFoundedOn ∅ r :=
  wellFounded_of_isEmpty _

section WellFoundedOn

variable {r r' : α → α → Prop}

section AnyRel

variable {f : β → α} {s t : Set α} {x y : α}

/-
**Set.wellFoundedOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_iff : s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧
 a in s ∧ b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `WellFounded.wellFounded_iff_has_min`：wellFounded_iff_has_min {r : α -> α
 -> Prop} : WellFounded r ↔ forall s : Set α, s.Nonempty -> exists m in s, foral
l x in s, ¬r x m
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_coe_nonempty`：preimage_coe_nonempty {s t : Set α} : (((
↑) : s -> α) ⁻¹' t).Nonempty ↔ (s inter t).Nonempty
· 使用定理 `RelEmbedding.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s), WellFounded s → WellFounded r
-/
theorem wellFoundedOn_iff :
    s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s := by
  have f : RelEmbedding (Subrel r (· ∈ s)) fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
    ⟨⟨(↑), Subtype.coe_injective⟩, by simp⟩
  refine ⟨fun h => ?_, f.wellFounded⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hst : (s ∩ t).Nonempty
  · rw [← Subtype.preimage_coe_nonempty] at hst
    rcases h.has_min (Subtype.val ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, _⟩ => hm ⟨x, xs⟩ xt xm⟩
  · rcases ht with ⟨m, mt⟩
    exact ⟨m, mt, fun x _ ⟨_, _, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩

@[simp]
/-
**Set.wellFoundedOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_univ : (univ : Set α).WellFoundedOn r ↔ WellFounded r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wellFoundedOn_univ : (univ : Set α).WellFoundedOn r ↔ WellFounded r := by
  simp [wellFoundedOn_iff]
/-
**Set._root_.WellFounded.wellFoundedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WellFounded.wellFoundedOn : WellFounded r → s.WellFoundedOn r :=
  InvImage.wf _

@[simp]
/-
**Set.wellFoundedOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_range : (range f).WellFoundedOn r ↔ WellFounded (r on f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.mono`：mono (hr : WellFounded r) (h : forall a b, r' a b -> r
 a b) : WellFounded r'
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Acc.of_downward_closed`：∀ {α : Type u_1} {β : Type u_2} {rβ : β → β → Pr
op} (f : α → β),   (∀ {a : α} {b : β}, rβ b (f a) → ∃ c, f c = b) → ∀ (a : α), A
cc (InvImage…
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
-/
theorem wellFoundedOn_range : (range f).WellFoundedOn r ↔ WellFounded (r on f) := by
  let f' : β → range f := fun c => ⟨f c, c, rfl⟩
  refine ⟨fun h => (InvImage.wf f' h).mono fun c c' => id, fun h => ⟨?_⟩⟩
  rintro ⟨_, c, rfl⟩
  refine Acc.of_downward_closed f' ?_ _ ?_
  · rintro _ ⟨_, c', rfl⟩ -
    exact ⟨c', rfl⟩
  · exact h.apply _

@[simp]
/-
**Set.wellFoundedOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_image {s : Set β} : (f '' s).WellFoundedOn r ↔ s.WellFounded
On (r on f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.wellFoundedOn_range`：wellFoundedOn_range : (range f).WellFoundedOn r
 ↔ WellFounded (r on f)
-/
theorem wellFoundedOn_image {s : Set β} : (f '' s).WellFoundedOn r ↔ s.WellFoundedOn (r on f) := by
  rw [image_eq_range]; exact wellFoundedOn_range

namespace WellFoundedOn

/-
**Set.WellFoundedOn.induction** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α} {x : α},   s.WellFoundedOn
 r → x ∈ s → ∀ {P : α → Prop}, (∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) → P x
参数：∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem induction (hs : s.WellFoundedOn r) (hx : x ∈ s) {P : α → Prop}
    (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x := by
  let Q : s → Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine WellFounded.induction hs ⟨x, hx⟩ ?_
  simpa only [Subtype.forall]
/-
**Set.WellFoundedOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：∀ {α : Type u_2} {r r' : α → α → Prop} {s t : Set α}, t.WellFoundedOn r' →
 r ≤ r' → s ⊆ t → s.WellFoundedOn r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.wellFoundedOn_iff`：wellFoundedOn_iff : s.WellFoundedOn r ↔ WellFound
ed fun a b : α => r a b ∧ a in s ∧ b in s
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem mono (h : t.WellFoundedOn r') (hle : r ≤ r') (hst : s ⊆ t) :
    s.WellFoundedOn r := by
  rw [wellFoundedOn_iff] at *
  exact Subrelation.wf (fun xy => ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩) h
/-
**Set.WellFoundedOn.mono'** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：mono' (h : forall (a) (_ : a in s) (b) (_ : b in s), r' a b -> r a b) : s.
WellFoundedOn r -> s.WellFoundedOn r'
参数：h : forall (a) (_ : a in s) (b) (_ : b in s), r' a b -> r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mono' (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), r' a b → r a b) :
    s.WellFoundedOn r → s.WellFoundedOn r' :=
  Subrelation.wf @fun a b => h _ a.2 _ b.2
/-
**Set.WellFoundedOn.subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：subset (h : t.WellFoundedOn r) (hst : s subseteq t) : s.WellFoundedOn r
参数：h : t.WellFoundedOn r；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.WellFoundedOn.mono`：∀ {α : Type u_2} {r r' : α → α → Prop} {s t : Se
t α}, t.WellFoundedOn r' → r ≤ r' → s ⊆ t → s.WellFoundedOn r
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem subset (h : t.WellFoundedOn r) (hst : s ⊆ t) : s.WellFoundedOn r :=
  h.mono le_rfl hst

open Relation

open List in
/-- `a` is accessible under the relation `r` iff `r` is well-founded on the downward transitive
closure of `a` under `r` (including `a` or not). -/
/-
**Set.WellFoundedOn.acc_iff_wellFoundedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFou
ndedOn`。
形式化陈述：acc_iff_wellFoundedOn {α} {r : α -> α -> Prop} {a : α} : TFAE [Acc r a, We
llFoundedOn { b | ReflTransGen r b a } r, WellFoundedOn { b | TransGen r b a } r
]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.accessible`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} {a :
 α} (f : α → β), Acc r (f a) → Acc (InvImage r f) a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `acc_transGen_iff`：∀ {α : Sort u_1} {r : α → α → Prop} {a : α}, Acc (Rela
tion.TransGen r) a ↔ Acc r a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `Set.WellFoundedOn.subset`：subset (h : t.WellFoundedOn r) (hst : s subset
eq t) : s.WellFoundedOn r
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `Acc.of_fibration`：∀ {α : Type u_1} {β : Type u_2} {rα : α → α → Prop} {r
β : β → β → Prop} (f : α → β),   Relation.Fibration rα rβ f → ∀ {a : α}, Acc rα 
a → Ac…
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
`a` is accessible under the relation `r` iff `r` is well-founded on the downward
 transitive
closure of `a` under `r` (including `a` or not).
-/
theorem acc_iff_wellFoundedOn {α} {r : α → α → Prop} {a : α} :
    TFAE [Acc r a,
      WellFoundedOn { b | ReflTransGen r b a } r,
      WellFoundedOn { b | TransGen r b a } r] := by
  tfae_have 1 → 2 := by
    refine fun h => ⟨fun b => InvImage.accessible Subtype.val ?_⟩
    rw [← acc_transGen_iff] at h ⊢
    obtain h' | h' := reflTransGen_iff_eq_or_transGen.1 b.2
    · rwa [h'] at h
    · exact h.inv h'
  tfae_have 2 → 3 := fun h => h.subset fun _ => TransGen.to_reflTransGen
  tfae_have 3 → 1 := by
    refine fun h => Acc.intro _ (fun b hb => (h.apply ⟨b, .single hb⟩).of_fibration Subtype.val ?_)
    exact fun ⟨c, hc⟩ d h => ⟨⟨d, .head h hc⟩, h, rfl⟩
  tfae_finish

end WellFoundedOn

end AnyRel

section IsStrictOrder

variable [IsStrictOrder α r] {s t : Set α}

/-
**Set.IsStrictOrder.subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsStrictOrder`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] {s : Set α}, IsStr
ictOrder α fun a b => r a b ∧ a ∈ s ∧ b ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `IsStrictOrder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsS
trictOrder α r], IsTrans α r
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance IsStrictOrder.subset : IsStrictOrder α fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s where
  toIrrefl := ⟨fun a con => irrefl_of r a con.1⟩
  toIsTrans := ⟨fun _ _ _ ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩
/-
**Set.wellFoundedOn_iff_no_descending_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_iff_no_descending_seq : s.WellFoundedOn r ↔ forall f : ((· >
 ·) : Nat -> Nat -> Prop) ↪r r, ¬forall n, f n in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.IsStrictOrder.subset`：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictO
rder α r] {s : Set α}, IsStrictOrder α fun a b => r a b ∧ a ∈ s ∧ b ∈ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem wellFoundedOn_iff_no_descending_seq :
    s.WellFoundedOn r ↔ ∀ f : ((· > ·) : ℕ → ℕ → Prop) ↪r r, ¬∀ n, f n ∈ s := by
  simp only [wellFoundedOn_iff, RelEmbedding.wellFounded_iff_isEmpty, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : ∀ n, f n ∈ s := fun n => (hf.2 n.lt_succ_self).2.2
    refine ⟨⟨f, ?_⟩, H⟩
    simpa only [H, and_true] using @hf
  · rintro ⟨⟨f, hf⟩, hfs : ∀ n, f n ∈ s⟩
    refine ⟨⟨f, ?_⟩⟩
    simpa only [hfs, and_true] using @hf
/-
**Set.WellFoundedOn.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] {s t : Set α},   s
.WellFoundedOn r → t.WellFoundedOn r → (s ∪ t).WellFoundedOn r
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.wellFoundedOn_iff_no_descending_seq`：wellFoundedOn_iff_no_descending
_seq : s.WellFoundedOn r ↔ forall f : ((· > ·) : Nat -> Nat -> Prop) ↪r r, ¬fora
ll n, f n in s
· 使用定理 `Nat.exists_subseq_of_forall_mem_union`：exists_subseq_of_forall_mem_union
 {s t : Set α} (e : Nat -> α) (he : forall n, e n in s union t) : exists g : Nat
 ↪o Nat, (forall n, e (g n)…
-/
theorem WellFoundedOn.union (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r) :
    (s ∪ t).WellFoundedOn r := by
  rw [wellFoundedOn_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts [hs (g.dual.ltEmbedding.trans f) hg, ht (g.dual.ltEmbedding.trans f) hg]

@[simp]
/-
**Set.wellFoundedOn_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_union : (s union t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.
WellFoundedOn r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.WellFoundedOn.subset`：subset (h : t.WellFoundedOn r) (hst : s subset
eq t) : s.WellFoundedOn r
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.WellFoundedOn.union`：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOr
der α r] {s t : Set α},   s.WellFoundedOn r → t.WellFoundedOn r → (s ∪ t).WellFo
undedOn r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem wellFoundedOn_union : (s ∪ t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r :=
  ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun h =>
    h.1.union h.2⟩

end IsStrictOrder

end WellFoundedOn

/-! ### Sets well-founded w.r.t. the strict inequality -/

section LT

variable [LT α] {s t : Set α}

/-- `s.IsWF` indicates that `<` is well-founded when restricted to `s`. -/
/-
**Set.IsWF** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：IsWF (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.IsWF` indicates that `<` is well-founded when restricted to `s`.
-/
def IsWF (s : Set α) : Prop :=
  WellFoundedOn s (· < ·)

@[simp]
/-
**Set.isWF_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isWF_empty : IsWF (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellFounded_of_isEmpty`：wellFounded_of_isEmpty {α} [IsEmpty α] (r : α ->
 α -> Prop) : WellFounded r
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem isWF_empty : IsWF (∅ : Set α) :=
  wellFounded_of_isEmpty _
/-
**Set.IsWF.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : LT α] {s t : Set α}, t.IsWF → s ⊆ t → s.IsWF
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.WellFoundedOn.subset`：subset (h : t.WellFoundedOn r) (hst : s subset
eq t) : s.WellFoundedOn r
-/
theorem IsWF.mono (h : IsWF t) (st : s ⊆ t) : IsWF s := h.subset st
/-
**Set.isWF_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isWF_univ_iff : IsWF (univ : Set α) ↔ WellFoundedLT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isWF_univ_iff : IsWF (univ : Set α) ↔ WellFoundedLT α := by
  simp [IsWF, wellFoundedOn_iff, isWellFounded_iff]
/-
**Set.IsWF.of_wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : LT α] [h : WellFoundedLT α] (s : Set α), s.IsWF
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsWF.mono`：∀ {α : Type u_2} [inst : LT α] {s t : Set α}, t.IsWF → s 
⊆ t → s.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.isWF_univ_iff`：isWF_univ_iff : IsWF (univ : Set α) ↔ WellFoundedLT α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem IsWF.of_wellFoundedLT [h : WellFoundedLT α] (s : Set α) : s.IsWF :=
  (Set.isWF_univ_iff.2 h).mono s.subset_univ

end LT

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

protected nonrec theorem IsWF.union (hs : IsWF s) (ht : IsWF t) : IsWF (s ∪ t) := hs.union ht

/-
**Set.isWF_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, (s ∪ t).IsWF ↔ s.IsWF 
∧ t.IsWF
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.wellFoundedOn_union`：wellFoundedOn_union : (s union t).WellFoundedOn
 r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
-/
@[simp] theorem isWF_union : IsWF (s ∪ t) ↔ IsWF s ∧ IsWF t := wellFoundedOn_union

end Preorder

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

/-
**Set.isWF_iff_no_descending_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isWF_iff_no_descending_seq : IsWF s ↔ forall f : Nat -> α, StrictAnti f ->
 ¬forall n, f n in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.wellFoundedOn_iff_no_descending_seq`：wellFoundedOn_iff_no_descending
_seq : s.WellFoundedOn r ↔ forall f : ((· > ·) : Nat -> Nat -> Prop) ↪r r, ¬fora
ll n, f n in s
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem isWF_iff_no_descending_seq :
    IsWF s ↔ ∀ f : ℕ → α, StrictAnti f → ¬∀ n, f n ∈ s :=
  wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.injective⟩, hf.lt_iff_gt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩

end Preorder

/-! ### Partially well-ordered sets -/

/-- `s.PartiallyWellOrderedOn r` indicates that the relation `r` is `WellQuasiOrdered` when
restricted to `s`.

A set is partially well-ordered by a relation `r` when any infinite sequence contains two elements
where the first is related to the second by `r`. Equivalently, any antichain (see `IsAntichain`) is
finite, see `Set.partiallyWellOrderedOn_iff_finite_antichains`.

TODO: rename this to `WellQuasiOrderedOn` to match `WellQuasiOrdered`. -/
/-
**Set.PartiallyWellOrderedOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：PartiallyWellOrderedOn (s : Set α) (r : α -> α -> Prop) : Prop
参数：s : Set α；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.PartiallyWellOrderedOn r` indicates that the relation `r` is `WellQuasiOrdere
d` when
restricted to `s`.

A set is partially well-ordered by a relation `r` when any infinite sequence con
tains two elements
where the first is related to the second by `r`. Equivalently, any antichain (se
e `IsAntichain`) is
finite, see `Set.partiallyWellOrderedOn_iff_finite_antichains`.

TODO: rename this to `WellQuasiOrderedOn` to match `WellQuasiOrdered`.
-/
def PartiallyWellOrderedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellQuasiOrdered (Subrel r (· ∈ s))

section PartiallyWellOrderedOn

variable {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α} {t : Set α} {a : α}

/-
**Set.PartiallyWellOrderedOn.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set.PartiallyW
ellOrderedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α},   s.PartiallyWellOrderedO
n r → ∀ {f : ℕ → α}, (∀ (n : ℕ), f n ∈ s) → ∃ m n, m < n ∧ r (f m) (f n)
参数：∀ (n : ℕ), f n ∈ s；f m；f n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PartiallyWellOrderedOn.exists_lt (hs : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ n, f n ∈ s) : ∃ m n, m < n ∧ r (f m) (f n) :=
  hs fun n ↦ ⟨_, hf n⟩
/-
**Set.partiallyWellOrderedOn_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partiallyWellOrderedOn_iff_exists_lt : s.PartiallyWellOrderedOn r ↔ forall
 f : Nat -> α, (forall n, f n in s) -> exists m n, m < n ∧ r (f m) (f n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.exists_lt`：∀ {α : Type u_2} {r : α → α → Prop
} {s : Set α},   s.PartiallyWellOrderedOn r → ∀ {f : ℕ → α}, (∀ (n : ℕ), f n ∈ s
) → ∃ m n, m < n ∧ r (f m)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem partiallyWellOrderedOn_iff_exists_lt : s.PartiallyWellOrderedOn r ↔
    ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ m n, m < n ∧ r (f m) (f n) :=
  ⟨PartiallyWellOrderedOn.exists_lt, fun hf f ↦ hf _ fun n ↦ (f n).2⟩
/-
**Set.partiallyWellOrderedOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partiallyWellOrderedOn_univ_iff : univ.PartiallyWellOrderedOn r ↔ WellQuas
iOrdered r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.wellQuasiOrdered_iff`：RelIso.wellQuasiOrdered_iff {α β} {r : α ->
 α -> Prop} {s : β -> β -> Prop} (f : r ≃r s) : WellQuasiOrdered r ↔ WellQuasiOr
dered s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem partiallyWellOrderedOn_univ_iff : univ.PartiallyWellOrderedOn r ↔ WellQuasiOrdered r :=
  (RelIso.subrelUnivIso (by simp)).wellQuasiOrdered_iff
/-
**Set.PartiallyWellOrderedOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.PartiallyWellOr
deredOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s t : Set α}, t.PartiallyWellOrderedO
n r → s ⊆ t → s.PartiallyWellOrderedOn r
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s ⊆ t) :
    s.PartiallyWellOrderedOn r :=
  fun f ↦ ht (Set.inclusion h ∘ f)
/-
**Set.partiallyWellOrderedOn_of_wellQuasiOrdered** 是 Mathlib 中的一个定理，位于命名空间 `Set`
。
形式化陈述：partiallyWellOrderedOn_of_wellQuasiOrdered (h : WellQuasiOrdered r) (s : S
et α) : s.PartiallyWellOrderedOn r
参数：h : WellQuasiOrdered r；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.mono`：∀ {α : Type u_2} {r : α → α → Prop} {s 
t : Set α}, t.PartiallyWellOrderedOn r → s ⊆ t → s.PartiallyWellOrderedOn r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.partiallyWellOrderedOn_univ_iff`：partiallyWellOrderedOn_univ_iff : u
niv.PartiallyWellOrderedOn r ↔ WellQuasiOrdered r
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem partiallyWellOrderedOn_of_wellQuasiOrdered (h : WellQuasiOrdered r) (s : Set α) :
    s.PartiallyWellOrderedOn r :=
  (partiallyWellOrderedOn_univ_iff.mpr h).mono s.subset_univ

@[simp]
/-
**Set.partiallyWellOrderedOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partiallyWellOrderedOn_empty (r : α -> α -> Prop) : PartiallyWellOrderedOn
 ∅ r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellQuasiOrdered_of_isEmpty`：wellQuasiOrdered_of_isEmpty [IsEmpty α] (r 
: α -> α -> Prop) : WellQuasiOrdered r
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem partiallyWellOrderedOn_empty (r : α → α → Prop) : PartiallyWellOrderedOn ∅ r :=
  wellQuasiOrdered_of_isEmpty _
/-
**Set.PartiallyWellOrderedOn.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.PartiallyWellO
rderedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s t : Set α},   s.PartiallyWellOrdere
dOn r → t.PartiallyWellOrderedOn r → (s ∪ t).PartiallyWellOrderedOn r
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_subseq_of_forall_mem_union`：exists_subseq_of_forall_mem_union
 {s t : Set α} (e : Nat -> α) (he : forall n, e n in s union t) : exists g : Nat
 ↪o Nat, (forall n, e (g n)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.PartiallyWellOrderedOn.exists_lt`：∀ {α : Type u_2} {r : α → α → Prop
} {s : Set α},   s.PartiallyWellOrderedOn r → ∀ {f : ℕ → α}, (∀ (n : ℕ), f n ∈ s
) → ∃ m n, m < n ∧ r (f m)…
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem PartiallyWellOrderedOn.union (hs : s.PartiallyWellOrderedOn r)
    (ht : t.PartiallyWellOrderedOn r) : (s ∪ t).PartiallyWellOrderedOn r := by
  intro f
  obtain ⟨g, hgs | hgt⟩ := Nat.exists_subseq_of_forall_mem_union _ fun x ↦ (f x).2
  · rcases hs.exists_lt hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
  · rcases ht.exists_lt hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩

@[simp]
/-
**Set.partiallyWellOrderedOn_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partiallyWellOrderedOn_union : (s union t).PartiallyWellOrderedOn r ↔ s.Pa
rtiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.mono`：∀ {α : Type u_2} {r : α → α → Prop} {s 
t : Set α}, t.PartiallyWellOrderedOn r → s ⊆ t → s.PartiallyWellOrderedOn r
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.PartiallyWellOrderedOn.union`：∀ {α : Type u_2} {r : α → α → Prop} {s
 t : Set α},   s.PartiallyWellOrderedOn r → t.PartiallyWellOrderedOn r → (s ∪ t)
.PartiallyWellOrderedO…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem partiallyWellOrderedOn_union :
    (s ∪ t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h ↦ h.1.union h.2⟩
/-
**Set.PartiallyWellOrderedOn.image_of_monotone_on** 是 Mathlib 中的一个定理，位于命名空间 `Set
.PartiallyWellOrderedOn`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → α → Prop} {r' : β → β → Prop} {f 
: α → β} {s : Set α},   s.PartiallyWellOrderedOn r → (∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a
₂ → r' (f a₁) (f a₂)) → (f '' s).PartiallyWellOrderedOn r'
参数：∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a₂ → r' (f a₁) (f a₂)；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_lt`：partiallyWellOrderedOn_iff_exi
sts_lt : s.PartiallyWellOrderedOn r ↔ forall f : Nat -> α, (forall n, f n in s) 
-> exists m n, m < n ∧ r (f m)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem PartiallyWellOrderedOn.image_of_monotone_on (hs : s.PartiallyWellOrderedOn r)
    (hf : ∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a₂ → r' (f a₁) (f a₂)) : (f '' s).PartiallyWellOrderedOn r' := by
  rw [partiallyWellOrderedOn_iff_exists_lt] at *
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g' := funext heq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩

-- TODO: prove this in terms of `IsAntichain.finite_of_wellQuasiOrdered`
/-
**Set._root_.IsAntichain.finite_of_partiallyWellOrderedOn** 是 Mathlib 中的一个定理，位于命
名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsAntichain.finite_of_partiallyWellOrderedOn (ha : IsAntichain r s)
    (hp : s.PartiallyWellOrderedOn r) : s.Finite := by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hp (hi.natEmbedding _)
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    ha.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

section Refl
variable [Std.Refl r]

/-
**Set.Finite.partiallyWellOrderedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α} [Std.Refl r], s.Finite → s
.PartiallyWellOrderedOn r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.wellQuasiOrdered`：Finite.wellQuasiOrdered (r : α -> α -> Prop) [F
inite α] [Std.Refl r] : WellQuasiOrdered r
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Subrel.instReflSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [Std.Refl r]
 (p : α → Prop), Std.Refl (Subrel r p)
-/
protected theorem Finite.partiallyWellOrderedOn (hs : s.Finite) : s.PartiallyWellOrderedOn r :=
  hs.to_subtype.wellQuasiOrdered _
/-
**Set._root_.IsAntichain.partiallyWellOrderedOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `S
et`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsAntichain.partiallyWellOrderedOn_iff (hs : IsAntichain r s) :
    s.PartiallyWellOrderedOn r ↔ s.Finite :=
  ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩

@[simp]
/-
**Set.partiallyWellOrderedOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partiallyWellOrderedOn_singleton (a : α) : PartiallyWellOrderedOn {a} r
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → α → Prop} {
s : Set α} [Std.Refl r], s.Finite → s.PartiallyWellOrderedOn r
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem partiallyWellOrderedOn_singleton (a : α) : PartiallyWellOrderedOn {a} r :=
  (finite_singleton a).partiallyWellOrderedOn

@[nontriviality]
/-
**Set.Subsingleton.partiallyWellOrderedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsing
leton`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α} [Std.Refl r], s.Subsinglet
on → s.PartiallyWellOrderedOn r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → α → Prop} {
s : Set α} [Std.Refl r], s.Finite → s.PartiallyWellOrderedOn r
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
theorem Subsingleton.partiallyWellOrderedOn (hs : s.Subsingleton) : PartiallyWellOrderedOn s r :=
  hs.finite.partiallyWellOrderedOn

@[simp]
/-
**Set.partiallyWellOrderedOn_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partiallyWellOrderedOn_insert : PartiallyWellOrderedOn (insert a s) r ↔ Pa
rtiallyWellOrderedOn s r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem partiallyWellOrderedOn_insert :
    PartiallyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r := by
  simp only [← singleton_union, partiallyWellOrderedOn_union,
    partiallyWellOrderedOn_singleton, true_and]
/-
**Set.PartiallyWellOrderedOn.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.PartiallyWell
OrderedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α} [Std.Refl r],   s.Partiall
yWellOrderedOn r → ∀ (a : α), (insert a s).PartiallyWellOrderedOn r
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.partiallyWellOrderedOn_insert`：partiallyWellOrderedOn_insert : Parti
allyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r
-/
protected theorem PartiallyWellOrderedOn.insert (h : PartiallyWellOrderedOn s r) (a : α) :
    PartiallyWellOrderedOn (insert a s) r :=
  partiallyWellOrderedOn_insert.2 h
/-
**Set.partiallyWellOrderedOn_iff_finite_antichains** 是 Mathlib 中的一个定理，位于命名空间 `Se
t`。
形式化陈述：partiallyWellOrderedOn_iff_finite_antichains [Std.Symm r] : s.PartiallyWel
lOrderedOn r ↔ forall t, t subseteq s -> IsAntichain r t -> t.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.finite_of_partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → 
α → Prop} {s : Set α}, IsAntichain r s → s.PartiallyWellOrderedOn r → s.Finite
· 使用定理 `Set.PartiallyWellOrderedOn.mono`：∀ {α : Type u_2} {r : α → α → Prop} {s 
t : Set α}, t.PartiallyWellOrderedOn r → s ⊆ t → s.PartiallyWellOrderedOn r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_lt`：partiallyWellOrderedOn_iff_exi
sts_lt : s.PartiallyWellOrderedOn r ↔ forall f : Nat -> α, (forall n, f n in s) 
-> exists m n, m < n ∧ r (f m)…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem partiallyWellOrderedOn_iff_finite_antichains [Std.Symm r] :
    s.PartiallyWellOrderedOn r ↔ ∀ t, t ⊆ s → IsAntichain r t → t.Finite := by
  refine ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), ?_⟩
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro hs f hf
  by_contra! H
  refine infinite_range_of_injective (fun m n hmn => ?_) (hs _ (range_subset_iff.2 hf) ?_)
  · obtain h | h | h := lt_trichotomy m n
    · refine (H _ _ h ?_).elim
      rw [hmn]
      exact refl _
    · exact h
    · refine (H _ _ h ?_).elim
      rw [hmn]
      exact refl _
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn
  obtain h | h := (ne_of_apply_ne _ hmn).lt_or_gt
  · exact H _ _ h
  · exact mt symm (H _ _ h)

end Refl

section IsPreorder
variable [IsPreorder α r]

/-
**Set.PartiallyWellOrderedOn.exists_monotone_subseq** 是 Mathlib 中的一个定理，位于命名空间 `S
et.PartiallyWellOrderedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α} [IsPreorder α r],   s.Part
iallyWellOrderedOn r → ∀ {f : ℕ → α}, (∀ (n : ℕ), f n ∈ s) → ∃ g, ∀ (m n : ℕ), m
 ≤ n → r (f (g m)) (f (g n))
参数：∀ (n : ℕ), f n ∈ s；m n : ℕ；f (g m)；f (g n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrdered.exists_monotone_subseq`：WellQuasiOrdered.exists_monoton
e_subseq [IsPreorder α r] (h : WellQuasiOrdered r) (f : Nat -> α) : exists g : N
at ↪o Nat, forall m n, m <= n…
· 使用定理 `Subrel.instIsPreorderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsPre
order α r] (p : α → Prop), IsPreorder (Subtype p) (Subrel r p)
-/
theorem PartiallyWellOrderedOn.exists_monotone_subseq (h : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ n, f n ∈ s) : ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
  WellQuasiOrdered.exists_monotone_subseq h fun n ↦ ⟨_, hf n⟩
/-
**Set.partiallyWellOrderedOn_iff_exists_monotone_subseq** 是 Mathlib 中的一个定理，位于命名空
间 `Set`。
形式化陈述：partiallyWellOrderedOn_iff_exists_monotone_subseq : s.PartiallyWellOrdered
On r ↔ forall f : Nat -> α, (forall n, f n in s) -> exists g : Nat ↪o Nat, foral
l m n : Nat, m <= n -> r (f (g m)) (f (g n))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.exists_monotone_subseq`：∀ {α : Type u_2} {r :
 α → α → Prop} {s : Set α} [IsPreorder α r],   s.PartiallyWellOrderedOn r → ∀ {f
 : ℕ → α}, (∀ (n : ℕ), f n ∈ s) → ∃ g, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.PartiallyWellOrderedOn.eq_1`：∀ {α : Type u_2} (s : Set α) (r : α → α
 → Prop), s.PartiallyWellOrderedOn r = WellQuasiOrdered (Subrel r fun x => x ∈ s
)
· 使用定理 `wellQuasiOrdered_iff_exists_monotone_subseq`：wellQuasiOrdered_iff_exists
_monotone_subseq [IsPreorder α r] : WellQuasiOrdered r ↔ forall f : Nat -> α, ex
ists g : Nat ↪o Nat, forall m n :…
· 使用定理 `Subrel.instIsPreorderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsPre
order α r] (p : α → Prop), IsPreorder (Subtype p) (Subrel r p)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem partiallyWellOrderedOn_iff_exists_monotone_subseq :
    s.PartiallyWellOrderedOn r ↔
      ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  use PartiallyWellOrderedOn.exists_monotone_subseq
  rw [PartiallyWellOrderedOn, wellQuasiOrdered_iff_exists_monotone_subseq]
  exact fun H f ↦ H _ fun n ↦ (f n).2
/-
**Set.PartiallyWellOrderedOn.prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.PartiallyWellOr
deredOn`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → α → Prop} {r' : β → β → Prop} {s 
: Set α} [IsPreorder α r] {t : Set β},   s.PartiallyWellOrderedOn r →     t.Part
iallyWellOrderedOn r' → (s ×ˢ t).PartiallyWellOrderedOn fun x y => r x.1 y.1 ∧ r
' x.2 y.2
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_lt`：partiallyWellOrderedOn_iff_exi
sts_lt : s.PartiallyWellOrderedOn r ↔ forall f : Nat -> α, (forall n, f n in s) 
-> exists m n, m < n ∧ r (f m)…
· 使用定理 `Set.PartiallyWellOrderedOn.exists_monotone_subseq`：∀ {α : Type u_2} {r :
 α → α → Prop} {s : Set α} [IsPreorder α r],   s.PartiallyWellOrderedOn r → ∀ {f
 : ℕ → α}, (∀ (n : ℕ), f n ∈ s) → ∃ g, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.PartiallyWellOrderedOn.exists_lt`：∀ {α : Type u_2} {r : α → α → Prop
} {s : Set α},   s.PartiallyWellOrderedOn r → ∀ {f : ℕ → α}, (∀ (n : ℕ), f n ∈ s
) → ∃ m n, m < n ∧ r (f m)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
protected theorem PartiallyWellOrderedOn.prod {t : Set β} (hs : PartiallyWellOrderedOn s r)
    (ht : PartiallyWellOrderedOn t r') :
    PartiallyWellOrderedOn (s ×ˢ t) fun x y : α × β => r x.1 y.1 ∧ r' x.2 y.2 := by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht.exists_lt fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strictMono hlt, h₁ _ _ hlt.le, hle⟩

/-- A version of **Dickson's lemma** on finite product of well-quasi-ordered sets. See
`WellQuasiOrdered.pi` when the type `α i` is well-quasi-ordered. -/
/-
**Set.PartiallyWellOrderedOn.pi** 是 Mathlib 中的一个定理，位于命名空间 `Set.PartiallyWellOrde
redOn`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_6} [Finite ι] {r : (i : ι) → α i → α i → 
Prop} [∀ (i : ι), IsPreorder (α i) (r i)]   {s : (i : ι) → Set (α i)},   (∀ (i :
 ι), (s i).PartiallyWellOrderedOn (r i)) →     (Set.univ.pi s).PartiallyWellOrde
redOn fun a b => ∀ (i : ι), r i (a i) (b i)
参数：i : ι；i : ι；α i；r i；i : ι；α i；∀ (i : ι), (s i).PartiallyWellOrderedOn (r i)；S
et.univ.pi s；i : ι；a i；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.PartiallyWellOrderedOn.exists_monotone_subseq`：∀ {α : Type u_2} {r :
 α → α → Prop} {s : Set α} [IsPreorder α r],   s.PartiallyWellOrderedOn r → ∀ {f
 : ℕ → α}, (∀ (n : ℕ), f n ∈ s) → ∃ g, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_monotone_subseq`：partiallyWellOrde
redOn_iff_exists_monotone_subseq : s.PartiallyWellOrderedOn r ↔ forall f : Nat -
> α, (forall n, f n in s) -> exists g : Nat…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A version of **Dickson's lemma** on finite product of well-quasi-ordered sets. S
ee
`WellQuasiOrdered.pi` when the type `α i` is well-quasi-ordered.
-/
protected theorem PartiallyWellOrderedOn.pi {α : ι → Type*} [Finite ι] {r : ∀ i, α i → α i → Prop}
    [∀ i, IsPreorder (α i) (r i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, PartiallyWellOrderedOn (s i) (r i)) :
    PartiallyWellOrderedOn (Set.univ.pi s) fun a b : ∀ i, α i => ∀ i, r i (a i) (b i) := by
  have := Fintype.ofFinite ι
  have : IsPreorder (∀ i, α i) (fun a b : ∀ i, α i => ∀ i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices ∀ (t : Finset ι), ∀ (f : ℕ → ∀ i, α i), (∀ n i, f n i ∈ s i) →
    ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ i, i ∈ t → r i ((f ∘ g) a i) ((f ∘ g) b i) by
    rw [partiallyWellOrderedOn_iff_exists_monotone_subseq]
    intro f hf
    simp only [mem_pi, mem_univ, forall_const] at hf
    simpa only [Finset.mem_univ, true_imp_iff] using! this Finset.univ f hf
  refine Finset.cons_induction ?_ ?_
  · intro f hf
    exists RelEmbedding.refl (· ≤ ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, Finset.notMem_empty]
  · intro i t hi ih f hf
    obtain ⟨g, hg⟩ := (hs i).exists_monotone_subseq (hf · i)
    obtain ⟨g', hg'⟩ := ih (f ∘ g) (hf <| g ·)
    refine ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 ?_⟩
    exact ⟨hg _ _ (OrderHomClass.mono g' hab), hg' hab⟩
/-
**Set.PartiallyWellOrderedOn.wellFoundedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Partia
llyWellOrderedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} {s : Set α} [IsPreorder α r],   s.Part
iallyWellOrderedOn r → s.WellFoundedOn fun a b => r a b ∧ ¬r b a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrdered.wellFounded`：WellQuasiOrdered.wellFounded {α : Type*} {
r : α -> α -> Prop} [IsPreorder α r] (h : WellQuasiOrdered r) : WellFounded fun 
a b => r a b ∧ ¬ r…
· 使用定理 `Subrel.instIsPreorderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsPre
order α r] (p : α → Prop), IsPreorder (Subtype p) (Subrel r p)
-/
theorem PartiallyWellOrderedOn.wellFoundedOn (h : s.PartiallyWellOrderedOn r) :
    s.WellFoundedOn fun a b => r a b ∧ ¬ r b a :=
  h.wellFounded

end IsPreorder

end PartiallyWellOrderedOn

section IsPWO

variable [Preorder α] [Preorder β] {s t : Set α}

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
/-
**Set.IsPWO** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：IsPWO (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a preorder is partially well-ordered when any infinite sequence cont
ains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subs
equence).
-/
def IsPWO (s : Set α) : Prop :=
  PartiallyWellOrderedOn s (· ≤ ·)

nonrec theorem IsPWO.mono (ht : t.IsPWO) : s ⊆ t → s.IsPWO := ht.mono

nonrec theorem IsPWO.exists_monotone_subseq (h : s.IsPWO) {f : ℕ → α} (hf : ∀ n, f n ∈ s) :
    ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq hf
/-
**Set.isPWO_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isPWO_univ_iff : (univ : Set α).IsPWO ↔ WellQuasiOrderedLE α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.partiallyWellOrderedOn_univ_iff`：partiallyWellOrderedOn_univ_iff : u
niv.PartiallyWellOrderedOn r ↔ WellQuasiOrdered r
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `wellQuasiOrderedLE_def`：∀ (α : Type u_3) [inst : LE α], WellQuasiOrdered
LE α ↔ WellQuasiOrdered fun x1 x2 => x1 ≤ x2
-/
theorem isPWO_univ_iff : (univ : Set α).IsPWO ↔ WellQuasiOrderedLE α :=
  partiallyWellOrderedOn_univ_iff.trans (wellQuasiOrderedLE_def _).symm
/-
**Set.isPWO_of_wellQuasiOrderedLE** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isPWO_of_wellQuasiOrderedLE [h : WellQuasiOrderedLE α] (s : Set α) : s.IsP
WO
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.partiallyWellOrderedOn_of_wellQuasiOrdered`：partiallyWellOrderedOn_o
f_wellQuasiOrdered (h : WellQuasiOrdered r) (s : Set α) : s.PartiallyWellOrdered
On r
· 使用定理 `WellQuasiOrderedLE.wqo`：∀ {α : Type u_3} {inst : LE α} [self : WellQuasi
OrderedLE α], WellQuasiOrdered fun x1 x2 => x1 ≤ x2
-/
theorem isPWO_of_wellQuasiOrderedLE [h : WellQuasiOrderedLE α] (s : Set α) : s.IsPWO :=
  partiallyWellOrderedOn_of_wellQuasiOrdered h.wqo s
/-
**Set.isPWO_iff_exists_monotone_subseq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isPWO_iff_exists_monotone_subseq : s.IsPWO ↔ forall f : Nat -> α, (forall 
n, f n in s) -> exists g : Nat ↪o Nat, Monotone (f ∘ g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_monotone_subseq`：partiallyWellOrde
redOn_iff_exists_monotone_subseq : s.PartiallyWellOrderedOn r ↔ forall f : Nat -
> α, (forall n, f n in s) -> exists g : Nat…
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem isPWO_iff_exists_monotone_subseq :
    s.IsPWO ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partiallyWellOrderedOn_iff_exists_monotone_subseq
/-
**Set.IsPWO.isWF** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPWO → s.IsWF
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.PartiallyWellOrderedOn.wellFoundedOn`：∀ {α : Type u_2} {r : α → α → 
Prop} {s : Set α} [IsPreorder α r],   s.PartiallyWellOrderedOn r → s.WellFounded
On fun a b => r a b ∧ ¬r b a
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
protected theorem IsPWO.isWF (h : s.IsPWO) : s.IsWF := by
  simpa only [← lt_iff_le_not_ge] using! h.wellFoundedOn

nonrec theorem IsPWO.prod {t : Set β} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s ×ˢ t) :=
  hs.prod ht

/-- A version of **Dickson's lemma** on finite product of well-quasi-ordered sets.
See `Pi.wellQuasiOrderedLE` when the type `α i` is `WellQuasiOrderedLE`. -/
/-
**Set.IsPWO.pi** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_6} [Finite ι] [inst : (i : ι) → Preorder 
(α i)] {s : (i : ι) → Set (α i)},   (∀ (i : ι), (s i).IsPWO) → (Set.univ.pi s).I
sPWO
参数：i : ι；α i；i : ι；α i；∀ (i : ι), (s i).IsPWO；Set.univ.pi s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.pi`：∀ {ι : Type u_1} {α : ι → Type u_6} [Fini
te ι] {r : (i : ι) → α i → α i → Prop} [∀ (i : ι), IsPreorder (α i) (r i)]   {s 
: (i : ι) → Set (α …
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2

--- 原说明 ---
A version of **Dickson's lemma** on finite product of well-quasi-ordered sets.
See `Pi.wellQuasiOrderedLE` when the type `α i` is `WellQuasiOrderedLE`.
-/
theorem IsPWO.pi {α : ι → Type*} [Finite ι] [∀ i, Preorder (α i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, (s i).IsPWO) : (Set.univ.pi s).IsPWO :=
  PartiallyWellOrderedOn.pi hs
/-
**Set.IsPWO.image_of_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
{s : Set α},   s.IsPWO → ∀ {f : α → β}, MonotoneOn f s → (f '' s).IsPWO
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.image_of_monotone_on`：∀ {α : Type u_2} {β : T
ype u_3} {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α},   s.Par
tiallyWellOrderedOn r → (∀ a₁ ∈ s, ∀ …
-/
theorem IsPWO.image_of_monotoneOn (hs : s.IsPWO) {f : α → β} (hf : MonotoneOn f s) :
    IsPWO (f '' s) :=
  hs.image_of_monotone_on hf
/-
**Set.IsPWO.image_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
{s : Set α},   s.IsPWO → ∀ {f : α → β}, Monotone f → (f '' s).IsPWO
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.image_of_monotone_on`：∀ {α : Type u_2} {β : T
ype u_3} {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α},   s.Par
tiallyWellOrderedOn r → (∀ a₁ ∈ s, ∀ …
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
theorem IsPWO.image_of_monotone (hs : s.IsPWO) {f : α → β} (hf : Monotone f) : IsPWO (f '' s) :=
  hs.image_of_monotone_on (hf.monotoneOn _)

protected nonrec theorem IsPWO.union (hs : IsPWO s) (ht : IsPWO t) : IsPWO (s ∪ t) :=
  hs.union ht

@[simp]
/-
**Set.isPWO_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isPWO_union : IsPWO (s union t) ↔ IsPWO s ∧ IsPWO t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.partiallyWellOrderedOn_union`：partiallyWellOrderedOn_union : (s unio
n t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrde
redOn r
-/
theorem isPWO_union : IsPWO (s ∪ t) ↔ IsPWO s ∧ IsPWO t :=
  partiallyWellOrderedOn_union
/-
**Set.Finite.isPWO** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Finite → s.IsPWO
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → α → Prop} {
s : Set α} [Std.Refl r], s.Finite → s.PartiallyWellOrderedOn r
-/
protected theorem Finite.isPWO (hs : s.Finite) : IsPWO s := hs.partiallyWellOrderedOn
/-
**Set.isPWO_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} [Finite α], s.IsPWO
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isPWO`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fi
nite → s.IsPWO
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
@[simp] theorem isPWO_of_finite [Finite α] : s.IsPWO := s.toFinite.isPWO
/-
**Set.isPWO_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (a : α), {a}.IsPWO
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isPWO`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fi
nite → s.IsPWO
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
@[simp] theorem isPWO_singleton (a : α) : IsPWO ({a} : Set α) := (finite_singleton a).isPWO
/-
**Set.isPWO_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α], ∅.IsPWO
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isPWO`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fi
nite → s.IsPWO
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
-/
@[simp] theorem isPWO_empty : IsPWO (∅ : Set α) := finite_empty.isPWO
/-
**Set.Subsingleton.isPWO** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Subsingleton → s.IsPWO
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isPWO`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fi
nite → s.IsPWO
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
protected theorem Subsingleton.isPWO (hs : s.Subsingleton) : IsPWO s := hs.finite.isPWO

@[simp]
/-
**Set.isPWO_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isPWO_insert {a} : IsPWO (insert a s) ↔ IsPWO s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPWO_insert {a} : IsPWO (insert a s) ↔ IsPWO s := by
  simp only [← singleton_union, isPWO_union, isPWO_singleton, true_and]
/-
**Set.IsPWO.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPWO → ∀ (a : α), (in
sert a s).IsPWO
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.isPWO_insert`：isPWO_insert {a} : IsPWO (insert a s) ↔ IsPWO s
-/
protected theorem IsPWO.insert (h : IsPWO s) (a : α) : IsPWO (insert a s) :=
  isPWO_insert.2 h
/-
**Set.Finite.isWF** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Finite → s.IsWF
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `Set.Finite.isPWO`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fi
nite → s.IsPWO
-/
protected theorem Finite.isWF (hs : s.Finite) : IsWF s := hs.isPWO.isWF
/-
**Set.isWF_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {a : α}, {a}.IsWF
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fin
ite → s.IsWF
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
@[simp] theorem isWF_singleton {a : α} : IsWF ({a} : Set α) := (finite_singleton a).isWF
/-
**Set.Subsingleton.isWF** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Subsingleton → s.IsWF
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `Set.Subsingleton.isPWO`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}
, s.Subsingleton → s.IsPWO
-/
protected theorem Subsingleton.isWF (hs : s.Subsingleton) : IsWF s := hs.isPWO.isWF

@[simp]
/-
**Set.isWF_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isWF_insert {a} : IsWF (insert a s) ↔ IsWF s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isWF_insert {a} : IsWF (insert a s) ↔ IsWF s := by
  simp only [← singleton_union, isWF_union, isWF_singleton, true_and]
/-
**Set.IsWF.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsWF → ∀ (a : α), (ins
ert a s).IsWF
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.isWF_insert`：isWF_insert {a} : IsWF (insert a s) ↔ IsWF s
-/
protected theorem IsWF.insert (h : IsWF s) (a : α) : IsWF (insert a s) :=
  isWF_insert.2 h
/-
**Set.IsPWO.exists_le_minimal** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a : α}, s.IsPWO → a ∈ s 
→ ∃ b ≤ a, Minimal (fun x => x ∈ s) b
参数：fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `WellQuasiOrdered.wellFounded`：WellQuasiOrdered.wellFounded {α : Type*} {
r : α -> α -> Prop} [IsPreorder α r] (h : WellQuasiOrdered r) : WellFounded fun 
a b => r a b ∧ ¬ r…
· 使用定理 `Subrel.instIsPreorderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsPre
order α r] (p : α → Prop), IsPreorder (Subtype p) (Subrel r p)
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsPWO.exists_le_minimal {a} (hs : s.IsPWO) (ha : a ∈ s) :
    ∃ b ≤ a, Minimal (· ∈ s) b := by
  let t : Set s := {x | x ≤ a}
  let h : t.Nonempty := ⟨⟨a, ha⟩, le_rfl⟩
  refine ⟨hs.wellFounded.min t h, hs.wellFounded.min_mem t h,
    (hs.wellFounded.min t h).2, fun y hy hle => ?_⟩
  by_contra hnle
  exact hs.wellFounded.not_lt_min t (x := ⟨y, hy⟩) (hle.trans (hs.wellFounded.min_mem t h))
    ⟨hle, hnle⟩
/-
**Set.IsPWO.exists_minimal** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPWO → s.Nonempty → ∃
 a, Minimal (fun x => x ∈ s) a
参数：fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.exists_le_minimal`：∀ {α : Type u_2} [inst : Preorder α] {s : S
et α} {a : α}, s.IsPWO → a ∈ s → ∃ b ≤ a, Minimal (fun x => x ∈ s) b
-/
theorem IsPWO.exists_minimal (h : s.IsPWO) (hs : s.Nonempty) :
    ∃ a, Minimal (· ∈ s) a := by
  rcases hs with ⟨a, ha⟩
  obtain ⟨b, _, hb⟩ := h.exists_le_minimal ha
  exact ⟨b, hb⟩
/-
**Set.IsPWO.exists_minimalFor** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : Preorder α] (f : ι → α) (s : Set ι
),   (f '' s).IsPWO → s.Nonempty → ∃ i, MinimalFor (fun x => x ∈ s) f i
参数：f : ι → α；s : Set ι；f '' s；fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.exists_minimal`：∀ {α : Type u_2} [inst : Preorder α] {s : Set 
α}, s.IsPWO → s.Nonempty → ∃ a, Minimal (fun x => x ∈ s) a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem IsPWO.exists_minimalFor (f : ι → α) (s : Set ι) (h : (f '' s).IsPWO) (hs : s.Nonempty) :
    ∃ i, MinimalFor (· ∈ s) f i := by
  obtain ⟨_, h⟩ := h.exists_minimal (hs.image _)
  obtain ⟨a, ha, rfl⟩ := h.1
  exact ⟨a, ha, fun b hb => h.2 (mem_image_of_mem _ hb)⟩

end IsPWO

section WellFoundedOn

variable {r : α → α → Prop} [IsStrictOrder α r] {s : Set α} {a : α}

/-
**Set.Finite.wellFoundedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] {s : Set α}, s.Fin
ite → s.WellFoundedOn r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fin
ite → s.IsWF
-/
protected theorem Finite.wellFoundedOn (hs : s.Finite) : s.WellFoundedOn r :=
  letI := partialOrderOfSO r
  hs.isWF

@[simp]
/-
**Set.wellFoundedOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_singleton : WellFoundedOn ({a} : Set α) r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.wellFoundedOn`：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictO
rder α r] {s : Set α}, s.Finite → s.WellFoundedOn r
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem wellFoundedOn_singleton : WellFoundedOn ({a} : Set α) r :=
  (finite_singleton a).wellFoundedOn
/-
**Set.Subsingleton.wellFoundedOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] {s : Set α}, s.Sub
singleton → s.WellFoundedOn r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.wellFoundedOn`：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictO
rder α r] {s : Set α}, s.Finite → s.WellFoundedOn r
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
protected theorem Subsingleton.wellFoundedOn (hs : s.Subsingleton) : s.WellFoundedOn r :=
  hs.finite.wellFoundedOn

@[simp]
/-
**Set.wellFoundedOn_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wellFoundedOn_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r := by
  simp only [← singleton_union, wellFoundedOn_union, wellFoundedOn_singleton, true_and]

@[simp]
/-
**Set.wellFoundedOn_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：wellFoundedOn_sdiff_singleton : WellFoundedOn (s \ {a}) r ↔ WellFoundedOn 
s r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.wellFoundedOn_insert`：wellFoundedOn_insert : WellFoundedOn (insert a
 s) r ↔ WellFoundedOn s r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wellFoundedOn_sdiff_singleton : WellFoundedOn (s \ {a}) r ↔ WellFoundedOn s r := by
  simp only [← wellFoundedOn_insert (a := a), insert_sdiff_singleton, mem_insert_iff, true_or,
    insert_eq_of_mem]
/-
**Set.WellFoundedOn.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] {s : Set α},   s.W
ellFoundedOn r → ∀ (a : α), (insert a s).WellFoundedOn r
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.wellFoundedOn_insert`：wellFoundedOn_insert : WellFoundedOn (insert a
 s) r ↔ WellFoundedOn s r
-/
protected theorem WellFoundedOn.insert (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (insert a s) r :=
  wellFoundedOn_insert.2 h
/-
**Set.WellFoundedOn.sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn
`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] {s : Set α},   s.W
ellFoundedOn r → ∀ (a : α), (s \ {a}).WellFoundedOn r
参数：a : α；s \ {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.wellFoundedOn_sdiff_singleton`：wellFoundedOn_sdiff_singleton : WellF
oundedOn (s \ {a}) r ↔ WellFoundedOn s r
-/
protected theorem WellFoundedOn.sdiff_singleton (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (s \ {a}) r :=
  wellFoundedOn_sdiff_singleton.2 h
/-
**Set.WellFoundedOn.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`。
形式化陈述：∀ {α : Type u_6} {β : Type u_7} {r : α → α → Prop} (f : β → α) {s : Set α}
 {t : Set β},   Set.MapsTo f t s → s.WellFoundedOn r → t.WellFoundedOn (Function
.onFun r f)
参数：f : β → α；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma WellFoundedOn.mapsTo {α β : Type*} {r : α → α → Prop} (f : β → α)
    {s : Set α} {t : Set β} (h : MapsTo f t s) (hw : s.WellFoundedOn r) :
    t.WellFoundedOn (r on f) := by
  exact InvImage.wf (fun x : t ↦ ⟨f x, h x.prop⟩) hw

@[to_dual]
/-
**Set.WellFoundedOn.exists_minimal** 是 Mathlib 中的一个定理，位于命名空间 `Set.WellFoundedOn`
。
形式化陈述：∀ {α : Type u_6} [inst : Preorder α] {s : Set α},   (s.WellFoundedOn fun x
1 x2 => x1 < x2) → s.Nonempty → ∃ a, Minimal (fun x => x ∈ s) a
参数：s.WellFoundedOn fun x1 x2 => x1 < x2；fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.exists_minimal`：∀ {α : Type u_1} [inst : Preorder α], Well
FoundedLT α → ∀ (s : Set α), s.Nonempty → ∃ m, Minimal (fun x => x ∈ s) m
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `trivial`：True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WellFoundedOn.exists_minimal {α : Type*} [Preorder α] {s : Set α}
    (h : s.WellFoundedOn (· < ·)) (nonempty : s.Nonempty) : ∃ a, Minimal (· ∈ s) a :=
  have ⟨m, hm⟩ := WellFoundedLT.exists_minimal ⟨h⟩ univ <| nonempty.elim (⟨⟨·, ·⟩, trivial⟩)
  ⟨m, m.property, fun y hy ↦ hm.right (y := ⟨y, hy⟩) trivial⟩

end WellFoundedOn

section LinearOrder

variable [LinearOrder α] {s : Set α}

/-- In a linear order, the predicates `Set.IsPWO` and `Set.IsWF` are equivalent. -/
/-
**Set.isPWO_iff_isWF** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isPWO_iff_isWF : s.IsPWO ↔ s.IsWF
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wellQuasiOrderedLE_def`：∀ (α : Type u_3) [inst : LE α], WellQuasiOrdered
LE α ↔ WellQuasiOrdered fun x1 x2 => x1 ≤ x2
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `wellQuasiOrderedLE_iff_wellFoundedLT`：wellQuasiOrderedLE_iff_wellFounded
LT : WellQuasiOrderedLE α ↔ WellFoundedLT α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a linear order, the predicates `Set.IsPWO` and `Set.IsWF` are equivalent.
-/
theorem isPWO_iff_isWF : s.IsPWO ↔ s.IsWF := by
  change WellQuasiOrdered (· ≤ ·) ↔ WellFounded (· < ·)
  rw [← wellQuasiOrderedLE_def, ← isWellFounded_iff, wellQuasiOrderedLE_iff_wellFoundedLT]

alias ⟨_, IsWF.isPWO⟩ := isPWO_iff_isWF

/--
If `α` is a linear order with well-founded `<`, then any set in it is a partially well-ordered set.
Note this does not hold without the linearity assumption.
-/
/-
**Set.IsPWO.of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] [WellFoundedLT α] (s : Set α), s.I
sPWO
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
· 使用定理 `Set.IsWF.of_wellFoundedLT`：∀ {α : Type u_2} [inst : LT α] [h : WellFound
edLT α] (s : Set α), s.IsWF

--- 原说明 ---
If `α` is a linear order with well-founded `<`, then any set in it is a partiall
y well-ordered set.
Note this does not hold without the linearity assumption.
-/
lemma IsPWO.of_linearOrder [WellFoundedLT α] (s : Set α) : s.IsPWO :=
  (IsWF.of_wellFoundedLT s).isPWO

end LinearOrder

end Set

namespace Finset

variable {r : α → α → Prop}

@[simp]
/-
**Finset.partiallyWellOrderedOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [Std.Refl r] (s : Finset α), (↑s).Part
iallyWellOrderedOn r
参数：s : Finset α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → α → Prop} {
s : Set α} [Std.Refl r], s.Finite → s.PartiallyWellOrderedOn r
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
protected theorem partiallyWellOrderedOn [Std.Refl r] (s : Finset α) :
    (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_toSet.partiallyWellOrderedOn

@[simp]
/-
**Finset.isPWO** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (s : Finset α), (↑s).IsPWO
参数：s : Finset α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → α → Prop} [Std.
Refl r] (s : Finset α), (↑s).PartiallyWellOrderedOn r
-/
protected theorem isPWO [Preorder α] (s : Finset α) : Set.IsPWO (↑s : Set α) :=
  s.partiallyWellOrderedOn

@[simp]
/-
**Finset.isWF** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (s : Finset α), (↑s).IsWF
参数：s : Finset α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.Fin
ite → s.IsWF
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
protected theorem isWF [Preorder α] (s : Finset α) : Set.IsWF (↑s : Set α) :=
  s.finite_toSet.isWF

@[simp]
/-
**Finset.wellFoundedOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictOrder α r] (s : Finset α), (↑
s).WellFoundedOn r
参数：s : Finset α；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.isWF`：∀ {α : Type u_2} [inst : Preorder α] (s : Finset α), (↑s).I
sWF
-/
protected theorem wellFoundedOn [IsStrictOrder α r] (s : Finset α) :
    Set.WellFoundedOn (↑s : Set α) r :=
  letI := partialOrderOfSO r
  s.isWF
/-
**Finset.wellFoundedOn_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：wellFoundedOn_sup [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α} : (s
.sup f).WellFoundedOn r ↔ forall i in s, (f i).WellFoundedOn r
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
-/
theorem wellFoundedOn_sup [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]
/-
**Finset.partiallyWellOrderedOn_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：partiallyWellOrderedOn_sup (s : Finset ι) {f : ι -> Set α} : (s.sup f).Par
tiallyWellOrderedOn r ↔ forall i in s, (f i).PartiallyWellOrderedOn r
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
-/
theorem partiallyWellOrderedOn_sup (s : Finset ι) {f : ι → Set α} :
    (s.sup f).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]
/-
**Finset.isWF_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isWF_sup [Preorder α] (s : Finset ι) {f : ι -> Set α} : (s.sup f).IsWF ↔ f
orall i in s, (f i).IsWF
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.wellFoundedOn_sup`：wellFoundedOn_sup [IsStrictOrder α r] (s : Fin
set ι) {f : ι -> Set α} : (s.sup f).WellFoundedOn r ↔ forall i in s, (f i).WellF
oundedOn r
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
-/
theorem isWF_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsWF ↔ ∀ i ∈ s, (f i).IsWF :=
  s.wellFoundedOn_sup
/-
**Finset.isPWO_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isPWO_sup [Preorder α] (s : Finset ι) {f : ι -> Set α} : (s.sup f).IsPWO ↔
 forall i in s, (f i).IsPWO
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.partiallyWellOrderedOn_sup`：partiallyWellOrderedOn_sup (s : Finse
t ι) {f : ι -> Set α} : (s.sup f).PartiallyWellOrderedOn r ↔ forall i in s, (f i
).PartiallyWellOrderedO…
-/
theorem isPWO_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsPWO ↔ ∀ i ∈ s, (f i).IsPWO :=
  s.partiallyWellOrderedOn_sup

@[simp]
/-
**Finset.wellFoundedOn_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：wellFoundedOn_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α} :
 (⋃ i in s, f i).WellFoundedOn r ↔ forall i in s, (f i).WellFoundedOn r
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `Finset.wellFoundedOn_sup`：wellFoundedOn_sup [IsStrictOrder α r] (s : Fin
set ι) {f : ι -> Set α} : (s.sup f).WellFoundedOn r ↔ forall i in s, (f i).WellF
oundedOn r
-/
theorem wellFoundedOn_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r := by
  simpa only [Finset.sup_eq_iSup] using! s.wellFoundedOn_sup

@[simp]
/-
**Finset.partiallyWellOrderedOn_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：partiallyWellOrderedOn_bUnion (s : Finset ι) {f : ι -> Set α} : (⋃ i in s,
 f i).PartiallyWellOrderedOn r ↔ forall i in s, (f i).PartiallyWellOrderedOn r
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `Finset.partiallyWellOrderedOn_sup`：partiallyWellOrderedOn_sup (s : Finse
t ι) {f : ι -> Set α} : (s.sup f).PartiallyWellOrderedOn r ↔ forall i in s, (f i
).PartiallyWellOrderedO…
-/
theorem partiallyWellOrderedOn_bUnion (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r := by
  simpa only [Finset.sup_eq_iSup] using! s.partiallyWellOrderedOn_sup

@[simp]
/-
**Finset.isWF_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isWF_bUnion [Preorder α] (s : Finset ι) {f : ι -> Set α} : (⋃ i in s, f i)
.IsWF ↔ forall i in s, (f i).IsWF
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.wellFoundedOn_bUnion`：wellFoundedOn_bUnion [IsStrictOrder α r] (s
 : Finset ι) {f : ι -> Set α} : (⋃ i in s, f i).WellFoundedOn r ↔ forall i in s,
 (f i).WellFounde…
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
-/
theorem isWF_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsWF ↔ ∀ i ∈ s, (f i).IsWF :=
  s.wellFoundedOn_bUnion

@[simp]
/-
**Finset.isPWO_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isPWO_bUnion [Preorder α] (s : Finset ι) {f : ι -> Set α} : (⋃ i in s, f i
).IsPWO ↔ forall i in s, (f i).IsPWO
参数：s : Finset ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.partiallyWellOrderedOn_bUnion`：partiallyWellOrderedOn_bUnion (s :
 Finset ι) {f : ι -> Set α} : (⋃ i in s, f i).PartiallyWellOrderedOn r ↔ forall 
i in s, (f i).PartiallyWel…
-/
theorem isPWO_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsPWO ↔ ∀ i ∈ s, (f i).IsPWO :=
  s.partiallyWellOrderedOn_bUnion

end Finset

namespace Set

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

/-- `Set.IsWF.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable nonrec def IsWF.min (hs : IsWF s) (hn : s.Nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

/-
**Set.IsWF.min_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs : s.IsWF) (hn : s.Non
empty), hs.min hn ∈ s
参数：hs : s.IsWF；hn : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
-/
theorem IsWF.min_mem (hs : IsWF s) (hn : s.Nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

nonrec theorem IsWF.not_lt_min (hs : IsWF s) (hn : s.Nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (mem_univ (⟨a, ha⟩ : s))
/-
**Set.IsWF.min_of_subset_not_lt_min** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α} {hs : s.IsWF} {hsn : s.
Nonempty} {ht : t.IsWF} {htn : t.Nonempty},   s ⊆ t → ¬hs.min hsn < ht.min htn
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem IsWF.min_of_subset_not_lt_min {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF}
    {htn : t.Nonempty} (hst : s ⊆ t) : ¬hs.min hsn < ht.min htn :=
  ht.not_lt_min htn (hst (min_mem hs hsn))

@[simp]
/-
**Set.isWF_min_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isWF_min_singleton (a) {hs : IsWF ({a} : Set α)} {hn : ({a} : Set α).Nonem
pty} : hs.min hn = a
参数：a；{a} : Set α；{a} : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem isWF_min_singleton (a) {hs : IsWF ({a} : Set α)} {hn : ({a} : Set α).Nonempty} :
    hs.min hn = a :=
  eq_of_mem_singleton (IsWF.min_mem hs hn)
/-
**Set.IsWF.min_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a : α} (hs : s.IsWF) (ha
 : a ∈ s),   (∀ b ∈ s, b ≠ a → a < b) → hs.min ⋯ = a
参数：hs : s.IsWF；ha : a ∈ s；∀ b ∈ s, b ≠ a → a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem IsWF.min_eq_of_lt (hs : s.IsWF) (ha : a ∈ s) (hlt : ∀ b ∈ s, b ≠ a → a < b) :
    hs.min (nonempty_of_mem ha) = a := by
  by_contra h
  exact (hs.not_lt_min (nonempty_of_mem ha) ha) (hlt (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha)) h)

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a : α}

/-
**Set.IsWF.min_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {s : Set α} {a : α} (hs : s.IsWF)
 (ha : a ∈ s), (∀ b ∈ s, a ≤ b) → hs.min ⋯ = a
参数：hs : s.IsWF；ha : a ∈ s；∀ b ∈ s, a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
-/
theorem IsWF.min_eq_of_le (hs : s.IsWF) (ha : a ∈ s) (hle : ∀ b ∈ s, a ≤ b) :
    hs.min (nonempty_of_mem ha) = a :=
  (eq_of_le_of_not_lt (hle (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha))) (hs.not_lt_min (nonempty_of_mem ha) ha)).symm

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α} {a : α}

/-
**Set.IsWF.min_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a : α} (hs : s.IsWF) 
(hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
参数：hs : s.IsWF；hn : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
-/
theorem IsWF.min_le (hs : s.IsWF) (hn : s.Nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_gt (hs.not_lt_min hn ha)
/-
**Set.IsWF.le_min_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a : α} (hs : s.IsWF) 
(hn : s.Nonempty),   a ≤ hs.min hn ↔ ∀ b ∈ s, a ≤ b
参数：hs : s.IsWF；hn : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem IsWF.le_min_iff (hs : s.IsWF) (hn : s.Nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha _b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩
/-
**Set.IsWF.min_le_min_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s t : Set α} {hs : s.IsWF} {hsn :
 s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty},   s ⊆ t → ht.min htn ≤ hs.min hsn
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.IsWF.le_min_iff`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}
 {a : α} (hs : s.IsWF) (hn : s.Nonempty),   a ≤ hs.min hn ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
-/
theorem IsWF.min_le_min_of_subset {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}
    (hst : s ⊆ t) : ht.min htn ≤ hs.min hsn :=
  (IsWF.le_min_iff _ _).2 fun _b hb => ht.min_le htn (hst hb)
/-
**Set.IsWF.min_union** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s t : Set α} (hs : s.IsWF) (hsn :
 s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty),   ⋯.min ⋯ = min (hs.min hsn) (ht.
min htn)
参数：hs : s.IsWF；hsn : s.Nonempty；ht : t.IsWF；htn : t.Nonempty；hs.min hsn；ht.min h
tn。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.IsWF.union`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, s.Is
WF → t.IsWF → (s ∪ t).IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_nonempty`：union_nonempty : (s union t).Nonempty ↔ s.Nonempty ∨
 t.Nonempty
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
-/
theorem IsWF.min_union (hs : s.IsWF) (hsn : s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty) :
    (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) =
      Min.min (hs.min hsn) (ht.min htn) := by
  refine le_antisymm (le_min (IsWF.min_le_min_of_subset subset_union_left)
    (IsWF.min_le_min_of_subset subset_union_right)) ?_
  rw [min_le_iff]
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (.inl hsn)))).imp
    (hs.min_le _) (ht.min_le _)

end LinearOrder

end Set

open Set

section LocallyFiniteOrder

variable {s : Set α} [Preorder α] [LocallyFiniteOrder α]

/-
**BddBelow.wellFoundedOn_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddBelow.wellFoundedOn_lt : BddBelow s -> s.WellFoundedOn (· < ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.wellFoundedOn_iff_no_descending_seq`：wellFoundedOn_iff_no_descending
_seq : s.WellFoundedOn r ↔ forall f : ((· > ·) : Nat -> Nat -> Prop) ↪r r, ¬fora
ll n, f n in s
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `antitone_iff_forall_lt`：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a 
b⦄, a < b -> f b <= f a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem BddBelow.wellFoundedOn_lt : BddBelow s → s.WellFoundedOn (· < ·) := by
  rw [wellFoundedOn_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf
  refine infinite_range_of_injective f.injective ?_
  exact (finite_Icc a <| f 0).subset <| range_subset_iff.2 <| fun n =>
    ⟨ha <| hf _,
      antitone_iff_forall_lt.2 (fun a b hab => (f.map_rel_iff.2 hab).le) <| Nat.zero_le _⟩
/-
**BddAbove.wellFoundedOn_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.wellFoundedOn_gt : BddAbove s -> s.WellFoundedOn (· > ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddBelow.wellFoundedOn_lt`：BddBelow.wellFoundedOn_lt : BddBelow s -> s.W
ellFoundedOn (· < ·)
· 使用定理 `BddAbove.dual`：BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s)
-/
theorem BddAbove.wellFoundedOn_gt : BddAbove s → s.WellFoundedOn (· > ·) :=
  fun h => h.dual.wellFoundedOn_lt
/-
**BddBelow.isWF** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddBelow.isWF : BddBelow s -> IsWF s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddBelow.wellFoundedOn_lt`：BddBelow.wellFoundedOn_lt : BddBelow s -> s.W
ellFoundedOn (· < ·)
-/
theorem BddBelow.isWF : BddBelow s → IsWF s :=
  BddBelow.wellFoundedOn_lt

end LocallyFiniteOrder

namespace Set.PartiallyWellOrderedOn

variable {r : α → α → Prop}

/-
**Set.PartiallyWellOrderedOn.bddAbove_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pa
rtiallyWellOrderedOn`。
形式化陈述：bddAbove_preimage {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : Nat -
> α} (hf : forall m n : Nat, m < n -> ¬ r (f m) (f n)) : BddAbove (s.preimage f)
参数：hs : s.PartiallyWellOrderedOn r；hf : forall m n : Nat, m < n -> ¬ r (f m) (f 
n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.exists_strictMono_subsequence`：exists_strictMono_subsequence {P : Na
t -> Prop} (h : forall N, exists n > N, P n) : exists φ : Nat -> Nat, StrictMono
 φ ∧ forall n, P (φ n)
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_lt`：partiallyWellOrderedOn_iff_exi
sts_lt : s.PartiallyWellOrderedOn r ↔ forall f : Nat -> α, (forall n, f n in s) 
-> exists m n, m < n ∧ r (f m)…
-/
theorem bddAbove_preimage {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ m n : ℕ, m < n → ¬ r (f m) (f n)) :
    BddAbove (s.preimage f) := by
  contrapose! hf
  rw [not_bddAbove_iff] at hf
  obtain ⟨φ, hφm, hφs⟩ := Nat.exists_strictMono_subsequence
    fun n ↦ (hf n).casesOn fun m h ↦ h.casesOn fun hs hmn ↦ Exists.intro m ⟨hmn, hs⟩
  rw [partiallyWellOrderedOn_iff_exists_lt] at hs
  obtain ⟨m, n, hmn, hr⟩ := hs (fun n ↦ f (φ n)) hφs
  use (φ m), (φ n)
  exact ⟨hφm hmn, hr⟩
/-
**Set.PartiallyWellOrderedOn.exists_notMem_of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Set.
PartiallyWellOrderedOn`。
形式化陈述：exists_notMem_of_gt {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : Nat
 -> α} (hf : forall m n : Nat, m < n -> ¬ r (f m) (f n)) : exists k : Nat, foral
l m, k < m -> f m ∉ s
参数：hs : s.PartiallyWellOrderedOn r；hf : forall m n : Nat, m < n -> ¬ r (f m) (f 
n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.bddAbove_preimage`：bddAbove_preimage {s : Set
 α} (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α} (hf : forall m n : Nat, m <
 n -> ¬ r (f m) (f n)) : BddAbove …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem exists_notMem_of_gt {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ m n : ℕ, m < n → ¬ r (f m) (f n)) :
    ∃ k : ℕ, ∀ m, k < m → f m ∉ s := by
  have := hs.bddAbove_preimage hf
  contrapose! this
  simpa [not_bddAbove_iff, and_comm]

-- TODO: move this material to the main file on WQOs.

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
/-
**Set.PartiallyWellOrderedOn.IsBadSeq** 是 Mathlib 中的一个定义，位于命名空间 `Set.PartiallyWe
llOrderedOn`。
形式化陈述：IsBadSeq (r : α -> α -> Prop) (s : Set α) (f : Nat -> α) : Prop
参数：r : α -> α -> Prop；s : Set α；f : Nat -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the context of partial well-orderings, a bad sequence is a nonincreasing sequ
ence
  whose range is contained in a particular set `s`. One exists if and only if `s
` is not
  partially well-ordered.
-/
def IsBadSeq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  (∀ n, f n ∈ s) ∧ ∀ m n : ℕ, m < n → ¬r (f m) (f n)
/-
**Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq** 是 Mathlib 中的一个定理，位于命名空间 `
Set.PartiallyWellOrderedOn`。
形式化陈述：iff_forall_not_isBadSeq (r : α -> α -> Prop) (s : Set α) : s.PartiallyWell
OrderedOn r ↔ forall f, ¬IsBadSeq r s f
参数：r : α -> α -> Prop；s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_lt`：partiallyWellOrderedOn_iff_exi
sts_lt : s.PartiallyWellOrderedOn r ↔ forall f : Nat -> α, (forall n, f n in s) 
-> exists m n, m < n ∧ r (f m)…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_forall_not_isBadSeq (r : α → α → Prop) (s : Set α) :
    s.PartiallyWellOrderedOn r ↔ ∀ f, ¬IsBadSeq r s f := by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  exact forall_congr' fun f => by simp [IsBadSeq]

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
/-
**Set.PartiallyWellOrderedOn.IsMinBadSeq** 是 Mathlib 中的一个定义，位于命名空间 `Set.Partiall
yWellOrderedOn`。
形式化陈述：IsMinBadSeq (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) (n : Nat) (f 
: Nat -> α) : Prop
参数：r : α -> α -> Prop；rk : α -> Nat；s : Set α；n : Nat；f : Nat -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`.
-/
def IsMinBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ g : ℕ → α, (∀ m : ℕ, m < n → f m = g m) → rk (g n) < rk (f n) → ¬IsBadSeq r s g

/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
/-
**Set.PartiallyWellOrderedOn.minBadSeqOfBadSeq** 是 Mathlib 中的一个定义，位于命名空间 `Set.Pa
rtiallyWellOrderedOn`。
形式化陈述：minBadSeqOfBadSeq (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) (n : Na
t) (f : Nat -> α) (hf : IsBadSeq r s f) : { g : Nat -> α // (forall m : Nat, m <
 n -> f m = g m) ∧ IsBadSeq r s g ∧ IsMinBadSeq r rk s n g }
参数：r : α -> α -> Prop；rk : α -> Nat；s : Set α；n : Nat；f : Nat -> α；hf : IsBadSeq
 r s f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on
 the first `n`
  terms and is minimal at `n`.
-/
noncomputable def minBadSeqOfBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α)
    (hf : IsBadSeq r s f) :
    { g : ℕ → α // (∀ m : ℕ, m < n → f m = g m) ∧ IsBadSeq r s g ∧ IsMinBadSeq r rk s n g } := by
  classical
    have h : ∃ (k : ℕ) (g : ℕ → α), (∀ m, m < n → f m = g m) ∧ IsBadSeq r s g ∧ rk (g n) = k :=
      ⟨_, f, fun _ _ => rfl, hf, rfl⟩
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Nat.find_spec h)
    refine ⟨Classical.choose (Nat.find_spec h), h1, by convert! h2, fun g hg1 hg2 con => ?_⟩
    refine Nat.find_min h ?_ ⟨g, fun m mn => (h1 m mn).trans (hg1 m mn), con, rfl⟩
    rwa [← h3]
/-
**Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad** 是 Mathlib 中的一个定理，位于命
名空间 `Set.PartiallyWellOrderedOn`。
形式化陈述：exists_min_bad_of_exists_bad (r : α -> α -> Prop) (rk : α -> Nat) (s : Set
 α) : (exists f, IsBadSeq r s f) -> exists f, IsBadSeq r s f ∧ forall n, IsMinBa
dSeq r rk s n f
参数：r : α -> α -> Prop；rk : α -> Nat；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem exists_min_bad_of_exists_bad (r : α → α → Prop) (rk : α → ℕ) (s : Set α) :
    (∃ f, IsBadSeq r s f) → ∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rintro ⟨f0, hf0 : IsBadSeq r s f0⟩
  let fs : ∀ n : ℕ, { f : ℕ → α // IsBadSeq r s f ∧ IsMinBadSeq r rk s n f } := by
    refine Nat.rec ?_ fun n fn => ?_
    · exact ⟨(minBadSeqOfBadSeq r rk s 0 f0 hf0).1, (minBadSeqOfBadSeq r rk s 0 f0 hf0).2.2⟩
    · exact ⟨(minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).1,
        (minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).2.2⟩
  have h : ∀ m n, m ≤ n → (fs m).1 m = (fs n).1 m := fun m n mn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le mn; clear mn
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [ih, (minBadSeqOfBadSeq r rk s (m + k + 1) (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (Nat.lt_succ_iff.2 (Nat.add_le_add_left k.zero_le m))]
      rfl
  refine ⟨fun n => (fs n).1 n, ⟨fun n => (fs n).2.1.1 n, fun m n mn => ?_⟩, fun n g hg1 hg2 => ?_⟩
  · dsimp
    rw [h m n mn.le]
    exact (fs n).2.1.2 m n mn
  · refine (fs n).2.2 g (fun m mn => ?_) hg2
    rw [← h m n mn.le, ← hg1 m mn]
/-
**Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq** 是 Mathlib 中的一个定理，位于命名空
间 `Set.PartiallyWellOrderedOn`。
形式化陈述：iff_not_exists_isMinBadSeq (rk : α -> Nat) {s : Set α} : s.PartiallyWellOr
deredOn r ↔ ¬exists f, IsBadSeq r s f ∧ forall n, IsMinBadSeq r rk s n f
参数：rk : α -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq`：iff_forall_not_isBad
Seq (r : α -> α -> Prop) (s : Set α) : s.PartiallyWellOrderedOn r ↔ forall f, ¬I
sBadSeq r s f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad`：exists_min_bad_
of_exists_bad (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) : (exists f, IsBa
dSeq r s f) -> exists f, IsBadSeq r s f ∧ for…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iff_not_exists_isMinBadSeq (rk : α → ℕ) {s : Set α} :
    s.PartiallyWellOrderedOn r ↔ ¬∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rw [iff_forall_not_isBadSeq, ← not_exists, not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
  · rintro ⟨f, hf1, -⟩
    exact ⟨f, hf1⟩

/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `List.SublistForall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `List.SublistForall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`. -/
/-
**Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall** 是 Mathlib 中的
一个定理，位于命名空间 `Set.PartiallyWellOrderedOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Higman's Lemma, which states that for any reflexive, transitive relation `r` whi
ch is
  partially well-ordered on a set `s`, the relation `List.SublistForall₂ r` is p
artially
  well-ordered on the set of lists of elements of `s`. That relation is defined 
so that
  `List.SublistForall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a subl
ist of `l₂`.
-/
theorem partiallyWellOrderedOn_sublistForall₂ (r : α → α → Prop) [IsPreorder α r]
    {s : Set α} (h : s.PartiallyWellOrderedOn r) :
    { l : List α | ∀ x, x ∈ l → x ∈ s }.PartiallyWellOrderedOn (List.SublistForall₂ r) := by
  rcases isEmpty_or_nonempty α
  · exact subsingleton_of_subsingleton.partiallyWellOrderedOn
  inhabit α
  rw [iff_not_exists_isMinBadSeq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : ∀ n, f n ≠ List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.nil)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq fun n => hf1.1 n _ (List.head!_mem_self (hnil n))
  have hf' :=
    hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0))))
      (fun m hm => (if_pos hm).symm) ?_
  swap
  · simp only [if_neg (lt_irrefl (g 0)), Nat.sub_self]
    rw [List.length_tail, ← Nat.pred_eq_sub_one]
    exact Nat.pred_lt fun con => hnil _ (List.length_eq_zero_iff.1 con)
  rw [IsBadSeq] at hf'
  push Not at hf'
  obtain ⟨m, n, mn, hmn⟩ := hf' fun n x hx => by
    split_ifs at hx with hn
    exacts [hf1.1 _ _ hx, hf1.1 _ _ (List.tail_subset _ hx)]
  by_cases hn : n < g 0
  · apply hf1.2 m n mn
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
    rw [if_neg hn, add_comm (g 0) n', Nat.add_sub_cancel_right] at hmn
    split_ifs at hmn with hm
    · apply hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le))
      exact _root_.trans hmn (List.tail_sublistForall₂_self _)
    · rw [← Nat.sub_lt_iff_lt_add' (le_of_not_gt hm)] at mn
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      rw [← List.cons_head!_tail (hnil (g (m - g 0))), ← List.cons_head!_tail (hnil (g n'))]
      exact List.SublistForall₂.cons (hg _ _ (le_of_lt mn)) hmn
/-
**Set.PartiallyWellOrderedOn.subsetProdLex** 是 Mathlib 中的一个定理，位于命名空间 `Set.Partia
llyWellOrderedOn`。
形式化陈述：subsetProdLex [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)} (hα : ((fun
 (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO) (hβ : forall a, {y | toLex (a, y) in 
s}.IsPWO) : s.IsPWO
参数：α ×ₗ β；hα : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO；hβ : forall a, {y 
| toLex (a, y) in s}.IsPWO。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.IsPWO.eq_1`：∀ {α : Type u_2} [inst : Preorder α] (s : Set α), s.IsPW
O = s.PartiallyWellOrderedOn fun x1 x2 => x1 ≤ x2
· 使用定理 `Set.partiallyWellOrderedOn_iff_exists_lt`：partiallyWellOrderedOn_iff_exi
sts_lt : s.PartiallyWellOrderedOn r ↔ forall f : Nat -> α, (forall n, f n in s) 
-> exists m n, m < n ∧ r (f m)…
· 使用定理 `Set.isPWO_iff_exists_monotone_subseq`：isPWO_iff_exists_monotone_subseq :
 s.IsPWO ↔ forall f : Nat -> α, (forall n, f n in s) -> exists g : Nat ↪o Nat, M
onotone (f ∘ g)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.Lex.toLex_le_toLex`：toLex_le_toLex [LT α] [LE β] {x y : α × β} : to
Lex x <= toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 <= y.2
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem subsetProdLex [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hα : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO)
    (hβ : ∀ a, {y | toLex (a, y) ∈ s}.IsPWO) : s.IsPWO := by
  rw [IsPWO, partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  rw [isPWO_iff_exists_monotone_subseq] at hα
  obtain ⟨g, hg⟩ : ∃ (g : (ℕ ↪o ℕ)), Monotone fun n => (ofLex f (g n)).1 :=
    hα (fun n => (ofLex f n).1) (fun k => mem_image_of_mem (fun x => (ofLex x).1) (hf k))
  have hhg : ∀ n, (ofLex f (g 0)).1 ≤ (ofLex f (g n)).1 := fun n => hg n.zero_le
  by_cases! hc : ∃ n, (ofLex f (g 0)).1 < (ofLex f (g n)).1
  · obtain ⟨n, hn⟩ := hc
    use (g 0), (g n)
    constructor
    · by_contra hx
      simp_all
    · exact Prod.Lex.toLex_le_toLex.mpr <| .inl hn
  · have hhc : ∀ n, (ofLex f (g 0)).1 = (ofLex f (g n)).1 := by
      intro n
      exact (hhg n).eq_of_not_lt (hc n)
    obtain ⟨g', hg'⟩ : ∃ g' : ℕ ↪o ℕ, Monotone ((fun n ↦ (ofLex f (g (g' n))).2)) := by
      simp_rw [isPWO_iff_exists_monotone_subseq] at hβ
      apply hβ (ofLex f (g 0)).1 fun n ↦ (ofLex f (g n)).2
      intro n
      rw [hhc n]
      simpa using! hf _
    use (g (g' 0)), (g (g' 1))
    suffices (f (g (g' 0))) ≤ (f (g (g' 1))) by simpa
    · refine Prod.Lex.toLex_le_toLex.mpr <| .inr ⟨?_, ?_⟩
      · exact (hhc (g' 0)).symm.trans (hhc (g' 1))
      · exact hg' (Nat.zero_le 1)
/-
**Set.PartiallyWellOrderedOn.imageProdLex** 是 Mathlib 中的一个定理，位于命名空间 `Set.Partial
lyWellOrderedOn`。
形式化陈述：imageProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)} (hαβ : s.IsPWO) 
: ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO
参数：α ×ₗ β；hαβ : s.IsPWO。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.image_of_monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Pre
order α] [inst_1 : Preorder β] {s : Set α},   s.IsPWO → ∀ {f : α → β}, Monotone 
f → (f '' s).IsPW…
· 使用定理 `Prod.Lex.monotone_fst`：monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (
h : t <= c) : (ofLex t).1 <= (ofLex c).1
-/
theorem imageProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hαβ : s.IsPWO) : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO :=
  IsPWO.image_of_monotone hαβ Prod.Lex.monotone_fst
/-
**Set.PartiallyWellOrderedOn.fiberProdLex** 是 Mathlib 中的一个定理，位于命名空间 `Set.Partial
lyWellOrderedOn`。
形式化陈述：fiberProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)} (hαβ : s.IsPWO) 
(a : α) : {y | toLex (a, y) in s}.IsPWO
参数：α ×ₗ β；hαβ : s.IsPWO；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.IsPWO.image_of_monotoneOn`：∀ {α : Type u_2} {β : Type u_3} [inst : P
reorder α] [inst_1 : Preorder β] {s : Set α},   s.IsPWO → ∀ {f : α → β}, Monoton
eOn f s → (f '' s).…
· 使用定理 `Set.IsPWO.mono`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, t.Is
PWO → s ⊆ t → s.IsPWO
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.Lex.toLex_le_toLex`：toLex_le_toLex [LT α] [LE β] {x y : α × β} : to
Lex x <= toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 <= y.2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem fiberProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hαβ : s.IsPWO) (a : α) : {y | toLex (a, y) ∈ s}.IsPWO := by
  let f : α ×ₗ β → β := fun x => (ofLex x).2
  have h : {y | toLex (a, y) ∈ s} = f '' (s ∩ (fun x ↦ (ofLex x).1) ⁻¹' {a}) := by
    ext x
    simp [f]
  rw [h]
  apply IsPWO.image_of_monotoneOn (hαβ.mono inter_subset_left)
  rintro b ⟨-, hb⟩ c ⟨-, hc⟩ hbc
  simp only [mem_preimage, mem_singleton_iff] at hb hc
  have : (ofLex b).1 < (ofLex c).1 ∨ (ofLex b).1 = (ofLex c).1 ∧ f b ≤ f c :=
    Prod.Lex.toLex_le_toLex.mp hbc
  simp_all only [lt_self_iff_false, true_and, false_or]
/-
**Set.PartiallyWellOrderedOn.ProdLex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Partiall
yWellOrderedOn`。
形式化陈述：ProdLex_iff [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)} : s.IsPWO ↔ (
(fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO ∧ forall a, {y | toLex (a, y) in s
}.IsPWO
参数：α ×ₗ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PartiallyWellOrderedOn.imageProdLex`：imageProdLex [Preorder α] [Preo
rder β] {s : Set (α ×ₗ β)} (hαβ : s.IsPWO) : ((fun (x : α ×ₗ β) => (ofLex x).1) 
'' s).IsPWO
· 使用定理 `Set.PartiallyWellOrderedOn.fiberProdLex`：fiberProdLex [Preorder α] [Preo
rder β] {s : Set (α ×ₗ β)} (hαβ : s.IsPWO) (a : α) : {y | toLex (a, y) in s}.IsP
WO
· 使用定理 `Set.PartiallyWellOrderedOn.subsetProdLex`：subsetProdLex [PartialOrder α]
 [Preorder β] {s : Set (α ×ₗ β)} (hα : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).
IsPWO) (hβ : forall a, {y | to…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ProdLex_iff [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)} :
    s.IsPWO ↔
      ((fun (x : α ×ₗ β) ↦ (ofLex x).1) '' s).IsPWO ∧ ∀ a, {y | toLex (a, y) ∈ s}.IsPWO :=
  ⟨fun h ↦ ⟨imageProdLex h, fiberProdLex h⟩, fun h ↦ subsetProdLex h.1 h.2⟩

end Set.PartiallyWellOrderedOn

section ProdLex
variable {rα : α → α → Prop} {rβ : β → β → Prop} {f : γ → α} {g : γ → β} {s : Set γ}

/-- Stronger version of `WellFounded.prod_lex`. Instead of requiring `rβ on g` to be well-founded,
we only require it to be well-founded on fibers of `f`. -/
/-
**WellFounded.prod_lex_of_wellFoundedOn_fiber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.prod_lex_of_wellFoundedOn_fiber (hα : WellFounded (rα on f)) (
hβ : forall a, (f ⁻¹' {a}).WellFoundedOn (rβ on g)) : WellFounded (Prod.Lex rα r
β on fun c => (f c, g c))
参数：hα : WellFounded (rα on f)；hβ : forall a, (f ⁻¹' {a}).WellFoundedOn (rβ on g)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.mono`：mono (hr : WellFounded r) (h : forall a b, r' a b -> r
 a b) : WellFounded r'
· 使用定理 `WellFounded.onFun`：onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β}
 : WellFounded r -> WellFounded (r on f)
· 使用定理 `WellFounded.psigma_lex`：WellFounded.psigma_lex {α : Sort*} {β : α -> Sor
t*} {r : α -> α -> Prop} {s : forall a : α, β a -> β a -> Prop} (ha : WellFounde
d r) (hb : f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.wellFoundedOn_range`：wellFoundedOn_range : (range f).WellFoundedOn r
 ↔ WellFounded (r on f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Prod.lex_iff`：lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2
 y.2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `PSigma.subtype_ext`：∀ {α : Sort u_1} {β : Sort u_3} {p : α → β → Prop} {
x₀ x₁ : (a : α) ×' Subtype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = 
x₁
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Stronger version of `WellFounded.prod_lex`. Instead of requiring `rβ on g` to be
 well-founded,
we only require it to be well-founded on fibers of `f`.
-/
theorem WellFounded.prod_lex_of_wellFoundedOn_fiber (hα : WellFounded (rα on f))
    (hβ : ∀ a, (f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    WellFounded (Prod.Lex rα rβ on fun c => (f c, g c)) := by
  refine ((psigma_lex (wellFoundedOn_range.2 hα) fun a => hβ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | h' := Prod.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    exacts [⟨c, h'.1⟩, PSigma.subtype_ext (Subtype.ext h'.1) rfl, h'.2]
/-
**Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber (hα : s.WellFoundedOn (r
α on f)) (hβ : forall a, (s inter f ⁻¹' {a}).WellFoundedOn (rβ on g)) : s.WellFo
undedOn (Prod.Lex rα rβ on fun c => (f c, g c))
参数：hα : s.WellFoundedOn (rα on f)；hβ : forall a, (s inter f ⁻¹' {a}).WellFounded
On (rβ on g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.prod_lex_of_wellFoundedOn_fiber`：WellFounded.prod_lex_of_wel
lFoundedOn_fiber (hα : WellFounded (rα on f)) (hβ : forall a, (f ⁻¹' {a}).WellFo
undedOn (rβ on g)) : WellFounded …
· 使用定理 `WellFounded.mono`：mono (hr : WellFounded r) (h : forall a b, r' a b -> r
 a b) : WellFounded r'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `WellFounded.onFun`：onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β}
 : WellFounded r -> WellFounded (r on f)
-/
theorem Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber (hα : s.WellFoundedOn (rα on f))
    (hβ : ∀ a, (s ∩ f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    s.WellFoundedOn (Prod.Lex rα rβ on fun c => (f c, g c)) :=
  WellFounded.prod_lex_of_wellFoundedOn_fiber hα
    fun a ↦ ((hβ a).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun _ _ h ↦ ‹_›)

end ProdLex

section SigmaLex

variable {rι : ι → ι → Prop} {rπ : ∀ i, π i → π i → Prop} {f : γ → ι} {g : ∀ i, γ → π i} {s : Set γ}

/-- Stronger version of `PSigma.lex_wf`. Instead of requiring `rπ on g` to be well-founded, we only
require it to be well-founded on fibers of `f`. -/
/-
**WellFounded.sigma_lex_of_wellFoundedOn_fiber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.sigma_lex_of_wellFoundedOn_fiber (hι : WellFounded (rι on f)) 
(hπ : forall i, (f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) : WellFounded (Sigma.Le
x rι rπ on fun c => ⟨f c, g (f c) c⟩)
参数：hι : WellFounded (rι on f)；hπ : forall i, (f ⁻¹' {i}).WellFoundedOn (rπ i on 
g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.mono`：mono (hr : WellFounded r) (h : forall a b, r' a b -> r
 a b) : WellFounded r'
· 使用定理 `WellFounded.onFun`：onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β}
 : WellFounded r -> WellFounded (r on f)
· 使用定理 `WellFounded.psigma_lex`：WellFounded.psigma_lex {α : Sort*} {β : α -> Sor
t*} {r : α -> α -> Prop} {s : forall a : α, β a -> β a -> Prop} (ha : WellFounde
d r) (hb : f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.wellFoundedOn_range`：wellFoundedOn_range : (range f).WellFoundedOn r
 ↔ WellFounded (r on f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sigma.lex_iff`：lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1,
 s b.1 (h.rec a.2) b.2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `PSigma.subtype_ext`：∀ {α : Sort u_1} {β : Sort u_3} {p : α → β → Prop} {
x₀ x₁ : (a : α) ×' Subtype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = 
x₁
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Stronger version of `PSigma.lex_wf`. Instead of requiring `rπ on g` to be well-f
ounded, we only
require it to be well-founded on fibers of `f`.
-/
theorem WellFounded.sigma_lex_of_wellFoundedOn_fiber (hι : WellFounded (rι on f))
    (hπ : ∀ i, (f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    WellFounded (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  refine ((psigma_lex (wellFoundedOn_range.2 hι) fun a => hπ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | ⟨h', h''⟩ := Sigma.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    · exact ⟨c, h'⟩
    · exact PSigma.subtype_ext (Subtype.ext h') rfl
    · dsimp only [Subtype.coe_mk, Subrel, Order.Preimage] at *
      grind
/-
**Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber (hι : s.WellFoundedOn (
rι on f)) (hπ : forall i, (s inter f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) : s.W
ellFoundedOn (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩)
参数：hι : s.WellFoundedOn (rι on f)；hπ : forall i, (s inter f ⁻¹' {i}).WellFounded
On (rπ i on g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.sigma_lex_of_wellFoundedOn_fiber`：WellFounded.sigma_lex_of_w
ellFoundedOn_fiber (hι : WellFounded (rι on f)) (hπ : forall i, (f ⁻¹' {i}).Well
FoundedOn (rπ i on g i)) : WellFou…
· 使用定理 `WellFounded.mono`：mono (hr : WellFounded r) (h : forall a b, r' a b -> r
 a b) : WellFounded r'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `WellFounded.onFun`：onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β}
 : WellFounded r -> WellFounded (r on f)
-/
theorem Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber (hι : s.WellFoundedOn (rι on f))
    (hπ : ∀ i, (s ∩ f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    s.WellFoundedOn (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  change WellFounded (Sigma.Lex rι rπ on fun c : s => ⟨f c, g (f c) c⟩)
  exact
    @WellFounded.sigma_lex_of_wellFoundedOn_fiber _ s _ _ rπ (fun c => f c) (fun i c => g _ c) hι
      fun i => ((hπ i).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun b c h => ‹_›)

end SigmaLex

