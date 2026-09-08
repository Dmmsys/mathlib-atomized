/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Data.DFinsupp.Defs

/-!
# Unique products and related notions

A group `G` has *unique products* if for any two non-empty finite subsets `A, B ⊆ G`, there is an
element `g ∈ A * B` that can be written uniquely as a product of an element of `A` and an element
of `B`.  We call the formalization this property `UniqueProds`.  Since the condition requires no
property of the group operation, we define it for a Type simply satisfying `Mul`.  We also
introduce the analogous "additive" companion, `UniqueSums`, and link the two so that `to_additive`
converts `UniqueProds` into `UniqueSums`.

A common way of *proving* that a group satisfies the `UniqueProds/Sums` property is by assuming
the existence of some kind of ordering on the group that is well-behaved with respect to the
group operation and showing that minima/maxima are the "unique products/sums".
However, the order is just a convenience and is not part of the `UniqueProds/Sums` setup.

Here you can see several examples of Types that have `UniqueSums/Prods`
(`inferInstance` uses `Covariant.to_uniqueProds_left` and `Covariant.to_uniqueSums_left`).
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Group.UniqueProds.Basic

example : UniqueSums ℕ   := inferInstance
example : UniqueSums ℕ+  := inferInstance
example : UniqueSums ℤ   := inferInstance
example : UniqueSums ℚ   := inferInstance
example : UniqueSums ℝ   := inferInstance
example : UniqueProds ℕ+ := inferInstance
```

## Use in `(Add)MonoidAlgebra`s

`UniqueProds/Sums` allow to decouple certain arguments about `(Add)MonoidAlgebra`s into an argument
about the grading type and then a generic statement of the form "look at the coefficient of the
'unique product/sum'".
The file `Algebra/MonoidAlgebra/NoZeroDivisors` contains several examples of this use.
-/

@[expose] public section

assert_not_exists Cardinal Subsemiring Algebra Submodule StarModule FreeMonoid IsOrderedMonoid

open Finset

/-- Let `G` be a Type with multiplication, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueMul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive
      /-- Let `G` be a Type with addition, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueAdd A B a0 b0` asserts `a0 + b0` can be written in at
most one way as a sum of an element from `A` and an element from `B`. -/]
/-
**UniqueMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniqueMul {G} [Mul G] (A B : Finset G) (a0 b0 : G) : Prop
参数：A B : Finset G；a0 b0 : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def UniqueMul {G} [Mul G] (A B : Finset G) (a0 b0 : G) : Prop :=
  ∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0

namespace UniqueMul

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

@[to_additive]
/-
**UniqueMul.mono** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：mono {A' B' : Finset G} (hA : A subseteq A') (hB : B subseteq B') (h : Uni
queMul A' B' a0 b0) : UniqueMul A B a0 b0
参数：hA : A subseteq A'；hB : B subseteq B'；h : UniqueMul A' B' a0 b0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono {A' B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (h : UniqueMul A' B' a0 b0) :
    UniqueMul A B a0 b0 := fun _ _ ha hb he ↦ h (hA ha) (hB hb) he

@[to_additive (attr := nontriviality, simp)]
/-
**UniqueMul.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0 := by
  simp [UniqueMul, eq_iff_true_of_subsingleton]

@[to_additive of_card_le_one]
/-
**UniqueMul.of_card_le_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：of_card_le_one (hA : A.Nonempty) (hB : B.Nonempty) (hA1 : #A <= 1) (hB1 : 
#B <= 1) : exists a in A, exists b in B, UniqueMul A B a b
参数：hA : A.Nonempty；hB : B.Nonempty；hA1 : #A <= 1；hB1 : #B <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_le_one_iff`：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s
 -> b in s -> a = b
-/
theorem of_card_le_one (hA : A.Nonempty) (hB : B.Nonempty) (hA1 : #A ≤ 1) (hB1 : #B ≤ 1) :
    ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  rw [Finset.card_le_one_iff] at hA1 hB1
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  exact ⟨a, ha, b, hb, fun _ _ ha' hb' _ ↦ ⟨hA1 ha' ha, hB1 hb' hb⟩⟩

@[to_additive]
/-
**UniqueMul.mt** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：mt (h : UniqueMul A B a0 b0) : forall ⦃a b⦄, a in A -> b in B -> a != a0 ∨
 b != b0 -> a * b != a0 * b0
参数：h : UniqueMul A B a0 b0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mt (h : UniqueMul A B a0 b0) :
    ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 := fun _ _ ha hb k ↦ by
  contrapose! k
  exact h ha hb k

@[to_additive]
/-
**UniqueMul.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：subsingleton (h : UniqueMul A B a0 b0) : Subsingleton { ab : G × G // ab.1
 in A ∧ ab.2 in B ∧ ab.1 * ab.2 = a0 * b0 }
参数：h : UniqueMul A B a0 b0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem subsingleton (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
  ⟨fun ⟨⟨_a, _b⟩, ha, hb, ab⟩ ⟨⟨_a', _b'⟩, ha', hb', ab'⟩ ↦
    Subtype.ext <|
      Prod.ext ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) <|
        (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩

@[to_additive]
/-
**UniqueMul.set_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：set_subsingleton (h : UniqueMul A B a0 b0) : Set.Subsingleton { ab : G × G
 | ab.1 in A ∧ ab.2 in B ∧ ab.1 * ab.2 = a0 * b0 }
参数：h : UniqueMul A B a0 b0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem set_subsingleton (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl

@[to_additive]
/-
**UniqueMul.iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：iff_existsUnique (aA : a0 in A) (bB : b0 in B) : UniqueMul A B a0 b0 ↔ exi
sts! ab, ab in A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0
参数：aA : a0 in A；bB : b0 in B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mk_mem_product`：mk_mem_product (ha : a in s) (hb : b in t) : (a, 
b) in s ×ˢ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `ExistsUnique.elim`：ExistsUnique.elim {p : α -> Prop} {b : Prop} (h₂ : ex
ists! x, p x) (h₁ : forall x, p x -> (forall y, p y -> y = x) -> b) : b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
-/
theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0 :=
  ⟨fun _ ↦ ⟨(a0, b0), ⟨Finset.mk_mem_product aA bB, rfl⟩, by simpa⟩,
    fun h ↦ h.elim
      (by
        rintro ⟨x1, x2⟩ _ J x y hx hy l
        rcases Prod.mk_inj.mp (J (a0, b0) ⟨Finset.mk_mem_product aA bB, rfl⟩) with ⟨rfl, rfl⟩
        exact Prod.mk_inj.mp (J (x, y) ⟨Finset.mk_mem_product hx hy, l⟩))⟩

open Finset in
@[to_additive iff_card_le_one]
/-
**UniqueMul.iff_card_le_one** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：iff_card_le_one [DecidableEq G] (ha0 : a0 in A) (hb0 : b0 in B) : UniqueMu
l A B a0 b0 ↔ #{p in A ×ˢ B | p.1 * p.2 = a0 * b0} <= 1
参数：ha0 : a0 in A；hb0 : b0 in B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem iff_card_le_one [DecidableEq G] (ha0 : a0 ∈ A) (hb0 : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ #{p ∈ A ×ˢ B | p.1 * p.2 = a0 * b0} ≤ 1 := by
  simp_rw [card_le_one_iff, mem_filter, mem_product]
  refine ⟨fun h p1 p2 ⟨⟨ha1, hb1⟩, he1⟩ ⟨⟨ha2, hb2⟩, he2⟩ ↦ ?_, fun h a b ha hb he ↦ ?_⟩
  · have h1 := h ha1 hb1 he1; have h2 := h ha2 hb2 he2
    grind
  · exact Prod.ext_iff.1 (@h (a, b) (a0, b0) ⟨⟨ha, hb⟩, he⟩ ⟨⟨ha0, hb0⟩, rfl⟩)

@[to_additive]
/-
**UniqueMul.exists_iff_exists_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`
。
形式化陈述：exists_iff_exists_existsUnique : (exists a0 b0 : G, a0 in A ∧ b0 in B ∧ Un
iqueMul A B a0 b0) ↔ exists g : G, exists! ab, ab in A ×ˢ B ∧ ab.1 * ab.2 = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniqueMul.iff_existsUnique`：iff_existsUnique (aA : a0 in A) (bB : b0 in 
B) : UniqueMul A B a0 b0 ↔ exists! ab, ab in A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = g :=
  ⟨fun ⟨_, _, hA, hB, h⟩ ↦ ⟨_, (iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ ↦ by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨a, b, ha, hb, (iff_existsUnique ha hb).mpr h⟩⟩

/-- `UniqueMul` is preserved by inverse images under injective, multiplicative maps. -/
@[to_additive /-- `UniqueAdd` is preserved by inverse images under injective, additive maps. -/]
/-
**UniqueMul.mulHom_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：mulHom_preimage (f : G ->ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A 
B : Finset H} (u : UniqueMul A B (f a0) (f b0)) : UniqueMul (A.preimage f hf.inj
On) (B.preimage f hf.injOn) a0 b0
参数：f : G ->ₙ* H；hf : Function.Injective f；a0 b0 : G；u : UniqueMul A B (f a0) (f 
b0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y

--- 原说明 ---
`UniqueMul` is preserved by inverse images under injective, multiplicative maps.
-/
theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.preimage f hf.injOn) (B.preimage f hf.injOn) a0 b0 := by
  intro a b ha hb ab
  simp only [← hf.eq_iff, map_mul] at ab ⊢
  exact u (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb) ab
/-
**UniqueMul.of_mulHom_image** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Mul G] [inst_1 : Mul H] {A B : Fin
set G} {a0 b0 : G} [inst_2 : DecidableEq H]   (f : G →ₙ* H),   (∀ ⦃a b c d : G⦄,
 a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d) →     UniqueMul (Finset.
image (⇑f) A) (Finset.image (⇑f) B) (f a0) (f b0) → UniqueMul A B a0 b0
参数：f : G →ₙ* H；∀ ⦃a b c d : G⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ 
b = d；Finset.image (⇑f) A；Finset.image (⇑f) B；f a0；f b0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] theorem of_mulHom_image [DecidableEq H] (f : G →ₙ* H)
    (hf : ∀ ⦃a b c d : G⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d)
    (h : UniqueMul (A.image f) (B.image f) (f a0) (f b0)) : UniqueMul A B a0 b0 :=
  fun a b ha hb ab ↦ hf ab
    (h (Finset.mem_image_of_mem f ha) (Finset.mem_image_of_mem f hb) <| by simp_rw [← map_mul, ab])

/-- `Unique_Mul` is preserved under multiplicative maps that are injective.

See `UniqueMul.mulHom_map_iff` for a version with swapped bundling. -/
@[to_additive
      /-- `UniqueAdd` is preserved under additive maps that are injective.

See `UniqueAdd.addHom_map_iff` for a version with swapped bundling. -/]
/-
**UniqueMul.mulHom_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：mulHom_image_iff [DecidableEq H] (f : G ->ₙ* H) (hf : Function.Injective f
) : UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0
参数：f : G ->ₙ* H；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMul.of_mulHom_image`：∀ {G : Type u_1} {H : Type u_2} [inst : Mul G
] [inst_1 : Mul H] {A B : Finset G} {a0 b0 : G} [inst_2 : DecidableEq H]   (f : 
G →ₙ* H),   (∀ …
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem mulHom_image_iff [DecidableEq H] (f : G →ₙ* H) (hf : Function.Injective f) :
    UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 :=
  ⟨of_mulHom_image f fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·), fun h _ _ ↦ by
    simp_rw [Finset.mem_image]
    rintro ⟨a, aA, rfl⟩ ⟨b, bB, rfl⟩ ab
    simp_rw [← map_mul, hf.eq_iff] at ab ⊢
    exact h aA bB ab⟩

/-- `UniqueMul` is preserved under embeddings that are multiplicative.

See `UniqueMul.mulHom_image_iff` for a version with swapped bundling. -/
@[to_additive
      /-- `UniqueAdd` is preserved under embeddings that are additive.

See `UniqueAdd.addHom_image_iff` for a version with swapped bundling. -/]
/-
**UniqueMul.mulHom_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：mulHom_map_iff (f : G ↪ H) (mul : forall x y, f (x * y) = f x * f y) : Uni
queMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0
参数：f : G ↪ H；mul : forall x y, f (x * y) = f x * f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueMul.mulHom_image_iff`：mulHom_image_iff [DecidableEq H] (f : G ->ₙ*
 H) (hf : Function.Injective f) : UniqueMul (A.image f) (B.image f) (f a0) (f b0
) ↔ UniqueMul A …
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical simp_rw [← mulHom_image_iff ⟨f, mul⟩ f.2, Finset.map_eq_image]; rfl

section Opposites
open Finset MulOpposite

@[to_additive]
/-
**UniqueMul.of_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：of_mulOpposite (h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_inje
ctive⟩) (op b0) (op a0)) : UniqueMul A B a0 b0
参数：h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op
 a0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem of_mulOpposite
    (h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) :
    UniqueMul A B a0 b0 := fun a b aA bB ab ↦ by
  simpa [and_comm] using h (mem_map_of_mem _ bB) (mem_map_of_mem _ aA) (congr_arg op ab)

@[to_additive]
/-
**UniqueMul.to_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：to_mulOpposite (h : UniqueMul A B a0 b0) : UniqueMul (B.map ⟨_, op_injecti
ve⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)
参数：h : UniqueMul A B a0 b0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMul.of_mulOpposite`：of_mulOpposite (h : UniqueMul (B.map ⟨_, op_in
jective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) : UniqueMul A B a0 b0
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniqueMul.mulHom_map_iff`：mulHom_map_iff (f : G ↪ H) (mul : forall x y, 
f (x * y) = f x * f y) : UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul
 A B a0 b0
-/
theorem to_mulOpposite (h : UniqueMul A B a0 b0) :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) :=
  of_mulOpposite (by simp_rw [map_map]; exact (mulHom_map_iff _ fun _ _ ↦ by rfl).mpr h)

@[to_additive]
/-
**UniqueMul.iff_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：iff_mulOpposite : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_inject
ive⟩) (op b0) (op a0) ↔ UniqueMul A B a0 b0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `UniqueMul.of_mulOpposite`：of_mulOpposite (h : UniqueMul (B.map ⟨_, op_in
jective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) : UniqueMul A B a0 b0
· 使用定理 `UniqueMul.to_mulOpposite`：to_mulOpposite (h : UniqueMul A B a0 b0) : Uni
queMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)
-/
theorem iff_mulOpposite :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) ↔
      UniqueMul A B a0 b0 :=
  ⟨of_mulOpposite, to_mulOpposite⟩

end Opposites

open Finset in
@[to_additive]
/-
**UniqueMul.of_image_filter** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMul`。
形式化陈述：of_image_filter [DecidableEq H] (f : G ->ₙ* H) {A B : Finset G} {aG bG : G
} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH) (huH : UniqueMul (A.image f) (
B.image f) aH bH) (huG : UniqueMul {a in A | f a = aH} {b in B | f b = bH} aG bG
) : UniqueMul A B aG bG
参数：f : G ->ₙ* H；hae : f aG = aH；hbe : f bG = bH；huH : UniqueMul (A.image f) (B.i
mage f) aH bH；huG : UniqueMul {a in A | f a = aH} {b in B | f b = bH} aG bG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem of_image_filter [DecidableEq H]
    (f : G →ₙ* H) {A B : Finset G} {aG bG : G} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH)
    (huH : UniqueMul (A.image f) (B.image f) aH bH)
    (huG : UniqueMul {a ∈ A | f a = aH} {b ∈ B | f b = bH} aG bG) :
    UniqueMul A B aG bG := fun a b ha hb he ↦ by
  specialize huH (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
  rw [← map_mul, he, map_mul, hae, hbe] at huH
  refine huG ?_ ?_ he <;> rw [mem_filter]
  exacts [⟨ha, (huH rfl).1⟩, ⟨hb, (huH rfl).2⟩]

end UniqueMul

/-- Let `G` be a Type with addition.  `UniqueSums G` asserts that any two non-empty
finite subsets of `G` have the `UniqueAdd` property, with respect to some element of their
sum `A + B`. -/
/-
**UniqueSums** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Add G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` be a Type with addition.  `UniqueSums G` asserts that any two non-empty
finite subsets of `G` have the `UniqueAdd` property, with respect to some elemen
t of their
sum `A + B`.
-/
class UniqueSums (G) [Add G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueAdd A B a0 b0` -/
  uniqueAdd_of_nonempty :
    ∀ {A B : Finset G}, A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueAdd A B a0 b0

/-- Let `G` be a Type with multiplication.  `UniqueProds G` asserts that any two non-empty
finite subsets of `G` have the `UniqueMul` property, with respect to some element of their
product `A * B`. -/
/-
**UniqueProds** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Mul G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` be a Type with multiplication.  `UniqueProds G` asserts that any two non
-empty
finite subsets of `G` have the `UniqueMul` property, with respect to some elemen
t of their
product `A * B`.
-/
class UniqueProds (G) [Mul G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueMul A B a0 b0` -/
  uniqueMul_of_nonempty :
    ∀ {A B : Finset G}, A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueMul A B a0 b0

attribute [to_additive] UniqueProds

/-- Let `G` be a Type with addition. `TwoUniqueSums G` asserts that any two non-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at least two pairs
of elements satisfying the `UniqueAdd` property. -/
/-
**TwoUniqueSums** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Add G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` be a Type with addition. `TwoUniqueSums G` asserts that any two non-empt
y
finite subsets of `G`, at least one of which is not a singleton, possesses at le
ast two pairs
of elements satisfying the `UniqueAdd` property.
-/
class TwoUniqueSums (G) [Add G] : Prop where
/-- For `A B` two finite sets whose product has cardinality at least 2,
  we can find at least two unique pairs. -/
  uniqueAdd_of_one_lt_card : ∀ {A B : Finset G}, 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueAdd A B p1.1 p1.2 ∧ UniqueAdd A B p2.1 p2.2

/-- Let `G` be a Type with multiplication. `TwoUniqueProds G` asserts that any two non-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at least two pairs
of elements satisfying the `UniqueMul` property. -/
/-
**TwoUniqueProds** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Mul G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` be a Type with multiplication. `TwoUniqueProds G` asserts that any two n
on-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at le
ast two pairs
of elements satisfying the `UniqueMul` property.
-/
class TwoUniqueProds (G) [Mul G] : Prop where
/-- For `A B` two finite sets whose product has cardinality at least 2,
  we can find at least two unique pairs. -/
  uniqueMul_of_one_lt_card : ∀ {A B : Finset G}, 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2

attribute [to_additive] TwoUniqueProds

@[to_additive]
/-
**uniqueMul_of_twoUniqueMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniqueMul_of_twoUniqueMul {G} [Mul G] {A B : Finset G} (h : 1 < #A * #B ->
 exists p1 in A ×ˢ B, exists p2 in A ×ˢ B, p1 != p2 ∧ UniqueMul A B p1.1 p1.2 ∧ 
UniqueMul A B p2.1 p2.2) (hA : A.Nonempty) (hB : B.Nonempty) : exists a in A, ex
ists b in B, UniqueMul A B a b
参数：h : 1 < #A * #B -> exists p1 in A ×ˢ B, exists p2 in A ×ˢ B, p1 != p2 ∧ Uniqu
eMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2；hA : A.Nonempty；hB : B.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMul.of_card_le_one`：of_card_le_one (hA : A.Nonempty) (hB : B.Nonem
pty) (hA1 : #A <= 1) (hB1 : #B <= 1) : exists a in A, exists b in B, UniqueMul A
 B a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_mul_iff`：∀ {m n : ℕ}, 1 < m * n ↔ 0 < m ∧ 0 < n ∧ (1 < m ∨ 1 
< n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
lemma uniqueMul_of_twoUniqueMul {G} [Mul G] {A B : Finset G} (h : 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2)
    (hA : A.Nonempty) (hB : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  by_cases! +distrib hc : #A ≤ 1 ∧ #B ≤ 1
  · exact UniqueMul.of_card_le_one hA hB hc.1 hc.2
  rw [← Finset.card_pos] at hA hB
  obtain ⟨p, hp, _, _, _, hu, _⟩ := h (Nat.one_lt_mul_iff.mpr ⟨hA, hB, hc⟩)
  rw [Finset.mem_product] at hp
  exact ⟨p.1, hp.1, p.2, hp.2, hu⟩
/-
**TwoUniqueProds.toUniqueProds** 是 Mathlib 中的一个定理，位于命名空间 `TwoUniqueProds`。
形式化陈述：∀ (G : Type u_1) [inst : Mul G] [TwoUniqueProds G], UniqueProds G
参数：G : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `uniqueMul_of_twoUniqueMul`：uniqueMul_of_twoUniqueMul {G} [Mul G] {A B : 
Finset G} (h : 1 < #A * #B -> exists p1 in A ×ˢ B, exists p2 in A ×ˢ B, p1 != p2
 ∧ UniqueMul A …
· 使用定理 `TwoUniqueProds.uniqueMul_of_one_lt_card`：∀ {G : Type u_1} {inst : Mul G}
 [self : TwoUniqueProds G] {A B : Finset G},   1 < A.card * B.card → ∃ p1 ∈ A ×ˢ
 B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ …
-/
@[to_additive] instance TwoUniqueProds.toUniqueProds (G) [Mul G] [TwoUniqueProds G] :
    UniqueProds G where
  uniqueMul_of_nonempty := uniqueMul_of_twoUniqueMul uniqueMul_of_one_lt_card

namespace Multiplicative

/-
**Multiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `Multiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M} [Add M] [UniqueSums M] : UniqueProds (Multiplicative M) where
  uniqueMul_of_nonempty := UniqueSums.uniqueAdd_of_nonempty (G := M)
/-
**Multiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `Multiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M} [Add M] [TwoUniqueSums M] : TwoUniqueProds (Multiplicative M) where
  uniqueMul_of_one_lt_card := TwoUniqueSums.uniqueAdd_of_one_lt_card (G := M)

end Multiplicative

namespace Additive

/-
**Additive.** 是 Mathlib 中的一个实例，位于命名空间 `Additive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M} [Mul M] [UniqueProds M] : UniqueSums (Additive M) where
  uniqueAdd_of_nonempty := UniqueProds.uniqueMul_of_nonempty (G := M)
/-
**Additive.** 是 Mathlib 中的一个实例，位于命名空间 `Additive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M} [Mul M] [TwoUniqueProds M] : TwoUniqueSums (Additive M) where
  uniqueAdd_of_one_lt_card := TwoUniqueProds.uniqueMul_of_one_lt_card (G := M)

end Additive

universe u v
variable (G : Type u) (H : Type v) [Mul G] [Mul H]

/-
**I** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private abbrev I : Bool → Type max u v := Bool.rec (ULift.{v} G) (ULift.{u} H)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] private instance : ∀ b, Mul (I G H b) := Bool.rec ULift.mul ULift.mul
/-
**Prod.upMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] private def Prod.upMulHom : G × H →ₙ* ∀ b, I G H b :=
  ⟨fun x ↦ Bool.rec ⟨x.1⟩ ⟨x.2⟩, fun x y ↦ by ext (_ | _) <;> rfl⟩
/-
**downMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] private def downMulHom : ULift G →ₙ* G := ⟨ULift.down, fun _ _ ↦ rfl⟩

variable {G H}

namespace UniqueProds

open Finset

/-
**UniqueProds.of_mulHom** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：∀ {G : Type u} {H : Type v} [inst : Mul G] [inst_1 : Mul H] (f : H →ₙ* G),
   (∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d) → ∀ 
[UniqueProds G], UniqueProds H
参数：f : H →ₙ* G；∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ 
b = d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueProds.uniqueMul_of_nonempty`：∀ {G : Type u_1} {inst : Mul G} [self
 : UniqueProds G] {A B : Finset G},   A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈
 B, UniqueMul A B a0 b0
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `UniqueMul.of_mulHom_image`：∀ {G : Type u_1} {H : Type u_2} [inst : Mul G
] [inst_1 : Mul H] {A B : Finset G} {a0 b0 : G} [inst_2 : DecidableEq H]   (f : 
G →ₙ* H),   (∀ …
-/
@[to_additive] theorem of_mulHom (f : H →ₙ* G)
    (hf : ∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d)
    [UniqueProds G] : UniqueProds H where
  uniqueMul_of_nonempty {A B} A0 B0 := by
    classical
    obtain ⟨a0, ha0, b0, hb0, h⟩ := uniqueMul_of_nonempty (A0.image f) (B0.image f)
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha0
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hb0
    exact ⟨a', ha', b', hb', UniqueMul.of_mulHom_image f hf h⟩

@[to_additive]
/-
**UniqueProds.of_injective_mulHom** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：of_injective_mulHom (f : H ->ₙ* G) (hf : Function.Injective f) (_ : Unique
Prods G) : UniqueProds H
参数：f : H ->ₙ* G；hf : Function.Injective f；_ : UniqueProds G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueProds.of_mulHom`：∀ {G : Type u} {H : Type v} [inst : Mul G] [inst_
1 : Mul H] (f : H →ₙ* G),   (∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = 
f d → a = c…
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
-/
theorem of_injective_mulHom (f : H →ₙ* G) (hf : Function.Injective f) (_ : UniqueProds G) :
    UniqueProds H := of_mulHom f (fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·))

/-- `UniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive /-- `UniqueSums` is preserved under additive equivalences. -/]
/-
**UniqueProds._root_.MulEquiv.uniqueProds_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniqueP
rods`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`UniqueProd` is preserved under multiplicative equivalences.
-/
theorem _root_.MulEquiv.uniqueProds_iff (f : G ≃* H) : UniqueProds G ↔ UniqueProds H :=
  ⟨of_injective_mulHom f.symm f.symm.injective, of_injective_mulHom f f.injective⟩

open Finset MulOpposite in
@[to_additive]
/-
**UniqueProds.of_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：of_mulOpposite (h : UniqueProds Gᵐᵒᵖ) : UniqueProds G where uniqueMul_of_n
onempty hA hB
参数：h : UniqueProds Gᵐᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `UniqueProds.uniqueMul_of_nonempty`：∀ {G : Type u_1} {inst : Mul G} [self
 : UniqueProds G] {A B : Finset G},   A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈
 B, UniqueMul A B a0 b0
· 使用定理 `Finset.Nonempty.map`：∀ {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s : Fi
nset α}, s.Nonempty → (Finset.map f s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
· 使用定理 `UniqueMul.of_mulOpposite`：of_mulOpposite (h : UniqueMul (B.map ⟨_, op_in
jective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) : UniqueMul A B a0 b0
-/
theorem of_mulOpposite (h : UniqueProds Gᵐᵒᵖ) : UniqueProds G where
  uniqueMul_of_nonempty hA hB :=
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    let ⟨y, yB, x, xA, hxy⟩ := h.uniqueMul_of_nonempty (hB.map (f := f)) (hA.map (f := f))
    ⟨unop x, (mem_map' _).mp xA, unop y, (mem_map' _).mp yB, hxy.of_mulOpposite⟩
/-
**UniqueProds.** 是 Mathlib 中的一个实例，位于命名空间 `UniqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [h : UniqueProds G] : UniqueProds Gᵐᵒᵖ :=
  of_mulOpposite <| (MulEquiv.opOp G).uniqueProds_iff.mp h
/-
**UniqueProds.toIsLeftCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] private theorem toIsLeftCancelMul [UniqueProds G] : IsLeftCancelMul G where
  mul_left_cancel a b1 b2 he := by
    classical
    have := mem_insert_self b1 {b2}
    obtain ⟨a, ha, b, hb, hu⟩ := uniqueMul_of_nonempty ⟨a, mem_singleton_self a⟩ ⟨b1, this⟩
    cases mem_singleton.mp ha
    simp_rw [mem_insert, mem_singleton] at hb
    obtain rfl | rfl := hb
    · exact (hu ha (mem_insert_of_mem <| mem_singleton_self b2) he.symm).2.symm
    · exact (hu ha this he).2

open MulOpposite in
/-
**UniqueProds.toIsCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：∀ {G : Type u} [inst : Mul G] [UniqueProds G], IsCancelMul G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Group.UniqueProds.Basic.0.UniqueProds.toIsLeftC
ancelMul`：∀ {G : Type u} [inst : Mul G] [UniqueProds G], IsLeftCancelMul G
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `IsLeftCancelMul.mul_left_cancel`：∀ {G : Type u} {inst : Mul G} [self : I
sLeftCancelMul G] (a : G), IsLeftRegular a
· 使用定理 `UniqueProds.instMulOpposite`：∀ {G : Type u} [inst : Mul G] [h : UniquePr
ods G], UniqueProds Gᵐᵒᵖ
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
@[to_additive] theorem toIsCancelMul [UniqueProds G] : IsCancelMul G where
  mul_left_cancel := toIsLeftCancelMul.mul_left_cancel
  mul_right_cancel _ _ _ h :=
    op_injective <| toIsLeftCancelMul.mul_left_cancel _ <| unop_injective h

/-! Two theorems in [Andrzej Strojnowski, *A note on u.p. groups*][Strojnowski1980] -/

/-- `UniqueProds G` says that for any two nonempty `Finset`s `A` and `B` in `G`, `A × B`
  contains a unique pair with the `UniqueMul` property. Strojnowski showed that if `G` is
  a group, then we only need to check this when `A = B`.
  Here we generalize the result to cancellative semigroups.
  Non-cancellative counterexample: the AddMonoid `{0,1}` with 1+1=1. -/
/-
**UniqueProds.of_same** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：∀ {G : Type u_1} [inst : Semigroup G] [IsCancelMul G],   (∀ {A : Finset G}
, A.Nonempty → ∃ a1 ∈ A, ∃ a2 ∈ A, UniqueMul A A a1 a2) → UniqueProds G
参数：∀ {A : Finset G}, A.Nonempty → ∃ a1 ∈ A, ∃ a2 ∈ A, UniqueMul A A a1 a2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.mul`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : M
ul α] {s t : Finset α}, s.Nonempty → t.Nonempty → (s * t).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_mul`：mem_mul {x : α} : x in s * t ↔ exists y in s, exists z i
n t, y * z = x
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`UniqueProds G` says that for any two nonempty `Finset`s `A` and `B` in `G`, `A 
× B`
  contains a unique pair with the `UniqueMul` property. Strojnowski showed that 
if `G` is
  a group, then we only need to check this when `A = B`.
  Here we generalize the result to cancellative semigroups.
  Non-cancellative counterexample: the AddMonoid `{0,1}` with 1+1=1.
-/
@[to_additive] theorem of_same {G} [Semigroup G] [IsCancelMul G]
    (h : ∀ {A : Finset G}, A.Nonempty → ∃ a1 ∈ A, ∃ a2 ∈ A, UniqueMul A A a1 a2) :
    UniqueProds G where
  uniqueMul_of_nonempty {A B} hA hB := by
    classical
    obtain ⟨g1, h1, g2, h2, hu⟩ := h (hB.mul hA)
    obtain ⟨b1, hb1, a1, ha1, rfl⟩ := mem_mul.mp h1
    obtain ⟨b2, hb2, a2, ha2, rfl⟩ := mem_mul.mp h2
    refine ⟨a1, ha1, b2, hb2, fun a b ha hb he => ?_⟩
    specialize hu (mul_mem_mul hb1 ha) (mul_mem_mul hb ha2) _
    · rw [mul_assoc b1, ← mul_assoc a, he, mul_assoc a1, ← mul_assoc b1]
    exact ⟨mul_left_cancel hu.1, mul_right_cancel hu.2⟩

/-- If a group has `UniqueProds`, then it actually has `TwoUniqueProds`.
  For an example of a semigroup `G` embeddable into a group that has `UniqueProds`
  but not `TwoUniqueProds`, see Example 10.13 in
  [J. Okniński, *Semigroup Algebras*][Okninski1991]. -/
/-
**UniqueProds.toTwoUniqueProds_of_group** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [UniqueProds G], TwoUniqueProds G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueProds.uniqueMul_of_nonempty`：∀ {G : Type u_1} {inst : Mul G} [self
 : UniqueProds G] {A B : Finset G},   A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈
 B, UniqueMul A B a0 b0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Finset.Nonempty.mul`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : M
ul α] {s t : Finset α}, s.Nonempty → t.Nonempty → (s * t).Nonempty
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.Nonempty.map`：∀ {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s : Fi
nset α}, s.Nonempty → (Finset.map f s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel_iff`：mul_right_cancel_iff : b * a = c * a ↔ b = c
· 使用定理 `mul_left_cancel_iff`：mul_left_cancel_iff : a * b = a * c ↔ b = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.exists_mem_ne`：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in 
s, b != a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If a group has `UniqueProds`, then it actually has `TwoUniqueProds`.
  For an example of a semigroup `G` embeddable into a group that has `UniqueProd
s`
  but not `TwoUniqueProds`, see Example 10.13 in
  [J. Okniński, *Semigroup Algebras*][Okninski1991].
-/
@[to_additive] theorem toTwoUniqueProds_of_group {G}
    [Group G] [UniqueProds G] : TwoUniqueProds G where
  uniqueMul_of_one_lt_card {A B} hc := by
    simp_rw [Nat.one_lt_mul_iff, card_pos] at hc
    obtain ⟨a, ha, b, hb, hu⟩ := uniqueMul_of_nonempty hc.1 hc.2.1
    let C := A.map ⟨_, mul_right_injective a⁻¹⟩ -- C = a⁻¹A
    let D := B.map ⟨_, mul_left_injective b⁻¹⟩  -- D = Bb⁻¹
    have hcard : 1 < #C ∨ 1 < #D := by simp_rw [C, D, card_map]; exact hc.2.2
    have hC : 1 ∈ C := mem_map.mpr ⟨a, ha, inv_mul_cancel a⟩
    have hD : 1 ∈ D := mem_map.mpr ⟨b, hb, mul_inv_cancel b⟩
    suffices ∃ c ∈ C, ∃ d ∈ D, (c ≠ 1 ∨ d ≠ 1) ∧ UniqueMul C D c d by
      simp_rw [mem_product]
      obtain ⟨c, hc, d, hd, hne, hu'⟩ := this
      obtain ⟨a0, ha0, rfl⟩ := mem_map.mp hc
      obtain ⟨b0, hb0, rfl⟩ := mem_map.mp hd
      refine ⟨(_, _), ⟨ha0, hb0⟩, (a, b), ⟨ha, hb⟩, ?_, fun a' b' ha' hb' he => ?_, hu⟩
      · simp_rw [Function.Embedding.coeFn_mk, Ne, inv_mul_eq_one, mul_inv_eq_one] at hne
        rwa [Ne, Prod.mk_inj, not_and_or, eq_comm]
      specialize hu' (mem_map_of_mem _ ha') (mem_map_of_mem _ hb')
      simp_rw [Function.Embedding.coeFn_mk, mul_left_cancel_iff, mul_right_cancel_iff] at hu'
      rw [mul_assoc, ← mul_assoc a', he, mul_assoc, mul_assoc] at hu'
      exact hu' rfl
    classical
    let _ := Finset.mul (α := G)              -- E = D⁻¹C, F = DC⁻¹
    have := uniqueMul_of_nonempty (A := D.image (·⁻¹) * C) (B := D * C.image (·⁻¹)) ?_ ?_
    · obtain ⟨e, he, f, hf, hu⟩ := this
      clear_value C D
      simp only [UniqueMul, mem_mul, mem_image] at he hf hu
      obtain ⟨_, ⟨d1, hd1, rfl⟩, c1, hc1, rfl⟩ := he
      obtain ⟨d2, hd2, _, ⟨c2, hc2, rfl⟩, rfl⟩ := hf
      by_cases! h12 : c1 ≠ 1 ∨ d2 ≠ 1
      · refine ⟨c1, hc1, d2, hd2, h12, fun c3 d3 hc3 hd3 he => ?_⟩
        specialize hu ⟨_, ⟨_, hd1, rfl⟩, _, hc3, rfl⟩ ⟨_, hd3, _, ⟨_, hc2, rfl⟩, rfl⟩
        rw [mul_left_cancel_iff, mul_right_cancel_iff,
            mul_assoc, ← mul_assoc c3, he, mul_assoc, mul_assoc] at hu; exact hu rfl
      obtain ⟨rfl, rfl⟩ := h12
      by_cases! h21 : c2 ≠ 1 ∨ d1 ≠ 1
      · refine ⟨c2, hc2, d1, hd1, h21, fun c4 d4 hc4 hd4 he => ?_⟩
        specialize hu ⟨_, ⟨_, hd4, rfl⟩, _, hC, rfl⟩ ⟨_, hD, _, ⟨_, hc4, rfl⟩, rfl⟩
        simpa only [mul_one, one_mul, ← mul_inv_rev, he, true_imp_iff, inv_inj, and_comm] using hu
      obtain ⟨rfl, rfl⟩ := h21
      rcases hcard with hC | hD
      · obtain ⟨c, hc, hc1⟩ := exists_mem_ne hC 1
        refine (hc1 ?_).elim
        simpa using hu ⟨_, ⟨_, hD, rfl⟩, _, hc, rfl⟩ ⟨_, hD, _, ⟨_, hc, rfl⟩, rfl⟩
      · obtain ⟨d, hd, hd1⟩ := exists_mem_ne hD 1
        refine (hd1 ?_).elim
        simpa using hu ⟨_, ⟨_, hd, rfl⟩, _, hC, rfl⟩ ⟨_, hd, _, ⟨_, hC, rfl⟩, rfl⟩
    all_goals apply_rules [Nonempty.mul, Nonempty.image, Finset.Nonempty.map, hc.1, hc.2.1]

open UniqueMul in
/-
**UniqueProds.instForall** 是 Mathlib 中的一个定理，位于命名空间 `UniqueProds`。
形式化陈述：∀ {ι : Type u_2} (G : ι → Type u_1) [inst : (i : ι) → Mul (G i)] [∀ (i : ι
), UniqueProds (G i)],   UniqueProds ((i : ι) → G i)
参数：G : ι → Type u_1；i : ι；G i；i : ι；G i；(i : ι) → G i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a
· 使用定理 `UniqueMul.of_card_le_one`：of_card_le_one (hA : A.Nonempty) (hB : B.Nonem
pty) (hA1 : #A <= 1) (hB1 : #B <= 1) : exists a in A, exists b in B, UniqueMul A
 B a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_or`：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) ↔ (∃ x, p
 x) ∨ ∃ x, q x
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `Finset.exists_of_one_lt_card_pi`：exists_of_one_lt_card_pi {ι : Type*} {α
 : ι -> Type*} [forall i, DecidableEq (α i)] {s : Finset (forall i, α i)} (h : 1
 < #s) : exists i, 1 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueProds.uniqueMul_of_nonempty`：∀ {G : Type u_1} {inst : Mul G} [self
 : UniqueProds G] {A B : Finset G},   A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈
 B, UniqueMul A B a0 b0
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_nonempty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (Finset.filter p s).Nonempty ↔ ∃ a ∈ s, p a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `UniqueMul.of_image_filter`：of_image_filter [DecidableEq H] (f : G ->ₙ* H
) {A B : Finset G} {aG bG : G} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH) (
huH : UniqueMul…
-/
@[to_additive] instance instForall {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, UniqueProds (G i)] :
    UniqueProds (∀ i, G i) where
  uniqueMul_of_nonempty {A} := by
    classical
    let _ := isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B hA
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hB
    by_cases! +distrib hc : #A ≤ 1 ∧ #B ≤ 1
    · exact of_card_le_one hA hB hc.1 hc.2
    obtain ⟨i, hc⟩ := exists_or.mpr (hc.imp exists_of_one_lt_card_pi exists_of_one_lt_card_pi)
    obtain ⟨ai, hA, bi, hB, hi⟩ := uniqueMul_of_nonempty (hA.image (· i)) (hB.image (· i))
    rw [mem_image, ← filter_nonempty_iff] at hA hB
    let A' := {a ∈ A | a i = ai}; let B' := {b ∈ B | b i = bi}
    obtain ⟨a0, ha0, b0, hb0, hu⟩ : ∃ a0 ∈ A', ∃ b0 ∈ B', UniqueMul A' B' a0 b0 := by
      rcases hc with hc | hc; · exact ihA A' (hc.2 ai) hA hB
      by_cases hA' : A' = A
      · rw [hA']
        exact ihB B' (hc.2 bi) hB
      · exact ihA A' ((A.filter_subset _).ssubset_of_ne hA') hA hB
    rw [mem_filter] at ha0 hb0
    exact ⟨a0, ha0.1, b0, hb0.1, of_image_filter (Pi.evalMulHom G i) ha0.2 hb0.2 hi hu⟩

open ULift in
/-
**UniqueProds._root_.Prod.instUniqueProds** 是 Mathlib 中的一个实例，位于命名空间 `UniqueProds
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance _root_.Prod.instUniqueProds [UniqueProds G] [UniqueProds H] :
    UniqueProds (G × H) := by
  have : ∀ b, UniqueProds (I G H b) := Bool.rec ?_ ?_
  · exact of_injective_mulHom (downMulHom H) down_injective ‹_›
  · refine of_injective_mulHom (Prod.upMulHom G H) (fun x y he => Prod.ext ?_ ?_)
      (UniqueProds.instForall <| I G H) <;> apply up_injective
    exacts [congr_fun he false, congr_fun he true]
  · exact of_injective_mulHom (downMulHom G) down_injective ‹_›

end UniqueProds

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, UniqueSums (G i)] :
    UniqueSums (Π₀ i, G i) :=
  UniqueSums.of_injective_addHom
    DFinsupp.coeFnAddMonoidHom.toAddHom DFunLike.coe_injective inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι G} [AddZeroClass G] [UniqueSums G] : UniqueSums (ι →₀ G) :=
  UniqueSums.of_injective_addHom
    Finsupp.coeFnAddHom.toAddHom DFunLike.coe_injective inferInstance

namespace TwoUniqueProds

open Finset

/-
**TwoUniqueProds.of_mulHom** 是 Mathlib 中的一个定理，位于命名空间 `TwoUniqueProds`。
形式化陈述：∀ {G : Type u} {H : Type v} [inst : Mul G] [inst_1 : Mul H] (f : H →ₙ* G),
   (∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d) → ∀ 
[TwoUniqueProds G], TwoUniqueProds H
参数：f : H →ₙ* G；∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ 
b = d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `TwoUniqueProds.uniqueMul_of_one_lt_card`：∀ {G : Type u_1} {inst : Mul G}
 [self : TwoUniqueProds G] {A B : Finset G},   1 < A.card * B.card → ∃ p1 ∈ A ×ˢ
 B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `UniqueMul.of_mulHom_image`：∀ {G : Type u_1} {H : Type u_2} [inst : Mul G
] [inst_1 : Mul H] {A B : Finset G} {a0 b0 : G} [inst_2 : DecidableEq H]   (f : 
G →ₙ* H),   (∀ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < #s ↔
 s.Nontrivial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniqueMul.iff_card_le_one`：iff_card_le_one [DecidableEq G] (ha0 : a0 in 
A) (hb0 : b0 in B) : UniqueMul A B a0 b0 ↔ #{p in A ×ˢ B | p.1 * p.2 = a0 * b0} 
<= 1
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
-/
@[to_additive] theorem of_mulHom (f : H →ₙ* G)
    (hf : ∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d)
    [TwoUniqueProds G] : TwoUniqueProds H where
  uniqueMul_of_one_lt_card {A B} hc := by
    classical
    obtain hc' | hc' := lt_or_ge 1 (#(A.image f) * #(B.image f))
    · obtain ⟨⟨a1, b1⟩, h1, ⟨a2, b2⟩, h2, hne, hu1, hu2⟩ := uniqueMul_of_one_lt_card hc'
      simp_rw [mem_product, mem_image] at h1 h2 ⊢
      obtain ⟨⟨a1, ha1, rfl⟩, b1, hb1, rfl⟩ := h1
      obtain ⟨⟨a2, ha2, rfl⟩, b2, hb2, rfl⟩ := h2
      exact ⟨(a1, b1), ⟨ha1, hb1⟩, (a2, b2), ⟨ha2, hb2⟩, mt (congr_arg (Prod.map f f)) hne,
        UniqueMul.of_mulHom_image f hf hu1, UniqueMul.of_mulHom_image f hf hu2⟩
    rw [← card_product] at hc hc'
    obtain ⟨p1, h1, p2, h2, hne⟩ := one_lt_card_iff_nontrivial.mp hc
    refine ⟨p1, h1, p2, h2, hne, ?_⟩
    cases mem_product.mp h1; cases mem_product.mp h2
    constructor <;> refine UniqueMul.of_mulHom_image f hf
      ((UniqueMul.iff_card_le_one ?_ ?_).mpr <| (card_filter_le _ _).trans hc') <;>
    apply mem_image_of_mem <;> assumption

@[to_additive]
/-
**TwoUniqueProds.of_injective_mulHom** 是 Mathlib 中的一个定理，位于命名空间 `TwoUniqueProds`。
形式化陈述：of_injective_mulHom (f : H ->ₙ* G) (hf : Function.Injective f) (_ : TwoUni
queProds G) : TwoUniqueProds H
参数：f : H ->ₙ* G；hf : Function.Injective f；_ : TwoUniqueProds G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TwoUniqueProds.of_mulHom`：∀ {G : Type u} {H : Type v} [inst : Mul G] [in
st_1 : Mul H] (f : H →ₙ* G),   (∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b
 = f d → a = c…
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
-/
theorem of_injective_mulHom (f : H →ₙ* G) (hf : Function.Injective f)
    (_ : TwoUniqueProds G) : TwoUniqueProds H :=
  of_mulHom f (fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·))

/-- `TwoUniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive /-- `TwoUniqueSums` is preserved under additive equivalences. -/]
/-
**TwoUniqueProds._root_.MulEquiv.twoUniqueProds_iff** 是 Mathlib 中的一个定理，位于命名空间 `T
woUniqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TwoUniqueProd` is preserved under multiplicative equivalences.
-/
theorem _root_.MulEquiv.twoUniqueProds_iff (f : G ≃* H) : TwoUniqueProds G ↔ TwoUniqueProds H :=
  ⟨of_injective_mulHom f.symm f.symm.injective, of_injective_mulHom f f.injective⟩

@[to_additive]
/-
**TwoUniqueProds.instForall** 是 Mathlib 中的一个实例，位于命名空间 `TwoUniqueProds`。
形式化陈述：instForall {ι} (G : ι -> Type*) [forall i, Mul (G i)] [forall i, TwoUnique
Prods (G i)] : TwoUniqueProds (forall i, G i) where uniqueMul_of_one_lt_card {A}
参数：G : ι -> Type*；G i；G i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_lt_mul_iff`：∀ {m n : ℕ}, 1 < m * n ↔ 0 < m ∧ 0 < n ∧ (1 < m ∨ 1 
< n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_or`：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) ↔ (∃ x, p
 x) ∨ ∃ x, q x
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `Finset.exists_of_one_lt_card_pi`：exists_of_one_lt_card_pi {ι : Type*} {α
 : ι -> Type*} [forall i, DecidableEq (α i)] {s : Finset (forall i, α i)} (h : 1
 < #s) : exists i, 1 …
· 使用定理 `TwoUniqueProds.uniqueMul_of_one_lt_card`：∀ {G : Type u_1} {inst : Mul G}
 [self : TwoUniqueProds G] {A B : Finset G},   1 < A.card * B.card → ∃ p1 ∈ A ×ˢ
 B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ …
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `uniqueMul_of_twoUniqueMul`：uniqueMul_of_twoUniqueMul {G} [Mul G] {A B : 
Finset G} (h : 1 < #A * #B -> exists p1 in A ×ˢ B, exists p2 in A ×ˢ B, p1 != p2
 ∧ UniqueMul A …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `UniqueMul.of_image_filter`：of_image_filter [DecidableEq H] (f : G ->ₙ* H
) {A B : Finset G} {aG bG : G} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH) (
huH : UniqueMul…
-/
instance instForall {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, TwoUniqueProds (G i)] :
    TwoUniqueProds (∀ i, G i) where
  uniqueMul_of_one_lt_card {A} := by
    classical
    let _ := isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hc
    obtain ⟨hA, hB, hc⟩ := Nat.one_lt_mul_iff.mp hc
    rw [card_pos] at hA hB
    obtain ⟨i, hc⟩ := exists_or.mpr (hc.imp exists_of_one_lt_card_pi exists_of_one_lt_card_pi)
    obtain ⟨p1, h1, p2, h2, hne, hi1, hi2⟩ := uniqueMul_of_one_lt_card (Nat.one_lt_mul_iff.mpr
      ⟨card_pos.2 (hA.image _), card_pos.2 (hB.image _), hc.imp And.left And.left⟩)
    simp_rw [mem_product, mem_image, ← filter_nonempty_iff] at h1 h2
    replace h1 := uniqueMul_of_twoUniqueMul ?_ h1.1 h1.2
    on_goal 1 => replace h2 := uniqueMul_of_twoUniqueMul ?_ h2.1 h2.2
    · obtain ⟨a1, ha1, b1, hb1, hu1⟩ := h1
      obtain ⟨a2, ha2, b2, hb2, hu2⟩ := h2
      rw [mem_filter] at ha1 hb1 ha2 hb2
      simp_rw [mem_product]
      refine ⟨(a1, b1), ⟨ha1.1, hb1.1⟩, (a2, b2), ⟨ha2.1, hb2.1⟩, ?_,
        UniqueMul.of_image_filter (Pi.evalMulHom G i) ha1.2 hb1.2 hi1 hu1,
        UniqueMul.of_image_filter (Pi.evalMulHom G i) ha2.2 hb2.2 hi2 hu2⟩
      grind
    all_goals rcases hc with hc | hc; · exact ihA _ (hc.2 _)
    · by_cases hA : {a ∈ A | a i = p2.1} = A
      · rw [hA]
        exact ihB _ (hc.2 _)
      · exact ihA _ ((A.filter_subset _).ssubset_of_ne hA)
    · by_cases hA : {a ∈ A | a i = p1.1} = A
      · rw [hA]
        exact ihB _ (hc.2 _)
      · exact ihA _ ((A.filter_subset _).ssubset_of_ne hA)

open ULift in
@[to_additive]
/-
**TwoUniqueProds._root_.Prod.instTwoUniqueProds** 是 Mathlib 中的一个实例，位于命名空间 `TwoUn
iqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prod.instTwoUniqueProds [TwoUniqueProds G] [TwoUniqueProds H] :
    TwoUniqueProds (G × H) := by
  have : ∀ b, TwoUniqueProds (I G H b) := Bool.rec ?_ ?_
  · exact of_injective_mulHom (downMulHom H) down_injective ‹_›
  · refine of_injective_mulHom (Prod.upMulHom G H) (fun x y he ↦ Prod.ext ?_ ?_)
      (TwoUniqueProds.instForall <| I G H) <;> apply up_injective
    exacts [congr_fun he false, congr_fun he true]
  · exact of_injective_mulHom (downMulHom G) down_injective ‹_›

open MulOpposite in
@[to_additive]
/-
**TwoUniqueProds.of_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `TwoUniqueProds`。
形式化陈述：of_mulOpposite (h : TwoUniqueProds Gᵐᵒᵖ) : TwoUniqueProds G where uniqueMu
l_of_one_lt_card hc
参数：h : TwoUniqueProds Gᵐᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `TwoUniqueProds.uniqueMul_of_one_lt_card`：∀ {G : Type u_1} {inst : Mul G}
 [self : TwoUniqueProds G] {A B : Finset G},   1 < A.card * B.card → ∃ p1 ∈ A ×ˢ
 B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `UniqueMul.of_mulOpposite`：of_mulOpposite (h : UniqueMul (B.map ⟨_, op_in
jective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) : UniqueMul A B a0 b0
-/
theorem of_mulOpposite (h : TwoUniqueProds Gᵐᵒᵖ) : TwoUniqueProds G where
  uniqueMul_of_one_lt_card hc := by
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    rw [← card_map f, ← card_map f, mul_comm] at hc
    obtain ⟨p1, h1, p2, h2, hne, hu1, hu2⟩ := h.uniqueMul_of_one_lt_card hc
    simp_rw [mem_product] at h1 h2 ⊢
    refine ⟨(_, _), ⟨?_, ?_⟩, (_, _), ⟨?_, ?_⟩, ?_, hu1.of_mulOpposite, hu2.of_mulOpposite⟩
    pick_goal 5
    · contrapose hne; rw [Prod.ext_iff] at hne ⊢
      exact ⟨unop_injective hne.2, unop_injective hne.1⟩
    all_goals apply (mem_map' f).mp
    exacts [h1.2, h1.1, h2.2, h2.1]
/-
**TwoUniqueProds.** 是 Mathlib 中的一个实例，位于命名空间 `TwoUniqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [h : TwoUniqueProds G] : TwoUniqueProds Gᵐᵒᵖ :=
  of_mulOpposite <| (MulEquiv.opOp G).twoUniqueProds_iff.mp h

-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a right-cancellative multiplication, a linear order, and
  multiplication is strictly monotone w.r.t. the second argument, then `G` has `TwoUniqueProds`. -/
@[to_additive
  /-- This instance asserts that if `G` has a right-cancellative addition, a linear order,
  and addition is strictly monotone w.r.t. the second argument, then `G` has `TwoUniqueSums`. -/]
/-
**TwoUniqueProds.** 是 Mathlib 中的一个实例，位于命名空间 `TwoUniqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_covariant_right [IsRightCancelMul G]
    [LinearOrder G] [MulLeftStrictMono G] :
    TwoUniqueProds G where
  uniqueMul_of_one_lt_card {A B} hc := by
    obtain ⟨hA, hB, -⟩ := Nat.one_lt_mul_iff.mp hc
    rw [card_pos] at hA hB
    rw [← card_product] at hc
    obtain ⟨a0, ha0, b0, hb0, he0⟩ := mem_mul.mp (max'_mem _ <| hA.mul hB)
    obtain ⟨a1, ha1, b1, hb1, he1⟩ := mem_mul.mp (min'_mem _ <| hA.mul hB)
    have : UniqueMul A B a0 b0 := by
      intro a b ha hb he
      obtain hl | rfl | hl := lt_trichotomy b b0
      · exact ((he0 ▸ he ▸ mul_lt_mul_right hl a).not_ge <| le_max' _ _ <| mul_mem_mul ha hb0).elim
      · exact ⟨mul_right_cancel he, rfl⟩
      · exact ((he0 ▸ mul_lt_mul_right hl a0).not_ge <| le_max' _ _ <| mul_mem_mul ha0 hb).elim
    refine ⟨_, mk_mem_product ha0 hb0, _, mk_mem_product ha1 hb1, fun he ↦ ?_, this, ?_⟩
    · rw [Prod.mk_inj] at he; rw [he.1, he.2, he1] at he0
      obtain ⟨⟨a2, b2⟩, h2, hne⟩ := exists_mem_ne hc (a0, b0)
      rw [mem_product] at h2
      refine (min'_lt_max' _ (mul_mem_mul ha0 hb0) (mul_mem_mul h2.1 h2.2) fun he ↦ hne ?_).ne he0
      exact Prod.ext_iff.mpr (this h2.1 h2.2 he.symm)
    · intro a b ha hb he
      obtain hl | rfl | hl := lt_trichotomy b b1
      · exact ((he1 ▸ mul_lt_mul_right hl a1).not_ge <| min'_le _ _ <| mul_mem_mul ha1 hb).elim
      · exact ⟨mul_right_cancel he, rfl⟩
      · exact ((he1 ▸ he ▸ mul_lt_mul_right hl a).not_ge <| min'_le _ _ <| mul_mem_mul ha hb1).elim

open MulOpposite in
-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a left-cancellative multiplication, a linear order, and
  multiplication is strictly monotone w.r.t. the first argument, then `G` has `TwoUniqueProds`. -/
@[to_additive
  /-- This instance asserts that if `G` has a left-cancellative addition, a linear order, and
  addition is strictly monotone w.r.t. the first argument, then `G` has `TwoUniqueSums`. -/]
/-
**TwoUniqueProds.** 是 Mathlib 中的一个实例，位于命名空间 `TwoUniqueProds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_covariant_left [IsLeftCancelMul G]
    [LinearOrder G] [MulRightStrictMono G] :
    TwoUniqueProds G :=
  let _ := LinearOrder.lift' (unop : Gᵐᵒᵖ → G) unop_injective
  let _ : MulLeftStrictMono Gᵐᵒᵖ :=
    { elim := fun _ _ _ bc ↦ mul_lt_mul_left (α := G) bc (unop _) }
  of_mulOpposite of_covariant_right

end TwoUniqueProds

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, TwoUniqueSums (G i)] :
    TwoUniqueSums (Π₀ i, G i) :=
  TwoUniqueSums.of_injective_addHom
    DFinsupp.coeFnAddMonoidHom.toAddHom DFunLike.coe_injective inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι G} [AddZeroClass G] [TwoUniqueSums G] : TwoUniqueSums (ι →₀ G) :=
  TwoUniqueSums.of_injective_addHom
    Finsupp.coeFnAddHom.toAddHom DFunLike.coe_injective inferInstance
