/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.OrdContinuous

/-!
# Semiconjugate by `sSup`

In this file we prove two facts about semiconjugate (families of) functions.

First, if an order isomorphism `fa : α → α` is semiconjugate to an order embedding `fb : β → β` by
`g : α → β`, then `fb` is semiconjugate to `fa` by `y ↦ sSup {x | g x ≤ y}`, see
`Semiconj.symm_adjoint`.

Second, consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`,
see `Function.sSup_div_semiconj`.  In the case of a conditionally complete lattice, a similar
statement holds true under an additional assumption that each set `{(f₁ g)⁻¹ (f₂ g x) | g : G}` is
bounded above, see `Function.csSup_div_semiconj`.

The lemmas come from [Étienne Ghys, Groupes d'homéomorphismes du cercle et cohomologie
bornée][ghys87:groupes], Proposition 2.1 and 5.4 respectively. In the paper they are formulated for
homeomorphisms of the circle, so in order to apply results from this file one has to lift these
homeomorphisms to the real line first.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

variable {α β γ : Type*}

open Set

/-- We say that `g : β → α` is an order right adjoint function for `f : α → β` if it sends each `y`
to a least upper bound for `{x | f x ≤ y}`. If `α` is a partial order, and `f : α → β` has
a right adjoint, then this right adjoint is unique. -/
/-
**IsOrderRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsOrderRightAdjoint [Preorder α] [Preorder β] (f : α -> β) (g : β -> α)
参数：f : α -> β；g : β -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `g : β → α` is an order right adjoint function for `f : α → β` if it
 sends each `y`
to a least upper bound for `{x | f x ≤ y}`. If `α` is a partial order, and `f : 
α → β` has
a right adjoint, then this right adjoint is unique.
-/
def IsOrderRightAdjoint [Preorder α] [Preorder β] (f : α → β) (g : β → α) :=
  ∀ y, IsLUB { x | f x ≤ y } (g y)
/-
**isOrderRightAdjoint_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOrderRightAdjoint_sSup [CompleteSemilatticeSup α] [Preorder β] (f : α ->
 β) : IsOrderRightAdjoint f fun y => sSup { x | f x <= y }
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem isOrderRightAdjoint_sSup [CompleteSemilatticeSup α] [Preorder β] (f : α → β) :
    IsOrderRightAdjoint f fun y => sSup { x | f x ≤ y } := fun _ => isLUB_sSup _
/-
**isOrderRightAdjoint_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOrderRightAdjoint_csSup [ConditionallyCompleteLattice α] [Preorder β] (f
 : α -> β) (hne : forall y, exists x, f x <= y) (hbdd : forall y, BddAbove { x |
 f x <= y }) : IsOrderRightAdjoint f fun y => sSup { x | f x <= y }
参数：f : α -> β；hne : forall y, exists x, f x <= y；hbdd : forall y, BddAbove { x |
 f x <= y }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem isOrderRightAdjoint_csSup [ConditionallyCompleteLattice α] [Preorder β] (f : α → β)
    (hne : ∀ y, ∃ x, f x ≤ y) (hbdd : ∀ y, BddAbove { x | f x ≤ y }) :
    IsOrderRightAdjoint f fun y => sSup { x | f x ≤ y } := fun y => isLUB_csSup (hne y) (hbdd y)

namespace IsOrderRightAdjoint

/-
**IsOrderRightAdjoint.unique** 是 Mathlib 中的一个定理，位于命名空间 `IsOrderRightAdjoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [inst_1 : Preorder
 β] {f : α → β} {g₁ g₂ : β → α},   IsOrderRightAdjoint f g₁ → IsOrderRightAdjoin
t f g₂ → g₁ = g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
-/
protected theorem unique [PartialOrder α] [Preorder β] {f : α → β} {g₁ g₂ : β → α}
    (h₁ : IsOrderRightAdjoint f g₁) (h₂ : IsOrderRightAdjoint f g₂) : g₁ = g₂ :=
  funext fun y => (h₁ y).unique (h₂ y)
/-
**IsOrderRightAdjoint.right_mono** 是 Mathlib 中的一个定理，位于命名空间 `IsOrderRightAdjoint`
。
形式化陈述：right_mono [Preorder α] [Preorder β] {f : α -> β} {g : β -> α} (h : IsOrde
rRightAdjoint f g) : Monotone g
参数：h : IsOrderRightAdjoint f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mono`：IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subset
eq t) : a <= b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem right_mono [Preorder α] [Preorder β] {f : α → β} {g : β → α} (h : IsOrderRightAdjoint f g) :
    Monotone g := fun y₁ y₂ hy => ((h y₁).mono (h y₂)) fun _ hx => le_trans hx hy
/-
**IsOrderRightAdjoint.orderIso_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsOrderRightAdjoi
nt`。
形式化陈述：orderIso_comp [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -
> α} (h : IsOrderRightAdjoint f g) (e : β ≃o γ) : IsOrderRightAdjoint (e ∘ f) (g
 ∘ e.symm)
参数：h : IsOrderRightAdjoint f g；e : β ≃o γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
-/
theorem orderIso_comp [Preorder α] [Preorder β] [Preorder γ] {f : α → β} {g : β → α}
    (h : IsOrderRightAdjoint f g) (e : β ≃o γ) : IsOrderRightAdjoint (e ∘ f) (g ∘ e.symm) :=
  fun y => by simpa [e.le_symm_apply] using h (e.symm y)
/-
**IsOrderRightAdjoint.comp_orderIso** 是 Mathlib 中的一个定理，位于命名空间 `IsOrderRightAdjoi
nt`。
形式化陈述：comp_orderIso [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -
> α} (h : IsOrderRightAdjoint f g) (e : γ ≃o α) : IsOrderRightAdjoint (f ∘ e) (e
.symm ∘ g)
参数：h : IsOrderRightAdjoint f g；e : γ ≃o α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.isLUB_preimage`：isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻
¹' s) x ↔ IsLUB s (f x)
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
theorem comp_orderIso [Preorder α] [Preorder β] [Preorder γ] {f : α → β} {g : β → α}
    (h : IsOrderRightAdjoint f g) (e : γ ≃o α) : IsOrderRightAdjoint (f ∘ e) (e.symm ∘ g) := by
  intro y
  change IsLUB (e ⁻¹' { x | f x ≤ y }) (e.symm (g y))
  rw [e.isLUB_preimage, e.apply_symm_apply]
  exact h y

end IsOrderRightAdjoint

namespace Function

/-- If an order automorphism `fa` is semiconjugate to an order embedding `fb` by a function `g`
and `g'` is an order right adjoint of `g` (i.e. `g' y = sSup {x | f x ≤ y}`), then `fb` is
semiconjugate to `fa` by `g'`.

This is a version of Proposition 2.1 from [Étienne Ghys, Groupes d'homéomorphismes du cercle et
cohomologie bornée][ghys87:groupes]. -/
/-
**Function.Semiconj.symm_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [inst_1 : Preorder
 β] {fa : α ≃o α} {fb : β ↪o β} {g : α → β},   Function.Semiconj g ⇑fa ⇑fb → ∀ {
g' : β → α}, IsOrderRightAdjoint g g' → Function.Semiconj g' ⇑fb ⇑fa
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `Set.preimage_ofPred_eq`：preimage_ofPred_eq {p : α -> Prop} {f : β -> α} 
: f ⁻¹' { a | p a } = { a | p (f a) }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.isLUB_image'`：isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s)
 (f x) ↔ IsLUB s x

--- 原说明 ---
If an order automorphism `fa` is semiconjugate to an order embedding `fb` by a f
unction `g`
and `g'` is an order right adjoint of `g` (i.e. `g' y = sSup {x | f x ≤ y}`), th
en `fb` is
semiconjugate to `fa` by `g'`.

This is a version of Proposition 2.1 from [Étienne Ghys, Groupes d'homéomorphism
es du cercle et
cohomologie bornée][ghys87:groupes].
-/
theorem Semiconj.symm_adjoint [PartialOrder α] [Preorder β] {fa : α ≃o α} {fb : β ↪o β} {g : α → β}
    (h : Function.Semiconj g fa fb) {g' : β → α} (hg' : IsOrderRightAdjoint g g') :
    Function.Semiconj g' fb fa := by
  refine fun y => (hg' _).unique ?_
  rw [← fa.surjective.image_preimage { x | g x ≤ fb y }, preimage_ofPred_eq]
  simp only [h.eq, fb.le_iff_le, fa.isLUB_image'.mpr (hg' _)]

variable {G : Type*}
/-
**Function.semiconj_of_isLUB** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：semiconj_of_isLUB [PartialOrder α] [Group G] (f₁ f₂ : G ->* α ≃o α) {h : α
 -> α} (H : forall x, IsLUB (range fun g' => (f₁ g')⁻¹ (f₂ g' x)) (h x)) (g : G)
 : Function.Semiconj h (f₂ g) (f₁ g)
参数：f₁ f₂ : G ->* α ≃o α；H : forall x, IsLUB (range fun g' => (f₁ g')⁻¹ (f₂ g' x)
) (h x)；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.isLUB_image'`：isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s)
 (f x) ↔ IsLUB s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `RelIso.apply_inv_self`：apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem semiconj_of_isLUB [PartialOrder α] [Group G] (f₁ f₂ : G →* α ≃o α) {h : α → α}
    (H : ∀ x, IsLUB (range fun g' => (f₁ g')⁻¹ (f₂ g' x)) (h x)) (g : G) :
    Function.Semiconj h (f₂ g) (f₁ g) := by
  refine fun y => (H _).unique ?_
  have := (f₁ g).isLUB_image'.mpr (H y)
  rw [← range_comp, ← (Equiv.mulRight g).surjective.range_comp _] at this
  simpa [comp_def] using this

/-- Consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphismes du cercle et
cohomologie bornée][ghys87:groupes]. -/
/-
**Function.sSup_div_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：sSup_div_semiconj [CompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α) (g 
: G) : Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g)
参数：f₁ f₂ : G ->* α ≃o α；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.semiconj_of_isLUB`：semiconj_of_isLUB [PartialOrder α] [Group G]
 (f₁ f₂ : G ->* α ≃o α) {h : α -> α} (H : forall x, IsLUB (range fun g' => (f₁ g
')⁻¹ (f₂ g' x)) …
· 使用定理 `isLUB_iSup`：isLUB_iSup : IsLUB (range f) (⨆ j, f j)

--- 原说明 ---
Consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by ord
er
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each 
`f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphism
es du cercle et
cohomologie bornée][ghys87:groupes].
-/
theorem sSup_div_semiconj [CompleteLattice α] [Group G] (f₁ f₂ : G →* α ≃o α) (g : G) :
    Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
  semiconj_of_isLUB f₁ f₂ (fun _ => isLUB_iSup) _

/-- Consider two actions `f₁ f₂ : G → α → α` of a group on a conditionally complete lattice by order
isomorphisms. Suppose that each set $s(x)=\{f_1(g)^{-1} (f_2(g)(x)) | g \in G\}$ is bounded above.
Then the map `x ↦ sSup s(x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphismes du cercle et
cohomologie bornée][ghys87:groupes]. -/
/-
**Function.csSup_div_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：csSup_div_semiconj [ConditionallyCompleteLattice α] [Group G] (f₁ f₂ : G -
>* α ≃o α) (hbdd : forall x, BddAbove (range fun g => (f₁ g)⁻¹ (f₂ g x))) (g : G
) : Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g)
参数：f₁ f₂ : G ->* α ≃o α；hbdd : forall x, BddAbove (range fun g => (f₁ g)⁻¹ (f₂ g
 x))；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.semiconj_of_isLUB`：semiconj_of_isLUB [PartialOrder α] [Group G]
 (f₁ f₂ : G ->* α ≃o α) {h : α -> α} (H : forall x, IsLUB (range fun g' => (f₁ g
')⁻¹ (f₂ g' x)) …
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α

--- 原说明 ---
Consider two actions `f₁ f₂ : G → α → α` of a group on a conditionally complete 
lattice by order
isomorphisms. Suppose that each set $s(x)=\{f_1(g)^{-1} (f_2(g)(x)) | g \in G\}$
 is bounded above.
Then the map `x ↦ sSup s(x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphism
es du cercle et
cohomologie bornée][ghys87:groupes].
-/
theorem csSup_div_semiconj [ConditionallyCompleteLattice α] [Group G] (f₁ f₂ : G →* α ≃o α)
    (hbdd : ∀ x, BddAbove (range fun g => (f₁ g)⁻¹ (f₂ g x))) (g : G) :
    Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
  semiconj_of_isLUB f₁ f₂ (fun x => isLUB_csSup (range_nonempty _) (hbdd x)) _

end Function

