/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Tactic.FunProp.Attr
public import Mathlib.Tactic.ToFun
import Mathlib.Order.Bounds.Image
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed

/-!
# Scott continuity

A function `f : α → β` between preorders is Scott continuous (referring to Dana Scott) if it
distributes over `IsLUB`. Scott continuity corresponds to continuity in Scott topological spaces
(defined in `Mathlib/Topology/Order/ScottTopology.lean`). It is distinct from the (more commonly
used) continuity from topology (see `Mathlib/Topology/Basic.lean`).

## Implementation notes

Given a set `D` of directed sets, we define say `f` is `ScottContinuousOn D` if it distributes over
`IsLUB` for all elements of `D`. This allows us to consider Scott Continuity on all directed sets
in this file, and ωScott Continuity on chains later in
`Mathlib/Order/OmegaCompletePartialOrder.lean`.

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

-/

@[expose] public section

open Set

variable {α β γ : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] [Preorder γ] {D D₁ D₂ : Set (Set α)}
  {f : α → β}

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

/-- A function between preorders is said to be Scott continuous on a set `D` of directed sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D →  d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
@[fun_prop]
/-
**ScottContinuousOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ScottContinuousOn (D : Set (Set α)) (f : α -> β) : Prop
参数：D : Set (Set α)；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between preorders is said to be Scott continuous on a set `D` of dire
cted sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D →  d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → I
sGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here
.
-/
def ScottContinuousOn (D : Set (Set α)) (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)
/-
**ScottContinuousOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.mono (hD : D₁ subseteq D₂) (hf : ScottContinuousOn D₂ f)
 : ScottContinuousOn D₁ f
参数：hD : D₁ subseteq D₂；hf : ScottContinuousOn D₂ f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ScottContinuousOn.mono (hD : D₁ ⊆ D₂) (hf : ScottContinuousOn D₂ f) :
    ScottContinuousOn D₁ f := fun _ hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda
/-
**ScottContinuousOn.monotone** 是 Mathlib 中的一个定理，位于命名空间 `ScottContinuousOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β} (D : Set (Set α)),   (∀ (a b : α), a ≤ b → {a, b} ∈ D) → ScottContin
uousOn D f → Monotone f
参数：D : Set (Set α)；∀ (a b : α), a ≤ b → {a, b} ∈ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
· 使用定理 `directedOn_pair`：directedOn_pair [Std.Refl r] {a b : α} (hab : a ≼ b) : 
DirectedOn r ({a, b} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), IsLUB s = IsLeas
t (upperBounds s)
· 使用定理 `upperBounds_insert`：upperBounds_insert (a : α) (s : Set α) : upperBounds
 (insert a s) = Ici a inter upperBounds s
· 使用定理 `upperBounds_singleton`：upperBounds_singleton : upperBounds {a} = Ici a
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `isLeast_Ici`：isLeast_Ici : IsLeast (Ici a) a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
protected theorem ScottContinuousOn.monotone (D : Set (Set α)) (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (h : ScottContinuousOn D f) : Monotone f := by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[fun_prop, to_fun (attr := simp)]
/-
**ScottContinuousOn.id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.id : ScottContinuousOn D (id : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma ScottContinuousOn.id : ScottContinuousOn D (id : α → α) := by simp [ScottContinuousOn]

@[fun_prop, to_fun (attr := simp)]
/-
**ScottContinuousOn.const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.const (x : β) : ScottContinuousOn D (Function.const α x)
参数：x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma ScottContinuousOn.const (x : β) : ScottContinuousOn D (Function.const α x) := by
  rintro s _ ⟨a⟩ _ _ _
  simp [IsLUB, IsLeast, upperBounds, lowerBounds]; grind

@[fun_prop, to_fun]
/-
**ScottContinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.comp {g : β -> γ} {D'} (hD : forall a b : α, a <= b -> {
a, b} in D) (hD' : Set.MapsTo (f '' ·) D D') (hg : ScottContinuousOn D' g) (hf :
 ScottContinuousOn D f) : ScottContinuousOn D (g ∘ f)
参数：hD : forall a b : α, a <= b -> {a, b} in D；hD' : Set.MapsTo (f '' ·) D D'；hg 
: ScottContinuousOn D' g；hf : ScottContinuousOn D f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ScottContinuousOn.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β} (D : Set (Set α)),   (∀ (a b : α), a ≤
 b → {a, b} ∈ D)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem ScottContinuousOn.comp {g : β → γ} {D'}
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D) (hD' : Set.MapsTo (f '' ·) D D')
    (hg : ScottContinuousOn D' g) (hf : ScottContinuousOn D f) :
    ScottContinuousOn D (g ∘ f) := by
  intro d hd₁ hd₂ hd₃ a ha
  have hd : DirectedOn (fun x1 x2 ↦ x1 ≤ x2) (f '' d) := by
    have := hf.monotone
    simp only [Monotone, DirectedOn, mem_image, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at ⊢ this hd₃
    grind
  rw [Set.image_comp]
  exact hg (hD' hd₁) ⟨f hd₂.choose, by grind⟩ hd (hf hd₁ hd₂ hd₃ ha)

@[fun_prop, to_fun]
/-
**ScottContinuousOn.image_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.image_comp {g : β -> γ} (hD : forall a b : α, a <= b -> 
{a, b} in D) (hg : ScottContinuousOn ((f '' ·) '' D) g) (hf : ScottContinuousOn 
D f) : ScottContinuousOn D (g ∘ f)
参数：hD : forall a b : α, a <= b -> {a, b} in D；hg : ScottContinuousOn ((f '' ·) '
' D) g；hf : ScottContinuousOn D f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ScottContinuousOn.comp`：ScottContinuousOn.comp {g : β -> γ} {D'} (hD : f
orall a b : α, a <= b -> {a, b} in D) (hD' : Set.MapsTo (f '' ·) D D') (hg : Sco
ttContinuous…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ScottContinuousOn.image_comp {g : β → γ}
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hg : ScottContinuousOn ((f '' ·) '' D) g)
    (hf : ScottContinuousOn D f) :
    ScottContinuousOn D (g ∘ f) :=
  ScottContinuousOn.comp hD (Set.mapsTo_image (f '' ·) D) hg hf

@[fun_prop]
/-
**ScottContinuousOn.prodMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.prodMk {g : α -> γ} (hD : forall a b : α, a <= b -> {a, 
b} in D) (hf : ScottContinuousOn D f) (hg : ScottContinuousOn D g) : ScottContin
uousOn D fun x => (f x, g x)
参数：hD : forall a b : α, a <= b -> {a, b} in D；hf : ScottContinuousOn D f；hg : Sc
ottContinuousOn D g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), IsLUB s = IsLeas
t (upperBounds s)
· 使用定理 `IsLeast.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α) (a : α), IsLeas
t s a = (a ∈ s ∧ a ∈ lowerBounds s)
· 使用定理 `upperBounds.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), upperBound
s s = {x | ∀ ⦃a : α⦄, a ∈ s → a ≤ x}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ScottContinuousOn.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β} (D : Set (Set α)),   (∀ (a b : α), a ≤
 b → {a, b} ∈ D)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma ScottContinuousOn.prodMk {g : α → γ} (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hf : ScottContinuousOn D f) (hg : ScottContinuousOn D g) :
    ScottContinuousOn D fun x => (f x, g x) := fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro ⟨p₁, p₂⟩ hp
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk] at hp
    constructor
    · rw [isLUB_le_iff (hf hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq]
      intro _ hb
      exact (hp _ hb).1
    · rw [isLUB_le_iff (hg hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq]
      intro _ hb
      exact (hp _ hb).2

@[simp, fun_prop]
/-
**ScottContinuousOn.fst** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.fst {D} : ScottContinuousOn D (Prod.fst : α × β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma ScottContinuousOn.fst {D} : ScottContinuousOn D (Prod.fst : α × β → α) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.1

@[simp, fun_prop]
/-
**ScottContinuousOn.snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.snd {D} : ScottContinuousOn D (Prod.snd : α × β -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma ScottContinuousOn.snd {D} : ScottContinuousOn D (Prod.snd : α × β → β) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.2

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous w.r.t. the
Scott topology.
-/
@[fun_prop]
/-
**ScottContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ScottContinuous (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between preorders is said to be Scott continuous if it preserves `IsL
UB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is c
ontinuous w.r.t. the
Scott topology.
-/
def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)
/-
**scottContinuousOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   ScottContinuousOn Set.univ f ↔ ScottContinuous f
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma scottContinuousOn_univ : ScottContinuousOn univ f ↔ ScottContinuous f := by
  simp [ScottContinuousOn, ScottContinuous]
/-
**ScottContinuous.scottContinuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.scottContinuousOn {D : Set (Set α)} : ScottContinuous f ->
 ScottContinuousOn D f
参数：Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ScottContinuous.scottContinuousOn {D : Set (Set α)} :
    ScottContinuous f → ScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda
/-
**ScottContinuous.monotone** 是 Mathlib 中的一个定理，位于命名空间 `ScottContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β}, ScottContinuous f → Monotone f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ScottContinuousOn.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β} (D : Set (Set α)),   (∀ (a b : α), a ≤
 b → {a, b} ∈ D)…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用引理 `ScottContinuous.scottContinuousOn`：ScottContinuous.scottContinuousOn {D 
: Set (Set α)} : ScottContinuous f -> ScottContinuousOn D f
-/
protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f :=
  h.scottContinuousOn.monotone univ (fun _ _ _ ↦ mem_univ _)

@[fun_prop, to_fun (attr := simp)]
/-
**ScottContinuous.id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.id : ScottContinuous (id : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma ScottContinuous.id : ScottContinuous (id : α → α) := by simp [ScottContinuous]

@[fun_prop, to_fun (attr := simp)]
/-
**ScottContinuous.const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.const (x : β) : ScottContinuous (Function.const α x)
参数：x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma ScottContinuous.const (x : β) : ScottContinuous (Function.const α x) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.const]

@[fun_prop, to_fun]
/-
**ScottContinuous.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.comp {g : β -> γ} (hf : ScottContinuous f) (hg : ScottCont
inuous g) : ScottContinuous (g ∘ f)
参数：hf : ScottContinuous f；hg : ScottContinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `scottContinuousOn_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder
 α] [inst_1 : Preorder β] {f : α → β},   ScottContinuousOn Set.univ f ↔ ScottCon
tinuous f
· 使用定理 `ScottContinuousOn.comp`：ScottContinuousOn.comp {g : β -> γ} {D'} (hD : f
orall a b : α, a <= b -> {a, b} in D) (hD' : Set.MapsTo (f '' ·) D D') (hg : Sco
ttContinuous…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma ScottContinuous.comp {g : β → γ}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (g ∘ f) := by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.comp (by simp) (by simp [MapsTo]) hg hf

@[fun_prop]
/-
**ScottContinuous.prodMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.prodMk {g : α -> γ} (hf : ScottContinuous f) (hg : ScottCo
ntinuous g) : ScottContinuous fun x => (f x, g x)
参数：hf : ScottContinuous f；hg : ScottContinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `scottContinuousOn_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder
 α] [inst_1 : Preorder β] {f : α → β},   ScottContinuousOn Set.univ f ↔ ScottCon
tinuous f
· 使用引理 `ScottContinuousOn.prodMk`：ScottContinuousOn.prodMk {g : α -> γ} (hD : fo
rall a b : α, a <= b -> {a, b} in D) (hf : ScottContinuousOn D f) (hg : ScottCon
tinuousOn D g)…
-/
lemma ScottContinuous.prodMk {g : α → γ}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous fun x => (f x, g x) := by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.prodMk (by grind) hf hg

@[simp, fun_prop]
/-
**ScottContinuous.fst** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.fst : ScottContinuous (Prod.fst : α × β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma ScottContinuous.fst : ScottContinuous (Prod.fst : α × β → α) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.fst]

@[simp, fun_prop]
/-
**ScottContinuous.snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.snd : ScottContinuous (Prod.snd : α × β -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma ScottContinuous.snd : ScottContinuous (Prod.snd : α × β → β) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.snd]

end ScottContinuous

section SemilatticeSup

variable [SemilatticeSup β]

/-- The join operation is Scott continuous -/
@[fun_prop]
/-
**ScottContinuous.sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The join operation is Scott continuous
-/
lemma ScottContinuous.sup₂ :
    ScottContinuous fun b : β × β => (b.1 ⊔ b.2 : β) := fun d _ _ ⟨p₁, p₂⟩ hdp => by
  simp only [IsLUB, IsLeast, upperBounds, Prod.forall, mem_ofPred_eq, Prod.mk_le_mk] at hdp
  simp only [IsLUB, IsLeast, upperBounds, mem_image, Prod.exists, forall_exists_index, and_imp]
  have e1 : (p₁, p₂) ∈ lowerBounds {x | ∀ (b₁ b₂ : β), (b₁, b₂) ∈ d → (b₁, b₂) ≤ x} := hdp.2
  simp only [lowerBounds, mem_ofPred_eq, Prod.forall, Prod.mk_le_mk] at e1
  refine ⟨fun a b₁ b₂ hbd hba => ?_,fun b hb => ?_⟩
  · rw [← hba]
    exact sup_le_sup (hdp.1 _ _ hbd).1 (hdp.1 _ _ hbd).2
  · rw [sup_le_iff]
    exact e1 _ _ fun b₁ b₂ hb' => sup_le_iff.mp (hb b₁ b₂ hb' rfl)

@[fun_prop]
/-
**ScottContinuousOn.sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ScottContinuousOn.sup₂ {D : Set (Set (β × β))} :
    ScottContinuousOn D fun (a, b) => (a ⊔ b : β) :=
  ScottContinuous.sup₂.scottContinuousOn

end SemilatticeSup

