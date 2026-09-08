/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.ScottContinuity
public import Mathlib.Order.Bounds.Lattice

/-!
# Scott continuity on product spaces

## Main result

- `ScottContinuous_prod_of_ScottContinuous`: A function is Scott continuous on a product space if it
  is Scott continuous in each variable.
- `ScottContinuousOn.inf₂`: For complete linear orders, the meet operation is Scott continuous.

-/

public section

open Set

variable {α β γ : Type*}

/-- If  is Scott continuous on a product space if it is Scott continuous and monotone in each
variable -/
/-
**ScottContinuousOn.fromProd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuousOn.fromProd [Preorder α] [Preorder β] [Preorder γ] {f : α ×
 β -> γ} {D : Set (Set (α × β))} (h₁ : forall a, ScottContinuousOn ((fun d => Pr
od.snd '' d) '' D) (fun b => f (a, b))) (h₂ : forall b, ScottContinuousOn ((fun 
d => Prod.fst '' d) '' D) (fun a => f (a, b))) (h₁' : forall a, Monotone (fun b 
=> f (a, b))) (h₂' : forall b, Monotone (fun a => f (a, b))) : ScottContinuousOn
 D f
参数：Set (α × β)；h₁ : forall a, ScottContinuousOn ((fun d => Prod.snd '' d) '' D) 
(fun b => f (a, b))；h₂ : forall b, ScottContinuousOn ((fun d => Prod.fst '' d) '
' D) (fun a => f (a, b))；h₁' : forall a, Monotone (fun b => f (a, b))；h₂' : fora
ll b, Monotone (fun a => f (a, b))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLUB_congr`：isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a
 ↔ IsLUB t a
· 使用引理 `Monotone.upperBounds_image_of_directedOn_prod`：Monotone.upperBounds_imag
e_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β -> γ} (hg : Monotone g)
 {d : Set (α × β)} (hd : DirectedOn…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `monotone_prod_iff`：monotone_prod_iff {h : α × β -> γ} : Monotone h ↔ (fo
rall a, Monotone (fun b => h (a, b))) ∧ (forall b, Monotone (fun a => h (a, b)))
 where …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_of_singleton_coe`：iUnion_of_singleton_coe (s : Set α) : ⋃ i :
 s, ({(i : α)} : Set α) = s
· 使用定理 `Set.iUnion_prod_const`：iUnion_prod_const {s : ι -> Set α} {t : Set β} : 
(⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `isLUB_iUnion_iff_of_isLUB`：isLUB_iUnion_iff_of_isLUB {u : ι -> α} (hs : 
forall i, IsLUB (s i) (u i)) (c : α) : IsLUB (Set.range u) c ↔ IsLUB (⋃ i, s i) 
c
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用引理 `DirectedOn.snd`：snd {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼
₁ q.1 ∧ p.2 ≼₂ q.2) d) : DirectedOn (· ≼₂ ·) (Prod.snd '' d)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLUB_prod`：isLUB_prod {s : Set (α × β)} {p : α × β} : IsLUB s p ↔ IsLUB
 (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2
· 使用定理 `Set.range.eq_1`：∀ {α : Type u} {ι : Sort u_1} (f : ι → α), Set.range f =
 {x | ∃ y, f y = x}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `DirectedOn.fst`：fst {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼
₁ q.1 ∧ p.2 ≼₂ q.2) d) : DirectedOn (· ≼₁ ·) (Prod.fst '' d)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If  is Scott continuous on a product space if it is Scott continuous and monoton
e in each
variable
-/
lemma ScottContinuousOn.fromProd [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β → γ} {D : Set (Set (α × β))}
    (h₁ : ∀ a, ScottContinuousOn ((fun d => Prod.snd '' d) '' D) (fun b => f (a, b)))
    (h₂ : ∀ b, ScottContinuousOn ((fun d => Prod.fst '' d) '' D) (fun a => f (a, b)))
    (h₁' : ∀ a, Monotone (fun b => f (a, b))) (h₂' : ∀ b, Monotone (fun a => f (a, b))) :
    ScottContinuousOn D f := fun d hX hd₁ hd₂ ⟨p1, p2⟩ hdp => by
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨h₁', h₂'⟩).upperBounds_image_of_directedOn_prod hd₂),
    ← iUnion_of_singleton_coe (Prod.fst '' d), iUnion_prod_const, image_iUnion,
    ← isLUB_iUnion_iff_of_isLUB (fun a => by
      rw [singleton_prod, image_image f (fun b ↦ (a, b))]
      exact h₁ _ (mem_image_of_mem (fun d ↦ Prod.snd '' d) hX) (Nonempty.image Prod.snd hd₁)
        (DirectedOn.snd hd₂) (isLUB_prod.mp hdp).2) _, Set.range]
  convert!
    (h₂ _ (mem_image_of_mem (fun d ↦ Prod.fst '' d) hX) (Nonempty.image Prod.fst hd₁)
      (DirectedOn.fst hd₂) (isLUB_prod.mp hdp).1)
  ext : 1
  simp_all only [Subtype.exists, mem_image, Prod.exists,
    exists_and_right, exists_eq_right, exists_prop, mem_ofPred_eq]
/-
**ScottContinuous.fromProd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.fromProd {γ : Type*} [Preorder α] [Preorder β] [Preorder γ
] {f : α × β -> γ} (h₁ : forall a, ScottContinuous (fun b => f (a, b))) (h₂ : fo
rall b, ScottContinuous (fun a => f (a, b))) : ScottContinuous f
参数：h₁ : forall a, ScottContinuous (fun b => f (a, b))；h₂ : forall b, ScottContin
uous (fun a => f (a, b))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ScottContinuousOn.fromProd`：ScottContinuousOn.fromProd [Preorder α] [Pre
order β] [Preorder γ] {f : α × β -> γ} {D : Set (Set (α × β))} (h₁ : forall a, S
cottContinuousOn…
· 使用引理 `ScottContinuous.scottContinuousOn`：ScottContinuous.scottContinuousOn {D 
: Set (Set α)} : ScottContinuous f -> ScottContinuousOn D f
· 使用定理 `ScottContinuous.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Preord
er α] [inst_1 : Preorder β] {f : α → β}, ScottContinuous f → Monotone f
-/
lemma ScottContinuous.fromProd {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β → γ} (h₁ : ∀ a, ScottContinuous (fun b => f (a, b)))
    (h₂ : ∀ b, ScottContinuous (fun a => f (a, b))) : ScottContinuous f := by
  simp_rw [← scottContinuousOn_univ] at ⊢
  exact .fromProd (fun a ↦ (h₁ a).scottContinuousOn) (fun b ↦ (h₂ b).scottContinuousOn)
    (fun a ↦ (h₁ a).monotone) (fun b ↦ (h₂ b).monotone)
/-
**ScottContinuous.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ScottContinuous.prod {α' β' : Type*} [Preorder α] [Preorder β] [Preorder α
'] [Preorder β'] {f : α -> α'} {g : β -> β'} (hf : ScottContinuous f) (hg : Scot
tContinuous g) : ScottContinuous (Prod.map f g)
参数：hf : ScottContinuous f；hg : ScottContinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ScottContinuous.fromProd`：ScottContinuous.fromProd {γ : Type*} [Preorder
 α] [Preorder β] [Preorder γ] {f : α × β -> γ} (h₁ : forall a, ScottContinuous (
fun b => f (a,…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `IsLUB.prod`：IsLUB.prod {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha :
 IsLUB s a) (hb : IsLUB t b) : IsLUB (s ×ˢ t) (a, b)
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma ScottContinuous.prod {α' β' : Type*} [Preorder α] [Preorder β] [Preorder α'] [Preorder β']
    {f : α → α'} {g : β → β'} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (Prod.map f g) := by
  refine .fromProd (fun a d hd₁ hd₂ c hdc ↦ ?_) (fun b d hd₁ hd₂ c hdc ↦ ?_)
  · have e1 : (fun b ↦ (f a, g b)) '' d = {f a} ×ˢ (g '' d) := by aesop
    simp_rw [Prod.map_apply, e1]
    exact .prod (singleton_nonempty _) (hd₁.image _) isLUB_singleton (hg hd₁ hd₂ hdc)
  · have e2 : ((fun a ↦ (f a, g b)) '' d) = (f '' d) ×ˢ {g b} := by aesop
    simp_rw [Prod.map_apply, e2]
    exact .prod (hd₁.image _) (singleton_nonempty _) (hf hd₁ hd₂ hdc) isLUB_singleton
