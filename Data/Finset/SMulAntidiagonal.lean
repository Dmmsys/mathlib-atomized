/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.SMulAntidiagonal

/-!
# Antidiagonal for scalar multiplication as a `Finset`.

Given sets `G` and `P`, with an action of `G` on `P`, we construct, for any element `a` in `P`,
the `Finset` of all pairs of an element in `s` and an element in `t` that scalar-multiply to `a`,
assuming that set is finite.

## Definitions
* Finset.SMulAntidiagonal : Finset antidiagonal for PWO inputs.
* Finset.VAddAntidiagonal : Finset antidiagonal for PWO inputs.

-/

@[expose] public section

variable {G P : Type*}

open scoped Pointwise

namespace Set

@[to_additive]
/-
**Set.IsPWO.smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {G : Type u_1} {P : Type u_2} [inst : Preorder G] [inst_1 : Preorder P] 
[inst_2 : SMul G P] [IsOrderedSMul G P]   {s : Set G} {t : Set P}, s.IsPWO → t.I
sPWO → (s • t).IsPWO
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_smul_prod`：image_smul_prod : (fun x : α × β => x.fst • x.snd) 
'' s ×ˢ t = s • t
· 使用定理 `Set.IsPWO.image_of_monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Pre
order α] [inst_1 : Preorder β] {s : Set α},   s.IsPWO → ∀ {f : α → β}, Monotone 
f → (f '' s).IsPW…
· 使用定理 `Set.IsPWO.prod`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [ins
t_1 : Preorder β] {s : Set α} {t : Set β},   s.IsPWO → t.IsPWO → (s ×ˢ t).IsPWO
· 使用定理 `Monotone.smul`：Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preo
rder γ] [SMul G P] [IsOrderedSMul G P] {f : γ -> G} {g : γ -> P} (hf : Monotone 
f) …
· 使用定理 `monotone_fst`：monotone_fst : Monotone (@Prod.fst α β)
· 使用定理 `monotone_snd`：monotone_snd : Monotone (@Prod.snd α β)
-/
theorem IsPWO.smul [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s • t) := by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.smul monotone_snd)

@[to_additive]
/-
**Set.IsWF.smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {G : Type u_1} {P : Type u_2} [inst : LinearOrder G] [inst_1 : LinearOrd
er P] [inst_2 : SMul G P] [IsOrderedSMul G P]   {s : Set G} {t : Set P}, s.IsWF 
→ t.IsWF → (s • t).IsWF
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `Set.IsPWO.smul`：∀ {G : Type u_1} {P : Type u_2} [inst : Preorder G] [ins
t_1 : Preorder P] [inst_2 : SMul G P] [IsOrderedSMul G P]   {s : Set G} {t : Set
 P},…
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
-/
theorem IsWF.smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) : IsWF (s • t) :=
  (hs.isPWO.smul ht.isPWO).isWF

@[to_additive]
/-
**Set.IsWF.min_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {G : Type u_1} {P : Type u_2} [inst : LinearOrder G] [inst_1 : LinearOrd
er P] [inst_2 : SMul G P]   [inst_3 : IsOrderedSMul G P] {s : Set G} {t : Set P}
 (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty)   (htn : t.Nonempty), ⋯.min ⋯ = 
hs.min hsn • ht.min htn
参数：hs : s.IsWF；ht : t.IsWF；hsn : s.Nonempty；htn : t.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.IsWF.smul`：∀ {G : Type u_1} {P : Type u_2} [inst : LinearOrder G] [i
nst_1 : LinearOrder P] [inst_2 : SMul G P] [IsOrderedSMul G P]   {s : Set G} {t 
: S…
· 使用定理 `Set.Nonempty.smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β}, s.Nonempty → t.Nonempty → (s • t).Nonempty
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set
 α} {t : Set β} {b : β},   b ∈ s • t ↔ ∃ x ∈ s, ∃ y ∈ t, x • y = b
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.IsWF.le_min_iff`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}
 {a : α} (hs : s.IsWF) (hn : s.Nonempty),   a ≤ hs.min hn ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `IsOrderedSMul.smul_le_smul`：IsOrderedSMul.smul_le_smul [LE G] [Preorder 
P] [SMul G P] [IsOrderedSMul G P] {a b : G} {c d : P} (hab : a <= b) (hcd : c <=
 d) : a • c <= b…
-/
theorem IsWF.min_smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.smul ht).min (hsn.smul htn) = hs.min hsn • ht.min htn := by
  refine le_antisymm (IsWF.min_le _ _ (mem_smul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact IsOrderedSMul.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

section

open Set

variable [SMul G P]

/-- `Finset.SMulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose scalar multiplication yields `a`, but its construction requires a proof that
the set-theoretic antidiagonal is finite. -/
@[to_additive /-- `Finset.VAddAntidiagonal hs ht a` is the set of all pairs of an element in `s`
and an element in `t` whose vector addition yields `a`, but its construction requires proofs that
`s` and `t` are well-ordered. -/]
/-
**Finset.SMulAntidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：SMulAntidiagonal {s : Set G} {t : Set P} (a : P) (h : (s.smulAntidiagonal 
t a).Finite) : Finset (G × P)
参数：a : P；h : (s.smulAntidiagonal t a).Finite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def SMulAntidiagonal {s : Set G}
    {t : Set P} (a : P) (h : (s.smulAntidiagonal t a).Finite) : Finset (G × P) :=
  h.toFinset

@[to_additive (attr := simp)]
/-
**Finset.mem_smulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_smulAntidiagonal {s : Set G} {t : Set P} (a : P) (h : (s.smulAntidiago
nal t a).Finite) {x : G × P} : x in SMulAntidiagonal a h ↔ x.1 in s ∧ x.2 in t ∧
 x.1 • x.2 = a
参数：a : P；h : (s.smulAntidiagonal t a).Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_sep_iff`：mem_sep_iff : x in { x in s | p x } ↔ x in s ∧ p x
-/
theorem mem_smulAntidiagonal {s : Set G}
    {t : Set P} (a : P) (h : (s.smulAntidiagonal t a).Finite) {x : G × P} :
    x ∈ SMulAntidiagonal a h ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a := by
  simp only [SMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]
/-
**Finset.smulAntidiagonal_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smulAntidiagonal_mono_left {s u : Set G} {t : Set P} (a : P) (h : u subset
eq s) (hst : (s.smulAntidiagonal t a).Finite) (hut : (u.smulAntidiagonal t a).Fi
nite) : SMulAntidiagonal a hut subseteq SMulAntidiagonal a hst
参数：a : P；h : u subseteq s；hst : (s.smulAntidiagonal t a).Finite；hut : (u.smulAnt
idiagonal t a).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_mono`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {
ht : t.Finite}, s ⊆ t → hs.toFinset ⊆ ht.toFinset
· 使用定理 `Set.smulAntidiagonal_mono_left`：smulAntidiagonal_mono_left (h : s₁ subse
teq s₂) : smulAntidiagonal s₁ t a subseteq smulAntidiagonal s₂ t a
-/
theorem smulAntidiagonal_mono_left {s u : Set G} {t : Set P} (a : P) (h : u ⊆ s)
    (hst : (s.smulAntidiagonal t a).Finite) (hut : (u.smulAntidiagonal t a).Finite) :
    SMulAntidiagonal a hut ⊆ SMulAntidiagonal a hst :=
  Set.Finite.toFinset_mono <| Set.smulAntidiagonal_mono_left h

@[to_additive]
/-
**Finset.smulAntidiagonal_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smulAntidiagonal_mono_right {s : Set G} {t v : Set P} (a : P) (hst : (s.sm
ulAntidiagonal t a).Finite) (hsv : (s.smulAntidiagonal v a).Finite) (h : v subse
teq t) : SMulAntidiagonal a hsv subseteq SMulAntidiagonal a hst
参数：a : P；hst : (s.smulAntidiagonal t a).Finite；hsv : (s.smulAntidiagonal v a).Fi
nite；h : v subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_mono`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {
ht : t.Finite}, s ⊆ t → hs.toFinset ⊆ ht.toFinset
· 使用定理 `Set.smulAntidiagonal_mono_right`：smulAntidiagonal_mono_right (h : t₁ sub
seteq t₂) : smulAntidiagonal s t₁ a subseteq smulAntidiagonal s t₂ a
-/
theorem smulAntidiagonal_mono_right {s : Set G}
    {t v : Set P} (a : P) (hst : (s.smulAntidiagonal t a).Finite)
    (hsv : (s.smulAntidiagonal v a).Finite) (h : v ⊆ t) :
    SMulAntidiagonal a hsv ⊆ SMulAntidiagonal a hst :=
  Set.Finite.toFinset_mono <| Set.smulAntidiagonal_mono_right h

@[to_additive]
/-
**Finset.support_smulAntidiagonal_subset_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：support_smulAntidiagonal_subset_smul {s : Set G} {t : Set P} (hst : forall
 a, (s.smulAntidiagonal t a).Finite) : { a | (SMulAntidiagonal a (hst a)).Nonemp
ty } subseteq (s • t)
参数：hst : forall a, (s.smulAntidiagonal t a).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_smulAntidiagonal_subset_smul {s : Set G}
    {t : Set P} (hst : ∀ a, (s.smulAntidiagonal t a).Finite) :
    { a | (SMulAntidiagonal a (hst a)).Nonempty } ⊆ (s • t) := by
  grind [mem_smul, mem_smulAntidiagonal]

variable [PartialOrder G] [PartialOrder P] [IsOrderedCancelSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) {u : Set G} {hu : u.IsPWO} {v : Set P}
    {hv : v.IsPWO} {x : G × P}

@[to_additive]
/-
**Finset.isPWO_support_smulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isPWO_support_smulAntidiagonal : { a | (SMulAntidiagonal a (Set.SMulAntidi
agonal.finite_of_isPWO hs ht a)).Nonempty }.IsPWO
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.mono`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, t.Is
PWO → s ⊆ t → s.IsPWO
· 使用定理 `Set.SMulAntidiagonal.finite_of_isPWO`：finite_of_isPWO (hs : s.IsPWO) (ht
 : t.IsPWO) (a) : (smulAntidiagonal s t a).Finite
· 使用定理 `Set.IsPWO.smul`：∀ {G : Type u_1} {P : Type u_2} [inst : Preorder G] [ins
t_1 : Preorder P] [inst_2 : SMul G P] [IsOrderedSMul G P]   {s : Set G} {t : Set
 P},…
· 使用定理 `IsOrderedCancelSMul.toIsOrderedSMul`：∀ {G : Type u_3} {P : Type u_4} {in
st : LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedCancelSMul G P],
   IsOrderedSMul G P
· 使用定理 `Finset.support_smulAntidiagonal_subset_smul`：support_smulAntidiagonal_su
bset_smul {s : Set G} {t : Set P} (hst : forall a, (s.smulAntidiagonal t a).Fini
te) : { a | (SMulAntidiagonal a (…
-/
theorem isPWO_support_smulAntidiagonal :
    { a | (SMulAntidiagonal a (Set.SMulAntidiagonal.finite_of_isPWO hs ht a)).Nonempty }.IsPWO :=
  (hs.smul ht).mono
    (support_smulAntidiagonal_subset_smul (fun a ↦ (Set.SMulAntidiagonal.finite_of_isPWO hs ht a)))

end

@[to_additive]
/-
**Finset.smulAntidiagonal_min_smul_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smulAntidiagonal_min_smul_min [LinearOrder G] [LinearOrder P] [SMul G P] [
IsOrderedCancelSMul G P] {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hn
s : s.Nonempty) (hnt : t.Nonempty) : SMulAntidiagonal (hs.min hns • ht.min hnt) 
(Set.SMulAntidiagonal.finite_of_isPWO hs.isPWO ht.isPWO (hs.min hns • ht.min hnt
)) = {(hs.min hns, ht.min hnt)}
参数：hs : s.IsWF；ht : t.IsWF；hns : s.Nonempty；hnt : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.SMulAntidiagonal.finite_of_isPWO`：finite_of_isPWO (hs : s.IsPWO) (ht
 : t.IsPWO) (a) : (smulAntidiagonal s t a).Finite
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsCancelSMul.left_cancel`：IsCancelSMul.left_cancel {G P} [SMul G P] [IsC
ancelSMul G P] (a : G) (b c : P) : a • b = a • c -> b = c
· 使用定理 `instIsCancelSMulOfIsOrderedCancelSMul`：∀ {G : Type u_1} {P : Type u_2} [
inst : PartialOrder G] [inst_1 : PartialOrder P] [inst_2 : SMul G P]   [IsOrdere
dCancelSMul G P], IsCancelS…
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `SMul.smul_lt_smul_of_lt_of_le`：smul_lt_smul_of_lt_of_le [Preorder G] [Pr
eorder P] [SMul G P] [IsOrderedCancelSMul G P] {a b : G} {c d : P} (h₁ : a < b) 
(h₂ : c <= d) : a •…
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smulAntidiagonal_min_smul_min [LinearOrder G] [LinearOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty)
    (hnt : t.Nonempty) :
    SMulAntidiagonal (hs.min hns • ht.min hnt)
      (Set.SMulAntidiagonal.finite_of_isPWO hs.isPWO ht.isPWO (hs.min hns • ht.min hnt)) =
      {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_smulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, IsCancelSMul.left_cancel _ _ _ hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset

