/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Inv

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `Fintype`s.

## Main definitions

- `Function.Embedding.toEquivRange`: computably turn an embedding of a
  fintype into an `Equiv` of the domain to its range
- `Equiv.Perm.viaFintypeEmbedding : Perm α → (α ↪ β) → Perm β` extends the domain of
  a permutation, fixing everything outside the range of the embedding

## Implementation details

- `Function.Embedding.toEquivRange` uses a computable inverse, but one that has poor
  computational performance, since it operates by exhaustive search over the input `Fintype`s.
-/

@[expose] public section

assert_not_exists Equiv.Perm.sign

section Fintype

variable {α β : Type*} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)

/-- Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ Set.range f`,
if `α` is a `Fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known, use `Equiv.ofLeftInverse'` or
`Equiv.ofLeftInverse` instead. This is the computable version of `Equiv.ofInjective`.
-/
/-
**Function.Embedding.toEquivRange** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.Embedding.toEquivRange : α ≃ Set.range f where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ Set.range f`,
if `α` is a `Fintype`. Has poor computational performance, due to exhaustive sea
rching in
constructed inverse. When a better inverse is known, use `Equiv.ofLeftInverse'` 
or
`Equiv.ofLeftInverse` instead. This is the computable version of `Equiv.ofInject
ive`.
-/
def Function.Embedding.toEquivRange : α ≃ Set.range f where
  toFun := fun a => ⟨f a, Set.mem_range_self a⟩
  invFun := f.invOfMemRange
  left_inv := fun _ => by simp
  right_inv := fun _ => by simp

@[simp]
/-
**Function.Embedding.toEquivRange_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Embedding.toEquivRange_apply (a : α) : f.toEquivRange a = ⟨f a, S
et.mem_range_self a⟩
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.Embedding.toEquivRange_apply (a : α) :
    f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩ :=
  rfl

@[simp]
/-
**Function.Embedding.toEquivRange_symm_apply_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Embedding.toEquivRange_symm_apply_self (a : α) : f.toEquivRange.s
ymm ⟨f a, Set.mem_range_self a⟩ = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.Embedding.toEquivRange_symm_apply_self (a : α) :
    f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a := by simp [Equiv.symm_apply_eq]
/-
**Function.Embedding.toEquivRange_eq_ofInjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Embedding.toEquivRange_eq_ofInjective : f.toEquivRange = Equiv.of
Injective f f.injective
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.Embedding.toEquivRange_eq_ofInjective :
    f.toEquivRange = Equiv.ofInjective f f.injective := by
  ext
  simp

/-- Extend the domain of `e : Equiv.Perm α`, mapping it through `f : α ↪ β`.
Everything outside of `Set.range f` is kept fixed. Has poor computational performance,
due to exhaustive searching in constructed inverse due to using `Function.Embedding.toEquivRange`.
When a better `α ≃ Set.range f` is known, use `Equiv.Perm.viaSetRange`.
When `[Fintype α]` is not available, a noncomputable version is available as
`Equiv.Perm.viaEmbedding`.
-/
/-
**Equiv.Perm.viaFintypeEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.Perm.viaFintypeEmbedding : Equiv.Perm β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the domain of `e : Equiv.Perm α`, mapping it through `f : α ↪ β`.
Everything outside of `Set.range f` is kept fixed. Has poor computational perfor
mance,
due to exhaustive searching in constructed inverse due to using `Function.Embedd
ing.toEquivRange`.
When a better `α ≃ Set.range f` is known, use `Equiv.Perm.viaSetRange`.
When `[Fintype α]` is not available, a noncomputable version is available as
`Equiv.Perm.viaEmbedding`.
-/
def Equiv.Perm.viaFintypeEmbedding : Equiv.Perm β :=
  e.extendDomain f.toEquivRange

@[simp]
/-
**Equiv.Perm.viaFintypeEmbedding_apply_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.viaFintypeEmbedding_apply_image (a : α) : e.viaFintypeEmbedding
 f (f a) = f (e a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.viaFintypeEmbedding.eq_1`：∀ {α : Type u_1} {β : Type u_2} [in
st : Fintype α] [inst_1 : DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β),   e.via
FintypeEmbedding f = e.ex…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
-/
theorem Equiv.Perm.viaFintypeEmbedding_apply_image (a : α) :
    e.viaFintypeEmbedding f (f a) = f (e a) := by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert! Equiv.Perm.extendDomain_apply_image e (Function.Embedding.toEquivRange f) a
/-
**Equiv.Perm.viaFintypeEmbedding_apply_mem_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.viaFintypeEmbedding_apply_mem_range {b : β} (h : b in Set.range
 f) : e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩))
参数：h : b in Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
-/
theorem Equiv.Perm.viaFintypeEmbedding_apply_mem_range {b : β} (h : b ∈ Set.range f) :
    e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩)) := by
  simp only [viaFintypeEmbedding, Function.Embedding.invOfMemRange]
  rw [Equiv.Perm.extendDomain_apply_subtype _ _ h]
  congr
/-
**Equiv.Perm.viaFintypeEmbedding_apply_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Equiv.Perm.viaFintypeEmbedding_apply_notMem_range {b : β} (h : b ∉ Set.ran
ge f) : e.viaFintypeEmbedding f b = b
参数：h : b ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.viaFintypeEmbedding.eq_1`：∀ {α : Type u_1} {β : Type u_2} [in
st : Fintype α] [inst_1 : DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β),   e.via
FintypeEmbedding f = e.ex…
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
-/
theorem Equiv.Perm.viaFintypeEmbedding_apply_notMem_range {b : β} (h : b ∉ Set.range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]

end Fintype

namespace Equiv

variable {α β : Type*}

/-- If two sets have the same finite cardinality, their set differences are equivalent. -/
/-
**Equiv.setDiffEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：setDiffEquiv {s t : Set α} [Fintype s] [Fintype t] (h : Fintype.card s = F
intype.card t) : (s \ t : Set α) ≃ (t \ s : Set α)
参数：h : Fintype.card s = Fintype.card t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two sets have the same finite cardinality, their set differences are equivale
nt.
-/
noncomputable def setDiffEquiv {s t : Set α} [Fintype s] [Fintype t]
    (h : Fintype.card s = Fintype.card t) : (s \ t : Set α) ≃ (t \ s : Set α) := by
  classical
  let fs : Finset α := Finset.univ.map (Function.Embedding.subtype (· ∈ s))
  let ft : Finset α := Finset.univ.map (Function.Embedding.subtype (· ∈ t))
  have hs (x : α) : x ∈ fs ↔ x ∈ s := by simp [fs]
  have ht (x : α) : x ∈ ft ↔ x ∈ t := by simp [ft]
  have hst (x : α) : x ∈ fs \ ft ↔ x ∈ s \ t := by simp [hs, ht]
  have hts (x : α) : x ∈ ft \ fs ↔ x ∈ t \ s := by simp [hs, ht]
  have hc : fs.card = ft.card := by
    rw [← Fintype.subtype_card fs hs, ← Fintype.subtype_card ft ht]; convert! h
  replace hc := Finset.card_sdiff_comm hc
  rw [← Fintype.subtype_card (fs \ ft) hst, ← Fintype.subtype_card (ft \ fs) hts] at hc
  exact ((Fintype.card_eq (_F := (_)) (_G := (_))).mp hc).some

open scoped Classical in
/-- If `e` is an equivalence between two subtypes of a type `α`, `e.toCompl`
is an equivalence between the complement of those subtypes.

See also `Equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known. -/
/-
**Equiv.toCompl** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toCompl {p q : α -> Prop} [Finite {x | p x}] (e : { x | p x } ≃ { x | q x 
}) : { x | ¬p x } ≃ { x | ¬q x }
参数：e : { x | p x } ≃ { x | q x }。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If `e` is an equivalence between two subtypes of a type `α`, `e.toCompl`
is an equivalence between the complement of those subtypes.

See also `Equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known.
-/
noncomputable def toCompl {p q : α → Prop} [Finite {x | p x}]
    (e : { x | p x } ≃ { x | q x }) : { x | ¬p x } ≃ { x | ¬q x } :=
  let sp : Set α := {x | p x}
  let sq : Set α := {x | q x}
  letI : Fintype sp := Fintype.ofFinite sp
  letI : Fintype sq := Fintype.ofEquiv sp e
  have h := setDiffEquiv (Fintype.card_congr e)
  have hpc : spᶜ = (sq \ sp) ∪ (sp ∪ sq)ᶜ := by ext; simp; tauto
  have hqc : sqᶜ = (sp \ sq) ∪ (sp ∪ sq)ᶜ := by ext; simp; tauto
  let epc := (Equiv.setCongr hpc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  let eqc := (Equiv.setCongr hqc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  epc.trans <| .trans (h.symm.sumCongr <| .refl _) eqc.symm

variable {p q : α → Prop} [DecidablePred p] [DecidablePred q] [Finite {x | p x}]

/-- If `e` is an equivalence between two subtypes of a type `α`, `e.extendSubtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbitrary outside.

Note that when `p = q`, `Equiv.Perm.subtypeCongr e (Equiv.refl _)` can be used instead. -/
/-
**Equiv.extendSubtype** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv`。
形式化陈述：extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α
参数：e : { x // p x } ≃ { x // q x }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e` is an equivalence between two subtypes of a type `α`, `e.extendSubtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbi
trary outside.

Note that when `p = q`, `Equiv.Perm.subtypeCongr e (Equiv.refl _)` can be used i
nstead.
-/
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.extendSubtype_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x
) : e.extendSubtype x = e ⟨x, hx⟩
参数：e : { x // p x } ≃ { x // q x }；x；hx : p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumCompl_symm_apply_of_pos`：sumCompl_symm_apply_of_pos {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : p a) : (sumCompl p).symm a = Sum.inl ⟨a,
 h⟩
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    e.extendSubtype x = e ⟨x, hx⟩ := by
  simp [extendSubtype, subtypeCongr, sumCompl_symm_apply_of_pos hx]
/-
**Equiv.extendSubtype_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) : q (e.
extendSubtype x)
参数：e : { x // p x } ≃ { x // q x }；x；hx : p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.extendSubtype_apply_of_mem`：extendSubtype_apply_of_mem (e : { x //
 p x } ≃ { x // q x }) (x) (hx : p x) : e.extendSubtype x = e ⟨x, hx⟩
-/
theorem extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    q (e.extendSubtype x) :=
  (e.extendSubtype_apply_of_mem _ hx).symm ▸ (e ⟨x, hx⟩).2
/-
**Equiv.extendSubtype_apply_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx :
 ¬p x) : e.extendSubtype x = e.toCompl ⟨x, hx⟩
参数：e : { x // p x } ≃ { x // q x }；x；hx : ¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.sumCompl_symm_apply_of_neg`：sumCompl_symm_apply_of_neg {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : ¬p a) : (sumCompl p).symm a = Sum.inr ⟨a
, h⟩
-/
theorem extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ := by
  simp only [extendSubtype, subtypeCongr, Equiv.trans_apply,
    sumCompl_symm_apply_of_neg hx]
  rfl
/-
**Equiv.extendSubtype_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) : 
¬q (e.extendSubtype x)
参数：e : { x // p x } ≃ { x // q x }；x；hx : ¬p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.extendSubtype_apply_of_not_mem`：extendSubtype_apply_of_not_mem (e 
: { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) : e.extendSubtype x = e.toCompl ⟨
x, hx⟩
-/
theorem extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    ¬q (e.extendSubtype x) :=
  e.extendSubtype_apply_of_not_mem _ hx ▸ (e.toCompl ⟨x, hx⟩).2

/-- Given two injective functions `f` and `g` from a finite type `α` to any type `β`,
there exists a permutation of `β` that maps `f` to `g`. -/
/-
**Equiv.Perm.exists_extending_pair** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Finite α] (f g : α → β),   Function.Injec
tive f → Function.Injective g → ∃ σ, ∀ (a : α), σ (f a) = g a
参数：f g : α → β；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.codRestrict_range_surjective`：codRestrict_range_surjective (f : ι ->
 α) : ((range f).codRestrict f mem_range_self).Surjective
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.extendSubtype_apply_of_mem`：extendSubtype_apply_of_mem (e : { x //
 p x } ≃ { x // q x }) (x) (hx : p x) : e.extendSubtype x = e ⟨x, hx⟩
· 使用定理 `Equiv.ofInjective_symm_apply`：ofInjective_symm_apply {α β} {f : α -> β} 
(hf : Injective f) (a : α) : (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Given two injective functions `f` and `g` from a finite type `α` to any type `β`
,
there exists a permutation of `β` that maps `f` to `g`.
-/
theorem Perm.exists_extending_pair [Finite α]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Perm β, ∀ a, σ (f a) = g a := by
  classical
  have : Finite {x | x ∈ Set.range f} := .of_surjective _ (Set.codRestrict_range_surjective f)
  refine ⟨((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).extendSubtype, ?_⟩
  simp [Equiv.extendSubtype_apply_of_mem]

/-- Any two same-cardinality finsets are related by a permutation. -/
/-
**Equiv.Perm.exists_map_finset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {β : Type u_2} (s t : Finset β), s.card = t.card → ∃ σ, Finset.map (Equi
v.toEmbedding σ) s = t
参数：s t : Finset β；Equiv.toEmbedding σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.exists_extending_pair`：∀ {α : Type u_1} {β : Type u_2} [Finit
e α] (f g : α → β),   Function.Injective f → Function.Injective g → ∃ σ, ∀ (a : 
α), σ (f a) = g a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s

--- 原说明 ---
Any two same-cardinality finsets are related by a permutation.
-/
theorem Perm.exists_map_finset_eq
    (s t : Finset β) (h : s.card = t.card) :
    ∃ σ : Perm β, s.map σ.toEmbedding = t := by
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair
    (fun x : s => (x : β)) (fun x : s => ((s.equivOfCardEq h) x : β))
    Subtype.val_injective (Subtype.val_injective.comp (s.equivOfCardEq h).injective)
  refine ⟨σ, Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [h])⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  exact (hσ ⟨a, ha⟩) ▸ ((s.equivOfCardEq h) ⟨a, ha⟩).2

end Equiv

