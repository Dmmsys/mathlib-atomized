/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Maps on modules and ideals

Main definitions include `Ideal.map`, `Ideal.comap`, `RingHom.ker`, `Module.annihilator`
and `Submodule.annihilator`.
-/

@[expose] public section

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`
  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open scoped Pointwise

namespace Ideal

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]
variable [FunLike F R S]
variable (f : F)
variable {I J : Ideal R} {K L : Ideal S}

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
/-
**Ideal.map** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：map (I : Ideal R) : Ideal S
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I.map f` is the span of the image of the ideal `I` under `f`, which may be bigg
er than
  the image itself.
-/
def map (I : Ideal R) : Ideal S :=
  span (f '' I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
/-
**Ideal.comap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：comap [RingHomClass F R S] (I : Ideal S) : Ideal R where carrier
参数：I : Ideal S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I.comap f` is the preimage of `I` under `f`.
-/
def comap [RingHomClass F R S] (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx

@[simp]
/-
**Ideal.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f I : Set R) = f ⁻¹'
 I
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f I : Set R) = f ⁻¹' I := rfl
/-
**Ideal.comap_coe** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap (f : R ->+* S) = I.
comap f
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap (f : R →+* S) = I.comap f := rfl
/-
**Ideal.map_coe** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_coe [RingHomClass F R S] (I : Ideal R) : I.map (f : R ->+* S) = I.map 
f
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_coe [RingHomClass F R S] (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

variable {f}

@[gcongr]
/-
**Ideal.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_mono (h : I <= J) : map f I <= map f J
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.span_mono`：span_mono {s t : Set α} : s subseteq t -> span s <= spa
n t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
  span_mono <| Set.image_mono h
/-
**Ideal.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x in I) : f x in map f I
参数：f : F；h : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
theorem mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
  subset_span ⟨x, h, rfl⟩
/-
**Ideal.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x in I.map f
参数：f : F；I : Ideal R；x : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x ∈ I.map f :=
  mem_map_of_mem f x.2
/-
**Ideal.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_le_iff_le_comap [RingHomClass F R S] : map f I <= K ↔ I <= comap f K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap [RingHomClass F R S] : map f I ≤ K ↔ I ≤ comap f K :=
  span_le.trans Set.image_subset_iff

@[simp]
/-
**Ideal.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap [RingHomClass F R S] {x} : x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl

@[gcongr]
/-
**Ideal.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_mono [RingHomClass F R S] (h : K <= L) : comap f K <= comap f L
参数：h : K <= L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem comap_mono [RingHomClass F R S] (h : K ≤ L) : comap f K ≤ comap f L :=
  Set.preimage_mono fun _ hx => h hx

variable (f)
/-
**Ideal.comap_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : comap f K != ⊤
参数：hK : K != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem comap_ne_top [RingHomClass F R S] (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
  (ne_top_iff_one _).2 <| by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK
/-
**Ideal.exists_ideal_comap_le_prime** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_ideal_comap_le_prime {S} [CommSemiring S] [FunLike F R S] [RingHomC
lass F R S] {f : F} (P : Ideal R) [P.IsPrime] (I : Ideal S) (le : I.comap f <= P
) : exists Q >= I, Q.IsPrime ∧ Q.comap f <= P
参数：P : Ideal R；I : Ideal S；le : I.comap f <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.exists_le_prime_disjoint`：exists_le_prime_disjoint (S : Submonoid 
α) (disjoint : Disjoint (I : Set α) S) : exists p : Ideal α, p.IsPrime ∧ I <= p 
∧ Disjoint (p : Set …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma exists_ideal_comap_le_prime {S} [CommSemiring S] [FunLike F R S] [RingHomClass F R S]
    {f : F} (P : Ideal R) [P.IsPrime] (I : Ideal S) (le : I.comap f ≤ P) :
    ∃ Q ≥ I, Q.IsPrime ∧ Q.comap f ≤ P :=
  have ⟨Q, hQ, hIQ, disj⟩ := I.exists_le_prime_disjoint (P.primeCompl.map f) <|
    Set.disjoint_left.mpr fun _ ↦ by rintro hI ⟨r, hp, rfl⟩; exact hp (le hI)
  ⟨Q, hIQ, hQ, fun r hp' ↦ of_not_not fun hp ↦ Set.disjoint_left.mp disj hp' ⟨_, hp, rfl⟩⟩

variable {G : Type*} [FunLike G S R]
/-
**Ideal.map_le_comap_of_inv_on** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_le_comap_of_inv_on [RingHomClass G S R] (g : G) (I : Ideal R) (hf : Se
t.LeftInvOn g f I) : I.map f <= I.comap g
参数：g : G；I : Ideal R；hf : Set.LeftInvOn g f I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
-/
theorem map_le_comap_of_inv_on [RingHomClass G S R] (g : G) (I : Ideal R)
    (hf : Set.LeftInvOn g f I) :
    I.map f ≤ I.comap g := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_comap, hf hx]
  exact hx
/-
**Ideal.comap_le_map_of_inv_on** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_le_map_of_inv_on [RingHomClass F R S] (g : G) (I : Ideal S) (hf : Se
t.LeftInvOn g f (f ⁻¹' I)) : I.comap f <= I.map g
参数：g : G；I : Ideal S；hf : Set.LeftInvOn g f (f ⁻¹' I)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
-/
theorem comap_le_map_of_inv_on [RingHomClass F R S] (g : G) (I : Ideal S)
    (hf : Set.LeftInvOn g f (f ⁻¹' I)) :
    I.comap f ≤ I.map g :=
  fun x (hx : f x ∈ I) => hf hx ▸ Ideal.mem_map_of_mem g hx

/-- The `Ideal` version of `Set.image_subset_preimage_of_inverse`. -/
/-
**Ideal.map_le_comap_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_le_comap_of_inverse [RingHomClass G S R] (g : G) (I : Ideal R) (h : Fu
nction.LeftInverse g f) : I.map f <= I.comap g
参数：g : G；I : Ideal R；h : Function.LeftInverse g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_le_comap_of_inv_on`：map_le_comap_of_inv_on [RingHomClass G S R
] (g : G) (I : Ideal R) (hf : Set.LeftInvOn g f I) : I.map f <= I.comap g
· 使用定理 `Function.LeftInverse.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {g : β → α}, Function.LeftInverse f g → ∀ (s : Set β), Set.LeftInvOn f g s

--- 原说明 ---
The `Ideal` version of `Set.image_subset_preimage_of_inverse`.
-/
theorem map_le_comap_of_inverse [RingHomClass G S R] (g : G) (I : Ideal R)
    (h : Function.LeftInverse g f) :
    I.map f ≤ I.comap g :=
  map_le_comap_of_inv_on _ _ _ <| h.leftInvOn _
/-
**Ideal.eq_bot_of_comap_eq_bot'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_bot_of_comap_eq_bot' {f : R ->+* S} (hf : Function.Surjective f) {I : I
deal S} (h : I.comap f = ⊥) : I = ⊥
参数：hf : Function.Surjective f；h : I.comap f = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_bot_of_comap_eq_bot' {f : R →+* S} (hf : Function.Surjective f)
    {I : Ideal S} (h : I.comap f = ⊥) :
    I = ⊥ := by
  ext x
  obtain ⟨y, hy⟩ := hf x
  aesop (add norm [Submodule.eq_bot_iff])

variable [RingHomClass F R S]
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [K.IsTwoSided] : (comap f K).IsTwoSided :=
  ⟨fun b ha ↦ by rw [mem_comap, map_mul]; exact mul_mem_right _ _ ha⟩

/-- The `Ideal` version of `Set.preimage_subset_image_of_inverse`. -/
/-
**Ideal.comap_le_map_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g 
f) : I.comap f <= I.map g
参数：g : G；I : Ideal S；h : Function.LeftInverse g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_le_map_of_inv_on`：comap_le_map_of_inv_on [RingHomClass F R S
] (g : G) (I : Ideal S) (hf : Set.LeftInvOn g f (f ⁻¹' I)) : I.comap f <= I.map 
g
· 使用定理 `Function.LeftInverse.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {g : β → α}, Function.LeftInverse f g → ∀ (s : Set β), Set.LeftInvOn f g s

--- 原说明 ---
The `Ideal` version of `Set.preimage_subset_image_of_inverse`.
-/
theorem comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g f) :
    I.comap f ≤ I.map g :=
  comap_le_map_of_inv_on _ _ _ <| h.leftInvOn _
/-
**Ideal.IsPrime.comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semiring R] [inst_1 : S
emiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal S} [inst_3 : RingHomCla
ss F R S] [hK : K.IsPrime], (Ideal.comap f K).IsPrime
参数：f : F；Ideal.comap f K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.IsPrime.mem_or_mem'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal
 α} [self : I.IsPrime] {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
instance IsPrime.comap [hK : K.IsPrime] : (comap f K).IsPrime :=
  ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩

variable (I J K L)
/-
**Ideal.map_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_top : map f ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `trivial`：True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem map_top : map f ⊤ = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span ⟨1, trivial, map_one f⟩
/-
**Ideal.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
-/
theorem gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f) := fun _ _ =>
  Ideal.map_le_iff_le_comap

@[simp]
/-
**Ideal.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_id : I.comap (RingHom.id R) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_id : I.comap (RingHom.id R) = I :=
  Ideal.ext fun _ => Iff.rfl

@[simp]
/-
**Ideal.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_id : I.comap (RingHom.id R) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comap_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S) :
    Ideal.comap (AlgHom.id R S) I = I :=
  I.comap_id

@[simp]
/-
**Ideal.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_id : I.map (RingHom.id R) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_unique`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →  
   ∀ {u' : α → …
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
· 使用定理 `GaloisConnection.id`：∀ {α : Type u} [pα : Preorder α], GaloisConnection 
id id
· 使用定理 `Ideal.comap_id`：comap_id : I.comap (RingHom.id R) = I
-/
theorem map_id : I.map (RingHom.id R) = I :=
  (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id

@[simp]
/-
**Ideal.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_id : I.map (RingHom.id R) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_unique`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →  
   ∀ {u' : α → …
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
· 使用定理 `GaloisConnection.id`：∀ {α : Type u} [pα : Preorder α], GaloisConnection 
id id
· 使用定理 `Ideal.comap_id`：comap_id : I.comap (RingHom.id R) = I
-/
lemma map_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S) :
    Ideal.map (AlgHom.id R S) I = I :=
  I.map_id
/-
**Ideal.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R ->+* S) (g : S -
>+* T) : (I.comap g).comap f = I.comap (g.comp f)
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R →+* S) (g : S →+* T) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  rfl
/-
**Ideal.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R ->+* S) (g : S -
>+* T) : (I.comap g).comap f = I.comap (g.comp f)
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_comapₐ {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [Algebra R B] [Semiring C] [Algebra R C] {I : Ideal C} (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  I.comap_comap f.toRingHom g.toRingHom
/-
**Ideal.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+* S) (g : S ->+* 
T) : (I.map f).map g = I.map (g.comp f)
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_unique`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →  
   ∀ {u' : α → …
· 使用定理 `GaloisConnection.compose`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {l1 : α → β}   {u1 : 
β → α} {l2 : β…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
-/
theorem map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R →+* S) (g : S →+* T) :
    (I.map f).map g = I.map (g.comp f) :=
  ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _
/-
**Ideal.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+* S) (g : S ->+* 
T) : (I.map f).map g = I.map (g.comp f)
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_unique`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →  
   ∀ {u' : α → …
· 使用定理 `GaloisConnection.compose`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {l1 : α → β}   {u1 : 
β → α} {l2 : β…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
-/
lemma map_mapₐ {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [Algebra R B] [Semiring C] [Algebra R C] {I : Ideal A} (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (I.map f).map g = I.map (g.comp f) :=
  I.map_map f.toRingHom g.toRingHom
/-
**Ideal.map_span** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_span (s : Set R) : map f (span s) = span (f '' s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Ideal.coe_comap`：coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f
 I : Set R) = f ⁻¹' I
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_span (s : Set R) : map f (span s) = span (f '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span

variable {f I J K L}
/-
**Ideal.map_le_of_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_le_of_le_comap : I <= K.comap f -> I.map f <= K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
  (gc_map_comap f).l_le
/-
**Ideal.le_comap_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_comap_of_map_le : I.map f <= K -> I <= K.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ {a : α}
 {b : β}, l…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
  (gc_map_comap f).le_u
/-
**Ideal.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_comap_map : I <= (I.map f).comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem le_comap_map : I ≤ (I.map f).comap f :=
  (gc_map_comap f).le_u_l _
/-
**Ideal.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_comap_le : (K.comap f).map f <= K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_comap_le : (K.comap f).map f ≤ K :=
  (gc_map_comap f).l_u_le _

@[simp]
/-
**Ideal.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_top : (⊤ : Ideal S).comap f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem comap_top : (⊤ : Ideal S).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
/-
**Ideal.comap_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
-/
theorem comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
  ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩

@[simp]
/-
**Ideal.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_bot : (⊥ : Ideal R).map f = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_bot : (⊥ : Ideal R).map f = ⊥ :=
  (gc_map_comap f).l_bot
/-
**Ideal.ne_bot_of_map_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ne_bot_of_map_ne_bot (hI : map f I != ⊥) : I != ⊥
参数：hI : map f I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
-/
theorem ne_bot_of_map_ne_bot (hI : map f I ≠ ⊥) : I ≠ ⊥ :=
  fun h => hI (Eq.mpr (congrArg (fun I ↦ map f I = ⊥) h) map_bot)

variable (f I J K L)

@[simp]
/-
**Ideal.map_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_comap_map : ((I.map f).comap f).map f = I.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_comap_map : ((I.map f).comap f).map f = I.map f :=
  (gc_map_comap f).l_u_l_eq_l I

@[simp]
/-
**Ideal.comap_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_map_comap : ((K.comap f).map f).comap f = K.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
  (gc_map_comap f).u_l_u_eq_u K
/-
**Ideal.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
/-
**Ideal.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L :=
  rfl

variable {ι : Sort*}
/-
**Ideal.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_iSup (K : ι -> Ideal R) : (iSup K).map f = ⨆ i, (K i).map f
参数：K : ι -> Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_iSup (K : ι → Ideal R) : (iSup K).map f = ⨆ i, (K i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
/-
**Ideal.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_iInf (K : ι -> Ideal S) : (iInf K).comap f = ⨅ i, (K i).comap f
参数：K : ι -> Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem comap_iInf (K : ι → Ideal S) : (iInf K).comap f = ⨅ i, (K i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf
/-
**Ideal.comap_finsetInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_finsetInf {ι : Type*} (s : Finset ι) (K : ι -> Ideal S) : (s.inf K).
comap f = s.inf fun i => (K i).comap f
参数：s : Finset ι；K : ι -> Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `Ideal.comap_iInf`：comap_iInf (K : ι -> Ideal S) : (iInf K).comap f = ⨅ i
, (K i).comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_finsetInf {ι : Type*} (s : Finset ι) (K : ι → Ideal S) :
    (s.inf K).comap f = s.inf fun i ↦ (K i).comap f := by
  simp [Finset.inf_eq_iInf, comap_iInf]
/-
**Ideal.map_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_sSup (s : Set (Ideal R)) : (sSup s).map f = ⨆ I in s, (I : Ideal R).ma
p f
参数：s : Set (Ideal R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_sSup (s : Set (Ideal R)) : (sSup s).map f = ⨆ I ∈ s, (I : Ideal R).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup
/-
**Ideal.comap_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I in s, (I : Ideal S
).comap f
参数：s : Set (Ideal S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ s, (I : Ideal S).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf
/-
**Ideal.comap_sInf'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I in comap f '' s, 
I
参数：s : Set (Ideal S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Ideal.comap_sInf`：comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ 
I in s, (I : Ideal S).comap f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
-/
theorem comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ comap f '' s, I :=
  _root_.trans (comap_sInf f s) (by rw [iInf_image])

/-- Variant of `Ideal.IsPrime.comap` where ideal is explicit rather than implicit. -/
/-
**Ideal.comap_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…

--- 原说明 ---
Variant of `Ideal.IsPrime.comap` where ideal is explicit rather than implicit.
-/
theorem comap_isPrime [H : IsPrime K] : IsPrime (comap f K) :=
  H.comap f

variable {I J K L}
/-
**Ideal.map_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_inf_le : map f (I ⊓ J) <= map f I ⊓ map f J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _
/-
**Ideal.le_comap_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_comap_sup : comap f K ⊔ comap f L <= comap f (K ⊔ L)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `Ideal.gc_map_comap`：gc_map_comap : GaloisConnection (Ideal.map f) (Ideal
.comap f)
-/
theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _

-- TODO: Should these be simp lemmas?
/-
**Ideal._root_.element_smul_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.element_smul_restrictScalars {R S M}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] (r : R) (N : Submodule S M) :
    (algebraMap R S r • N).restrictScalars R = r • N.restrictScalars R :=
  SetLike.coe_injective (congrArg (· '' _) (funext (algebraMap_smul S r)))
/-
**Ideal.smul_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_restrictScalars {R S M} [CommSemiring R] [CommSemiring S] [Algebra R 
S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal 
R) (N : Submodule S M) : (I.map (algebraMap R S) • N).restrictScalars R = I • N.
restrictScalars R
参数：I : Ideal R；N : Submodule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用引理 `Submodule.span_smul_eq`：span_smul_eq (s : Set R) (N : Submodule R M) : I
deal.span s • N = s • N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Submodule.set_smul_eq_iSup`：set_smul_eq_iSup [SMulCommClass S R M] (s : 
Set S) (N : Submodule R M) : s • N = ⨆ (a in s), a • N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `map_iSup₂`：map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) 
(g : forall i, κ i -> α) : f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j)
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
-/
theorem smul_restrictScalars {R S M} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R) (N : Submodule S M) :
    (I.map (algebraMap R S) • N).restrictScalars R = I • N.restrictScalars R := by
  simp_rw [map, Submodule.span_smul_eq, ← Submodule.coe_set_smul,
    Submodule.set_smul_eq_iSup, ← element_smul_restrictScalars, iSup_image]
  exact map_iSup₂ (Submodule.restrictScalarsLatticeHom R S M) _

@[simp]
/-
**Ideal.smul_top_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_top_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R
 S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictS
calars R
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.smul_restrictScalars`：smul_restrictScalars {R S M} [CommSemiring R
] [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M] [Is
ScalarTower R S …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.smul_eq_mul`：∀ {R : Type u} [inst : Semiring R] (I J : Ideal R), I
 • J = I * J
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
-/
theorem smul_top_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictScalars R :=
  Eq.trans (smul_restrictScalars I (⊤ : Ideal S)).symm <|
    congrArg _ <| Eq.trans (Ideal.smul_eq_mul _ _) (Ideal.mul_top _)

@[simp]
/-
**Ideal.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coe_restrictScalars {R S : Type*} [Semiring R] [Semiring S] [Module R S] [
IsScalarTower R S S] (I : Ideal S) : (I.restrictScalars R : Set S) = ↑I
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars {R S : Type*} [Semiring R] [Semiring S] [Module R S]
    [IsScalarTower R S S] (I : Ideal S) : (I.restrictScalars R : Set S) = ↑I :=
  rfl

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp]
/-
**Ideal.restrictScalars_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：restrictScalars_mul {R S : Type*} [Semiring R] [Semiring S] [Module R S] [
IsScalarTower R S S] (I J : Ideal S) : (I * J).restrictScalars R = I.restrictSca
lars R * J.restrictScalars R
参数：I J : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so.
-/
theorem restrictScalars_mul {R S : Type*} [Semiring R] [Semiring S] [Module R S]
    [IsScalarTower R S S] (I J : Ideal S) :
    (I * J).restrictScalars R = I.restrictScalars R * J.restrictScalars R :=
  rfl

section Surjective

section

variable (hf : Function.Surjective f)
include hf

open Function

/-
**Ideal.map_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I :=
  le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r ∈ I from hfrs.symm ▸ hsi)

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
/-
**Ideal.giMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：giMapComap : GaloisInsertion (map f) (comap f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I

--- 原说明 ---
`map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity
-/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)
/-
**Ideal.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_surjective_of_surjective : Surjective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_surjective`：l_surjective [Preorder α] [PartialOrder β]
 (gi : GaloisInsertion l u) : Surjective l
-/
theorem map_surjective_of_surjective : Surjective (map f) :=
  (giMapComap f hf).l_surjective
/-
**Ideal.comap_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_injective_of_surjective : Injective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
-/
theorem comap_injective_of_surjective : Injective (comap f) :=
  (giMapComap f hf).u_injective
/-
**Ideal.map_sup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f ⊔ J.comap f).map 
f = I ⊔ J
参数：I J : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
  (giMapComap f hf).l_sup_u _ _
/-
**Ideal.map_iSup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_iSup_comap_of_surjective (K : ι -> Ideal S) : (⨆ i, (K i).comap f).map
 f = iSup K
参数：K : ι -> Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem map_iSup_comap_of_surjective (K : ι → Ideal S) : (⨆ i, (K i).comap f).map f = iSup K :=
  (giMapComap f hf).l_iSup_u _
/-
**Ideal.map_inf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f ⊓ J.comap f).map 
f = I ⊓ J
参数：I J : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_inf_u`：l_inf_u [SemilatticeInf α] [SemilatticeInf β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊓ u b) = a ⊓ b
-/
theorem map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
  (giMapComap f hf).l_inf_u _ _
/-
**Ideal.map_iInf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_iInf_comap_of_surjective (K : ι -> Ideal S) : (⨅ i, (K i).comap f).map
 f = iInf K
参数：K : ι -> Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_u`：l_iInf_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨅ i, u (f i)) = ⨅ i
, f i
-/
theorem map_iInf_comap_of_surjective (K : ι → Ideal S) : (⨅ i, (K i).comap f).map f = iInf K :=
  (giMapComap f hf).l_iInf_u _
/-
**Ideal.mem_image_of_mem_map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y in map f I) : 
y in f '' I
参数：H : y in map f I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y ∈ map f I) : y ∈ f '' I :=
  Submodule.span_induction (hx := H) (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩
/-
**Ideal.mem_map_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_map_iff_of_surjective {I : Ideal R} {y} : y in map f I ↔ exists x, x i
n I ∧ f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Ideal.mem_image_of_mem_map_of_surjective`：mem_image_of_mem_map_of_surjec
tive {I : Ideal R} {y} (H : y in map f I) : y in f '' I
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_map_iff_of_surjective {I : Ideal R} {y} : y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
  ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩
/-
**Ideal.le_map_of_comap_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_map_of_comap_le_of_surjective : comap f K <= I -> K <= map f I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
-/
theorem le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I := fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h

end

/-
**Ideal.map_comap_eq_self_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_comap_eq_self_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E
 R S] (e : E) (I : Ideal S) : map e (comap e I) = I
参数：e : E；I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
theorem map_comap_eq_self_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    (I : Ideal S) : map e (comap e I) = I :=
  I.map_comap_of_surjective e (EquivLike.surjective e)
/-
**Ideal.map_eq_submodule_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_eq_submodule_map (f : R ->+* S) [h : RingHomSurjective f] (I : Ideal R
) : I.map f = Submodule.map f.toSemilinearMap I
参数：f : R ->+* S；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `RingHomSurjective.is_surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst
 : Semiring R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   [self : RingHomSurjecti
ve σ], Function.Surje…
-/
theorem map_eq_submodule_map (f : R →+* S) [h : RingHomSurjective f] (I : Ideal R) :
    I.map f = Submodule.map f.toSemilinearMap I :=
  Submodule.ext fun _ => mem_map_iff_of_surjective f h.1
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (f : R →+* S) [RingHomSurjective f] (I : Ideal R) [I.IsTwoSided] :
    (I.map f).IsTwoSided where
  mul_mem_of_left b ha := by
    rw [map_eq_submodule_map] at ha ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := f.surjective b
    rw [RingHom.coe_toSemilinearMap, ← map_mul]
    exact ⟨_, I.mul_mem_right _ ha, rfl⟩

open Function in
/-
**Ideal.IsMaximal.comap_piEvalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal
`。
形式化陈述：∀ {ι : Type u_4} {R : ι → Type u_5} [inst : (i : ι) → Semiring (R i)] {i :
 ι} {I : Ideal (R i)},   I.IsMaximal → (Ideal.comap (Pi.evalRingHom R i) I).IsMa
ximal
参数：i : ι；R i；R i；Ideal.comap (Pi.evalRingHom R i) I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.exists_inv`：∀ {α : Type u} [inst : Semiring α] {I : Idea
l α}, I.IsMaximal → ∀ {x : α}, x ∉ I → ∃ y, ∃ i ∈ I, y * x + i = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
theorem IsMaximal.comap_piEvalRingHom {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    {i : ι} {I : Ideal (R i)} (h : I.IsMaximal) : (I.comap <| Pi.evalRingHom R i).IsMaximal := by
  refine isMaximal_iff.mpr ⟨I.ne_top_iff_one.mp h.ne_top, fun J x le hxI hxJ ↦ ?_⟩
  have ⟨r, y, hy, eq⟩ := h.exists_inv hxI
  classical
  convert!
    J.add_mem (J.mul_mem_left (update 0 i r) hxJ) (b := update 1 i y)
      (le <| by apply update_self i y 1 ▸ hy)
  ext j
  obtain rfl | ne := eq_or_ne j i
  · simpa [eq_comm] using eq
  · simp [update_of_ne ne]
/-
**Ideal.comap_le_comap_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_le_comap_iff_of_surjective (hf : Function.Surjective f) (I J : Ideal
 S) : comap f I <= comap f J ↔ I <= J
参数：hf : Function.Surjective f；I J : Ideal S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `Ideal.map_le_of_le_comap`：map_le_of_le_comap : I <= K.comap f -> I.map f
 <= K
· 使用定理 `Ideal.le_comap_of_map_le`：le_comap_of_map_le : I.map f <= K -> I <= K.co
map f
-/
theorem comap_le_comap_iff_of_surjective (hf : Function.Surjective f) (I J : Ideal S) :
    comap f I ≤ comap f J ↔ I ≤ J :=
  ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩

/-- The map on ideals induced by a surjective map preserves inclusion. -/
@[simps]
/-
**Ideal.orderEmbeddingOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：orderEmbeddingOfSurjective (hf : Function.Surjective f) : Ideal S ↪o Ideal
 R where toFun
参数：hf : Function.Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_le_comap_iff_of_surjective`：comap_le_comap_iff_of_surjective
 (hf : Function.Surjective f) (I J : Ideal S) : comap f I <= comap f J ↔ I <= J

--- 原说明 ---
The map on ideals induced by a surjective map preserves inclusion.
-/
def orderEmbeddingOfSurjective (hf : Function.Surjective f) : Ideal S ↪o Ideal R where
  toFun := comap f
  inj' _ _ eq := SetLike.ext' (Set.preimage_injective.mpr hf <| SetLike.ext'_iff.mp eq)
  map_rel_iff' := comap_le_comap_iff_of_surjective _ hf ..
/-
**Ideal.map_eq_top_or_isMaximal_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_eq_top_or_isMaximal_of_surjective (hf : Function.Surjective f) {I : Id
eal R} (H : IsMaximal I) : map f I = ⊤ ∨ IsMaximal (map f I)
参数：hf : Function.Surjective f；H : IsMaximal I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem map_eq_top_or_isMaximal_of_surjective (hf : Function.Surjective f) {I : Ideal R}
    (H : IsMaximal I) : map f I = ⊤ ∨ IsMaximal (map f I) :=
  or_iff_not_imp_left.2 fun ne_top ↦ ⟨⟨ne_top, fun _J hJ ↦ comap_injective_of_surjective f hf <|
    H.1.2 _ (le_comap_map.trans_lt <| (orderEmbeddingOfSurjective f hf).strictMono hJ)⟩⟩

end Surjective

section Pi

variable {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]

/-
**Ideal.map_evalRingHom_pi** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_evalRingHom_pi {I : Π i, Ideal (R i)} (i : ι) : (pi I).map (Pi.evalRin
gHom R i) = I i
参数：R i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Ideal.single_mem_pi`：single_mem_pi [DecidableEq ι] {i : ι} {r : R i} (hr
 : r in I i) : Pi.single i r in pi I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_evalRingHom_pi {I : Π i, Ideal (R i)} (i : ι) :
    (pi I).map (Pi.evalRingHom R i) = I i := by
  ext r
  rw [mem_map_iff_of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)]
  classical refine ⟨?_, fun hr ↦ ⟨_, single_mem_pi hr, by simp⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact hr i

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Ideals in a finite direct product semiring `Πᵢ Rᵢ` are identified with tuples of ideals
in the individual semirings, in an order-preserving way.

(Note that this is not in general true for infinite direct products:
If infinitely many of the `Rᵢ` are nontrivial, then there exists an ideal of `Πᵢ Rᵢ` that
is not of the form `Πᵢ Iᵢ`, namely the ideal of finitely supported elements of `Πᵢ Rᵢ`
(it is also not a principal ideal).) -/
/-
**Ideal.piOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{ι : Type u_4} →   {R : ι → Type u_5} → [inst : (i : ι) → Semiring (R i)] 
→ [Finite ι] → Ideal ((i : ι) → R i) ≃o ((i : ι) → Ideal (R i))
参数：i : ι；R i；(i : ι) → R i；(i : ι) → Ideal (R i)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.pi_le_pi_iff`：∀ {ι : Type u_1} {R : ι → Type u_5} [inst : (i : ι) 
→ Semiring (R i)] {I J : (i : ι) → Ideal (R i)},   Ideal.pi I ≤ Ideal.pi J ↔ I ≤
 J

--- 原说明 ---
Ideals in a finite direct product semiring `Πᵢ Rᵢ` are identified with tuples of
 ideals
in the individual semirings, in an order-preserving way.

(Note that this is not in general true for infinite direct products:
If infinitely many of the `Rᵢ` are nontrivial, then there exists an ideal of `Πᵢ
 Rᵢ` that
is not of the form `Πᵢ Iᵢ`, namely the ideal of finitely supported elements of `
Πᵢ Rᵢ`
(it is also not a principal ideal).)
-/
@[simps!] def piOrderIso [Finite ι] : Ideal (Π i, R i) ≃o Π i, Ideal (R i) := .symm
  { toFun := pi
    invFun I i := I.map (Pi.evalRingHom R i)
    left_inv _ := funext map_evalRingHom_pi
    right_inv I := by
      ext r
      simp_rw [mem_pi, mem_map_iff_of_surjective (Pi.evalRingHom R _) (Function.surjective_eval _)]
      refine ⟨(fun ⟨r', hr'⟩ ↦ ?_) ∘ Classical.skolem.mp, fun hr i ↦ ⟨r, hr, rfl⟩⟩
      have := Fintype.ofFinite ι
      classical rw [show r = ∑ i, Pi.single i 1 * r' i from funext fun i ↦ by
        rw [← (hr' _).2, Finset.sum_apply, Fintype.sum_eq_single i fun j ne ↦ by simp [ne]]; simp]
      exact sum_mem fun i _ ↦ I.mul_mem_left _ (hr' i).1
    map_rel_iff' := pi_le_pi_iff }
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite ι] [∀ i, IsPrincipalIdealRing (R i)] : IsPrincipalIdealRing (Π i, R i) where
  principal I := by
    rw [← piOrderIso.symm_apply_apply I]
    exact ⟨_, congr(pi $(funext fun i ↦
      (Submodule.IsPrincipal.span_singleton_generator _).symm)).trans pi_span⟩

end Pi

section Injective

/-
**Ideal.comap_bot_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_bot_le_of_injective (hf : Function.Injective f) : comap f ⊥ <= I
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem comap_bot_le_of_injective (hf : Function.Injective f) : comap f ⊥ ≤ I := by
  refine le_trans (fun x hx => ?_) bot_le
  rw [mem_comap, Submodule.mem_bot, ← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥
/-
**Ideal.comap_bot_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_bot_of_injective (hf : Function.Injective f) : Ideal.comap f ⊥ = ⊥
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.comap_bot_le_of_injective`：comap_bot_le_of_injective (hf : Functio
n.Injective f) : comap f ⊥ <= I
-/
theorem comap_bot_of_injective (hf : Function.Injective f) : Ideal.comap f ⊥ = ⊥ :=
  le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)

end Injective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm (map f I) = I`. -/
@[simp]
/-
**Ideal.map_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_of_equiv {I : Ideal R} (f : R ≃+* S) : (I.map (f : R ->+* S)).map (f.s
ymm : S ->+* R) = I
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.toRingHom_eq_coe`：∀ {R : Type u_4} {S : Type u_5} [inst : NonA
ssocSemiring R] [inst_1 : NonAssocSemiring S] (f : R ≃+* S),   f.toRingHom = ↑f
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `RingEquiv.symm_comp`：symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp 
(e : R ->+* S) = RingHom.id R
· 使用定理 `Ideal.map_id`：map_id : I.map (RingHom.id R) = I

--- 原说明 ---
If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm (map 
f I) = I`.
-/
theorem map_of_equiv {I : Ideal R} (f : R ≃+* S) :
    (I.map (f : R →+* S)).map (f.symm : S →+* R) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, map_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, map_id]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`,
  then `comap f (comap f.symm I) = I`. -/
@[simp]
/-
**Ideal.comap_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_of_equiv {I : Ideal R} (f : R ≃+* S) : (I.comap (f.symm : S ->+* R))
.comap (f : R ->+* S) = I
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.toRingHom_eq_coe`：∀ {R : Type u_4} {S : Type u_5} [inst : NonA
ssocSemiring R] [inst_1 : NonAssocSemiring S] (f : R ≃+* S),   f.toRingHom = ↑f
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `RingEquiv.symm_comp`：symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp 
(e : R ->+* S) = RingHom.id R
· 使用定理 `Ideal.comap_id`：comap_id : I.comap (RingHom.id R) = I

--- 原说明 ---
If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`,
  then `comap f (comap f.symm I) = I`.
-/
theorem comap_of_equiv {I : Ideal R} (f : R ≃+* S) :
    (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, comap_comap,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, comap_id]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f I = comap f.symm I`. -/
/-
**Ideal.map_comap_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S) : I.map (f : R ->+* S) = I.
comap f.symm
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.map_le_comap_of_inverse`：map_le_comap_of_inverse [RingHomClass G S
 R] (g : G) (I : Ideal R) (h : Function.LeftInverse g f) : I.map f <= I.comap g
· 使用定理 `Equiv.left_inv'`：left_inv' (e : α ≃ β) : Function.LeftInverse e.symm e
· 使用定理 `Ideal.comap_le_map_of_inverse`：comap_le_map_of_inverse (g : G) (I : Idea
l S) (h : Function.LeftInverse g f) : I.comap f <= I.map g
· 使用定理 `Equiv.right_inv'`：right_inv' (e : α ≃ β) : Function.RightInverse e.symm 
e

--- 原说明 ---
If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f I = comap 
f.symm I`.
-/
theorem map_comap_of_equiv {I : Ideal R} (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
  le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
    (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `comap f.symm I = map f I`. -/
@[simp]
/-
**Ideal.comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.symm = I.map f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm

--- 原说明 ---
If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `comap f.symm I =
 map f I`.
-/
theorem comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.symm = I.map f :=
  (map_comap_of_equiv f).symm

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm I = comap f I`. -/
@[simp]
/-
**Ideal.map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_symm {I : Ideal S} (f : R ≃+* S) : I.map f.symm = I.comap f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm

--- 原说明 ---
If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm I = c
omap f I`.
-/
theorem map_symm {I : Ideal S} (f : R ≃+* S) : I.map f.symm = I.comap f :=
  map_comap_of_equiv (RingEquiv.symm f)

@[simp]
/-
**Ideal.symm_apply_mem_of_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：symm_apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {y : S} : f.symm y
 in I ↔ y in I.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symm_apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {y : S} :
    f.symm y ∈ I ↔ y ∈ I.map f := by
  rw [← comap_symm, mem_comap]

@[simp]
/-
**Ideal.apply_mem_of_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {x : R} : f x in I.map 
f ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {x : R} :
    f x ∈ I.map f ↔ x ∈ I := by
  rw [← comap_symm, Ideal.mem_comap, f.symm_apply_apply]
/-
**Ideal.mem_map_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_map_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e :
 E) {I : Ideal R} (y : S) : y in map e I ↔ exists x in I, e x = y
参数：e : E；y : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
-/
theorem mem_map_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {I : Ideal R} (y : S) : y ∈ map e I ↔ ∃ x ∈ I, e x = y := by
  constructor
  · intro h
    simp_rw [show map e I = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : R ≃+* S)] at h
    exact ⟨(EquivLike.toEquiv e).symm y, h, (EquivLike.toEquiv e).apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem e hx
/-
**Ideal.map_primeCompl_comap_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_primeCompl_comap_of_surjective (hf : Function.Surjective f) (p : Ideal
 S) [p.IsPrime] : Submonoid.map f (p.comap f).primeCompl = p.primeCompl
参数：hf : Function.Surjective f；p : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
-/
lemma map_primeCompl_comap_of_surjective (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    Submonoid.map f (p.comap f).primeCompl = p.primeCompl := by
  rw [SetLike.ext_iff, hf.forall]
  grind [Submonoid.mem_map, mem_primeCompl_iff, mem_comap]
/-
**Ideal._root_.RingEquiv.map_primeCompl_comap_eq** 是 Mathlib 中的一个引理，位于命名空间 `Idea
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingEquiv.map_primeCompl_comap_eq (e : R ≃+* S) (p : Ideal S) [p.IsPrime] :
    (p.comap e).primeCompl.map e = p.primeCompl :=
  p.map_primeCompl_comap_of_surjective e e.surjective

section Bijective

variable (hf : Function.Bijective f) {I : Ideal R} {K : Ideal S}
include hf

set_option backward.isDefEq.respectTransparency false in
/-- Special case of the correspondence theorem for isomorphic rings -/
/-
**Ideal.relIsoOfBijective** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：relIsoOfBijective : Ideal S ≃o Ideal R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Special case of the correspondence theorem for isomorphic rings
-/
def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := map_comap_of_surjective _ hf.2
  right_inv J :=
    le_antisymm
      (fun _ h ↦ have ⟨y, hy, eq⟩ := (mem_map_iff_of_surjective _ hf.2).mp h; hf.1 eq ▸ hy)
      le_comap_map
  map_rel_iff' {_ _} := by
    refine ⟨fun h ↦ ?_, comap_mono⟩
    have := map_mono (f := f) h
    simpa only [Equiv.coe_fn_mk, map_comap_of_surjective f hf.2] using this
/-
**Ideal.comap_le_iff_le_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_le_iff_le_map : comap f K <= I ↔ K <= map f I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.le_map_of_comap_le_of_surjective`：le_map_of_comap_le_of_surjective
 : comap f K <= I -> K <= map f I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem comap_le_iff_le_map : comap f K ≤ I ↔ K ≤ map f I :=
  ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩
/-
**Ideal.map_eq_top_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_eq_top_of_bijective : I.map f = ⊤ ↔ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_le_iff_le_map`：comap_le_iff_le_map : comap f K <= I ↔ K <= m
ap f I
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_top_of_bijective : I.map f = ⊤ ↔ I = ⊤ := by
  rw [eq_top_iff, ← comap_le_iff_le_map f hf, comap_top, top_le_iff]
/-
**Ideal.comap_map_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_map_of_bijective : (I.map f).comap f = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.comap_le_iff_le_map`：comap_le_iff_le_map : comap f K <= I ↔ K <= m
ap f I
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
-/
theorem comap_map_of_bijective : (I.map f).comap f = I :=
  le_antisymm ((comap_le_iff_le_map f hf).mpr fun _ ↦ id) le_comap_map
/-
**Ideal.isMaximal_map_iff_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isMaximal_map_iff_of_bijective : IsMaximal (map f I) ↔ IsMaximal I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.isCoatom_iff`：isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o 
β) (a : α) : IsCoatom (f a) ↔ IsCoatom a
-/
theorem isMaximal_map_iff_of_bijective : IsMaximal (map f I) ↔ IsMaximal I := by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).symm.isCoatom_iff _
/-
**Ideal.isMaximal_comap_iff_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isMaximal_comap_iff_of_bijective : IsMaximal (comap f K) ↔ IsMaximal K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.isCoatom_iff`：isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o 
β) (a : α) : IsCoatom (f a) ↔ IsCoatom a
-/
theorem isMaximal_comap_iff_of_bijective : IsMaximal (comap f K) ↔ IsMaximal K := by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).isCoatom_iff _

alias ⟨_, IsMaximal.map_bijective⟩ := isMaximal_map_iff_of_bijective
alias ⟨_, IsMaximal.comap_bijective⟩ := isMaximal_comap_iff_of_bijective

/-- A ring isomorphism sends a maximal ideal to a maximal ideal. -/
/-
**Ideal.map_isMaximal_of_equiv** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：map_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S
] (e : E) {p : Ideal R} [hp : p.IsMaximal] : (map e p).IsMaximal
参数：e : E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.map_bijective`：∀ {R : Type u} {S : Type v} {F : Type u_1
} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   [
RingHomClass F R S]…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e

--- 原说明 ---
A ring isomorphism sends a maximal ideal to a maximal ideal.
-/
instance map_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {p : Ideal R} [hp : p.IsMaximal] : (map e p).IsMaximal :=
  hp.map_bijective e (EquivLike.bijective e)

/-- The pullback of a maximal ideal under a ring isomorphism is a maximal ideal. -/
/-
**Ideal.comap_isMaximal_of_equiv** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：comap_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R
 S] (e : E) {p : Ideal S} [hp : p.IsMaximal] : (comap e p).IsMaximal
参数：e : E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.comap_bijective`：∀ {R : Type u} {S : Type v} {F : Type u
_1} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)  
 [inst_3 : RingHomCla…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e

--- 原说明 ---
The pullback of a maximal ideal under a ring isomorphism is a maximal ideal.
-/
instance comap_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {p : Ideal S} [hp : p.IsMaximal] : (comap e p).IsMaximal :=
  hp.comap_bijective e (EquivLike.bijective e)
/-
**Ideal.isMaximal_iff_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isMaximal_iff_of_bijective : (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMax
imal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.map_bijective`：∀ {R : Type u} {S : Type v} {F : Type u_1
} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   [
RingHomClass F R S]…
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
theorem isMaximal_iff_of_bijective : (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal :=
  ⟨fun h ↦ map_bot (f := f) ▸ h.map_bijective f hf, fun h ↦ have e := RingEquiv.ofBijective f hf
    map_bot (f := e.symm) ▸ h.map_bijective _ e.symm.bijective⟩

end Bijective

end Semiring

section Ring

variable {F : Type*} [Ring R] [Ring S]
variable [FunLike F R S] [RingHomClass F R S] (f : F) {I : Ideal R}

section Surjective

/-
**Ideal.comap_map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_map_of_surjective (hf : Function.Surjective f) (I : Ideal R) : comap
 f (map f I) = I ⊔ comap f ⊥
参数：hf : Function.Surjective f；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.mem_image_of_mem_map_of_surjective`：mem_image_of_mem_map_of_surjec
tive {I : Ideal R} {y} (H : y in map f I) : y in f '' I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem comap_map_of_surjective (hf : Function.Surjective f) (I : Ideal R) :
    comap f (map f I) = I ⊔ comap f ⊥ :=
  le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
        ⟨s, hsi, r - s, (Submodule.mem_bot S).2 <| by rw [map_sub, hfsr, sub_self],
          add_sub_cancel s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))
/-
**Ideal.coheight_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coheight_comap_of_surjective (hf : Function.Surjective f) (I : Ideal S) : 
Order.coheight (I.comap f) = Order.coheight I
参数：hf : Function.Surjective f；I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coheight_eq_of_strictMono`：coheight_eq_of_strictMono (f : α -> β) 
(hf : StrictMono f) (h : forall a : α, forall b : β, f a < b -> exists (a' : α),
 a < a' ∧ f a' = b) (…
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.orderEmbeddingOfSurjective_apply`：∀ {R : Type u} {S : Type v} {F :
 Type u_1} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f
 : F)   [inst_3 : RingHomCla…
· 使用定理 `Ideal.comap_map_comap`：comap_map_comap : ((K.comap f).map f).comap f = K
.comap f
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem coheight_comap_of_surjective (hf : Function.Surjective f) (I : Ideal S) :
    Order.coheight (I.comap f) = Order.coheight I := by
  let φ := orderEmbeddingOfSurjective f hf
  refine (Order.coheight_eq_of_strictMono φ φ.strictMono (fun J K h ↦ ⟨K.map f, ?_, ?_⟩) I).symm
  · rw [← J.map_comap_of_surjective f hf]
    apply lt_of_le_not_ge (map_mono h.le)
    simpa [map_le_iff_le_comap, φ] using h.not_ge
  · exact (K.comap_map_of_surjective f hf).trans (sup_of_le_left ((comap_mono bot_le).trans h.le))

/-- Correspondence theorem -/
/-
**Ideal.relIsoOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：relIsoOfSurjective (hf : Function.Surjective f) : Ideal S ≃o { p : Ideal R
 // comap f ⊥ <= p } where toFun J
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Correspondence theorem
-/
def relIsoOfSurjective (hf : Function.Surjective f) :
    Ideal S ≃o { p : Ideal R // comap f ⊥ ≤ p } where
  toFun J := ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
    Subtype.ext <|
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩

-- May not hold if `R` is a semiring: consider `ℕ →+* ZMod 2`.
/-
**Ideal.comap_isMaximal_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_isMaximal_of_surjective (hf : Function.Surjective f) {K : Ideal S} [
H : IsMaximal K] : IsMaximal (comap f K)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ideal.le_map_of_comap_le_of_surjective`：le_map_of_comap_le_of_surjective
 : comap f K <= I -> K <= map f I
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem comap_isMaximal_of_surjective (hf : Function.Surjective f) {K : Ideal S} [H : IsMaximal K] :
    IsMaximal (comap f K) := by
  refine ⟨⟨comap_ne_top _ H.1.1, fun J hJ => ?_⟩⟩
  suffices map f J = ⊤ by
    have := congr_arg (comap f) this
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this
    rw [eq_top_iff]
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono bot_le) (le_of_lt hJ)))
  refine
    H.1.2 (map f J)
      (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ)) fun h =>
        ne_of_lt hJ (_root_.trans (congr_arg (comap f) h) ?_))
  rw [comap_map_of_surjective _ hf, sup_eq_left]
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)

end Surjective


end Ring

section CommRing

variable {F : Type*} [CommSemiring R] [CommSemiring S]
variable [FunLike F R S] [rc : RingHomClass F R S]
variable (f : F)
variable (I J : Ideal R) (K L : Ideal S)

/-
**Ideal.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R : Type u_2} [inst
_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S] (f : F) (I J : 
Ideal R), Ideal.map f (I * J) = Ideal.map f I * Ideal.map f J
参数：f : F；I J : Ideal R；I * J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mul_le`：mul_le : I * J <= K ↔ forall r in I, forall s in J, r * s 
in K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_mul_span`：span_mul_span (S T : Set R) [(span S).IsTwoSided] :
 span S * span T = span (S * T)
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
-/
protected theorem map_mul {R} [Semiring R] [FunLike F R S] [RingHomClass F R S]
    (f : F) (I J : Ideal R) :
    map f (I * J) = map f I * map f J :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) ∈ map f I * map f J by
          rw [map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <| by
      rintro _ ⟨_, ⟨r, hri, rfl⟩, _, ⟨s, hsj, rfl⟩, rfl⟩
      simp_rw [← map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))

/-- The pushforward `Ideal.map` as a (semi)ring homomorphism. -/
@[simps]
/-
**Ideal.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：mapHom : Ideal R ->+* Ideal S where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward `Ideal.map` as a (semi)ring homomorphism.
-/
def mapHom : Ideal R →+* Ideal S where
  toFun := map f
  map_mul' := Ideal.map_mul f
  map_one' := by simp only [one_eq_top, Ideal.map_top f]
  map_add' I J := Ideal.map_sup f I J
  map_zero' := Ideal.map_bot
/-
**Ideal.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSemiring R] [inst_1
 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClass F R S] (f : F) 
(I : Ideal R) (n : ℕ), Ideal.map f (I ^ n) = Ideal.map f I ^ n
参数：f : F；I : Ideal R；n : ℕ；I ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
protected theorem map_pow (n : ℕ) : map f (I ^ n) = map f I ^ n :=
  map_pow (mapHom f) I n

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.comap_radical** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_radical : comap f (radical K) = radical (comap f K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mk.congr_simp`：∀ {R : Type u} {M : Type v} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (toAddSubmonoid toAdd
Submonoid_1 :…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_radical : comap f (radical K) = radical (comap f K) := by
  ext
  simp [radical]

variable {K}
/-
**Ideal.IsRadical.comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsRadical`。
形式化陈述：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSemiring R] [inst_1
 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClass F R S] (f : F) 
{K : Ideal S}, K.IsRadical → (Ideal.comap f K).IsRadical
参数：f : F；Ideal.comap f K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsRadical.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsRadical → I.radical = I
· 使用定理 `Ideal.comap_radical`：comap_radical : comap f (radical K) = radical (coma
p f K)
· 使用定理 `Ideal.radical_isRadical`：radical_isRadical : (radical I).IsRadical
-/
theorem IsRadical.comap (hK : K.IsRadical) : (comap f K).IsRadical := by
  rw [← hK.radical, comap_radical]
  apply radical_isRadical

variable {I J L}
/-
**Ideal.map_radical_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_radical_le : map f (radical I) <= radical (map f I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
  map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩
/-
**Ideal.le_comap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_comap_mul : comap f K * comap f L <= comap f (K * L)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mul_mono`：mul_mono (hik : I <= K) (hjl : J <= L) : I * J <= K * L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
-/
theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
  map_le_iff_le_comap.1 <|
    (Ideal.map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)
/-
**Ideal.le_comap_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_comap_pow (n : Nat) : K.comap f ^ n <= (K ^ n).comap f
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.mul_mono_left`：mul_mono_left (h : I <= J) : I * K <= J * K
· 使用定理 `Ideal.le_comap_mul`：le_comap_mul : comap f K * comap f L <= comap f (K *
 L)
-/
theorem le_comap_pow (n : ℕ) : K.comap f ^ n ≤ (K ^ n).comap f := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top, Ideal.one_eq_top]
    exact rfl.le
  | succ n n_ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left n_ih).trans (Ideal.le_comap_mul f)
/-
**Ideal.disjoint_map_primeCompl_iff_comap_le** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：disjoint_map_primeCompl_iff_comap_le {S : Type*} [Semiring S] {f : R ->+* 
S} {p : Ideal R} {I : Ideal S} [p.IsPrime] : Disjoint (I : Set S) (p.primeCompl.
map f) ↔ I.comap f <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.disjoint_image_right`：disjoint_image_right {f : α -> β} {s : Set α} 
{t : Set β} : Disjoint t (f '' s) ↔ Disjoint (f ⁻¹' t) s
· 使用定理 `disjoint_compl_right_iff`：disjoint_compl_right_iff : Disjoint x yᶜ ↔ x <
= y
-/
lemma disjoint_map_primeCompl_iff_comap_le {S : Type*} [Semiring S] {f : R →+* S}
    {p : Ideal R} {I : Ideal S} [p.IsPrime] :
    Disjoint (I : Set S) (p.primeCompl.map f) ↔ I.comap f ≤ p :=
  (@Set.disjoint_image_right _ _ f p.primeCompl I).trans disjoint_compl_right_iff

/-- For a prime ideal `p` of `R`, `p` extended to `S` and
restricted back to `R` is `p` if and only if `p` is the restriction of a prime in `S`. -/
/-
**Ideal.comap_map_eq_self_iff_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：comap_map_eq_self_iff_of_isPrime {S : Type*} [CommSemiring S] {f : R ->+* 
S} (p : Ideal R) [p.IsPrime] : (p.map f).comap f = p ↔ (exists (q : Ideal S), q.
IsPrime ∧ q.comap f = p)
参数：p : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.exists_le_prime_disjoint`：exists_le_prime_disjoint (S : Submonoid 
α) (disjoint : Disjoint (I : Set α) S) : exists p : Ideal α, p.IsPrime ∧ I <= p 
∧ Disjoint (p : Set …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ideal.disjoint_map_primeCompl_iff_comap_le`：disjoint_map_primeCompl_iff_
comap_le {S : Type*} [Semiring S] {f : R ->+* S} {p : Ideal R} {I : Ideal S} [p.
IsPrime] : Disjoint (I : Set S) …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_map_comap`：comap_map_comap : ((K.comap f).map f).comap f = K
.comap f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a prime ideal `p` of `R`, `p` extended to `S` and
restricted back to `R` is `p` if and only if `p` is the restriction of a prime i
n `S`.
-/
lemma comap_map_eq_self_iff_of_isPrime {S : Type*} [CommSemiring S] {f : R →+* S}
    (p : Ideal R) [p.IsPrime] :
    (p.map f).comap f = p ↔ (∃ (q : Ideal S), q.IsPrime ∧ q.comap f = p) := by
  refine ⟨fun hp ↦ ?_, ?_⟩
  · obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_le_prime_disjoint _ _
      (disjoint_map_primeCompl_iff_comap_le.mpr hp.le)
    exact ⟨q, hq₁, le_antisymm (disjoint_map_primeCompl_iff_comap_le.mp hq₃)
      (map_le_iff_le_comap.mp hq₂)⟩
  · rintro ⟨q, hq, rfl⟩
    simp

/--
For a maximal ideal `p` of `R`, `p` extended to `S` and restricted back to `R` is `p` if
its image in `S` is not equal to `⊤`.
-/
/-
**Ideal.comap_map_eq_self_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_map_eq_self_of_isMaximal (f : R ->+* S) {p : Ideal R} [hP' : p.IsMax
imal] (hP : Ideal.map f p != ⊤) : (map f p).comap f = p
参数：f : R ->+* S；hP : Ideal.map f p != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsCoatom.le_iff_eq`：IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b != ⊤) :
 a <= b ↔ b = a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f

--- 原说明 ---
For a maximal ideal `p` of `R`, `p` extended to `S` and restricted back to `R` i
s `p` if
its image in `S` is not equal to `⊤`.
-/
theorem comap_map_eq_self_of_isMaximal (f : R →+* S) {p : Ideal R} [hP' : p.IsMaximal]
    (hP : Ideal.map f p ≠ ⊤) : (map f p).comap f = p :=
  (IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp <| le_comap_map

end CommRing

end MapAndComap

end Ideal

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type w}

section Semiring

variable {F : Type*} {G : Type*} [Semiring R] [Semiring S] [Semiring T]
variable [FunLike F R S] [rcf : RingHomClass F R S] [FunLike G T S] [rcg : RingHomClass G T S]
variable (f : F) (g : G)

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
/-
**RingHom.ker** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：ker : Ideal R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kernel of a ring homomorphism as an ideal of the domain.
-/
def ker : Ideal R :=
  Ideal.comap f ⊥
/-
**RingHom.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : (ker f).IsTwoSided := inferInstanceAs (Ideal.comap f ⊥).IsTwoSided

variable {f} in
/-- An element is in the kernel if and only if it maps to zero. -/
/-
**RingHom.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semiring R] [inst_1 : S
emiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R S] {f : F} {r : R}
, r ∈ RingHom.ker f ↔ f r = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element is in the kernel if and only if it maps to zero.
-/
@[simp] theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 := by rw [ker, Ideal.mem_comap, Submodule.mem_bot]
/-
**RingHom.ker_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_eq : (ker f : Set R) = Set.preimage f {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element is in the kernel if and only if it maps to zero.
-/
theorem ker_eq : (ker f : Set R) = Set.preimage f {0} :=
  rfl
/-
**RingHom.ker_eq_comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥ :=
  rfl
/-
**RingHom.comap_ker** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).comap g = ker (f.comp g)
参数：f : S ->+* R；g : T ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
-/
theorem comap_ker (f : S →+* R) (g : T →+* S) : (ker f).comap g = ker (f.comp g) := by
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, RingHom.ker_eq_comap_bot]

/-- If the target is not the zero ring, then one is not in the kernel. -/
/-
**RingHom.one_notMem_ker** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：one_notMem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
If the target is not the zero ring, then one is not in the kernel.
-/
theorem one_notMem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f := by
  rw [mem_ker, map_one]
  exact one_ne_zero
/-
**RingHom.ker_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_ne_top [Nontrivial S] (f : F) : ker f != ⊤
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `RingHom.one_notMem_ker`：one_notMem_ker [Nontrivial S] (f : F) : (1 : R) 
∉ ker f
-/
theorem ker_ne_top [Nontrivial S] (f : F) : ker f ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr <| one_notMem_ker f
/-
**RingHom.ker_eq_top_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：ker_eq_top_of_subsingleton [Subsingleton S] (f : F) : ker f = ⊤
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma ker_eq_top_of_subsingleton [Subsingleton S] (f : F) : ker f = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ Subsingleton.elim _ _
/-
**RingHom._root_.Pi.ker_ringHom** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Pi.ker_ringHom {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    (φ : ∀ i, S →+* R i) : ker (RingHom.pi φ) = ⨅ i, ker (φ i) := by
  ext x
  simp [mem_ker, funext_iff]

@[simp]
/-
**RingHom.ker_rangeSRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_rangeSRestrict (f : R ->+* S) : ker f.rangeSRestrict = ker f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ker_rangeSRestrict (f : R →+* S) : ker f.rangeSRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

@[simp]
/-
**RingHom.ker_coe_equiv** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_coe_equiv (f : R ≃+* S) : ker (f : R ->+* S) = ⊥
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ := by
  ext; simp
/-
**RingHom.ker_coe_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_coe_toRingHom : ker (f : R ->+* S) = ker f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_coe_toRingHom : ker (f : R →+* S) = ker f := rfl

@[simp]
/-
**RingHom.ker_equiv** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F')
 : ker f = ⊥
参数：f : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F') :
    ker f = ⊥ := by
  ext; simp
/-
**RingHom.ker_equiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：ker_equiv_comp (f : R ->+* S) (e : S ≃+* T) : ker (e.toRingHom.comp f) = R
ingHom.ker f
参数：f : R ->+* S；e : S ≃+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.toRingHom_eq_coe`：∀ {R : Type u_4} {S : Type u_5} [inst : NonA
ssocSemiring R] [inst_1 : NonAssocSemiring S] (f : R ≃+* S),   f.toRingHom = ↑f
· 使用定理 `RingHom.ker_coe_equiv`：ker_coe_equiv (f : R ≃+* S) : ker (f : R ->+* S) 
= ⊥
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
-/
lemma ker_equiv_comp (f : R →+* S) (e : S ≃+* T) :
    ker (e.toRingHom.comp f) = RingHom.ker f := by
  rw [← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, RingHom.ker_coe_equiv, RingHom.ker]

end Semiring

section Ring

variable {F : Type*} [Ring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

/-
**RingHom.injective_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `RingHom.ker_eq`：ker_eq : (ker f : Set R) = Set.preimage f {0}
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `injective_iff_map_eq_zero'`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_
9} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [Add
MonoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥ := by
  rw [SetLike.ext'_iff, ker_eq, Set.ext_iff]
  exact injective_iff_map_eq_zero' f
/-
**RingHom.ker_eq_bot_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ forall x, f x = 0 -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 := by
  rw [← injective_iff_map_eq_zero f, injective_iff_ker_eq_bot]
/-
**RingHom.ker_comp_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：ker_comp_of_injective [Semiring T] (g : T ->+* R) {f : R ->+* S} (hf : Fun
ction.Injective f) : ker (f.comp g) = RingHom.ker g
参数：g : T ->+* R；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
-/
lemma ker_comp_of_injective [Semiring T] (g : T →+* R) {f : R →+* S} (hf : Function.Injective f) :
    ker (f.comp g) = RingHom.ker g := by
  rw [← RingHom.comap_ker, (injective_iff_ker_eq_bot f).mp hf, RingHom.ker]

/-- Synonym for `RingHom.ker_coe_equiv`, but given an algebra equivalence. -/
/-
**RingHom._root_.AlgHom.ker_coe_equiv** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Synonym for `RingHom.ker_coe_equiv`, but given an algebra equivalence.
-/
@[simp] theorem _root_.AlgHom.ker_coe_equiv {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    RingHom.ker (e : A →+* B) = ⊥ :=
  RingHom.ker_coe_equiv (e.toRingEquiv)

end Ring

section RingRing

variable {F : Type*} [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

/-
**RingHom.sub_mem_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：sub_mem_ker_iff {x y} : x - y in ker f ↔ f x = f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]

@[simp]
/-
**RingHom.ker_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_rangeRestrict (f : R ->+* S) : ker f.rangeRestrict = ker f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ker_rangeRestrict (f : R →+* S) : ker f.rangeRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end RingRing

/-- The kernel of a homomorphism to a domain is a prime ideal. -/
/-
**RingHom.ker_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_isPrime {F : Type*} [Semiring R] [Semiring S] [IsDomain S] [FunLike F 
R S] [RingHomClass F R S] (f : F) : (ker f).IsPrime
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a homomorphism to a domain is a prime ideal.
-/
theorem ker_isPrime {F : Type*} [Semiring R] [Semiring S] [IsDomain S]
    [FunLike F R S] [RingHomClass F R S] (f : F) :
    (ker f).IsPrime :=
  inferInstanceAs (Ideal.comap f ⊥).IsPrime

/-- The kernel of a homomorphism to a division ring is a maximal ideal. -/
/-
**RingHom.ker_isMaximal_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ker_isMaximal_of_surjective {R K F : Type*} [Ring R] [DivisionRing K] [Fun
Like F R K] [RingHomClass F R K] (f : F) (hf : Function.Surjective f) : (ker f).
IsMaximal
参数：f : F；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.bot_isMaximal`：bot_isMaximal : IsMaximal (⊥ : Ideal K)
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)

--- 原说明 ---
The kernel of a homomorphism to a division ring is a maximal ideal.
-/
theorem ker_isMaximal_of_surjective {R K F : Type*} [Ring R] [DivisionRing K]
    [FunLike F R K] [RingHomClass F R K] (f : F)
    (hf : Function.Surjective f) : (ker f).IsMaximal :=
  have := Ideal.bot_isMaximal (K := K)
  Ideal.comap_isMaximal_of_surjective _ hf

end RingHom

section annihilator

section Semiring

variable {R M M' : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (R M) in
/-- `Module.annihilator R M` is the ideal of all elements `r : R` such that `r • M = 0`. -/
/-
**Module.annihilator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.annihilator : Ideal R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Module.annihilator R M` is the ideal of all elements `r : R` such that `r • M =
 0`.
-/
def Module.annihilator : Ideal R := RingHom.ker (Module.toAddMonoidEnd R M)
/-
**Module.mem_annihilator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.mem_annihilator {r} : r in Module.annihilator R M ↔ forall m : M, r
 • m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
-/
theorem Module.mem_annihilator {r} : r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0 :=
  ⟨fun h ↦ (congr($h ·)), (AddMonoidHom.ext ·)⟩
/-
**Module.mem_annihilator_iff_lsmul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.mem_annihilator_iff_lsmul_eq_zero {R : Type*} [CommSemiring R] [Mod
ule R M] {r : R} : r in Module.annihilator R M ↔ LinearMap.lsmul R M r = 0
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
lemma Module.mem_annihilator_iff_lsmul_eq_zero {R : Type*} [CommSemiring R]
    [Module R M] {r : R} : r ∈ Module.annihilator R M ↔ LinearMap.lsmul R M r = 0 := by
  simp [Module.mem_annihilator, LinearMap.ext_iff]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : (Module.annihilator R M).IsTwoSided :=
  inferInstanceAs (RingHom.ker _).IsTwoSided
/-
**LinearMap.annihilator_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.annihilator_le_of_injective (f : M ->ₗ[R] M') (hf : Function.Inj
ective f) : Module.annihilator R M' <= Module.annihilator R M
参数：f : M ->ₗ[R] M'；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem LinearMap.annihilator_le_of_injective (f : M →ₗ[R] M') (hf : Function.Injective f) :
    Module.annihilator R M' ≤ Module.annihilator R M := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢; exact fun m ↦ hf (by rw [map_smul, h, f.map_zero])
/-
**LinearMap.annihilator_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.annihilator_le_of_surjective (f : M ->ₗ[R] M') (hf : Function.Su
rjective f) : Module.annihilator R M <= Module.annihilator R M'
参数：f : M ->ₗ[R] M'；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem LinearMap.annihilator_le_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : Module.annihilator R M ≤ Module.annihilator R M' := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul, h, f.map_zero]
/-
**LinearEquiv.annihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') : Module.annihilator R M = Mod
ule.annihilator R M'
参数：e : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LinearMap.annihilator_le_of_surjective`：LinearMap.annihilator_le_of_surj
ective (f : M ->ₗ[R] M') (hf : Function.Surjective f) : Module.annihilator R M <
= Module.annihilator R M'
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `LinearMap.annihilator_le_of_injective`：LinearMap.annihilator_le_of_injec
tive (f : M ->ₗ[R] M') (hf : Function.Injective f) : Module.annihilator R M' <= 
Module.annihilator R M
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') :
    Module.annihilator R M = Module.annihilator R M' :=
  (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)
/-
**Module.comap_annihilator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.comap_annihilator {R₀} [CommSemiring R₀] [Module R₀ M] [Algebra R₀ 
R] [IsScalarTower R₀ R M] : (Module.annihilator R M).comap (algebraMap R₀ R) = M
odule.annihilator R₀ M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Module.comap_annihilator {R₀} [CommSemiring R₀] [Module R₀ M]
    [Algebra R₀ R] [IsScalarTower R₀ R M] :
    (Module.annihilator R M).comap (algebraMap R₀ R) = Module.annihilator R₀ M := by
  ext x
  simp [mem_annihilator]
/-
**Module.annihilator_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.annihilator_eq_bot {R M} [Ring R] [AddCommGroup M] [Module R M] : M
odule.annihilator R M = ⊥ ↔ FaithfulSMul R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma Module.annihilator_eq_bot {R M} [Ring R] [AddCommGroup M] [Module R M] :
    Module.annihilator R M = ⊥ ↔ FaithfulSMul R M := by
  rw [← le_bot_iff]
  refine ⟨fun H ↦ ⟨fun {r s} H' ↦ ?_⟩, fun ⟨H⟩ {a} ha ↦ ?_⟩
  · rw [← sub_eq_zero]
    exact H (Module.mem_annihilator (r := r - s).mpr
      (by simp only [sub_smul, H', sub_self, implies_true]))
  · exact @H a 0 (by simp [Module.mem_annihilator.mp ha])
/-
**Module.annihilator_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.annihilator_eq_top_iff : annihilator R M = ⊤ ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Module.annihilator_eq_top_iff : annihilator R M = ⊤ ↔ Subsingleton M :=
  ⟨fun h ↦ ⟨fun m m' ↦ by
      rw [← one_smul R m, ← one_smul R m']
      simp_rw [mem_annihilator.mp (h ▸ Submodule.mem_top)]⟩,
    fun _ ↦ top_le_iff.mp fun _ _ ↦ mem_annihilator.mpr fun _ ↦ Subsingleton.elim _ _⟩
/-
**Module.annihilator_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.annihilator_prod : annihilator R (M × M') = annihilator R M ⊓ annih
ilator R M'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Module.annihilator_prod : annihilator R (M × M') = annihilator R M ⊓ annihilator R M' := by
  ext
  simp_rw [Ideal.mem_inf, mem_annihilator,
    Prod.forall, Prod.smul_mk, Prod.mk_eq_zero, forall_and_left, ← forall_and_right]
/-
**Module.annihilator_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.annihilator_finsupp {ι : Type*} [Nonempty ι] : annihilator R (ι ->₀
 M) = annihilator R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem Module.annihilator_finsupp {ι : Type*} [Nonempty ι] :
    annihilator R (ι →₀ M) = annihilator R M := by
  ext r; simp_rw [mem_annihilator]
  constructor <;> intro h
  · refine Nonempty.elim ‹_› fun i : ι ↦ ?_
    simpa using fun m ↦ congr($(h (Finsupp.single i m)) i)
  · intro m; ext i; exact h _

section

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-
**Module.annihilator_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.annihilator_dfinsupp : annihilator R (Π₀ i, M i) = ⨅ i, annihilator
 R (M i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem Module.annihilator_dfinsupp : annihilator R (Π₀ i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using DFunLike.congr_fun (h (DFinsupp.single i m)) i
  · intro m; ext i; exact h i _
/-
**Module.annihilator_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.annihilator_pi : annihilator R (Π i, M i) = ⨅ i, annihilator R (M i
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Module.annihilator_pi : annihilator R (Π i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using congr_fun (h (Pi.single i m)) i
  · intro m; ext i; exact h i _

end

namespace Submodule

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
/-
**Submodule.annihilator** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：annihilator (N : Submodule R M) : Ideal R
参数：N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`.
-/
abbrev annihilator (N : Submodule R M) : Ideal R :=
  Module.annihilator R N
/-
**Submodule.annihilator_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_top : (⊤ : Submodule R M).annihilator = Module.annihilator R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.annihilator_eq`：LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') 
: Module.annihilator R M = Module.annihilator R M'
-/
theorem annihilator_top : (⊤ : Submodule R M).annihilator = Module.annihilator R M :=
  topEquiv.annihilator_eq

variable {I J : Ideal R} {N P : Submodule R M}
/-
**Submodule.mem_annihilator** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_annihilator {r} : r in N.annihilator ↔ forall n in N, r • n = (0 : M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0 : M) := by
  simp_rw [annihilator, Module.mem_annihilator, Subtype.forall, Subtype.ext_iff]; rfl
/-
**Submodule.annihilator_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_bot : (⊥ : Submodule R M).annihilator = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem annihilator_bot : (⊥ : Submodule R M).annihilator = ⊤ :=
  top_le_iff.mp fun _ _ ↦ mem_annihilator.mpr fun _ ↦ by rintro rfl; rw [smul_zero]
/-
**Submodule.annihilator_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.annihilator.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule
 R M), N.annihil…
· 使用定理 `Module.annihilator_eq_top_iff`：Module.annihilator_eq_top_iff : annihilat
or R M = ⊤ ↔ Subsingleton M
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ := by
  rw [annihilator, Module.annihilator_eq_top_iff, Submodule.subsingleton_iff_eq_bot]
/-
**Submodule.annihilator_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_mono (h : N <= P) : P.annihilator <= N.annihilator
参数：h : N <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator := fun _ hrp =>
  mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n <| h hn
/-
**Submodule.annihilator_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_iSup (ι : Sort w) (f : ι -> Submodule R M) : annihilator (⨆ i,
 f i) = ⨅ i, annihilator (f i)
参数：ι : Sort w；f : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Submodule.annihilator_mono`：annihilator_mono (h : N <= P) : P.annihilato
r <= N.annihilator
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `Submodule.iSup_induction`：iSup_induction {ι : Sort*} (p : ι -> Submodule
 R M) {motive : M -> Prop} {x : M} (hx : x in ⨆ i, p i) (mem : forall (i), foral
l x in p i, mo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem annihilator_iSup (ι : Sort w) (f : ι → Submodule R M) :
    annihilator (⨆ i, f i) = ⨅ i, annihilator (f i) :=
  le_antisymm (le_iInf fun _ => annihilator_mono <| le_iSup _ _) fun r H =>
    mem_annihilator.2 fun n hn ↦ iSup_induction f (motive := (r • · = 0)) hn
      (fun i ↦ mem_annihilator.1 <| (mem_iInf _).mp H i) (smul_zero _)
      fun m₁ m₂ h₁ h₂ ↦ by simp_rw [smul_add, h₁, h₂, add_zero]
/-
**Submodule.annihilator_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_sup (N P : Submodule R M) : (N ⊔ P).annihilator = N.annihilato
r ⊓ P.annihilator
参数：N P : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_pair`：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Submodule.annihilator_iSup`：annihilator_iSup (ι : Sort w) (f : ι -> Subm
odule R M) : annihilator (⨆ i, f i) = ⨅ i, annihilator (f i)
· 使用定理 `iInf_pair`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α} {a b : β}, ⨅ x ∈ {a, b}, f x = f a ⊓ f b
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
-/
theorem annihilator_sup (N P : Submodule R M) :
    (N ⊔ P).annihilator = N.annihilator ⊓ P.annihilator := by
  rw [← sSup_pair, sSup_eq_iSup, iSup_subtype', annihilator_iSup, ← iInf_pair, iInf_subtype']
/-
**Submodule.le_annihilator_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_annihilator_iff {N : Submodule R M} {I : Ideal R} : I <= annihilator N 
↔ I • N = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_annihilator_iff {N : Submodule R M} {I : Ideal R} : I ≤ annihilator N ↔ I • N = ⊥ := by
  simp_rw [← le_bot_iff, smul_le, SetLike.le_def, mem_annihilator]; rfl

@[simp]
/-
**Submodule.annihilator_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_smul (N : Submodule R M) : annihilator N • N = ⊥
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
-/
theorem annihilator_smul (N : Submodule R M) : annihilator N • N = ⊥ :=
  eq_bot_iff.2 (smul_le.2 fun _ => mem_annihilator.1)

@[simp]
/-
**Submodule.annihilator_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_mul (I : Ideal R) : annihilator I * I = ⊥
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.annihilator_smul`：annihilator_smul (N : Submodule R M) : annih
ilator N • N = ⊥
-/
theorem annihilator_mul (I : Ideal R) : annihilator I * I = ⊥ :=
  annihilator_smul I

end Submodule

end Semiring

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Submodule R M}

/-
**Submodule.mem_annihilator'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_annihilator' {r} : r in N.annihilator ↔ N <= comap (r • (LinearMap.id 
: M ->ₗ[R] M)) ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) ⊥ :=
  mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 <| H n hn, fun H _ hn => (mem_bot R).1 <| H hn⟩
/-
**Submodule.mem_annihilator_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_annihilator_span (s : Set M) (r : R) : r in (Submodule.span R s).annih
ilator ↔ forall n : s, r • (n : M) = 0
参数：s : Set M；r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem mem_annihilator_span (s : Set M) (r : R) :
    r ∈ (Submodule.span R s).annihilator ↔ ∀ n : s, r • (n : M) = 0 := by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
  · intro h n hn
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
    · intro x hx
      exact h ⟨x, hx⟩
    · exact smul_zero _
    · intro x y _ _ hx hy
      rw [smul_add, hx, hy, zero_add]
    · intro a x _ hx
      rw [smul_comm, hx, smul_zero]
/-
**Submodule.mem_annihilator_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：mem_annihilator_span_singleton (g : M) (r : R) : r in (Submodule.span R ({
g} : Set M)).annihilator ↔ r • g = 0
参数：g : M；r : R。
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
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_annihilator_span_singleton (g : M) (r : R) :
    r ∈ (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0 := by simp [mem_annihilator_span]

open LinearMap in
/-
**Submodule.annihilator_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_span (s : Set M) : (Submodule.span R s).annihilator = ⨅ g : s,
 ker (toSpanSingleton R M g.1)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem annihilator_span (s : Set M) :
    (Submodule.span R s).annihilator = ⨅ g : s, ker (toSpanSingleton R M g.1) := by
  ext; simp [mem_annihilator_span]

open LinearMap in
/-
**Submodule.annihilator_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_span_singleton (g : M) : (Submodule.span R {g}).annihilator = 
ker (toSpanSingleton R M g)
参数：g : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.annihilator_span`：annihilator_span (s : Set M) : (Submodule.sp
an R s).annihilator = ⨅ g : s, ker (toSpanSingleton R M g.1)
· 使用定理 `ciInf_unique`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyCompl
etePartialOrderInf α] [inst_1 : Unique ι] {s : ι → α},   ⨅ i, s i = s default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem annihilator_span_singleton (g : M) :
    (Submodule.span R {g}).annihilator = ker (toSpanSingleton R M g) := by
  simp [annihilator_span]

@[simp]
/-
**Submodule.mul_annihilator** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_annihilator (I : Ideal R) : I * annihilator I = ⊥
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submodule.annihilator_mul`：annihilator_mul (I : Ideal R) : annihilator I
 * I = ⊥
-/
theorem mul_annihilator (I : Ideal R) : I * annihilator I = ⊥ := by rw [mul_comm, annihilator_mul]
/-
**Submodule.restrictScalars_map_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_map_smul_eq {S M : Type*} [CommSemiring S] [Algebra S R] [
AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M] (I : Ideal S) (
N : Submodule R M) : ((I.map (algebraMap S R)) • N).restrictScalars S = I • N.re
strictScalars S
参数：I : Ideal S；N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.restrictScalars_image_smul_eq`：restrictScalars_image_smul_eq {
S M : Type*} [CommSemiring S] [Algebra S R] [AddCommMonoid M] [Module R M] [Modu
le S M] [IsScalarTower S R M]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用引理 `Submodule.span_smul_eq`：span_smul_eq (s : Set R) (N : Submodule R M) : I
deal.span s • N = s • N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.coe_set_smul`：coe_set_smul : (I : Set A) • N = I • N
-/
theorem restrictScalars_map_smul_eq {S M : Type*}
    [CommSemiring S] [Algebra S R]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M]
    (I : Ideal S) (N : Submodule R M) :
    ((I.map (algebraMap S R)) • N).restrictScalars S = I • N.restrictScalars S := by
  have := N.restrictScalars_image_smul_eq (I : Set S)
  rw [coe_set_smul] at this
  rw [Ideal.map, span_smul_eq, ← this]

end Submodule

end annihilator

namespace Ideal

variable {R : Type*} {S : Type*} {F : Type*}

section Semiring

variable [Semiring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S]

/-
**Ideal.map_eq_bot_iff_le_ker** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I <= RingHom.k
er f
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I ≤ RingHom.ker f := by
  rw [RingHom.ker, eq_bot_iff, map_le_iff_le_comap]
/-
**Ideal.ker_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <= comap f K
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
-/
theorem ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f ≤ comap f K := fun _ hx =>
  mem_comap.2 (RingHom.mem_ker.1 hx ▸ K.zero_mem)

/-- A ring isomorphism sends a prime ideal to a prime ideal. -/
/-
**Ideal.map_isPrime_of_equiv** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：map_isPrime_of_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R 
S] (f : F') {I : Ideal R} [IsPrime I] : IsPrime (map f I)
参数：f : F'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…

--- 原说明 ---
A ring isomorphism sends a prime ideal to a prime ideal.
-/
instance map_isPrime_of_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S]
    (f : F') {I : Ideal R} [IsPrime I] : IsPrime (map f I) := by
  have h : I.map f = I.map ((RingEquivClass.toRingEquiv f : R ≃+* S) : R →+* S) := rfl
  rw [h, map_comap_of_equiv (RingEquivClass.toRingEquiv f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquivClass.toRingEquiv f : R ≃+* S).symm
/-
**Ideal.map_eq_bot_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_eq_bot_iff_of_injective {I : Ideal R} {f : F} (hf : Function.Injective
 f) : I.map f = ⊥ ↔ I = ⊥
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_bot_iff_of_injective {I : Ideal R} {f : F} (hf : Function.Injective f) :
    I.map f = ⊥ ↔ I = ⊥ := by
  simp [map, ← map_zero f, -map_zero, hf.eq_iff, I.eq_bot_iff]

end Semiring

open scoped Pointwise in
/-
**Ideal.map_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_pointwise_smul {R S : Type*} [CommSemiring R] [CommSemiring S] (r : R)
 (I : Ideal R) (f : R ->+* S) : Ideal.map f (r • I) = f r • I.map f
参数：r : R；I : Ideal R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ideal_span_singleton_smul`：ideal_span_singleton_smul (r : R) (
N : Submodule R M) : (Ideal.span {r} : Ideal R) • N = r • N
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
lemma map_pointwise_smul {R S : Type*} [CommSemiring R] [CommSemiring S]
    (r : R) (I : Ideal R) (f : R →+* S) :
    Ideal.map f (r • I) = f r • I.map f := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.map_mul, Ideal.map_span,
    Set.image_singleton, ← smul_eq_mul, Submodule.ideal_span_singleton_smul]

section Ring

variable [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S]

/-
**Ideal.comap_map_of_surjective'** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：comap_map_of_surjective' (f : F) (hf : Function.Surjective f) (I : Ideal R
) : (I.map f).comap f = I ⊔ RingHom.ker f
参数：f : F；hf : Function.Surjective f；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
-/
lemma comap_map_of_surjective' (f : F) (hf : Function.Surjective f) (I : Ideal R) :
    (I.map f).comap f = I ⊔ RingHom.ker f :=
  comap_map_of_surjective f hf I
/-
**Ideal.map_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) : (foral
l J in A, RingHom.ker f <= J) -> map f (sInf A) = sInf (map f '' A)
参数：Ideal R；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `sInf_le_of_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : S
et α} {a b : α}, b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
theorem map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) :
    (∀ J ∈ A, RingHom.ker f ≤ J) → map f (sInf A) = sInf (map f '' A) := by
  refine fun h => le_antisymm (le_sInf ?_) ?_
  · intro j hj y hy
    obtain ⟨x, hx⟩ := (mem_map_iff_of_surjective f hf).1 hy
    obtain ⟨J, hJ⟩ := (Set.mem_image _ _ _).mp hj
    rw [← hJ.right, ← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    obtain ⟨x, hx⟩ := hf y
    refine hx ▸ mem_map_of_mem f ?_
    have : ∀ I ∈ A, y ∈ map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' ∈ J := by
      apply h J hJ
      rw [RingHom.mem_ker, map_sub, hx, sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'
/-
**Ideal.map_isPrime_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_isPrime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal 
R} [H : IsPrime I] (hk : RingHom.ker f <= I) : IsPrime (map f I)
参数：hf : Function.Surjective f；hk : RingHom.ker f <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Maps.0.Ideal.map_isPrime_of_surjective
._abel_1_1`：∀ {R : Type u_1} [inst : Ring R] (a b c : R), a * b = c - (c - a * b
)
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem map_isPrime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
    (hk : RingHom.ker f ≤ I) : IsPrime (map f I) := by
  refine ⟨fun h => H.ne_top (eq_top_iff.2 ?_), fun {x y} => ?_⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf, comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => ?_
    rw [← ha, ← hb, ← map_mul f, mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero, ← map_sub] at hc'
    have : a * b ∈ I := by
      convert! I.sub_mem hc (hk (hc' : c - a * b ∈ RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h
/-
**Ideal.IsMaximal.map_of_surjective_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.I
sMaximal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {F : Type u_3} [inst : Ring R] [inst_1 : R
ing S] [inst_2 : FunLike F R S]   [rc : RingHomClass F R S] {f : F},   Function.
Surjective ⇑f → ∀ {m : Ideal R} [m.IsMaximal], RingHom.ker f ≤ m → (Ideal.map f 
m).IsMaximal
参数：Ideal.map f m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.map_eq_top_or_isMaximal_of_surjective`：map_eq_top_or_isMaximal_of_
surjective (hf : Function.Surjective f) {I : Ideal R} (H : IsMaximal I) : map f 
I = ⊤ ∨ IsMaximal (map f I)
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma IsMaximal.map_of_surjective_of_ker_le {f : F} (hf : Function.Surjective f) {m : Ideal R}
    [m.IsMaximal] (hk : RingHom.ker f ≤ m) : (m.map f).IsMaximal := by
  refine m.map_eq_top_or_isMaximal_of_surjective f hf ‹_› |>.resolve_left fun h => ?_
  apply congr_arg (comap f) at h
  rw [comap_map_of_surjective _ hf, comap_top, ← RingHom.ker_eq_comap_bot, sup_of_le_left hk] at h
  exact IsMaximal.ne_top ‹_› h

end Ring

section CommRing

variable [CommRing R] [CommRing S]

/-
**Ideal.map_ne_bot_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_ne_bot_of_ne_bot {R S : Type*} [CommSemiring R] [Semiring S] [Algebra 
R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥) : map (algebraMap R S) I != ⊥
参数：h : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem map_ne_bot_of_ne_bot {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [FaithfulSMul R S] {I : Ideal R} (h : I ≠ ⊥) : map (algebraMap R S) I ≠ ⊥ :=
  (map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)).mp.mt h
/-
**Ideal.map_eq_iff_sup_ker_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R ->+* S) (hf : F
unction.Surjective f) : map f I = map f J ↔ I ⊔ RingHom.ker f = J ⊔ RingHom.ker 
f
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R →+* S)
    (hf : Function.Surjective f) : map f I = map f J ↔ I ⊔ RingHom.ker f = J ⊔ RingHom.ker f := by
  rw [← (comap_injective_of_surjective f hf).eq_iff, comap_map_of_surjective f hf,
    comap_map_of_surjective f hf, RingHom.ker_eq_comap_bot]
/-
**Ideal.map_radical_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_radical_of_surjective {f : R ->+* S} (hf : Function.Surjective f) {I :
 Ideal R} (h : RingHom.ker f <= I) : map f I.radical = (map f I).radical
参数：hf : Function.Surjective f；h : RingHom.ker f <= I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.map_sInf`：map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surj
ective f) : (forall J in A, RingHom.ker f <= J) -> map f (sInf A) = sInf (map f 
'' A…
-/
theorem map_radical_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R}
    (h : RingHom.ker f ≤ I) : map f I.radical = (map f I).radical := by
  rw [radical_eq_sInf, radical_eq_sInf]
  have : ∀ J ∈ {J : Ideal R | I ≤ J ∧ J.IsPrime}, RingHom.ker f ≤ J := fun J hJ => h.trans hJ.left
  convert! map_sInf hf this
  ext j
  constructor
  · rintro ⟨hj, hj'⟩
    have : j.IsPrime := hj'
    exact
      ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_isPrime f j⟩, map_comap_of_surjective f hf j⟩⟩
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    have : J.IsPrime := hJ.right
    exact ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_isPrime_of_surjective hf (le_trans h hJ.left)⟩

end CommRing

end Ideal

namespace RingHom

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
variable (f : A →+* B) (f_inv : B → A)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
/-
**RingHom.liftOfRightInverseAux** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A ->+* C) 
(hg : RingHom.ker f <= RingHom.ker g) : B ->+* C
参数：hf : Function.RightInverse f_inv f；g : A ->+* C；hg : RingHom.ker f <= RingHom
.ker g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition used to define `liftOfRightInverse`
-/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) :
    B →+* C :=
  { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g, ← sub_eq_zero, ← map_sub g, ← mem_ker]
      apply hg
      rw [mem_ker, map_sub f, sub_eq_zero, map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g, ← sub_eq_zero, ← map_sub g, ← mem_ker]
      apply hg
      rw [mem_ker, map_sub f, sub_eq_zero, map_mul f]
      simp only [hf _] }

@[simp]
/-
**RingHom.liftOfRightInverseAux_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g :
 A ->+* C) (hg : RingHom.ker f <= RingHom.ker g) (a : A) : (f.liftOfRightInverse
Aux f_inv hf g hg) (f a) = g a
参数：hf : Function.RightInverse f_inv f；g : A ->+* C；hg : RingHom.ker f <= RingHom
.ker g；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.liftOfRightInverse_comp_apply`：∀ {G₁ : Type u_5} {G₂ : Type
 u_6} {G₃ : Type u_7} [inst : AddGroup G₁] [inst_1 : AddGroup G₂] [inst_2 : AddG
roup G₃]   (f : G₁ →+ G₂) (f_neg…
-/
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

/-- `liftOfRightInverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`RingHom.liftOfRightInverse_comp`),
* where `f : A →+* B` has a right inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `RingHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
/-
**RingHom.liftOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：liftOfRightInverse (hf : Function.RightInverse f_inv f) : { g : A ->+* C /
/ RingHom.ker f <= RingHom.ker g } ≃ (B ->+* C) where toFun g
参数：hf : Function.RightInverse f_inv f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftOfRightInverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`RingHom.liftOfRightInverse_comp`),
* where `f : A →+* B` has a right inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `RingHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr <| by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `RingHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[simp]
/-
**RingHom.liftOfSurjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingHom`。
形式化陈述：liftOfSurjective (hf : Function.Surjective f) : { g : A ->+* C // RingHom.
ker f <= RingHom.ker g } ≃ (B ->+* C)
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-computable version of `RingHom.liftOfRightInverse` for when no computable 
right
inverse is available, that uses `Function.surjInv`.
-/
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
/-
**RingHom.liftOfRightInverse_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f) (g : { 
g : A ->+* C // RingHom.ker f <= RingHom.ker g }) (x : A) : (f.liftOfRightInvers
e f_inv hf g) (f x) = g.1 x
参数：hf : Function.RightInverse f_inv f；g : { g : A ->+* C // RingHom.ker f <= Rin
gHom.ker g }；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.liftOfRightInverseAux_comp_apply`：liftOfRightInverseAux_comp_app
ly (hf : Function.RightInverse f_inv f) (g : A ->+* C) (hg : RingHom.ker f <= Ri
ngHom.ker g) (a : A) : (f.lift…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x
/-
**RingHom.liftOfRightInverse_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：liftOfRightInverse_comp (hf : Function.RightInverse f_inv f) (g : { g : A 
->+* C // RingHom.ker f <= RingHom.ker g }) : (f.liftOfRightInverse f_inv hf g).
comp f = g
参数：hf : Function.RightInverse f_inv f；g : { g : A ->+* C // RingHom.ker f <= Rin
gHom.ker g }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingHom.liftOfRightInverse_comp_apply`：liftOfRightInverse_comp_apply (hf
 : Function.RightInverse f_inv f) (g : { g : A ->+* C // RingHom.ker f <= RingHo
m.ker g }) (x : A) : (f.lif…
-/
theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
  RingHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g
/-
**RingHom.eq_liftOfRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A ->+* C) 
(hg : RingHom.ker f <= RingHom.ker g) (h : B ->+* C) (hh : h.comp f = g) : h = f
.liftOfRightInverse f_inv hf ⟨g, hg⟩
参数：hf : Function.RightInverse f_inv f；g : A ->+* C；hg : RingHom.ker f <= RingHom
.ker g；h : B ->+* C；hh : h.comp f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →+* C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm
/-
**RingHom.liftOfSurjective_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：liftOfSurjective_comp_apply (hf : Function.Surjective f) (g : { g : A ->+*
 C // RingHom.ker f <= RingHom.ker g }) (x : A) : (f.liftOfSurjective hf) g (f x
) = (g : A ->+* C) x
参数：hf : Function.Surjective f；g : { g : A ->+* C // RingHom.ker f <= RingHom.ker
 g }；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.liftOfRightInverse_comp_apply`：liftOfRightInverse_comp_apply (hf
 : Function.RightInverse f_inv f) (g : { g : A ->+* C // RingHom.ker f <= RingHo
m.ker g }) (x : A) : (f.lif…
-/
theorem liftOfSurjective_comp_apply (hf : Function.Surjective f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    (f.liftOfSurjective hf) g (f x) = (g : A →+* C) x :=
  RingHom.liftOfRightInverse_comp_apply f _ _ g x
/-
**RingHom.liftOfSurjective_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：liftOfSurjective_comp (hf : Function.Surjective f) (g : { g : A ->+* C // 
RingHom.ker f <= RingHom.ker g }) : ((f.liftOfSurjective hf) g).comp f = (g : A 
->+* C)
参数：hf : Function.Surjective f；g : { g : A ->+* C // RingHom.ker f <= RingHom.ker
 g }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.liftOfRightInverse_comp`：liftOfRightInverse_comp (hf : Function.
RightInverse f_inv f) (g : { g : A ->+* C // RingHom.ker f <= RingHom.ker g }) :
 (f.liftOfRightInvers…
-/
theorem liftOfSurjective_comp (hf : Function.Surjective f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) :
    ((f.liftOfSurjective hf) g).comp f = (g : A →+* C) :=
  RingHom.liftOfRightInverse_comp f _ _ g
/-
**RingHom.eq_liftOfSurjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_liftOfSurjective (hf : Function.Surjective f) (g : A ->+* C) (hg : Ring
Hom.ker f <= RingHom.ker g) (h : B ->+* C) (hh : h.comp f = g) : h = f.liftOfSur
jective hf ⟨g, hg⟩
参数：hf : Function.Surjective f；g : A ->+* C；hg : RingHom.ker f <= RingHom.ker g；h
 : B ->+* C；hh : h.comp f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.eq_liftOfRightInverse`：eq_liftOfRightInverse (hf : Function.Righ
tInverse f_inv f) (g : A ->+* C) (hg : RingHom.ker f <= RingHom.ker g) (h : B ->
+* C) (hh : h.comp …
-/
theorem eq_liftOfSurjective (hf : Function.Surjective f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →+* C) (hh : h.comp f = g) :
    h = f.liftOfSurjective hf ⟨g, hg⟩ :=
  RingHom.eq_liftOfRightInverse f _ _ g _ _ hh

end RingHom

set_option backward.isDefEq.respectTransparency false in
/-- Any ring isomorphism induces an order isomorphism of ideals. -/
@[simps apply]
/-
**RingEquiv.idealComapOrderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.idealComapOrderIso {R S : Type*} [Semiring R] [Semiring S] (e : 
R ≃+* S) : Ideal S ≃o Ideal R where toFun I
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any ring isomorphism induces an order isomorphism of ideals.
-/
def RingEquiv.idealComapOrderIso {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    Ideal S ≃o Ideal R where
  toFun I := I.comap e
  invFun I := I.map e
  left_inv I := I.map_comap_of_surjective _ e.surjective
  right_inv I := I.comap_map_of_bijective _ e.bijective
  map_rel_iff' := by
    simp [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective _ e.surjective]

@[simp]
/-
**RingEquiv.idealComapOrderIso_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingEquiv.idealComapOrderIso_symm_apply {R S : Type*} [Semiring R] [Semiri
ng S] (e : R ≃+* S) (I : Ideal R) : e.idealComapOrderIso.symm I = I.map e
参数：e : R ≃+* S；I : Ideal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingEquiv.idealComapOrderIso_symm_apply
    {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) (I : Ideal R) :
    e.idealComapOrderIso.symm I = I.map e :=
  rfl

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)

/-
**AlgHom.ker_coe** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：ker_coe : RingHom.ker f = RingHom.ker (f : A ->+* B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma ker_coe : RingHom.ker f = RingHom.ker (f : A →+* B) := rfl
/-
**AlgHom.coe_ideal_map** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：coe_ideal_map (I : Ideal A) : Ideal.map f I = Ideal.map (f : A ->+* B) I
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ideal_map (I : Ideal A) :
    Ideal.map f I = Ideal.map (f : A →+* B) I := rfl
/-
**AlgHom.comap_ker** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：comap_ker {C : Type*} [Semiring C] [Algebra R C] (f : B ->ₐ[R] C) (g : A -
>ₐ[R] B) : (RingHom.ker f).comap g = RingHom.ker (f.comp g)
参数：f : B ->ₐ[R] C；g : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
-/
lemma comap_ker {C : Type*} [Semiring C] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (RingHom.ker f).comap g = RingHom.ker (f.comp g) :=
  RingHom.comap_ker f.toRingHom g.toRingHom

end AlgHom

namespace Algebra

variable {R : Type*} [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S]

/-- The induced linear map from `I` to the span of `I` in an `R`-algebra `S`. -/
@[simps!]
/-
**Algebra.idealMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：idealMap (I : Ideal R) : I ->ₗ[R] I.map (algebraMap R S)
参数：I : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The induced linear map from `I` to the span of `I` in an `R`-algebra `S`.
-/
def idealMap (I : Ideal R) : I →ₗ[R] I.map (algebraMap R S) :=
  (Algebra.linearMap R S).restrict (q := (I.map (algebraMap R S)).restrictScalars R)
    (fun _ ↦ Ideal.mem_map_of_mem _)

@[simp]
/-
**Algebra.idealMap_mul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：idealMap_mul (I : Ideal R) (x y : I) : idealMap S I (x * y) = idealMap S I
 x * idealMap S I y
参数：I : Ideal R；x y : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNonUnitalSubsemiringClassIdeal`：∀ {R : Type u_1} [inst : Semiring R]
, NonUnitalSubsemiringClass (Ideal R) R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.idealMap_apply_coe`：∀ {R : Type u_1} [inst : CommSemiring R] (S 
: Type u_2) [inst_1 : Semiring S] [inst_2 : Algebra R S] (I : Ideal R)   (c : ↥I
), ↑((Algebra.id…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma idealMap_mul (I : Ideal R) (x y : I) :
    idealMap S I (x * y) = idealMap S I x * idealMap S I y := by
  ext
  simp

end Algebra

@[simp]
/-
**FaithfulSMul.ker_algebraMap_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FaithfulSMul.ker_algebraMap_eq_bot (R A : Type*) [CommSemiring R] [Semirin
g A] [Algebra R A] [FaithfulSMul R A] : RingHom.ker (algebraMap R A) = ⊥
参数：R A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem FaithfulSMul.ker_algebraMap_eq_bot (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] : RingHom.ker (algebraMap R A) = ⊥ := by
  ext; simp

section PrincipalIdeal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (I : Ideal R) [I.IsPrincipal] :
    (I.map f).IsPrincipal := by
  obtain ⟨x, rfl⟩ := Submodule.IsPrincipal.principal I
  exact ⟨f x, by
    rw [← Ideal.span, ← Set.image_singleton, Ideal.map_span, Set.image_singleton,
      Ideal.submodule_span_eq]⟩

end PrincipalIdeal

/-
**RingHom.ker_evalRingHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.ker_evalRingHom {ι : Type*} [DecidableEq ι] (R : ι -> Type*) [fora
ll i, CommRing (R i)] (i : ι) : RingHom.ker (Pi.evalRingHom R i) = Ideal.span {1
 - Pi.single i 1}
参数：R : ι -> Type*；R i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Pi.single_zero`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι), Pi.single i 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingHom.ker_evalRingHom {ι : Type*} [DecidableEq ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] (i : ι) :
    RingHom.ker (Pi.evalRingHom R i) = Ideal.span {1 - Pi.single i 1} := by
  refine le_antisymm (fun x hx ↦ ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
  rw [Ideal.mem_span_singleton]
  use x + Pi.single i 1
  simp [mul_add, sub_mul, one_mul, ← Pi.single_mul_left, hx]
/-
**Ideal.exists_of_comap_eq_ker_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_of_comap_eq_ker_sup {A B : Type*} [Ring A] [Ring B] (f : A ->
+* B) (surj : Function.Surjective f) {I : Ideal B} {J : Ideal A} (eq : I.comap f
 = RingHom.ker f ⊔ J) {x : B} (hx : x in I) : exists y in J, f y = x
参数：f : A ->+* B；surj : Function.Surjective f；eq : I.comap f = RingHom.ker f ⊔ J；
hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma Ideal.exists_of_comap_eq_ker_sup {A B : Type*} [Ring A] [Ring B] (f : A →+* B)
    (surj : Function.Surjective f) {I : Ideal B} {J : Ideal A}
    (eq : I.comap f = RingHom.ker f ⊔ J) {x : B} (hx : x ∈ I) : ∃ y ∈ J, f y = x := by
  rcases surj x with ⟨x', hx'⟩
  rw [← hx', ← Ideal.mem_comap, eq] at hx
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
  use z, hz
  simpa [← hx', ← hyz, ← RingHom.mem_ker] using hy
/-
**Ideal.eq_map_of_comap_eq_ker_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.eq_map_of_comap_eq_ker_sup {A B : Type*} [CommRing A] [CommRing B] (
f : A ->+* B) (surj : Function.Surjective f) {I : Ideal B} {J : Ideal A} (eq : I
.comap f = RingHom.ker f ⊔ J) : I = J.map f
参数：f : A ->+* B；surj : Function.Surjective f；eq : I.comap f = RingHom.ker f ⊔ J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Ideal.exists_of_comap_eq_ker_sup`：Ideal.exists_of_comap_eq_ker_sup {A B 
: Type*} [Ring A] [Ring B] (f : A ->+* B) (surj : Function.Surjective f) {I : Id
eal B} {J : Ideal A} (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma Ideal.eq_map_of_comap_eq_ker_sup {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (surj : Function.Surjective f) {I : Ideal B} {J : Ideal A}
    (eq : I.comap f = RingHom.ker f ⊔ J) : I = J.map f := by
  refine le_antisymm (fun x hx ↦ ?_)
    (Ideal.map_le_iff_le_comap.mpr (le_of_le_of_eq le_sup_right eq.symm))
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq hx with ⟨y, mem, hy⟩
  simpa [← hy] using Ideal.mem_map_of_mem _ mem
