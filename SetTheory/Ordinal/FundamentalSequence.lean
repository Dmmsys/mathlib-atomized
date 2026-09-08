/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Fundamental sequences

A fundamental sequence for a countable limit ordinal `o` is a strictly monotone function `ℕ → Iio o`
with cofinal range. We can generalize this notion to arbitrary ordinals by setting the domain as
`Iio o.cof.card`. Note that for a countable limit ordinal, one has `o.cof.card = ω`.

## Main results

- `Ordinal.exists_isFundamentalSeq`: every ordinal has a fundamental sequence.
-/

@[expose] public section

universe u

open Cardinal Order Set

namespace Ordinal

variable {a b o : Ordinal}

/-- A fundamental sequence for `o` is a strictly monotonic function `Iio o.cof.ord → Iio o` with
cofinal range. We provide `a = o.cof.ord` explicitly to avoid type rewrites. -/
/-
**Ordinal.IsFundamentalSeq** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ordinal`。
形式化陈述：{a o : Ordinal.{u_1}} → (↑(Set.Iio a) → ↑(Set.Iio o)) → Prop
参数：↑(Set.Iio a) → ↑(Set.Iio o)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fundamental sequence for `o` is a strictly monotonic function `Iio o.cof.ord →
 Iio o` with
cofinal range. We provide `a = o.cof.ord` explicitly to avoid type rewrites.
-/
structure IsFundamentalSeq (f : Iio a → Iio o) : Prop where
  /-- This condition alongside the others is enough to conclude `o.cof.ord = a`, see
  `IsFundamentalSeq.ord_cof`. -/
  le_ord_cof : a ≤ o.cof.ord
  /-- A fundamental sequence is strictly monotonic. -/
  strictMono : StrictMono f
  /-- A fundamental sequence for `o` has cofinal range, i.e. its least strict upper bound equals the
  ordinal `o`. See `IsFundamentalSeq.iSup_add_one_eq` and `IsFundamentalSeq.iSup_eq`. -/
  isCofinal_range : IsCofinal (range f)

namespace IsFundamentalSeq
variable {f : Iio a → Iio o} {g : Iio b → Iio a}

/-
**Ordinal.IsFundamentalSeq.iSup_add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.Is
FundamentalSeq`。
形式化陈述：iSup_add_one_eq (hf : IsFundamentalSeq f) : ⨆ i, (f i).1 + 1 = o
参数：hf : IsFundamentalSeq f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Ordinal.IsFundamentalSeq.isCofinal_range`：∀ {a o : Ordinal.{u_1}} {f : ↑
(Set.Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → IsCofinal (Set.range f
)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.add_one_le_iff`：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
-/
theorem iSup_add_one_eq (hf : IsFundamentalSeq f) : ⨆ i, (f i).1 + 1 = o := by
  apply le_antisymm
  · simp_rw [Ordinal.iSup_le_iff, add_one_le_iff]
    exact fun i ↦ (f i).2
  · refine le_of_forall_lt fun b hb ↦ ?_
    obtain ⟨_, ⟨c, rfl⟩, hc : b ≤ _⟩ := hf.isCofinal_range ⟨b, hb⟩
    apply hc.trans_lt
    rw [← add_one_le_iff]
    apply Ordinal.le_iSup
/-
**Ordinal.IsFundamentalSeq.ord_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamen
talSeq`。
形式化陈述：ord_cof (hf : IsFundamentalSeq f) : o.cof.ord = a
参数：hf : IsFundamentalSeq f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Ordinal.IsFundamentalSeq.le_ord_cof`：∀ {a o : Ordinal.{u_1}} {f : ↑(Set.
Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → a ≤ o.cof.ord
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsFundamentalSeq.iSup_add_one_eq`：iSup_add_one_eq (hf : IsFundam
entalSeq f) : ⨆ i, (f i).1 + 1 = o
· 使用定理 `Ordinal.cof_iSup_Iio_add_one`：cof_iSup_Iio_add_one {a} {f : Iio a -> Ord
inal} (hf : StrictMono f) : cof (⨆ i, f i + 1) = cof a
· 使用定理 `Ordinal.IsFundamentalSeq.strictMono`：∀ {a o : Ordinal.{u_1}} {f : ↑(Set.
Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → StrictMono f
· 使用定理 `Ordinal.ord_cof_le`：ord_cof_le (o : Ordinal) : o.cof.ord <= o
-/
theorem ord_cof (hf : IsFundamentalSeq f) : o.cof.ord = a := by
  apply hf.le_ord_cof.antisymm'
  rw [← hf.iSup_add_one_eq, cof_iSup_Iio_add_one hf.strictMono]
  exact ord_cof_le a
/-
**Ordinal.IsFundamentalSeq.iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamen
talSeq`。
形式化陈述：iSup_eq (hf : IsFundamentalSeq f) (ha : 1 < a) : ⨆ i, (f i).1 = o
参数：hf : IsFundamentalSeq f；ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_Iio_add_one`：iSup_Iio_add_one {a : Ordinal.{u}} {f : Iio a 
-> Ordinal.{u}} (hf : StrictMono f) (ha : IsSuccPrelimit a) : ⨆ i : Iio a, f i +
 1 = ⨆ i : Iio…
· 使用定理 `Ordinal.IsFundamentalSeq.strictMono`：∀ {a o : Ordinal.{u_1}} {f : ↑(Set.
Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → StrictMono f
· 使用定理 `Ordinal.IsFundamentalSeq.ord_cof`：ord_cof (hf : IsFundamentalSeq f) : o.
cof.ord = a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Ordinal.aleph0_le_cof_iff`：aleph0_le_cof_iff {o : Ordinal} : ℵ₀ <= cof o
 ↔ 1 < cof o
· 使用定理 `Cardinal.ord_lt_ord`：ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂
· 使用定理 `Cardinal.ord_one`：ord_one : ord 1 = 1
· 使用定理 `Ordinal.IsFundamentalSeq.iSup_add_one_eq`：iSup_add_one_eq (hf : IsFundam
entalSeq f) : ⨆ i, (f i).1 + 1 = o
-/
theorem iSup_eq (hf : IsFundamentalSeq f) (ha : 1 < a) : ⨆ i, (f i).1 = o := by
  rw [← iSup_Iio_add_one hf.strictMono, hf.iSup_add_one_eq]
  rw [← hf.ord_cof]
  apply (isSuccLimit_ord _).isSuccPrelimit
  rwa [aleph0_le_cof_iff, ← ord_lt_ord, hf.ord_cof, ord_one]

/-- A regular ordinal `o` has a fundamental sequence given by all smaller ordinals. -/
/-
**Ordinal.IsFundamentalSeq.id** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamentalSe
q`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o ≤ o.cof.ord → Ordinal.IsFundamentalSeq id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ

--- 原说明 ---
A regular ordinal `o` has a fundamental sequence given by all smaller ordinals.
-/
protected theorem id (ho : o ≤ o.cof.ord) : IsFundamentalSeq (o := o) id where
  strictMono := strictMono_id
  isCofinal_range := by simp
  le_ord_cof := ho

/-- The empty function is a fundamental sequence for 0. -/
/-
**Ordinal.IsFundamentalSeq.zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamental
Seq`。
形式化陈述：∀ (f : ↑(Set.Iio 0) → ↑(Set.Iio 0)), Ordinal.IsFundamentalSeq f
参数：f : ↑(Set.Iio 0) → ↑(Set.Iio 0)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `Cardinal.ord_zero`：ord_zero : ord 0 = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Set.isEmpty_Iio_zero`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Zer
o α] [IsBotZeroClass α], IsEmpty ↑(Set.Iio 0)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsCofinal.of_isEmpty`：IsCofinal.of_isEmpty [IsEmpty α] {s : Set α} : IsC
ofinal s

--- 原说明 ---
The empty function is a fundamental sequence for 0.
-/
protected theorem zero (f : Iio 0 → Iio 0) : IsFundamentalSeq f where
  strictMono _ := by simp
  le_ord_cof := by simp
  isCofinal_range := .of_isEmpty

set_option backward.isDefEq.respectTransparency false in
/-- The length one sequence `(o)` is a fundamental sequence for `o + 1`. -/
/-
**Ordinal.IsFundamentalSeq.add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamen
talSeq`。
形式化陈述：∀ (o : Ordinal.{u_1}), Ordinal.IsFundamentalSeq fun x => ⟨o, ⋯⟩
参数：o : Ordinal.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_add`：cof_add (a : Ordinal) {b : Ordinal} (hb : b != 0) : cof
 (a + b) = cof b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.cof_one`：cof_one : cof 1 = 1
· 使用定理 `Cardinal.ord_one`：ord_one : ord 1 = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b

--- 原说明 ---
The length one sequence `(o)` is a fundamental sequence for `o + 1`.
-/
protected theorem add_one (o : Ordinal) :
    @IsFundamentalSeq 1 (o + 1) fun _ ↦ ⟨o, lt_add_one o⟩ where
  strictMono _ := by simp
  le_ord_cof := by simp
  isCofinal_range := by simp [IsTop]
/-
**Ordinal.IsFundamentalSeq.comp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamental
Seq`。
形式化陈述：∀ {a b o : Ordinal.{u_1}} {f : ↑(Set.Iio a) → ↑(Set.Iio o)} {g : ↑(Set.Iio
 b) → ↑(Set.Iio a)},   Ordinal.IsFundamentalSeq f → Ordinal.IsFundamentalSeq g →
 Ordinal.IsFundamentalSeq (f ∘ g)
参数：Set.Iio a；Set.Iio o；Set.Iio b；Set.Iio a；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.IsFundamentalSeq.ord_cof`：ord_cof (hf : IsFundamentalSeq f) : o.
cof.ord = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.ord_cof_le`：ord_cof_le (o : Ordinal) : o.cof.ord <= o
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Ordinal.IsFundamentalSeq.strictMono`：∀ {a o : Ordinal.{u_1}} {f : ↑(Set.
Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → StrictMono f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `IsCofinal.image`：IsCofinal.image {f : α -> β} {s : Set α} (hs : IsCofina
l s) (hf : Monotone f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s)
· 使用定理 `Ordinal.IsFundamentalSeq.isCofinal_range`：∀ {a o : Ordinal.{u_1}} {f : ↑
(Set.Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → IsCofinal (Set.range f
)
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
-/
protected theorem comp (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
    IsFundamentalSeq (f ∘ g) where
  strictMono := hf.strictMono.comp hg.strictMono
  le_ord_cof := by rw [hf.ord_cof, ← hg.ord_cof]; exact a.ord_cof_le
  isCofinal_range := by
    rw [range_comp]
    exact hg.isCofinal_range.image hf.strictMono.monotone hf.isCofinal_range

/-- If `f` is a fundamental sequence for a limit ordinal `o` and `g` is normal, then `g ∘ f` is a
fundamental sequence for `g o`. -/
/-
**Ordinal.IsFundamentalSeq.comp_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFu
ndamentalSeq`。
形式化陈述：comp_isNormal {g : Ordinal -> Ordinal} (hg : IsNormal g) (hf : IsFundament
alSeq f) (ho : IsSuccLimit o) : IsFundamentalSeq fun i => ⟨g (f i), hg.strictMon
o (f i).2⟩ where strictMono
参数：hg : IsNormal g；hf : IsFundamentalSeq f；ho : IsSuccLimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_map_of_isNormal`：cof_map_of_isNormal {f} (hf : IsNormal f) {
a} (ha : IsSuccLimit a) : cof (f a) = cof a
· 使用定理 `Ordinal.IsFundamentalSeq.ord_cof`：ord_cof (hf : IsFundamentalSeq f) : o.
cof.ord = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Ordinal.IsFundamentalSeq.strictMono`：∀ {a o : Ordinal.{u_1}} {f : ↑(Set.
Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → StrictMono f
· 使用定理 `Order.IsNormal.lt_iff_exists_lt`：lt_iff_exists_lt (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : b < f a ↔ exists a' < a, b < f a'
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Ordinal.IsFundamentalSeq.isCofinal_range`：∀ {a o : Ordinal.{u_1}} {f : ↑
(Set.Iio a) → ↑(Set.Iio o)}, Ordinal.IsFundamentalSeq f → IsCofinal (Set.range f
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f

--- 原说明 ---
If `f` is a fundamental sequence for a limit ordinal `o` and `g` is normal, then
 `g ∘ f` is a
fundamental sequence for `g o`.
-/
theorem comp_isNormal {g : Ordinal → Ordinal} (hg : IsNormal g) (hf : IsFundamentalSeq f)
    (ho : IsSuccLimit o) : IsFundamentalSeq fun i ↦ ⟨g (f i), hg.strictMono (f i).2⟩ where
  strictMono := hg.strictMono.comp hf.strictMono
  le_ord_cof := by rw [cof_map_of_isNormal hg ho, hf.ord_cof]
  isCofinal_range := by
    rintro ⟨b, hb⟩
    rw [mem_Iio, hg.lt_iff_exists_lt ho] at hb
    obtain ⟨c, hc, hc'⟩ := hb
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hf.isCofinal_range ⟨c, hc⟩
    refine ⟨⟨_, hg.strictMono (f d).2⟩, ?_, hc'.le.trans (hg.monotone hd)⟩
    simp

end IsFundamentalSeq

/-- Every ordinal has a fundamental sequence. -/
/-
**Ordinal.exists_isFundamentalSeq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_isFundamentalSeq (ha : o.cof.ord = a) : exists f : Iio a -> Iio o, 
IsFundamentalSeq f
参数：ha : o.cof.ord = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.exists_ord_cof_eq`：exists_ord_cof_eq [LinearOrder α] [WellFounde
dLT α] : exists s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.cof_toType`：cof_toType (o : Ordinal) : Order.cof o.ToType = o.co
f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `OrderIso.map_isCofinal_iff`：OrderIso.map_isCofinal_iff (e : α ≃o β) {s :
 Set α} : IsCofinal (e '' s) ↔ IsCofinal s
· 使用定理 `OrderIso.range_eq`：range_eq (e : α ≃o β) : Set.range e = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }

--- 原说明 ---
Every ordinal has a fundamental sequence.
-/
theorem exists_isFundamentalSeq (ha : o.cof.ord = a) : ∃ f : Iio a → Iio o, IsFundamentalSeq f := by
  subst ha
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq o.ToType
  rw [cof_toType] at hs'
  let g := (OrderIso.setCongr _ _ (congrArg _ hs'.symm)).trans <|
    .ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun i ↦ g i, le_rfl, fun _ ↦ by simp, ?_⟩
  rw [range_comp', OrderIso.map_isCofinal_iff, range_comp', g.range_eq]
  simpa

/-! ### Deprecated material -/

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
@[deprecated IsFundamentalSeq (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：IsFundamentalSequence (a o : Ordinal.{u}) (f : forall b < o, Ordinal.{u}) 
: Prop
参数：a o : Ordinal.{u}；f : forall b < o, Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fundamental sequence for `a` is an increasing sequence of length `o = cof a` t
hat converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites.
-/
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}}

@[deprecated IsFundamentalSeq.ord_cof (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.cof_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFund
amentalSequence`。
形式化陈述：∀ {a o : Ordinal.{u}} {f : (b : Ordinal.{u}) → b < o → Ordinal.{u}}, a.IsF
undamentalSequence o f → a.cof.ord = o
参数：b : Ordinal.{u}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
· 使用定理 `Ordinal.cof_blsub_le`：cof_blsub_le {o} (f : forall a < o, Ordinal) : cof
 (blsub.{u, u} o f) <= o.card
· 使用定理 `Cardinal.ord_card_le`：ord_card_le (o : Ordinal) : o.card.ord <= o
-/
protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
  hf.1.antisymm' <| by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.I
sFundamentalSequence`。
形式化陈述：∀ {a o : Ordinal.{u}} {f : (b : Ordinal.{u}) → b < o → Ordinal.{u}},   a.I
sFundamentalSequence o f → ∀ {i j : Ordinal.{u}} (hi : i < o) (hj : j < o), i < 
j → f i hi < f j hj
参数：b : Ordinal.{u}；hi : i < o；hj : j < o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    ∀ hi hj, i < j → f i hi < f j hj :=
  hf.2.1

@[deprecated IsFundamentalSeq.iSup_add_one_eq (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.blsub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFu
ndamentalSequence`。
形式化陈述：blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a
参数：hf : IsFundamentalSequence a o f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.ord_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFun
damentalSequence`。
形式化陈述：ord_cof (hf : IsFundamentalSequence a o f) : IsFundamentalSequence a a.cof
.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq]))
参数：hf : IsFundamentalSequence a o f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsFundamentalSequence.cof_eq`：∀ {a o : Ordinal.{u}} {f : (b : Or
dinal.{u}) → b < o → Ordinal.{u}}, a.IsFundamentalSequence o f → a.cof.ord = o
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq])) := by
  have H := hf.cof_eq
  subst H
  exact hf

@[deprecated IsFundamentalSeq.id (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.id_of_le_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.
IsFundamentalSequence`。
形式化陈述：id_of_le_cof (h : o <= o.cof.ord) : IsFundamentalSequence o o fun a _ => a
参数：h : o <= o.cof.ord。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.blsub_id`：blsub_id : forall o, (blsub.{u, u} o fun x _ => x) = o
-/
theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, @fun _ _ _ _ => id, blsub_id o⟩

@[deprecated IsFundamentalSeq.zero (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundam
entalSequence`。
形式化陈述：∀ {f : (b : Ordinal.{u_1}) → b < 0 → Ordinal.{u_1}}, Ordinal.IsFundamental
Sequence 0 0 f
参数：b : Ordinal.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `Cardinal.ord_zero`：ord_zero : ord 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.blsub_zero`：blsub_zero (f : forall a < (0 : Ordinal), Ordinal) :
 blsub 0 f = 0
-/
protected theorem zero {f : ∀ b < (0 : Ordinal), Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (not_lt_zero hi).elim, blsub_zero f⟩

@[deprecated IsFundamentalSeq.add_one (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundam
entalSequence`。
形式化陈述：∀ {o : Ordinal.{u}}, (Order.succ o).IsFundamentalSequence 1 fun x x_1 => o
参数：Order.succ o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_succ`：cof_succ (o) : cof (succ o) = 1
· 使用定理 `Cardinal.ord_one`：ord_one : ord 1 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Ordinal.lt_one_iff_zero`：lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0
· 使用定理 `Ordinal.blsub_const`：blsub_const {o : Ordinal} (ho : o != 0) (a : Ordina
l) : (blsub.{u, v} o fun _ _ => a) = succ a
· 使用定理 `Ordinal.one_ne_zero`：1 ≠ 0
-/
protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o := by
  refine ⟨?_, @fun i j hi hj h => ?_, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi, hj] at h
    exact h.false.elim

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFu
ndamentalSequence`。
形式化陈述：∀ {a o : Ordinal.{u}} {f : (b : Ordinal.{u}) → b < o → Ordinal.{u}},   a.I
sFundamentalSequence o f → ∀ {i j : Ordinal.{u}} (hi : i < o) (hj : j < o), i ≤ 
j → f i hi ≤ f j hj
参数：b : Ordinal.{u}；hi : i < o；hj : j < o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
    (hj : j < o) (hij : i ≤ j) : f i hi ≤ f j hj := by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl

@[deprecated IsFundamentalSeq.comp (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.trans** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFunda
mentalSequence`。
形式化陈述：trans {a o o' : Ordinal.{u}} {f : forall b < o, Ordinal.{u}} (hf : IsFunda
mentalSequence a o f) {g : forall b < o', Ordinal.{u}} (hg : IsFundamentalSequen
ce o o' g) : IsFundamentalSequence a o' fun i hi => f (g i hi) (by rw [← hg.2.2]
; apply lt_blsub)
参数：hf : IsFundamentalSequence a o f；hg : IsFundamentalSequence o o' g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.IsFundamentalSequence.cof_eq`：∀ {a o : Ordinal.{u}} {f : (b : Or
dinal.{u}) → b < o → Ordinal.{u}}, a.IsFundamentalSequence o f → a.cof.ord = o
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordinal.ord_cof_le`：ord_cof_le (o : Ordinal) : o.cof.ord <= o
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordinal.blsub_comp`：blsub_comp {o o' : Ordinal.{max u v}} {f : forall a 
< o, Ordinal.{max u v w}} (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j 
hj) {g :…
· 使用定理 `Ordinal.IsFundamentalSequence.monotone`：∀ {a o : Ordinal.{u}} {f : (b : 
Ordinal.{u}) → b < o → Ordinal.{u}},   a.IsFundamentalSequence o f → ∀ {i j : Or
dinal.{u}} (hi : i < o) (hj …
-/
theorem trans {a o o' : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : ∀ b < o', Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi) (by rw [← hg.2.2]; apply lt_blsub) := by
  refine ⟨?_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), ?_⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    · exact hf.2.2
    · exact hg.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsFundamen
talSequence`。
形式化陈述：∀ {a o : Ordinal.{u_1}} {s : (p : Ordinal.{u_1}) → p < o → Ordinal.{u_1}},
   a.IsFundamentalSequence o s → ∀ {p : Ordinal.{u_1}} (hp : p < o), s p hp < a
参数：p : Ordinal.{u_1}；hp : p < o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lt_blsub`：lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h
 < blsub o f
· 使用定理 `Ordinal.IsFundamentalSequence.blsub_eq`：blsub_eq (hf : IsFundamentalSequ
ence a o f) : blsub.{u, u} o f = a
-/
protected theorem lt {a o : Ordinal} {s : Π p < o, Ordinal}
    (h : IsFundamentalSequence a o s) {p : Ordinal} (hp : p < o) : s p hp < a :=
  h.blsub_eq ▸ lt_blsub s p hp

end IsFundamentalSequence

/-- Every ordinal has a fundamental sequence. -/
@[deprecated exists_isFundamentalSeq (since := "2026-03-23")]
/-
**Ordinal.exists_fundamental_sequence** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_fundamental_sequence (a : Ordinal.{u}) : exists f, IsFundamentalSeq
uence a a.cof.ord f
参数：a : Ordinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.exists_lsub_cof`：exists_lsub_cof (o : Ordinal) : exists (ι : _) 
(f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = cof o
· 使用定理 `Cardinal.ord_eq`：∀ (α : Type u_1), ∃ r, ∃ (x : IsWellOrder α r), (Cardin
al.mk α).ord = Ordinal.type r
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `RelEmbedding.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → 
Prop} {s : β → β → Prop} (self : r ↪r s) {a b : α},   s (self.toEmbedding a) (se
lf.toEmbedding …
· 使用定理 `Ordinal.enum_lt_enum`：enum_lt_enum {r : α -> α -> Prop} [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : r (enum r o₁) (enum r o₂) ↔ o₁ < o₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.blsub_le`：blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a}
 : (forall i h, f i h < a) -> blsub o f <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lsub_le_iff`：lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= 
a ↔ forall i, f i < a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `Ordinal.bfamilyOfFamily'_typein`：∀ {α : Type u_1} {ι : Type u_3} (r : ι 
→ ι → Prop) [inst : IsWellOrder ι r] (f : ι → α) (i : ι),   Ordinal.bfamilyOfFam
ily' r f ((Ordinal.ty…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `instIsTransOfIsWellOrder`：∀ {α : Type u} (r : α → α → Prop) [IsWellOrder
 α r], IsTrans α r
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Every ordinal has a fundamental sequence.
-/
theorem exists_fundamental_sequence (a : Ordinal.{u}) :
    ∃ f, IsFundamentalSequence a a.cof.ord f := by
  suffices h : ∃ o f, IsFundamentalSequence a o f by
    rcases h with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  let r' := Subrel r fun i ↦ ∀ j, r j i → f j < f i
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  have := hrr'.isWellOrder
  refine
    ⟨_, _, hrr'.ordinal_type_le.trans ?_, @fun i j _ h _ => (enum r' ⟨j, h⟩).prop _ ?_,
      le_antisymm (blsub_le fun i hi => lsub_le_iff.1 hf.le _) ?_⟩
  · rw [← hι, hr]
  · change r (hrr'.1 _) (hrr'.1 _)
    rwa [hrr'.2, @enum_lt_enum _ r']
  · rw [← hf, lsub_le_iff]
    intro i
    suffices h : ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f i) i' hi' by
      rcases h with ⟨i', hi', hfg⟩
      exact hfg.trans_lt (lt_blsub _ _ _)
    by_cases! h : ∀ j, r j i → f j < f i
    · refine ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, ?_⟩
      rw [bfamilyOfFamily'_typein]
    · obtain ⟨hji, hij⟩ := wo.wf.min_mem _ h
      refine ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le ?_ hij⟩, typein_lt_type _ _, ?_⟩
      · by_contra! H
        exact (wo.wf.not_lt_min {j | r j i ∧ f i ≤ f j} ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
      · rwa [bfamilyOfFamily'_typein]

@[deprecated IsFundamentalSeq.comp_isNormal (since := "2026-03-23")]
/-
**Ordinal.IsFundamentalSequence.of_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.I
sFundamentalSequence`。
形式化陈述：∀ {f : Ordinal.{u} → Ordinal.{u}},   Order.IsNormal f →     ∀ {a o : Ordin
al.{u}},       Order.IsSuccLimit a →         ∀ {g : (b : Ordinal.{u}) → b < o → 
Ordinal.{u}},           a.IsFundamentalSequence o g → (f a).IsFundamentalSequenc
e o fun b hb => f (g b hb)
参数：b : Ordinal.{u}；f a；g b hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.blsub_comp`：blsub_comp {o o' : Ordinal.{max u v}} {f : forall a 
< o, Ordinal.{max u v w}} (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j 
hj) {g :…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Ordinal.IsNormal.blsub_eq`：∀ {f : Ordinal.{u} → Ordinal.{max u v}},   Or
der.IsNormal f → ∀ {o : Ordinal.{u}}, Order.IsSuccLimit o → (o.blsub fun x x_1 =
> f x) = f o
-/
theorem IsFundamentalSequence.of_isNormal {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsSuccLimit a) {g} (hg : IsFundamentalSequence a o g) :
    IsFundamentalSequence (f a) o fun b hb => f (g b hb) := by
  refine ⟨?_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), ?_⟩
  · grind [Ordinal.IsFundamentalSequence, cof_map_of_isNormal]
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

end Ordinal

