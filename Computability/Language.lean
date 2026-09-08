/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Martin Dvorak, Rudy Peterson
-/
module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Set.Lattice
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Lattice.Image

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet.
Note that "strings" are implemented as lists over the alphabet.

Union and concatenation define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.

In addition to that, we define a reversal of a language and prove that it behaves well
with respect to other language operations.

## Notation

* `l + m`: union of languages `l` and `m`
* `l - m`: difference of languages `l` and `m`
* `l * m`: language of strings `x ++ y` such that `x ∈ l` and `y ∈ m`
* `l ^ n`: language of strings consisting of `n` members of `l` concatenated together
* `1`: language consisting of only the empty string. This is because it is the unit of the `*`
  operator.
* `l∗`: Kleene star – language of strings consisting of arbitrarily many members of `l`
  concatenated together. Note that this notation uses the Unicode asterisk operator `∗`, as opposed
  to the more common ASCII asterisk `*`.
* `lᶜ`: complement, language of strings `x` such that `x ∉ l`
* `l ⊓ m`: intersection of languages `l` and `m`

## Main definitions

* `Language α`: a set of strings over the alphabet `α`
* `l.map f`: transform a language `l` over `α` into a language over `β`
  by translating through `f : α → β`

## Main theorems

* `Language.self_eq_mul_add_iff`: Arden's lemma – if a language `l` satisfies the equation
  `l = m * l + n`, and `m` doesn't contain the empty string,
  then `l` is the language `m∗ * n`

-/

@[expose] public section


open List Set Computability

universe v

variable {α β γ : Type*}

/-- A language is a set of strings over an alphabet. -/
/-
**Language** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Language (α)
参数：α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language is a set of strings over an alphabet.
-/
def Language (α) :=
  Set (List α)
deriving CompleteAtomicBooleanAlgebra

namespace Language

/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (List α) (Language α) := ⟨Set.Mem⟩
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Singleton (List α) (Language α) := ⟨Set.singleton⟩
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Insert (List α) (Language α) := ⟨Set.insert⟩

variable {l m : Language α} {a b x : List α}

/-- Zero language has no elements. -/
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Zero language has no elements.
-/
instance : Zero (Language α) :=
  ⟨(∅ : Set _)⟩

/-- `1 : Language α` contains only one element `[]`. -/
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1 : Language α` contains only one element `[]`.
-/
instance : One (Language α) :=
  ⟨{[]}⟩
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Language α) := ⟨(∅ : Set _)⟩

/-- The sum of two languages is their union. -/
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two languages is their union.
-/
instance : Add (Language α) :=
  ⟨((· ∪ ·) : Set (List α) → Set (List α) → Set (List α))⟩

/-- The subtraction of two languages is their difference. -/
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtraction of two languages is their difference.
-/
instance : Sub (Language α) where
  sub := SDiff.sdiff

/-- The product of two languages `l` and `m` is the language made of the strings `x ++ y` where
`x ∈ l` and `y ∈ m`. -/
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two languages `l` and `m` is the language made of the strings `x 
++ y` where
`x ∈ l` and `y ∈ m`.
-/
instance : Mul (Language α) :=
  ⟨image2 (· ++ ·)⟩
/-
**Language.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：zero_def : (0 : Language α) = (∅ : Set _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl
/-
**Language.one_def** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：one_def : (1 : Language α) = ({[]} : Set (List α))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : Language α) = ({[]} : Set (List α)) :=
  rfl
/-
**Language.add_def** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：add_def (l m : Language α) : l + m = (l union m : Set (List α))
参数：l m : Language α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_def (l m : Language α) : l + m = (l ∪ m : Set (List α)) :=
  rfl
/-
**Language.sub_def** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：sub_def (l m : Language α) : l - m = (l \ m : Set (List α))
参数：l m : Language α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_def (l m : Language α) : l - m = (l \ m : Set (List α)) :=
  rfl
/-
**Language.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mul_def (l m : Language α) : l * m = image2 (· ++ ·) l m
参数：l m : Language α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (l m : Language α) : l * m = image2 (· ++ ·) l m :=
  rfl

/-- The Kleene star of a language `L` is the set of all strings which can be written by
concatenating strings from `L`. -/
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Kleene star of a language `L` is the set of all strings which can be written
 by
concatenating strings from `L`.
-/
instance : KStar (Language α) := ⟨fun l ↦ {x | ∃ L : List (List α), x = L.flatten ∧ ∀ y ∈ L, y ∈ l}⟩
/-
**Language.kstar_def** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：kstar_def (l : Language α) : l∗ = {x | exists L : List (List α), x = L.fla
tten ∧ forall y in L, y in l}
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma kstar_def (l : Language α) : l∗ = {x | ∃ L : List (List α), x = L.flatten ∧ ∀ y ∈ L, y ∈ l} :=
  rfl

@[ext]
/-
**Language.ext** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：ext {l m : Language α} (h : forall (x : List α), x in l ↔ x in m) : l = m
参数：h : forall (x : List α), x in l ↔ x in m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem ext {l m : Language α} (h : ∀ (x : List α), x ∈ l ↔ x ∈ m) : l = m :=
  Set.ext h

@[simp]
/-
**Language.notMem_zero** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：notMem_zero (x : List α) : x ∉ (0 : Language α)
参数：x : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_zero (x : List α) : x ∉ (0 : Language α) :=
  id

@[simp]
/-
**Language.mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_one (x : List α) : x in (1 : Language α) ↔ x = []
参数：x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_one (x : List α) : x ∈ (1 : Language α) ↔ x = [] := by rfl
/-
**Language.nil_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：nil_mem_one : [] in (1 : Language α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem nil_mem_one : [] ∈ (1 : Language α) :=
  Set.mem_singleton _
/-
**Language.mem_add** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_add (l m : Language α) (x : List α) : x in l + m ↔ x in l ∨ x in m
参数：l m : Language α；x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_add (l m : Language α) (x : List α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
  Iff.rfl
/-
**Language.mem_sub** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_sub (l m : Language α) (x : List α) : x in l - m ↔ x in l ∧ x ∉ m
参数：l m : Language α；x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sub (l m : Language α) (x : List α) : x ∈ l - m ↔ x ∈ l ∧ x ∉ m :=
  Iff.rfl
/-
**Language.mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_mul : x in l * m ↔ exists a in l, exists b in m, a ++ b = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2`：∀ {α : Type u} {β : Type v} {γ : Type w} {f : α → β → γ}
 {s : Set α} {t : Set β} {c : γ},   c ∈ Set.image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a
 b =…
-/
theorem mem_mul : x ∈ l * m ↔ ∃ a ∈ l, ∃ b ∈ m, a ++ b = x :=
  mem_image2
/-
**Language.append_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：append_mem_mul : a in l -> b in m -> a ++ b in l * m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem append_mem_mul : a ∈ l → b ∈ m → a ++ b ∈ l * m :=
  mem_image2_of_mem
/-
**Language.mem_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_kstar : x in l∗ ↔ exists L : List (List α), x = L.flatten ∧ forall y i
n L, y in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_kstar : x ∈ l∗ ↔ ∃ L : List (List α), x = L.flatten ∧ ∀ y ∈ L, y ∈ l :=
  Iff.rfl
/-
**Language.join_mem_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：join_mem_kstar {L : List (List α)} (h : forall y in L, y in l) : L.flatten
 in l∗
参数：List α；h : forall y in L, y in l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join_mem_kstar {L : List (List α)} (h : ∀ y ∈ L, y ∈ l) : L.flatten ∈ l∗ :=
  ⟨L, rfl, h⟩
/-
**Language.nil_mem_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：nil_mem_kstar (l : Language α) : [] in l∗
参数：l : Language α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem nil_mem_kstar (l : Language α) : [] ∈ l∗ :=
  ⟨[], rfl, fun _ h ↦ by contradiction⟩
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderedSub (Language α) where
  tsub_le_iff_right _ _ _ := sdiff_le_iff'

set_option backward.isDefEq.respectTransparency false in
/-
**Language.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
形式化陈述：instSemiring : Semiring (Language α) where add_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring : Semiring (Language α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  mul_assoc _ _ _ := image2_assoc append_assoc
  zero_mul _ := image2_empty_left
  mul_zero _ := image2_empty_right
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n := if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp [add_def, zero_def]
  left_distrib _ _ _ := image2_union_right
  right_distrib _ _ _ := image2_union_left
  nsmul := nsmulRec

@[simp]
/-
**Language.add_self** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：add_self (l : Language α) : l + l = l
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
theorem add_self (l : Language α) : l + l = l :=
  sup_idem _

/-- Maps the alphabet of a language. -/
/-
**Language.map** 是 Mathlib 中的一个定义，位于命名空间 `Language`。
形式化陈述：map (f : α -> β) : Language α ->+* Language β where toFun
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps the alphabet of a language.
-/
def map (f : α → β) : Language α →+* Language β where
  toFun := image (List.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
  map_mul' _ _ := image_image2_distrib <| fun _ _ => map_append

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Language.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：map_id (l : Language α) : map id l = l
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `Set.image_id_eq`：image_id_eq : image (id : α -> α) = id
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id (l : Language α) : map id l = l := by simp [map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Language.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：map_map (g : β -> γ) (f : α -> β) (l : Language α) : map g (map f l) = map
 (g ∘ f) l
参数：g : β -> γ；f : α -> β；l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map (g : β → γ) (f : α → β) (l : Language α) : map g (map f l) = map (g ∘ f) l := by
  simp [map, image_image]
/-
**Language.mem_kstar_iff_exists_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：mem_kstar_iff_exists_nonempty {x : List α} : x in l∗ ↔ exists S : List (Li
st α), x = S.flatten ∧ forall y in S, y in l ∧ y != []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatten_filter_not_isEmpty`：∀ {α : Type u_1} {L : List (List α)}, (
List.filter (fun l => !l.isEmpty) L).flatten = L.flatten
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_kstar_iff_exists_nonempty {x : List α} :
    x ∈ l∗ ↔ ∃ S : List (List α), x = S.flatten ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ [] := by
  constructor
  · rintro ⟨S, rfl, h⟩
    refine ⟨S.filter fun l ↦ !List.isEmpty l,
      by simp [List.flatten_filter_not_isEmpty], fun y hy ↦ ?_⟩
    simp only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, isEmpty_eq_false_iff, ne_eq] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy ↦ (h y hy).1⟩
/-
**Language.kstar_def_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：kstar_def_nonempty (l : Language α) : l∗ = { x | exists S : List (List α),
 x = S.flatten ∧ forall y in S, y in l ∧ y != [] }
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用引理 `Language.mem_kstar_iff_exists_nonempty`：mem_kstar_iff_exists_nonempty {x
 : List α} : x in l∗ ↔ exists S : List (List α), x = S.flatten ∧ forall y in S, 
y in l ∧ y != []
-/
theorem kstar_def_nonempty (l : Language α) :
    l∗ = { x | ∃ S : List (List α), x = S.flatten ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ [] } := by
  ext x; apply mem_kstar_iff_exists_nonempty
/-
**Language.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：le_iff (l m : Language α) : l <= m ↔ l + m = m
参数：l m : Language α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
theorem le_iff (l m : Language α) : l ≤ m ↔ l + m = m :=
  sup_eq_right.symm
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulLeftMono (Language α) where
  elim _ _ _ := image2_subset_left
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulRightMono (Language α) where
  elim _ _ _ := image2_subset_right
/-
**Language.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_iSup {ι : Sort v} {l : ι -> Language α} {x : List α} : (x in ⨆ i, l i)
 ↔ exists i, x in l i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem mem_iSup {ι : Sort v} {l : ι → Language α} {x : List α} : (x ∈ ⨆ i, l i) ↔ ∃ i, x ∈ l i :=
  mem_iUnion
/-
**Language.iSup_mul** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：iSup_mul {ι : Sort v} (l : ι -> Language α) (m : Language α) : (⨆ i, l i) 
* m = ⨆ i, l i * m
参数：l : ι -> Language α；m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_left`：image2_iUnion_left (s : ι -> Set α) (t : Set β) 
: image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t
-/
theorem iSup_mul {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) * m = ⨆ i, l i * m :=
  image2_iUnion_left _ _ _
/-
**Language.mul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mul_iSup {ι : Sort v} (l : ι -> Language α) (m : Language α) : (m * ⨆ i, l
 i) = ⨆ i, m * l i
参数：l : ι -> Language α；m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
theorem mul_iSup {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (m * ⨆ i, l i) = ⨆ i, m * l i :=
  image2_iUnion_right _ _ _
/-
**Language.iSup_add** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：iSup_add {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α) 
: (⨆ i, l i) + m = ⨆ i, l i + m
参数：l : ι -> Language α；m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_sup`：iSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ x, f x) ⊔ a = 
⨆ x, f x ⊔ a
-/
theorem iSup_add {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) + m = ⨆ i, l i + m :=
  iSup_sup
/-
**Language.add_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：add_iSup {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α) 
: (m + ⨆ i, l i) = ⨆ i, m + l i
参数：l : ι -> Language α；m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_iSup`：sup_iSup [Nonempty ι] {f : ι -> α} {a : α} : (a ⊔ ⨆ x, f x) = 
⨆ x, a ⊔ f x
-/
theorem add_iSup {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (m + ⨆ i, l i) = ⨆ i, m + l i :=
  sup_iSup
/-
**Language.iSup_sub** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：iSup_sub {ι : Sort v} (l : ι -> Language α) (m : Language α) : (⨆ i, l i) 
- m = ⨆ i, l i - m
参数：l : ι -> Language α；m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_sdiff`：iUnion_sdiff (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 \ s = ⋃ i, t i \ s
-/
theorem iSup_sub {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) - m = ⨆ i, l i - m :=
  iUnion_sdiff _ _
/-
**Language.sub_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：sub_iSup {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α) 
: (m - ⨆ i, l i) = ⨅ i, m - l i
参数：l : ι -> Language α；m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_iUnion`：sdiff_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s \ ⋃ i, t i) = ⋂ i, s \ t i
-/
theorem sub_iSup {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (m - ⨆ i, l i) = ⨅ i, m - l i :=
  sdiff_iUnion _ _
/-
**Language.mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mem_pow {l : Language α} {x : List α} {n : Nat} : x in l ^ n ↔ exists S : 
List (List α), x = S.flatten ∧ S.length = n ∧ forall y in S, y in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem mem_pow {l : Language α} {x : List α} {n : ℕ} :
    x ∈ l ^ n ↔ ∃ S : List (List α), x = S.flatten ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l := by
  induction n generalizing x with
  | zero => simp
  | succ n ihn =>
    simp only [pow_succ', mem_mul, ihn]
    constructor
    · rintro ⟨a, ha, b, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [forall_mem_cons] at hS
      exact ⟨a, hS.1, _, ⟨S, rfl, rfl, hS.2⟩, rfl⟩
/-
**Language.kstar_eq_iSup_pow** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ i : Nat, l ^ i
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Language.ext`：ext {l m : Language α} (h : forall (x : List α), x in l ↔ 
x in m) : l = m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ i : ℕ, l ^ i := by
  ext x
  simp only [mem_kstar, mem_iSup, mem_pow]
  grind

@[simp]
/-
**Language.map_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：map_kstar (f : α -> β) (l : Language α) : map f l∗ = (map f l)∗
参数：f : α -> β；l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.kstar_eq_iSup_pow`：kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ 
i : Nat, l ^ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
-/
theorem map_kstar (f : α → β) (l : Language α) : map f l∗ = (map f l)∗ := by
  rw [kstar_eq_iSup_pow, kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  exact image_iUnion
/-
**Language.mul_self_kstar_comm** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Language.kstar_eq_iSup_pow`：kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ 
i : Nat, l ^ i
· 使用定理 `Language.iSup_mul`：iSup_mul {ι : Sort v} (l : ι -> Language α) (m : Lang
uage α) : (⨆ i, l i) * m = ⨆ i, l i * m
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Language.mul_iSup`：mul_iSup {ι : Sort v} (l : ι -> Language α) (m : Lang
uage α) : (m * ⨆ i, l i) = ⨆ i, m * l i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

@[simp]
/-
**Language.one_add_self_mul_kstar_eq_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：one_add_self_mul_kstar_eq_kstar (l : Language α) : 1 + l * l∗ = l∗
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Language.kstar_eq_iSup_pow`：kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ 
i : Nat, l ^ i
· 使用定理 `Language.mul_iSup`：mul_iSup {ι : Sort v} (l : ι -> Language α) (m : Lang
uage α) : (m * ⨆ i, l i) = ⨆ i, m * l i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sup_iSup_nat_succ`：sup_iSup_nat_succ (u : Nat -> α) : (u 0 ⊔ ⨆ i, u (i +
 1)) = ⨆ i, u i
-/
theorem one_add_self_mul_kstar_eq_kstar (l : Language α) : 1 + l * l∗ = l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ', ← pow_zero l]
  exact sup_iSup_nat_succ _

@[simp]
/-
**Language.one_add_kstar_mul_self_eq_kstar** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.mul_self_kstar_comm`：mul_self_kstar_comm (l : Language α) : l∗ 
* l = l * l∗
· 使用定理 `Language.one_add_self_mul_kstar_eq_kstar`：one_add_self_mul_kstar_eq_ksta
r (l : Language α) : 1 + l * l∗ = l∗
-/
theorem one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗ := by
  rw [mul_self_kstar_comm, one_add_self_mul_kstar_eq_kstar]
/-
**Language.** 是 Mathlib 中的一个实例，位于命名空间 `Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : KleeneAlgebra (Language α) where
  __ : OrderBot (Language α) := inferInstance
  one_le_kstar a _ hl := ⟨[], hl, by simp⟩
  mul_kstar_le_kstar a := (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_kstar a := (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_self l m h := by
    rw [kstar_eq_iSup_pow, iSup_mul]
    refine iSup_le fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih => grw [pow_succ, mul_assoc, h, ih]
  mul_kstar_le_self l m h := by
    rw [kstar_eq_iSup_pow, mul_iSup]
    refine iSup_le fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih => grw [pow_succ, ← mul_assoc m (l ^ n) l, ih, h]

/-- **Arden's lemma** -/
/-
**Language.self_eq_mul_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Language`。
形式化陈述：self_eq_mul_add_iff {l m n : Language α} (hm : [] ∉ m) : l = m * l + n ↔ l
 = m∗ * n where mp h
参数：hm : [] ∉ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Language.mem_mul`：mem_mul : x in l * m ↔ exists a in l, exists b in m, a
 ++ b = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Language.one_add_self_mul_kstar_eq_kstar`：one_add_self_mul_kstar_eq_ksta
r (l : Language α) : 1 + l * l∗ = l∗
· 使用定理 `one_add_mul`：one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b =
 b + a * b
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Nat.lt_add_left_iff_pos`：∀ {n k : ℕ}, n < k + n ↔ 0 < k
· 使用定理 `Language.nil_mem_kstar`：nil_mem_kstar (l : Language α) : [] in l∗
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `Language.kstar_eq_iSup_pow`：kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ 
i : Nat, l ^ i
· 使用定理 `Language.iSup_mul`：iSup_mul {ι : Sort v} (l : ι -> Language α) (m : Lang
uage α) : (⨆ i, l i) * m = ⨆ i, l i * m
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `IdemSemiring.toCanonicallyOrderedAdd`：∀ {α : Type u_1} [inst : IdemSemir
ing α], CanonicallyOrderedAdd α
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Language.instMulLeftMono`：∀ {α : Type u_1}, MulLeftMono (Language α)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**Arden's lemma**
-/
theorem self_eq_mul_add_iff {l m n : Language α} (hm : [] ∉ m) : l = m * l + n ↔ l = m∗ * n where
  mp h := by
    apply le_antisymm
    · intro x hx
      induction hlen : x.length using Nat.strong_induction_on generalizing x with | _ _ ih
      subst hlen
      rw [h] at hx
      obtain hx | hx := hx
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hx
        rw [length_append] at ih
        have hal : 0 < a.length := length_pos_iff.mpr <| ne_of_mem_of_not_mem ha hm
        specialize ih b.length (Nat.lt_add_left_iff_pos.mpr hal) hb rfl
        rw [← one_add_self_mul_kstar_eq_kstar, one_add_mul, mul_assoc]
        right
        exact ⟨_, ha, _, ih, rfl⟩
      · exact ⟨[], nil_mem_kstar _, _, ⟨hx, nil_append _⟩⟩
    · rw [kstar_eq_iSup_pow, iSup_mul, iSup_le_iff]
      intro i
      induction i with rw [h]
      | zero =>
        rw [pow_zero, one_mul, add_comm]
        exact le_self_add
      | succ _ ih =>
        grw [add_comm, pow_add, pow_one, mul_assoc, ih]
        exact le_self_add
  mpr h := by rw [h, add_comm, ← mul_assoc, ← one_add_mul, one_add_self_mul_kstar_eq_kstar]

/-- Language `l.reverse` is defined as the set of words from `l` backwards. -/
/-
**Language.reverse** 是 Mathlib 中的一个定义，位于命名空间 `Language`。
形式化陈述：reverse (l : Language α) : Language α
参数：l : Language α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Language `l.reverse` is defined as the set of words from `l` backwards.
-/
def reverse (l : Language α) : Language α := { w : List α | w.reverse ∈ l }

@[simp]
/-
**Language.mem_reverse** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：mem_reverse : a in l.reverse ↔ a.reverse in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_reverse : a ∈ l.reverse ↔ a.reverse ∈ l := Iff.rfl
/-
**Language.reverse_mem_reverse** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_mem_reverse : a.reverse in l.reverse ↔ a in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Language.mem_reverse`：mem_reverse : a in l.reverse ↔ a.reverse in l
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma reverse_mem_reverse : a.reverse ∈ l.reverse ↔ a ∈ l := by
  rw [mem_reverse, List.reverse_reverse]
/-
**Language.reverse_eq_image** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_eq_image (l : Language α) : l.reverse = List.reverse '' l
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_involutive`：reverse_involutive : Involutive (@reverse α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
lemma reverse_eq_image (l : Language α) : l.reverse = List.reverse '' l :=
  ((List.reverse_involutive.toPerm _).image_eq_preimage_symm _).symm

@[simp]
/-
**Language.reverse_zero** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_zero : (0 : Language α).reverse = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reverse_zero : (0 : Language α).reverse = 0 := rfl

@[simp]
/-
**Language.reverse_one** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_one : (1 : Language α).reverse = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reverse_one : (1 : Language α).reverse = 1 := by
  simp [reverse, ← one_def]
/-
**Language.reverse_involutive** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_involutive : Function.Involutive (reverse : Language α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.preimage`：∀ {α : Type u_1} {f : α → α}, Function.Inv
olutive f → Function.Involutive (Set.preimage f)
· 使用定理 `List.reverse_involutive`：reverse_involutive : Involutive (@reverse α)
-/
lemma reverse_involutive : Function.Involutive (reverse : Language α → _) :=
  List.reverse_involutive.preimage
/-
**Language.reverse_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_bijective : Function.Bijective (reverse : Language α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用引理 `Language.reverse_involutive`：reverse_involutive : Function.Involutive (r
everse : Language α -> _)
-/
lemma reverse_bijective : Function.Bijective (reverse : Language α → _) :=
  reverse_involutive.bijective
/-
**Language.reverse_injective** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_injective : Function.Injective (reverse : Language α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用引理 `Language.reverse_involutive`：reverse_involutive : Function.Involutive (r
everse : Language α -> _)
-/
lemma reverse_injective : Function.Injective (reverse : Language α → _) :=
  reverse_involutive.injective
/-
**Language.reverse_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_surjective : Function.Surjective (reverse : Language α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用引理 `Language.reverse_involutive`：reverse_involutive : Function.Involutive (r
everse : Language α -> _)
-/
lemma reverse_surjective : Function.Surjective (reverse : Language α → _) :=
  reverse_involutive.surjective

@[simp]
/-
**Language.reverse_reverse** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_reverse (l : Language α) : l.reverse.reverse = l
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Language.reverse_involutive`：reverse_involutive : Function.Involutive (r
everse : Language α -> _)
-/
lemma reverse_reverse (l : Language α) : l.reverse.reverse = l := reverse_involutive l

@[simp]
/-
**Language.reverse_add** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_add (l m : Language α) : (l + m).reverse = l.reverse + m.reverse
参数：l m : Language α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reverse_add (l m : Language α) : (l + m).reverse = l.reverse + m.reverse := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Language.reverse_mul** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_mul (l m : Language α) : (l * m).reverse = m.reverse * l.reverse
参数：l m : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Language.reverse_eq_image`：reverse_eq_image (l : Language α) : l.reverse
 = List.reverse '' l
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
-/
lemma reverse_mul (l m : Language α) : (l * m).reverse = m.reverse * l.reverse := by
  simp only [mul_def, reverse_eq_image, image2_image_left, image2_image_right, image_image2,
    List.reverse_append]
  apply image2_swap

@[simp]
/-
**Language.reverse_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_iSup {ι : Sort*} (l : ι -> Language α) : (⨆ i, l i).reverse = ⨆ i,
 (l i).reverse
参数：l : ι -> Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
-/
lemma reverse_iSup {ι : Sort*} (l : ι → Language α) : (⨆ i, l i).reverse = ⨆ i, (l i).reverse :=
  preimage_iUnion

@[simp]
/-
**Language.reverse_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_iInf {ι : Sort*} (l : ι -> Language α) : (⨅ i, l i).reverse = ⨅ i,
 (l i).reverse
参数：l : ι -> Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
-/
lemma reverse_iInf {ι : Sort*} (l : ι → Language α) : (⨅ i, l i).reverse = ⨅ i, (l i).reverse :=
  preimage_iInter

variable (α) in
/-- `Language.reverse` as a ring isomorphism to the opposite ring. -/
@[simps]
/-
**Language.reverseIso** 是 Mathlib 中的一个定义，位于命名空间 `Language`。
形式化陈述：reverseIso : Language α ≃+* (Language α)ᵐᵒᵖ where toFun l
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Language.reverse_reverse`：reverse_reverse (l : Language α) : l.reverse.r
everse = l

--- 原说明 ---
`Language.reverse` as a ring isomorphism to the opposite ring.
-/
def reverseIso : Language α ≃+* (Language α)ᵐᵒᵖ where
  toFun l := .op l.reverse
  invFun l' := l'.unop.reverse
  left_inv := reverse_reverse
  right_inv l' := MulOpposite.unop_injective <| reverse_reverse l'.unop
  map_mul' l₁ l₂ := MulOpposite.unop_injective <| reverse_mul l₁ l₂
  map_add' l₁ l₂ := MulOpposite.unop_injective <| reverse_add l₁ l₂

@[simp]
/-
**Language.reverse_pow** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_pow (l : Language α) (n : Nat) : (l ^ n).reverse = l.reverse ^ n
参数：l : Language α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma reverse_pow (l : Language α) (n : ℕ) : (l ^ n).reverse = l.reverse ^ n :=
  MulOpposite.op_injective (map_pow (reverseIso α) l n)

@[simp]
/-
**Language.reverse_kstar** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：reverse_kstar (l : Language α) : l∗.reverse = l.reverse∗
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Language.kstar_eq_iSup_pow`：kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ 
i : Nat, l ^ i
· 使用引理 `Language.reverse_iSup`：reverse_iSup {ι : Sort*} (l : ι -> Language α) : 
(⨆ i, l i).reverse = ⨆ i, (l i).reverse
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Language.reverse_pow`：reverse_pow (l : Language α) (n : Nat) : (l ^ n).r
everse = l.reverse ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reverse_kstar (l : Language α) : l∗.reverse = l.reverse∗ := by
  simp only [kstar_eq_iSup_pow, reverse_iSup, reverse_pow]

@[simp]
/-
**Language.mem_inf** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：mem_inf {x : List α} {l m : Language α} : x in l ⊓ m ↔ x in l ∧ x in m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
-/
lemma mem_inf {x : List α} {l m : Language α} : x ∈ l ⊓ m ↔ x ∈ l ∧ x ∈ m := by
  apply Set.mem_inter_iff
/-
**Language.compl_compl** 是 Mathlib 中的一个引理，位于命名空间 `Language`。
形式化陈述：compl_compl (l : Language α) : lᶜᶜ = l
参数：l : Language α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma compl_compl (l : Language α) : lᶜᶜ = l :=
  _root_.compl_compl l

end Language

/-- Symbols for use by all kinds of grammars. -/
/-
**Symbol** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_5 → Type (max u_4 u_5)
参数：max u_4 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Symbols for use by all kinds of grammars.
-/
inductive Symbol (T N : Type*)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr, Fintype

attribute [nolint docBlame] Symbol.proxyType Symbol.proxyTypeEquiv
