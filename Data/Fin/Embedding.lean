/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Embedding.Basic

/-!
# Embeddings of `Fin n`

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file defines embeddings between `Fin n` and other types,

## Main definitions

* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.succEmb` : `Fin.succ` as an `Embedding`;
* `Fin.castLEEmb h` : `Fin.castLE` as an `Embedding`, embed `Fin n` into `Fin m`, `h : n ≤ m`;
* `Fin.castAddEmb m` : `Fin.castAdd` as an `Embedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccEmb` : `Fin.castSucc` as an `Embedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatEmb m i` : `Fin.addNat` as an `Embedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddEmb n i` : `Fin.natAdd` as an `Embedding`, adds `n` on `i` on the left;

-/

@[expose] public section

assert_not_exists Monoid Finset

open Fin Nat Function

namespace Fin

variable {n m : ℕ}

section Order

/-!
### order
-/

/-- The inclusion map `Fin n → ℕ` is an embedding. -/
@[simps -fullyApplied apply]
/-
**Fin.valEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：valEmbedding : Fin n ↪ Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)

--- 原说明 ---
The inclusion map `Fin n → ℕ` is an embedding.
-/
def valEmbedding : Fin n ↪ ℕ :=
  ⟨val, val_injective⟩

@[simp]
/-
**Fin.equivSubtype_symm_trans_valEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：equivSubtype_symm_trans_valEmbedding : equivSubtype.symm.toEmbedding.trans
 valEmbedding = Embedding.subtype (· < n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivSubtype_symm_trans_valEmbedding :
    equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n) :=
  rfl

end Order

section Succ

/-!
### succ and casts into larger Fin types
-/

/-- `Fin.succ` as an `Embedding` -/
/-
**Fin.succEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：succEmb (n : Nat) : Fin n ↪ Fin (n + 1) where toFun
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)

--- 原说明 ---
`Fin.succ` as an `Embedding`
-/
def succEmb (n : ℕ) : Fin n ↪ Fin (n + 1) where
  toFun := succ
  inj' := succ_injective _

@[simp]
/-
**Fin.coe_succEmb** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_succEmb : ⇑(succEmb n) = Fin.succ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_succEmb : ⇑(succEmb n) = Fin.succ :=
  rfl

attribute [simp] castSucc_inj

/-- `Fin.castLE` as an `Embedding`, `castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps apply]
/-
**Fin.castLEEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castLEEmb (h : n <= m) : Fin n ↪ Fin m where toFun
参数：h : n <= m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.castLE_injective`：castLE_injective (hmn : m <= n) : Injective (castL
E hmn)

--- 原说明 ---
`Fin.castLE` as an `Embedding`, `castLEEmb h i` embeds `i` into a larger `Fin` t
ype.
-/
def castLEEmb (h : n ≤ m) : Fin n ↪ Fin m where
  toFun := castLE h
  inj' := castLE_injective _
/-
**Fin.coe_castLEEmb** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {m n : ℕ} (hmn : m ≤ n), ⇑(Fin.castLEEmb hmn) = Fin.castLE hmn
参数：hmn : m ≤ n；Fin.castLEEmb hmn。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_castLEEmb {m n} (hmn : m ≤ n) : castLEEmb hmn = castLE hmn := rfl

/- The next proof can be golfed a lot using `Fintype.card`.
It is written this way to define `ENat.card` and `Nat.card` without a `Fintype` dependency
(not done yet). -/
/-
**Fin.nonempty_embedding_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：nonempty_embedding_iff : Nonempty (Fin n ↪ Fin m) ↔ n <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.pos_iff_nonempty`：∀ {n : ℕ}, 0 < n ↔ Nonempty (Fin n)
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Embedding.setValue_eq_iff`：setValue_eq_iff {α β} (f : α ↪ β) {a
 a' : α} {b : β} [forall a', Decidable (a' = a)] [forall a', Decidable (f a' = b
)] : setValue f a b a' =…
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The next proof can be golfed a lot using `Fintype.card`.
It is written this way to define `ENat.card` and `Nat.card` without a `Fintype` 
dependency
(not done yet).
-/
lemma nonempty_embedding_iff : Nonempty (Fin n ↪ Fin m) ↔ n ≤ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨castLEEmb h⟩⟩
  induction n generalizing m with
  | zero => exact m.zero_le
  | succ n ihn =>
    obtain ⟨e⟩ := h
    rcases exists_eq_succ_of_ne_zero (pos_iff_nonempty.2 (Nonempty.map e inferInstance)).ne'
      with ⟨m, rfl⟩
    refine Nat.succ_le_succ <| ihn ⟨?_⟩
    refine ⟨fun i ↦ (e.setValue 0 0 i.succ).pred (mt e.setValue_eq_iff.1 i.succ_ne_zero),
      fun i j h ↦ ?_⟩
    simpa only [pred_inj, EmbeddingLike.apply_eq_iff_eq, succ_inj] using h
/-
**Fin.equiv_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.nonempty_embedding_iff`：nonempty_embedding_iff : Nonempty (Fin n ↪ F
in m) ↔ n <= m
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
lemma equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n :=
  ⟨fun ⟨e⟩ ↦ le_antisymm (nonempty_embedding_iff.1 ⟨e⟩) (nonempty_embedding_iff.1 ⟨e.symm⟩),
    fun h ↦ h ▸ ⟨.refl _⟩⟩

/-- `Fin.castAdd` as an `Embedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
/-
**Fin.castAddEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castAddEmb (m) : Fin n ↪ Fin (n + m)
参数：m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
`Fin.castAdd` as an `Embedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+
m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`.
-/
def castAddEmb (m) : Fin n ↪ Fin (n + m) := castLEEmb (le_add_right n m)

@[simp]
/-
**Fin.coe_castAddEmb** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：coe_castAddEmb (m) : (castAddEmb m : Fin n -> Fin (n + m)) = castAdd m
参数：m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_castAddEmb (m) : (castAddEmb m : Fin n → Fin (n + m)) = castAdd m := rfl
/-
**Fin.castAddEmb_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castAddEmb_apply (m) (i : Fin n) : castAddEmb m i = castAdd m i
参数：m；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma castAddEmb_apply (m) (i : Fin n) : castAddEmb m i = castAdd m i := rfl

/-- `Fin.castSucc` as an `Embedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
/-
**Fin.castSuccEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castSuccEmb : Fin n ↪ Fin (n + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.castSucc` as an `Embedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+
1)`.
-/
def castSuccEmb : Fin n ↪ Fin (n + 1) := castAddEmb _
/-
**Fin.coe_castSuccEmb** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, ⇑Fin.castSuccEmb = Fin.castSucc
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_castSuccEmb : (castSuccEmb : Fin n → Fin (n + 1)) = Fin.castSucc := rfl
/-
**Fin.castSuccEmb_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castSuccEmb_apply (i : Fin n) : castSuccEmb i = i.castSucc
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma castSuccEmb_apply (i : Fin n) : castSuccEmb i = i.castSucc := rfl

/-- `Fin.addNat` as an `Embedding`, `addNatEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply]
/-
**Fin.addNatEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：addNatEmb (m) : Fin n ↪ Fin (n + m) where toFun
参数：m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.addNat` as an `Embedding`, `addNatEmb m i` adds `m` to `i`, generalizes `Fi
n.succ`.
-/
def addNatEmb (m) : Fin n ↪ Fin (n + m) where
  toFun := (addNat · m)
  inj' a b := by simp [Fin.ext_iff]

/-- `Fin.natAdd` as an `Embedding`, `natAddEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply]
/-
**Fin.natAddEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：natAddEmb (n) {m} : Fin m ↪ Fin (n + m) where toFun
参数：n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.natAdd` as an `Embedding`, `natAddEmb n i` adds `n` to `i` "on the left".
-/
def natAddEmb (n) {m} : Fin m ↪ Fin (n + m) where
  toFun := natAdd n
  inj' a b := by simp [Fin.ext_iff]

end Succ

section SuccAbove

variable {p : Fin (n + 1)}

/-- `Fin.succAbove p` as an `Embedding`. -/
@[simps!]
/-
**Fin.succAboveEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：succAboveEmb (p : Fin (n + 1)) : Fin n ↪ Fin (n + 1)
参数：p : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_right_injective`：succAbove_right_injective : Injective p.s
uccAbove

--- 原说明 ---
`Fin.succAbove p` as an `Embedding`.
-/
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪ Fin (n + 1) := ⟨p.succAbove, succAbove_right_injective⟩
/-
**Fin.coe_succAboveEmb** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (p : Fin (n + 1)), ⇑p.succAboveEmb = p.succAbove
参数：p : Fin (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_succAboveEmb (p : Fin (n + 1)) : p.succAboveEmb = p.succAbove := rfl

/-- `Fin.natAdd_castLEEmb` as an `Embedding` from `Fin n` to `Fin m`, by appending the former
at the end of the latter.
`natAdd_castLEEmb hmn i` maps `i : Fin m` to `i + (m - n) : Fin n` by adding `m - n` to `i` -/
@[simps!]
/-
**Fin.natAdd_castLEEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：natAdd_castLEEmb (hmn : n <= m) : Fin n ↪ Fin m
参数：hmn : n <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.natAdd_castLEEmb` as an `Embedding` from `Fin n` to `Fin m`, by appending t
he former
at the end of the latter.
`natAdd_castLEEmb hmn i` maps `i : Fin m` to `i + (m - n) : Fin n` by adding `m 
- n` to `i`
-/
def natAdd_castLEEmb (hmn : n ≤ m) : Fin n ↪ Fin m :=
  (addNatEmb (m - n)).trans (finCongr (by lia)).toEmbedding
/-
**Fin.range_natAdd_castLEEmb** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：range_natAdd_castLEEmb {n m : Nat} (hmn : n <= m) : Set.range (natAdd_cast
LEEmb hmn) = {i | m - n <= i.1}
参数：hmn : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `Nat.sub_le_of_le_add`：∀ {a b c : ℕ}, a ≤ c + b → a - b ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.addNat_subNat`：∀ {n m : ℕ} {i : Fin (n + m)} (h : m ≤ ↑i), (Fin.subN
at m i h).addNat m = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_natAdd_castLEEmb {n m : ℕ} (hmn : n ≤ m) :
    Set.range (natAdd_castLEEmb hmn) = {i | m - n ≤ i.1} := by
  simp only [natAdd_castLEEmb, Nat.sub_le_iff_le_add]
  ext y
  exact ⟨fun ⟨x, hx⟩ ↦ by simp [← hx]; lia,
    fun xin ↦ ⟨subNat (m - n) (y.cast (Nat.add_sub_of_le hmn).symm)
    (Nat.sub_le_of_le_add xin), by simp⟩⟩

end SuccAbove

end Fin

