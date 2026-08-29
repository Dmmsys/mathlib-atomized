/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Logic.Encodable.Basic

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `Encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/

@[expose] public section

assert_not_exists Monoid

variable {α β : Type*}

/--
Definition of `Denumerable` / `Denumerable` 的定义

English:
class Denumerable
  parameters: (α : Type*)
  extends: Encodable α
  axioms and operations (1):
    - decode_inv : forall n, exists a in decode n, encode a = n

中文:
类 可枚举
  参数: (α : 类型)
  继承: 可编码 α
  公理与运算 (1 个):
    - decode_inv : 对任意 n, 存在 a in decode n, encode a = n
-/
class Denumerable (α : Type*) extends Encodable α where
  /-- `decode` and `encode` are inverses. -/
  decode_inv : forall n, exists a in decode n, encode a = n

open Finset Nat

namespace Denumerable

section

variable [Denumerable α] [Denumerable β]

open Encodable

/--
theorem `decode_isSome` / 定理 `decode_isSome`

English:
theorem decode_isSome
  given: (α) [Denumerable α] (n : Nat)
  statement: (decode (α := α) n).isSome
  proof: Option.isSome_iff_exists.2 (decode_inv n).imp fun _ => And.left

中文:
定理 decode_isSome
  条件: (α) [可枚举 α] (n : 自然数)
  结论: (decode (α := α) n).isSome
  证明: Option.isSome_iff_exists.2 (decode_inv n).imp fun _ => And.left

Depends on / 依赖: isSome
-/
theorem decode_isSome (α) [Denumerable α] (n : Nat) : (decode (α := α) n).isSome :=
Option.isSome_iff_exists.2 (decode_inv n).imp fun _ => And.left

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: (α) [Denumerable α] (n : Nat)
  body: Option.get _ (decode_isSome α n)

@[simp]

中文:
定义 of自然数
  签名: (α) [可枚举 α] (n : 自然数)
  定义体: Option.get _ (decode_isSome α n)

@[simp]

Depends on / 依赖: Option.get, decode_isSome
-/
def ofNat (α) [Denumerable α] (n : Nat) : α :=
  Option.get _ (decode_isSome α n)

@[simp]
/--
theorem `decode_eq_ofNat` / 定理 `decode_eq_ofNat`

English:
theorem decode_eq_ofNat
  given: (α) [Denumerable α] (n : Nat)
  statement: decode (α := α) n = some (ofNat α n)
  proof: Option.eq_some_of_isSome _

中文:
定理 decode_eq_of自然数
  条件: (α) [可枚举 α] (n : 自然数)
  结论: decode (α := α) n = some (of自然数 α n)
  证明: Option.eq_some_of_isSome _
-/
theorem decode_eq_ofNat (α) [Denumerable α] (n : Nat) : decode (α := α) n = some (ofNat α n) :=
  Option.eq_some_of_isSome _

/--
theorem `ofNat_of_decode` / 定理 `ofNat_of_decode`

English:
theorem ofNat_of_decode
  given: {n b} (h : decode (α := α) n = some b)
  statement: ofNat (α := α) n = b
  proof: by
  simpa using h

@[simp]

中文:
定理 of自然数_of_decode
  条件: {n b} (h : decode (α := α) n = some b)
  结论: of自然数 (α := α) n = b
  证明: by
  simpa using h

@[simp]
-/
theorem ofNat_of_decode {n b} (h : decode (α := α) n = some b) : ofNat (α := α) n = b := by
  simpa using h

@[simp]
/--
theorem `encode_ofNat` / 定理 `encode_ofNat`

English:
theorem encode_ofNat
  given: (n)
  statement: encode (ofNat α n) = n
  proof: by
  obtain ⟨a, h, e⟩ := decode_inv (α := α) n
  rwa [ofNat_of_decode h]

@[simp]

中文:
定理 encode_of自然数
  条件: (n)
  结论: encode (of自然数 α n) = n
  证明: by
  obtain ⟨a, h, e⟩ := decode_inv (α := α) n
  rwa [ofNat_of_decode h]

@[simp]

Depends on / 依赖: decode_inv, ofNat_of_decode
-/
theorem encode_ofNat (n) : encode (ofNat α n) = n := by
  obtain ⟨a, h, e⟩ := decode_inv (α := α) n
  rwa [ofNat_of_decode h]

@[simp]
/--
theorem `ofNat_encode` / 定理 `ofNat_encode`

English:
theorem ofNat_encode
  given: (a)
  statement: ofNat α (encode a) = a
  proof: ofNat_of_decode (encodek _)

中文:
定理 of自然数_encode
  条件: (a)
  结论: of自然数 α (encode a) = a
  证明: ofNat_of_decode (encodek _)

Depends on / 依赖: encodek, ofNat_of_decode
-/
theorem ofNat_encode (a) : ofNat α (encode a) = a :=
  ofNat_of_decode (encodek _)

/--
Definition of `eqv` / `eqv` 的定义

English:
definition eqv
  signature: (α) [Denumerable α]
  body: ⟨encode, ofNat α, ofNat_encode, encode_ofNat⟩

中文:
定义 eqv
  签名: (α) [可枚举 α]
  定义体: ⟨encode, ofNat α, ofNat_encode, encode_ofNat⟩

Depends on / 依赖: encode, encode_ofNat, ofNat_encode
-/
def eqv (α) [Denumerable α] : α ≃ Nat :=
  ⟨encode, ofNat α, ofNat_encode, encode_ofNat⟩

-- See Note [lower instance priority]
instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).surjective

/-- A type equivalent to `ℕ` is denumerable. -/
@[instance_reducible]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {α} (e : α ≃ Nat)
  body: e
  decode := some ∘ e.symm
  encodek _ := congr_arg some (e.symm_apply_apply _)
  decode_inv _ := ⟨_, rfl, e.apply_symm_apply _⟩

中文:
定义 mk'
  签名: {α} (e : α ≃ 自然数)
  定义体: e
  decode := some ∘ e.symm
  encodek _ := congr_arg some (e.symm_apply_apply _)
  decode_inv _ := ⟨_, rfl, e.apply_symm_apply _⟩
-/
def mk' {α} (e : α ≃ Nat) : Denumerable α where
  encode := e
  decode := some ∘ e.symm
  encodek _ := congr_arg some (e.symm_apply_apply _)
  decode_inv _ := ⟨_, rfl, e.apply_symm_apply _⟩

/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (α) {β} [Denumerable α] (e : β ≃ α)
  body: { Encodable.ofEquiv _ e with
    decode_inv := fun n => by
      simp [decode_ofEquiv, encode_ofEquiv] }

@[simp]

中文:
定义 ofEquiv
  签名: (α) {β} [可枚举 α] (e : β ≃ α)
  定义体: { Encodable.ofEquiv _ e with
    decode_inv := fun n => by
      simp [decode_ofEquiv, encode_ofEquiv] }

@[simp]

Depends on / 依赖: Encodable, Encodable.ofEquiv, decode_inv, decode_ofEquiv, encode_ofEquiv, ofEquiv
-/
def ofEquiv (α) {β} [Denumerable α] (e : β ≃ α) : Denumerable β :=
  { Encodable.ofEquiv _ e with
    decode_inv := fun n => by
      simp [decode_ofEquiv, encode_ofEquiv] }

@[simp]
/--
theorem `ofEquiv_ofNat` / 定理 `ofEquiv_ofNat`

English:
theorem ofEquiv_ofNat
  given: (α) {β} [Denumerable α] (e : β ≃ α) (n)
  proof: by
  let := ofEquiv _ e
  refine ofNat_of_decode ?_
  rw [decode_ofEquiv e]
  simp

中文:
定理 ofEquiv_of自然数
  条件: (α) {β} [可枚举 α] (e : β ≃ α) (n)
  证明: by
  let := ofEquiv _ e
  refine ofNat_of_decode ?_
  rw [decode_ofEquiv e]
  simp

Depends on / 依赖: decode_ofEquiv, ofEquiv, ofNat_of_decode
-/
theorem ofEquiv_ofNat (α) {β} [Denumerable α] (e : β ≃ α) (n) :
    @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n) := by
  let := ofEquiv _ e
  refine ofNat_of_decode ?_
  rw [decode_ofEquiv e]
  simp

/--
Definition of `equiv₂` / `equiv₂` 的定义

English:
definition equiv₂
  signature: (α β) [Denumerable α] [Denumerable β]
  body: (eqv α).trans (eqv β).symm

中文:
定义 equiv₂
  签名: (α β) [可枚举 α] [可枚举 β]
  定义体: (eqv α).trans (eqv β).symm
-/
def equiv₂ (α β) [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm

/--
Instance `nat` / 实例 `nat`

English:
instance nat
  signature: : Denumerable Nat
  body: ⟨fun _ => ⟨_, rfl, rfl⟩⟩

@[simp]

中文:
实例 nat
  签名: : 可枚举 自然数
  定义体: ⟨fun _ => ⟨_, rfl, rfl⟩⟩

@[simp]
-/
instance nat : Denumerable Nat :=
  ⟨fun _ => ⟨_, rfl, rfl⟩⟩

@[simp]
/--
theorem `ofNat_nat` / 定理 `ofNat_nat`

English:
theorem ofNat_nat
  given: (n)
  statement: ofNat Nat n = n
  proof: rfl

中文:
定理 of自然数_nat
  条件: (n)
  结论: of自然数 自然数 n = n
  证明: rfl
-/
theorem ofNat_nat (n) : ofNat Nat n = n :=
  rfl

/--
Instance `option` / 实例 `option`

English:
instance option
  signature: : Denumerable (Option α)
  body: ⟨fun n => by
    cases n with
    | zero =>
      refine ⟨none, ?_, encode_none⟩
      rw [decode_option_zero]; rw [Option.mem_def]
    | succ n =>
      refine ⟨some (ofNat α n), ?_, ?_⟩
      · rw [decode_option_succ, decode_eq_ofNat, Option.map_some, Option.mem_def]
      rw [encode_some]; rw [encode_ofNat]⟩

中文:
实例 option
  签名: : 可枚举 (选项类型 α)
  定义体: ⟨fun n => by
    cases n with
    | zero =>
      refine ⟨none, ?_, encode_none⟩
      rw [decode_option_zero]; rw [Option.mem_def]
    | succ n =>
      refine ⟨some (ofNat α n), ?_, ?_⟩
      · rw [decode_option_succ, decode_eq_ofNat, Option.map_some, Option.mem_def]
      rw [encode_some]; rw [encode_ofNat]⟩

Depends on / 依赖: Option.map_some, Option.mem_def, decode_eq_ofNat, decode_option_succ, decode_option_zero, encode_none, encode_ofNat, encode_some, map_some, mem_def
-/
instance option : Denumerable (Option α) :=
  ⟨fun n => by
    cases n with
    | zero =>
      refine ⟨none, ?_, encode_none⟩
      rw [decode_option_zero]; rw [Option.mem_def]
    | succ n =>
      refine ⟨some (ofNat α n), ?_, ?_⟩
      · rw [decode_option_succ, decode_eq_ofNat, Option.map_some, Option.mem_def]
      rw [encode_some]; rw [encode_ofNat]⟩

/--
Instance `sum` / 实例 `sum`

English:
instance sum
  signature: : Denumerable (α oplus β)
  body: ⟨fun n => by
    suffices exists a in @decodeSum α β _ _ n, encodeSum a = bit (bodd n) (div2 n) by
      simpa [bit_bodd_div2]
    simp only [decodeSum, decode_eq_ofNat, Option.map_some, Sum.exists]
    cases bodd n <;> simp [bit_val, encodeSum]⟩

中文:
实例 求和
  签名: : 可枚举 (α oplus β)
  定义体: ⟨fun n => by
    suffices exists a in @decodeSum α β _ _ n, encodeSum a = bit (bodd n) (div2 n) by
      simpa [bit_bodd_div2]
    simp only [decodeSum, decode_eq_ofNat, Option.map_some, Sum.exists]
    cases bodd n <;> simp [bit_val, encodeSum]⟩

Depends on / 依赖: Option.map_some, Sum.exists, bit_bodd_div2, bit_val, decodeSum, decode_eq_ofNat, encodeSum, map_some
-/
instance sum : Denumerable (α oplus β) :=
  ⟨fun n => by
    suffices exists a in @decodeSum α β _ _ n, encodeSum a = bit (bodd n) (div2 n) by
      simpa [bit_bodd_div2]
    simp only [decodeSum, decode_eq_ofNat, Option.map_some, Sum.exists]
    cases bodd n <;> simp [bit_val, encodeSum]⟩

section Sigma

variable {γ : α -> Type*} [forall a, Denumerable (γ a)]

/--
Instance `sigma` / 实例 `sigma`

English:
instance sigma
  signature: : Denumerable (Sigma γ)
  body: ⟨fun n => by simp⟩

@[simp]

中文:
实例 sigma
  签名: : 可枚举 (依赖和类型 γ)
  定义体: ⟨fun n => by simp⟩

@[simp]
-/
instance sigma : Denumerable (Sigma γ) :=
  ⟨fun n => by simp⟩

@[simp]
/--
theorem `sigma_ofNat_val` / 定理 `sigma_ofNat_val`

English:
theorem sigma_ofNat_val
  given: (n : Nat)
  proof: Option.some.inj by rw [← decode_eq_ofNat, decode_sigma_val]; simp

中文:
定理 sigma_of自然数_val
  条件: (n : 自然数)
  证明: Option.some.inj by rw [← decode_eq_ofNat, decode_sigma_val]; simp

Depends on / 依赖: Option.some.inj, decode_eq_ofNat, decode_sigma_val
-/
theorem sigma_ofNat_val (n : Nat) :
    ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩ :=
Option.some.inj by rw [← decode_eq_ofNat, decode_sigma_val]; simp

end Sigma

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: : Denumerable (α × β)
  body: ofEquiv _ (Equiv.sigmaEquivProd α β).symm

中文:
实例 乘积
  签名: : 可枚举 (α × β)
  定义体: ofEquiv _ (Equiv.sigmaEquivProd α β).symm

Depends on / 依赖: Equiv.sigmaEquivProd, ofEquiv, sigmaEquivProd
-/
instance prod : Denumerable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm

/--
theorem `prod_ofNat_val` / 定理 `prod_ofNat_val`

English:
theorem prod_ofNat_val
  given: (n : Nat)
  proof: by simp

@[simp]

中文:
定理 prod_of自然数_val
  条件: (n : 自然数)
  证明: by simp

@[simp]
-/
theorem prod_ofNat_val (n : Nat) :
    ofNat (α × β) n = (ofNat α (unpair n).1, ofNat β (unpair n).2) := by simp

@[simp]
/--
theorem `prod_nat_ofNat` / 定理 `prod_nat_ofNat`

English:
theorem prod_nat_ofNat
  statement: ofNat (Nat × Nat) = unpair
  proof: by funext; simp

中文:
定理 prod_nat_of自然数
  结论: of自然数 (自然数 × 自然数) = unpair
  证明: by funext; simp
-/
theorem prod_nat_ofNat : ofNat (Nat × Nat) = unpair := by funext; simp

/--
Instance `int` / 实例 `int`

English:
instance int
  signature: : Denumerable Int
  body: fast_instance% Denumerable.mk' Equiv.intEquivNat

中文:
实例 int
  签名: : 可枚举 整数
  定义体: fast_instance% Denumerable.mk' Equiv.intEquivNat

Depends on / 依赖: Denumerable, Denumerable.mk, Equiv.intEquivNat, fast_instance, intEquivNat
-/
instance int : Denumerable Int :=
  fast_instance% Denumerable.mk' Equiv.intEquivNat

/--
Instance `pnat` / 实例 `pnat`

English:
instance pnat
  signature: : Denumerable Nat+
  body: fast_instance% Denumerable.mk' Equiv.pnatEquivNat

中文:
实例 pnat
  签名: : 可枚举 自然数+
  定义体: fast_instance% Denumerable.mk' Equiv.pnatEquivNat

Depends on / 依赖: Denumerable, Denumerable.mk, Equiv.pnatEquivNat, fast_instance, pnatEquivNat
-/
instance pnat : Denumerable Nat+ :=
  fast_instance% Denumerable.mk' Equiv.pnatEquivNat

/--
Instance `ulift` / 实例 `ulift`

English:
instance ulift
  signature: : Denumerable (ULift α)
  body: ofEquiv _ Equiv.ulift

中文:
实例 ulift
  签名: : 可枚举 (类型层提升 α)
  定义体: ofEquiv _ Equiv.ulift

Depends on / 依赖: Equiv.ulift, ofEquiv
-/
instance ulift : Denumerable (ULift α) :=
  ofEquiv _ Equiv.ulift

/--
Instance `plift` / 实例 `plift`

English:
instance plift
  signature: : Denumerable (PLift α)
  body: ofEquiv _ Equiv.plift

中文:
实例 plift
  签名: : 可枚举 (命题层提升 α)
  定义体: ofEquiv _ Equiv.plift

Depends on / 依赖: Equiv.plift, ofEquiv
-/
instance plift : Denumerable (PLift α) :=
  ofEquiv _ Equiv.plift

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: : α × α ≃ α
  body: equiv₂ _ _

中文:
定义 pair
  签名: : α × α ≃ α
  定义体: equiv₂ _ _
-/
def pair : α × α ≃ α :=
  equiv₂ _ _

end

end Denumerable

namespace Nat.Subtype

open Function Encodable

/-! ### Subsets of `ℕ` -/

variable {s : Set Nat} [Infinite s]

section Classical

/--
theorem `exists_succ` / 定理 `exists_succ`

English:
theorem exists_succ
  given: (x : s)
  statement: exists n, (x : Nat) + n + 1 in s
  proof: by
  by_contra h
  have (a : Nat) (ha : a in s) : a < x + 1 :=
    lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [Nat.add_right_comm, Nat.add_sub_cancel' hax]⟩
  classical
  exact Fintype.false
    ⟨(((Multiset.range (succ x)).filter (· in s)).pmap
      (fun (y : Nat) (hy : y in s) => Subtype.mk y hy) (by simp [-Multiset.range_succ])).toFinset,
      by simpa [Subtype.ext_iff, Multiset.mem_filter, -Multiset.range_succ] ⟩

中文:
定理 存在_succ
  条件: (x : s)
  结论: 存在 n, (x : 自然数) + n + 1 in s
  证明: by
  by_contra h
  have (a : Nat) (ha : a in s) : a < x + 1 :=
    lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [Nat.add_right_comm, Nat.add_sub_cancel' hax]⟩
  classical
  exact Fintype.false
    ⟨(((Multiset.range (succ x)).filter (· in s)).pmap
      (fun (y : Nat) (hy : y in s) => Subtype.mk y hy) (by simp [-Multiset.range_succ])).toFinset,
      by simpa [Subtype.ext_iff, Multiset.mem_filter, -Multiset.range_succ] ⟩

Depends on / 依赖: Fintype, Fintype.false, Multiset, Multiset.mem_filter, Multiset.range, Multiset.range_succ, Nat.add_right_comm, Nat.add_sub_cancel, Subtype, Subtype.ext_iff, Subtype.mk, add_right_comm, add_sub_cancel, classical, ext_iff, filter, lt_of_not_ge, mem_filter, range_succ, toFinset
-/
theorem exists_succ (x : s) : exists n, (x : Nat) + n + 1 in s := by
  by_contra h
  have (a : Nat) (ha : a in s) : a < x + 1 :=
    lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [Nat.add_right_comm, Nat.add_sub_cancel' hax]⟩
  classical
  exact Fintype.false
    ⟨(((Multiset.range (succ x)).filter (· in s)).pmap
      (fun (y : Nat) (hy : y in s) => Subtype.mk y hy) (by simp [-Multiset.range_succ])).toFinset,
      by simpa [Subtype.ext_iff, Multiset.mem_filter, -Multiset.range_succ] ⟩

end Classical

variable [DecidablePred (· in s)]

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: (x : s)
  body: have h : exists m, (x : Nat) + m + 1 in s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩

中文:
定义 succ
  签名: (x : s)
  定义体: have h : exists m, (x : Nat) + m + 1 in s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩

Depends on / 依赖: Nat.find, Nat.find_spec, exists_succ, find_spec
-/
def succ (x : s) : s :=
  have h : exists m, (x : Nat) + m + 1 in s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩

/--
theorem `succ_le_of_lt` / 定理 `succ_le_of_lt`

English:
theorem succ_le_of_lt
  given: {x y : s} (h : y < x)
  statement: succ y <= x
  proof: have hx : exists m, (y : Nat) + m + 1 in s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx <= k := Nat.find_min' _ (hk ▸ x.2)
  show (y : Nat) + Nat.find hx + 1 <= x by lia

中文:
定理 succ_le_of_lt
  条件: {x y : s} (h : y < x)
  结论: succ y <= x
  证明: have hx : exists m, (y : Nat) + m + 1 in s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx <= k := Nat.find_min' _ (hk ▸ x.2)
  show (y : Nat) + Nat.find hx + 1 <= x by lia

Depends on / 依赖: Nat.exists_eq_add_of_lt, Nat.find, Nat.find_min, exists_eq_add_of_lt, exists_succ, find_min
-/
theorem succ_le_of_lt {x y : s} (h : y < x) : succ y <= x :=
  have hx : exists m, (y : Nat) + m + 1 in s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx <= k := Nat.find_min' _ (hk ▸ x.2)
  show (y : Nat) + Nat.find hx + 1 <= x by lia

/--
theorem `le_succ_of_forall_lt_le` / 定理 `le_succ_of_forall_lt_le`

English:
theorem le_succ_of_forall_lt_le
  given: {x y : s} (h : forall z < x, z <= y)
  statement: x <= succ y
  proof: have hx : exists m, (y : Nat) + m + 1 in s := exists_succ _
  show (x : Nat) <= (y : Nat) + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
(h ⟨_, Nat.find_spec hx⟩ hxy).not_gt
        (by lia : (y : Nat) < (y : Nat) + Nat.find hx + 1)

中文:
定理 le_succ_of_对任意_lt_le
  条件: {x y : s} (h : 对任意 z < x, z <= y)
  结论: x <= succ y
  证明: have hx : exists m, (y : Nat) + m + 1 in s := exists_succ _
  show (x : Nat) <= (y : Nat) + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
(h ⟨_, Nat.find_spec hx⟩ hxy).not_gt
        (by lia : (y : Nat) < (y : Nat) + Nat.find hx + 1)

Depends on / 依赖: Nat.find, Nat.find_spec, exists_succ, find_spec, le_of_not_gt, not_gt
-/
theorem le_succ_of_forall_lt_le {x y : s} (h : forall z < x, z <= y) : x <= succ y :=
  have hx : exists m, (y : Nat) + m + 1 in s := exists_succ _
  show (x : Nat) <= (y : Nat) + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
(h ⟨_, Nat.find_spec hx⟩ hxy).not_gt
        (by lia : (y : Nat) < (y : Nat) + Nat.find hx + 1)

/--
theorem `lt_succ_self` / 定理 `lt_succ_self`

English:
theorem lt_succ_self
  given: (x : s)
  statement: x < succ x
  proof: calc
    (x : Nat) <= (x + _) := le_add_right ..
    _ < (succ x) := Nat.lt_succ_self (x + _)

中文:
定理 lt_succ_self
  条件: (x : s)
  结论: x < succ x
  证明: calc
    (x : Nat) <= (x + _) := le_add_right ..
    _ < (succ x) := Nat.lt_succ_self (x + _)

Depends on / 依赖: Nat.lt_succ_self, le_add_right, lt_succ_self
-/
theorem lt_succ_self (x : s) : x < succ x :=
  calc
    (x : Nat) <= (x + _) := le_add_right ..
    _ < (succ x) := Nat.lt_succ_self (x + _)

/--
theorem `lt_succ_iff_le` / 定理 `lt_succ_iff_le`

English:
theorem lt_succ_iff_le
  given: {x y : s}
  statement: x < succ y ↔ x <= y
  proof: ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩

中文:
定理 lt_succ_iff_le
  条件: {x y : s}
  结论: x < succ y ↔ x <= y
  证明: ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩

Depends on / 依赖: le_of_not_gt, lt_of_le_of_lt, lt_succ_self, not_le_of_gt, succ_le_of_lt
-/
theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x <= y :=
  ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: (s : Set Nat) [DecidablePred (· in s)] [Infinite s]

中文:
定义 of自然数
  签名: (s : 集合 自然数) [DecidablePred (· in s)] [无限 s]
-/
def ofNat (s : Set Nat) [DecidablePred (· in s)] [Infinite s] : Nat -> s
  | 0 => ⊥
  | n + 1 => succ (ofNat s n)

/--
theorem `ofNat_surjective` / 定理 `ofNat_surjective`

English:
theorem ofNat_surjective
  statement: Surjective (ofNat s)
  proof: ((List.range x).filter fun y => y in s).pmap
        (fun (y : Nat) (hy : y in s) => ⟨y, hy⟩)
        (by intro a ha; simpa using! (List.mem_filter.mp ha).2) with ht
    have hmt : forall {y : s}, y in t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff, ht]
    cases hmax : List.maximum t with
    | bot =>
      refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (a := (⊥ : s)) ?_)⟩
      rwa [← List.maximum_eq_bot.1 hmax, hmt]
    | coe m =>
      have wf : ↑m < x := by simpa using! hmt.mp (List.maximum_mem hmax)
      rcases ofNat_surjective m with ⟨a, rfl⟩
      refine ⟨a + 1, le_antisymm (succ_le_of_lt wf) ?_⟩
      exact le_succ_of_forall_lt_le fun z hz => List.le_maximum_of_mem (hmt.2 hz) hmax
  termination_by n => n.val

@[simp]

中文:
定理 of自然数_surjective
  结论: 满射 (of自然数 s)
  证明: ((List.range x).filter fun y => y in s).pmap
        (fun (y : Nat) (hy : y in s) => ⟨y, hy⟩)
        (by intro a ha; simpa using! (List.mem_filter.mp ha).2) with ht
    have hmt : forall {y : s}, y in t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff, ht]
    cases hmax : List.maximum t with
    | bot =>
      refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (a := (⊥ : s)) ?_)⟩
      rwa [← List.maximum_eq_bot.1 hmax, hmt]
    | coe m =>
      have wf : ↑m < x := by simpa using! hmt.mp (List.maximum_mem hmax)
      rcases ofNat_surjective m with ⟨a, rfl⟩
      refine ⟨a + 1, le_antisymm (succ_le_of_lt wf) ?_⟩
      exact le_succ_of_forall_lt_le fun z hz => List.le_maximum_of_mem (hmt.2 hz) hmax
  termination_by n => n.val

@[simp]

Depends on / 依赖: List.maximum, List.maximum_eq_bot, List.maximum_mem, List.mem_filter, List.mem_filter.mp, List.not_mem_nil, List.range, Subtype, Subtype.ext_iff, bot_le, ext_iff, filter, hmt.mp, le_antisymm, le_of_not_gt, maximum, maximum_eq_bot, maximum_mem, mem_filter, not_mem_nil
-/
theorem ofNat_surjective : Surjective (ofNat s)
  | ⟨x, hx⟩ => by
    set t : List s :=
      ((List.range x).filter fun y => y in s).pmap
        (fun (y : Nat) (hy : y in s) => ⟨y, hy⟩)
        (by intro a ha; simpa using! (List.mem_filter.mp ha).2) with ht
    have hmt : forall {y : s}, y in t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff, ht]
    cases hmax : List.maximum t with
    | bot =>
      refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (a := (⊥ : s)) ?_)⟩
      rwa [← List.maximum_eq_bot.1 hmax, hmt]
    | coe m =>
      have wf : ↑m < x := by simpa using! hmt.mp (List.maximum_mem hmax)
      rcases ofNat_surjective m with ⟨a, rfl⟩
      refine ⟨a + 1, le_antisymm (succ_le_of_lt wf) ?_⟩
      exact le_succ_of_forall_lt_le fun z hz => List.le_maximum_of_mem (hmt.2 hz) hmax
  termination_by n => n.val

@[simp]
/--
theorem `ofNat_range` / 定理 `ofNat_range`

English:
theorem ofNat_range
  statement: Set.range (ofNat s) = Set.univ
  proof: ofNat_surjective.range_eq

@[simp]

中文:
定理 of自然数_range
  结论: 集合.range (of自然数 s) = 集合.univ
  证明: ofNat_surjective.range_eq

@[simp]

Depends on / 依赖: ofNat_surjective, ofNat_surjective.range_eq, range_eq
-/
theorem ofNat_range : Set.range (ofNat s) = Set.univ :=
  ofNat_surjective.range_eq

@[simp]
/--
theorem `coe_comp_ofNat_range` / 定理 `coe_comp_ofNat_range`

English:
theorem coe_comp_ofNat_range
  statement: Set.range ((↑) ∘ ofNat s : Nat -> Nat) = s
  proof: by
  rw [Set.range_comp Subtype.val]; rw [ofNat_range]; rw [Set.image_univ]; rw [Subtype.range_coe]

中文:
定理 coe_comp_of自然数_range
  结论: 集合.range ((↑) ∘ of自然数 s : 自然数 -> 自然数) = s
  证明: by
  rw [Set.range_comp Subtype.val]; rw [ofNat_range]; rw [Set.image_univ]; rw [Subtype.range_coe]

Depends on / 依赖: Set.image_univ, Set.range_comp, Subtype, Subtype.range_coe, Subtype.val, image_univ, ofNat_range, range_coe, range_comp
-/
theorem coe_comp_ofNat_range : Set.range ((↑) ∘ ofNat s : Nat -> Nat) = s := by
  rw [Set.range_comp Subtype.val]; rw [ofNat_range]; rw [Set.image_univ]; rw [Subtype.range_coe]

set_option backward.privateInPublic true in
/--
Definition of `toFunAux` / `toFunAux` 的定义

English:
definition toFunAux
  signature: (x : s)
  body: (List.range x).countP (· in s)

中文:
定义 toFunAux
  签名: (x : s)
  定义体: (List.range x).countP (· in s)
-/
private def toFunAux (x : s) : Nat :=
  (List.range x).countP (· in s)

/--
theorem `toFunAux_eq` / 定理 `toFunAux_eq`

English:
theorem toFunAux_eq
  given: {s : Set Nat} [DecidablePred (· in s)] (x : s)
  proof: by
  rw [toFunAux]; rw [List.countP_eq_length_filter]
  rfl

中文:
定理 toFunAux_eq
  条件: {s : 集合 自然数} [DecidablePred (· in s)] (x : s)
  证明: by
  rw [toFunAux]; rw [List.countP_eq_length_filter]
  rfl
-/
private theorem toFunAux_eq {s : Set Nat} [DecidablePred (· in s)] (x : s) :
    toFunAux x = #{y in Finset.range x | y in s} := by
  rw [toFunAux]; rw [List.countP_eq_length_filter]
  rfl

set_option backward.privateInPublic true in
/--
theorem `right_inverse_aux` / 定理 `right_inverse_aux`

English:
theorem right_inverse_aux
  statement: forall n, toFunAux (ofNat s n) = n
  proof: right_inverse_aux n
    have h₁ : (ofNat s n : Nat) ∉ {x in range (ofNat s n) | x in s} := by simp
    have h₂ : {x in range (succ (ofNat s n)) | x in s} =
        insert ↑(ofNat s n) {x in range (ofNat s n) | x in s} := by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true]
          exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
         fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (ofNat s n).prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [toFunAux_eq, ofNat] at ih ⊢
    conv =>
      rhs
      rw [← ih]; rw [← card_insert_of_notMem h₁]; rw [← h₂]

中文:
定理 right_inverse_aux
  结论: 对任意 n, toFunAux (of自然数 s n) = n
  证明: right_inverse_aux n
    have h₁ : (ofNat s n : Nat) ∉ {x in range (ofNat s n) | x in s} := by simp
    have h₂ : {x in range (succ (ofNat s n)) | x in s} =
        insert ↑(ofNat s n) {x in range (ofNat s n) | x in s} := by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true]
          exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
         fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (ofNat s n).prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [toFunAux_eq, ofNat] at ih ⊢
    conv =>
      rhs
      rw [← ih]; rw [← card_insert_of_notMem h₁]; rw [← h₂]
-/
private theorem right_inverse_aux : forall n, toFunAux (ofNat s n) = n
  | 0 => by
    rw [toFunAux_eq]; rw [card_eq_zero]; rw [eq_empty_iff_forall_notMem]
    rintro n hn
    rw [mem_filter]; rw [ofNat]; rw [mem_range] at hn
    exact bot_le.not_gt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
  | n + 1 => by
    have ih : toFunAux (ofNat s n) = n := right_inverse_aux n
    have h₁ : (ofNat s n : Nat) ∉ {x in range (ofNat s n) | x in s} := by simp
    have h₂ : {x in range (succ (ofNat s n)) | x in s} =
        insert ↑(ofNat s n) {x in range (ofNat s n) | x in s} := by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true]
          exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
         fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (ofNat s n).prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [toFunAux_eq, ofNat] at ih ⊢
    conv =>
      rhs
      rw [← ih]; rw [← card_insert_of_notMem h₁]; rw [← h₂]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Any infinite set of naturals is denumerable. -/
@[instance_reducible]
/--
Definition of `denumerable` / `denumerable` 的定义

English:
definition denumerable
  signature: (s : Set Nat) [DecidablePred (· in s)] [Infinite s]
  body: Denumerable.ofEquiv Nat
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse ofNat_surjective right_inverse_aux
      right_inv := right_inverse_aux }

中文:
定义 denumerable
  签名: (s : 集合 自然数) [DecidablePred (· in s)] [无限 s]
  定义体: Denumerable.ofEquiv Nat
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse ofNat_surjective right_inverse_aux
      right_inv := right_inverse_aux }

Depends on / 依赖: Denumerable, Denumerable.ofEquiv, invFun, leftInverse_of_surjective_of_rightInverse, left_inv, ofEquiv, ofNat_surjective, right_inv, right_inverse_aux, toFunAux
-/
def denumerable (s : Set Nat) [DecidablePred (· in s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv Nat
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse ofNat_surjective right_inverse_aux
      right_inv := right_inverse_aux }

end Nat.Subtype

namespace Denumerable

open Encodable

/-- An infinite encodable type is denumerable. -/
@[instance_reducible]
/--
Definition of `ofEncodableOfInfinite` / `ofEncodableOfInfinite` 的定义

English:
definition ofEncodableOfInfinite
  signature: (α : Type*) [Encodable α] [Infinite α]
  body: by
  letI := @decidableRangeEncode α _
  letI : Infinite (Set.range (@encode α _)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equivRangeEncode α)

中文:
定义 ofEncodableOfInfinite
  签名: (α : 类型) [可编码 α] [无限 α]
  定义体: by
  letI := @decidableRangeEncode α _
  letI : Infinite (Set.range (@encode α _)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equivRangeEncode α)

Depends on / 依赖: Denumerable, Denumerable.ofEquiv, Equiv.ofInjective, Infinite, Infinite.of_injective, Nat.Subtype.denumerable, Set.range, Subtype, decidableRangeEncode, denumerable, encode, encode_injective, equivRangeEncode, injective, ofEquiv, ofInjective, of_injective
-/
def ofEncodableOfInfinite (α : Type*) [Encodable α] [Infinite α] : Denumerable α := by
  letI := @decidableRangeEncode α _
  letI : Infinite (Set.range (@encode α _)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equivRangeEncode α)

end Denumerable

/--
theorem `nonempty_denumerable` / 定理 `nonempty_denumerable`

English:
theorem nonempty_denumerable
  given: (α : Type*) [Countable α] [Infinite α]
  statement: Nonempty (Denumerable α)
  proof: (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _

中文:
定理 nonempty_denumerable
  条件: (α : 类型) [可数 α] [无限 α]
  结论: 非空 (可枚举 α)
  证明: (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _

Depends on / 依赖: Denumerable, Denumerable.ofEncodableOfInfinite, nonempty_encodable, ofEncodableOfInfinite
-/
theorem nonempty_denumerable (α : Type*) [Countable α] [Infinite α] : Nonempty (Denumerable α) :=
  (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _

/--
theorem `nonempty_denumerable_iff` / 定理 `nonempty_denumerable_iff`

English:
theorem nonempty_denumerable_iff
  given: {α : Type*}
  proof: ⟨fun ⟨_⟩ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => nonempty_denumerable _⟩

中文:
定理 nonempty_denumerable_iff
  条件: {α : 类型}
  证明: ⟨fun ⟨_⟩ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => nonempty_denumerable _⟩

Depends on / 依赖: nonempty_denumerable
-/
theorem nonempty_denumerable_iff {α : Type*} :
    Nonempty (Denumerable α) ↔ Countable α ∧ Infinite α :=
  ⟨fun ⟨_⟩ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => nonempty_denumerable _⟩

/--
Instance `nonempty_equiv_of_countable` / 实例 `nonempty_equiv_of_countable`

English:
instance nonempty_equiv_of_countable
  signature: [Countable α] [Infinite α] [Countable β] [Infinite β]
  body: by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩

中文:
实例 nonempty_equiv_of_countable
  签名: [可数 α] [无限 α] [可数 β] [无限 β]
  定义体: by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩

Depends on / 依赖: Denumerable, Denumerable.eqv, nonempty_denumerable
-/
instance nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infinite β] :
    Nonempty (α ≃ β) := by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩
