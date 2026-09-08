/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Tian Chen
-/
module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Separation.Regular

/-!
# Not normal topological spaces

In this file we prove (see `IsClosed.not_normal_of_continuum_le_mk`) that a separable space with a
discrete subspace of cardinality continuum is not a normal topological space.

## References

* [Willard's *General Topology*][zbMATH02107988]
-/

public section

open Set Function Cardinal TopologicalSpace

universe u
variable {X : Type u} [TopologicalSpace X]

namespace IsClosed

/-- Let `s` be a closed set in a normal space and `d` be a dense set. If the induced topology on `s`
is discrete, then `𝒫 s` has cardinality less than or equal to `𝒫 d`. -/
/-
**IsClosed.two_pow_mk_le_two_pow_mk_dense** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：two_pow_mk_le_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClose
d s) [DiscreteTopology s] (hd : Dense d) : (2 : Cardinal) ^ #s <= 2 ^ #d
参数：hs : IsClosed s；hd : Dense d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Dense.inter_open_nonempty`：∀ {X : Type u} [inst : TopologicalSpace X] {s
 : Set X},   Dense s → ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.sdiff_nonempty`：sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s
 subseteq t
· 使用定理 `Set.Nonempty.not_disjoint`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempt
y → ¬Disjoint s t
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.mk_powerset`：mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) =
 2 ^ #(↥s)
· 使用定理 `Cardinal.mk_range_eq`：mk_range_eq (f : α -> β) (h : Injective f) : #(ran
ge f) = #α
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Let `s` be a closed set in a normal space and `d` be a dense set. If the induced
 topology on `s`
is discrete, then `𝒫 s` has cardinality less than or equal to `𝒫 d`.
-/
theorem two_pow_mk_le_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hd : Dense d) : (2 : Cardinal) ^ #s ≤ 2 ^ #d := by
  have h_closed (t) (ht : t ∈ 𝒫 s) : IsClosed t := by
    rw [← inter_eq_self_of_subset_right ht, ← Subtype.image_preimage_val]
    exact hs.isClosedMap_subtype_val _ (isClosed_discrete _)
  choose U V hU hV hUs hVs hUV using fun t : 𝒫 s ↦
    normal_separation (h_closed t t.2) (h_closed _ sdiff_subset) disjoint_sdiff_right
  have hUd {t₁ t₂} (h : U t₁ ∩ d = U t₂ ∩ d) : t₁.1 ⊆ t₂.1 := by
    by_contra ht
    rw [← sdiff_nonempty] at ht
    have hUVd := hd.inter_open_nonempty _ ((hU t₁).inter (hV t₂)) <| ht.mono <|
      subset_inter (sdiff_subset.trans (hUs t₁)) ((sdiff_subset_sdiff_left t₁.2).trans (hVs t₂))
    rw [inter_right_comm, h] at hUVd
    exact hUVd.not_disjoint <| disjoint_of_subset_left inter_subset_left (hUV t₂)
  have h_inj : Injective (U · ∩ d) := fun _ _ h ↦ SetCoe.ext <| (hUd h).antisymm (hUd h.symm)
  rw [← mk_powerset, ← mk_powerset, ← mk_range_eq _ h_inj]
  apply mk_le_mk_of_subset
  rw [range_subset_iff]
  intro
  exact inter_subset_right
/-
**IsClosed.mk_lt_two_pow_mk_dense** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：mk_lt_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s) [Di
screteTopology s] (hd : Dense d) : #s < 2 ^ #d
参数：hs : IsClosed s；hd : Dense d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
· 使用定理 `IsClosed.two_pow_mk_le_two_pow_mk_dense`：two_pow_mk_le_two_pow_mk_dense 
[NormalSpace X] {s d : Set X} (hs : IsClosed s) [DiscreteTopology s] (hd : Dense
 d) : (2 : Cardinal) ^ #s <= …
-/
theorem mk_lt_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hd : Dense d) : #s < 2 ^ #d :=
  (#s).cantor.trans_le <| hs.two_pow_mk_le_two_pow_mk_dense hd

variable [SeparableSpace X]
/-
**IsClosed.two_pow_mk_lt_continuum** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：two_pow_mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s) [Dis
creteTopology s] : 2 ^ #s <= 𝔠
参数：hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `IsClosed.two_pow_mk_le_two_pow_mk_dense`：two_pow_mk_le_two_pow_mk_dense 
[NormalSpace X] {s d : Set X} (hs : IsClosed s) [DiscreteTopology s] (hd : Dense
 d) : (2 : Cardinal) ^ #s <= …
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Set.Countable.le_aleph0`：∀ {α : Type u} {s : Set α}, s.Countable → Cardi
nal.mk ↑s ≤ Cardinal.aleph0
· 使用定理 `Cardinal.two_power_aleph0`：two_power_aleph0 : 2 ^ ℵ₀ = 𝔠
-/
theorem two_pow_mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s)
    [DiscreteTopology s] : 2 ^ #s ≤ 𝔠 :=
  have ⟨d, hd_countable, hd_dense⟩ := exists_countable_dense X
  calc
    2 ^ #s ≤ 2 ^ #d := hs.two_pow_mk_le_two_pow_mk_dense hd_dense
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero hd_countable.le_aleph0
    _ = 𝔠 := two_power_aleph0

/-- Let `s` be a closed set in a separable normal space. If the induced topology on `s` is discrete,
then `s` has cardinality less than continuum. -/
/-
**IsClosed.mk_lt_continuum** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s) [DiscreteTop
ology s] : #s < 𝔠
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
· 使用定理 `IsClosed.two_pow_mk_lt_continuum`：two_pow_mk_lt_continuum [NormalSpace X
] {s : Set X} (hs : IsClosed s) [DiscreteTopology s] : 2 ^ #s <= 𝔠

--- 原说明 ---
Let `s` be a closed set in a separable normal space. If the induced topology on 
`s` is discrete,
then `s` has cardinality less than continuum.
-/
theorem mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s)
  [DiscreteTopology s] : #s < 𝔠 := (#s).cantor.trans_le hs.two_pow_mk_lt_continuum

/-- Let `s` be a closed set in a separable space. If the induced topology on `s` is discrete and `s`
has cardinality at least continuum, then the ambient space is not a normal space. -/
/-
**IsClosed.not_normal_of_continuum_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：not_normal_of_continuum_le_mk {s : Set X} (hs : IsClosed s) [DiscreteTopol
ogy s] (hmk : 𝔠 <= #s) : ¬NormalSpace X
参数：hs : IsClosed s；hmk : 𝔠 <= #s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `IsClosed.mk_lt_continuum`：mk_lt_continuum [NormalSpace X] {s : Set X} (h
s : IsClosed s) [DiscreteTopology s] : #s < 𝔠

--- 原说明 ---
Let `s` be a closed set in a separable space. If the induced topology on `s` is 
discrete and `s`
has cardinality at least continuum, then the ambient space is not a normal space
.
-/
theorem not_normal_of_continuum_le_mk {s : Set X} (hs : IsClosed s) [DiscreteTopology s]
    (hmk : 𝔠 ≤ #s) : ¬NormalSpace X := fun _ ↦ hs.mk_lt_continuum.not_ge hmk

end IsClosed

