/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Subsingleton

/-!
# Basic results on `Filter.atTop` and `Filter.atBot` filters

In this file we prove many lemmas like “if `f → +∞`, then `f ± c → +∞`”.
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

section IsDirected
variable [Preorder α] [IsDirectedOrder α] {p : α -> Prop}

-- `Filter.HasMonotoneBasis` doesn't exist, so we cannot use `to_dual` here.
/--
theorem `hasAntitoneBasis_atTop` / 定理 `hasAntitoneBasis_atTop`

English:
theorem hasAntitoneBasis_atTop
  given: [Nonempty α]
  statement: (@atTop α _).HasAntitoneBasis Ici
  proof: .iInf_principal fun _ _ => Ici_subset_Ici.2

中文:
定理 hasAntitoneBasis_atTop
  条件: [非空 α]
  结论: (@atTop α _).有AntitoneBasis 左闭右无界区间
  证明: .iInf_principal fun _ _ => Ici_subset_Ici.2

Depends on / 依赖: Ici_subset_Ici, iInf_principal
-/
theorem hasAntitoneBasis_atTop [Nonempty α] : (@atTop α _).HasAntitoneBasis Ici :=
  .iInf_principal fun _ _ => Ici_subset_Ici.2

/--
theorem `atTop_basis` / 定理 `atTop_basis`

English:
theorem atTop_basis
  given: [Nonempty α]
  statement: (@atTop α _).HasBasis (fun _ => True) Ici
  proof: hasAntitoneBasis_atTop.1

@[to_dual existing]

中文:
定理 atTop_basis
  条件: [非空 α]
  结论: (@atTop α _).有基 (fun _ => 真) 左闭右无界区间
  证明: hasAntitoneBasis_atTop.1

@[to_dual existing]

Depends on / 依赖: hasAntitoneBasis_atTop
-/
theorem atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fun _ => True) Ici :=
  hasAntitoneBasis_atTop.1

@[to_dual existing]
/--
lemma `atBot_basis` / 引理 `atBot_basis`

English:
lemma atBot_basis
  given: {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α]
  proof: atTop_basis (α := αᵒᵈ)

@[to_dual]

中文:
引理 atBot_basis
  条件: {α : 类型} [预序 α] [IsCodirectedOrder α] [非空 α]
  证明: atTop_basis (α := αᵒᵈ)

@[to_dual]

Depends on / 依赖: atTop_basis
-/
lemma atBot_basis {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α] :
    (@atBot α _).HasBasis (fun _ => True) Iic := atTop_basis (α := αᵒᵈ)

@[to_dual]
/--
lemma `atTop_basis_Ioi` / 引理 `atTop_basis_Ioi`

English:
lemma atTop_basis_Ioi
  given: [Nonempty α] [NoMaxOrder α]
  statement: (@atTop α _).HasBasis (fun _ => True) Ioi
  proof: atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩

@[to_dual]

中文:
引理 atTop_basis_Ioi
  条件: [非空 α] [NoMax序 α]
  结论: (@atTop α _).有基 (fun _ => 真) 左开右无界区间
  证明: atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩

@[to_dual]

Depends on / 依赖: Ici_subset_Ioi, Ioi_subset_Ici_self, atTop_basis, atTop_basis.to_hasBasis, exists_gt, to_hasBasis
-/
lemma atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@atTop α _).HasBasis (fun _ => True) Ioi :=
  atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩

@[to_dual]
/--
lemma `atTop_basis_Ioi'` / 引理 `atTop_basis_Ioi'`

English:
lemma atTop_basis_Ioi'
  given: [NoMaxOrder α] (a : α)
  statement: atTop.HasBasis (a < ·) Ioi
  proof: by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ => ?_) fun b _ => ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩

@[to_dual]

中文:
引理 atTop_basis_Ioi'
  条件: [NoMax序 α] (a : α)
  结论: atTop.有基 (a < ·) 左开右无界区间
  证明: by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ => ?_) fun b _ => ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩

@[to_dual]

Depends on / 依赖: Ioi_subset_Ioi, Nonempty, Subset, Subset.rfl, atTop_basis_Ioi, atTop_basis_Ioi.to_hasBasis, exists_ge_ge, exists_gt, hac.trans_lt, hbc.trans, hcd.le, to_hasBasis, trans_lt
-/
lemma atTop_basis_Ioi' [NoMaxOrder α] (a : α) : atTop.HasBasis (a < ·) Ioi := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ => ?_) fun b _ => ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩

@[to_dual]
/--
theorem `atTop_basis'` / 定理 `atTop_basis'`

English:
theorem atTop_basis'
  given: (a : α)
  statement: atTop.HasBasis (a <= ·) Ici
  proof: by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ => ?_) fun b _ => ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩

中文:
定理 atTop_basis'
  条件: (a : α)
  结论: atTop.有基 (a <= ·) 左闭右无界区间
  证明: by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ => ?_) fun b _ => ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩

Depends on / 依赖: Ici_subset_Ici, Nonempty, Subset, Subset.rfl, atTop_basis, atTop_basis.to_hasBasis, exists_ge_ge, to_hasBasis
-/
theorem atTop_basis' (a : α) : atTop.HasBasis (a <= ·) Ici := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ => ?_) fun b _ => ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩

variable [Nonempty α]

@[to_dual]
/--
Instance `atTop_neBot` / 实例 `atTop_neBot`

English:
instance atTop_neBot
  signature: : NeBot (atTop : Filter α)
  body: atTop_basis.neBot_iff.2 fun _ => nonempty_Ici

@[to_dual]

中文:
实例 atTop_neBot
  签名: : NeBot (atTop : 滤子 α)
  定义体: atTop_basis.neBot_iff.2 fun _ => nonempty_Ici

@[to_dual]

Depends on / 依赖: atTop_basis, atTop_basis.neBot_iff, neBot_iff, nonempty_Ici
-/
instance atTop_neBot : NeBot (atTop : Filter α) := atTop_basis.neBot_iff.2 fun _ => nonempty_Ici

@[to_dual]
/--
theorem `atTop_neBot_iff` / 定理 `atTop_neBot_iff`

English:
theorem atTop_neBot_iff
  given: {α : Type*} [Preorder α]
  proof: by
  refine ⟨fun h => ⟨nonempty_of_neBot atTop, ⟨fun x y => ?_⟩⟩, fun ⟨h₁, h₂⟩ => atTop_neBot⟩
  exact ((eventually_ge_atTop x).and (eventually_ge_atTop y)).exists

@[to_dual (attr := simp)]

中文:
定理 atTop_neBot_iff
  条件: {α : 类型} [预序 α]
  证明: by
  refine ⟨fun h => ⟨nonempty_of_neBot atTop, ⟨fun x y => ?_⟩⟩, fun ⟨h₁, h₂⟩ => atTop_neBot⟩
  exact ((eventually_ge_atTop x).and (eventually_ge_atTop y)).exists

@[to_dual (attr := simp)]

Depends on / 依赖: atTop_neBot, eventually_ge_atTop, nonempty_of_neBot
-/
theorem atTop_neBot_iff {α : Type*} [Preorder α] :
    (atTop : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α := by
  refine ⟨fun h => ⟨nonempty_of_neBot atTop, ⟨fun x y => ?_⟩⟩, fun ⟨h₁, h₂⟩ => atTop_neBot⟩
  exact ((eventually_ge_atTop x).and (eventually_ge_atTop y)).exists

@[to_dual (attr := simp)]
/--
lemma `mem_atTop_sets` / 引理 `mem_atTop_sets`

English:
lemma mem_atTop_sets
  given: {s : Set α}
  statement: s in (atTop : Filter α) ↔ exists a : α, forall b, a <= b -> b in s
  proof: atTop_basis.mem_iff.trans exists_congr fun _ => iff_of_eq (true_and _)

@[to_dual (attr := simp)]

中文:
引理 mem_atTop_sets
  条件: {s : 集合 α}
  结论: s in (atTop : 滤子 α) ↔ 存在 a : α, 对任意 b, a <= b -> b in s
  证明: atTop_basis.mem_iff.trans exists_congr fun _ => iff_of_eq (true_and _)

@[to_dual (attr := simp)]

Depends on / 依赖: atTop_basis, atTop_basis.mem_iff.trans, exists_congr, iff_of_eq, mem_iff, true_and
-/
lemma mem_atTop_sets {s : Set α} : s in (atTop : Filter α) ↔ exists a : α, forall b, a <= b -> b in s :=
atTop_basis.mem_iff.trans exists_congr fun _ => iff_of_eq (true_and _)

@[to_dual (attr := simp)]
/--
lemma `eventually_atTop` / 引理 `eventually_atTop`

English:
lemma eventually_atTop
  statement: (forallᶠ x in atTop, p x) ↔ exists a, forall b, a <= b -> p b
  proof: mem_atTop_sets

@[to_dual]

中文:
引理 eventually_atTop
  结论: (对任意ᶠ x in atTop, p x) ↔ 存在 a, 对任意 b, a <= b -> p b
  证明: mem_atTop_sets

@[to_dual]

Depends on / 依赖: mem_atTop_sets
-/
lemma eventually_atTop : (forallᶠ x in atTop, p x) ↔ exists a, forall b, a <= b -> p b := mem_atTop_sets

@[to_dual]
/--
theorem `frequently_atTop` / 定理 `frequently_atTop`

English:
theorem frequently_atTop
  statement: (existsᶠ x in atTop, p x) ↔ forall a, exists b, a <= b ∧ p b
  proof: atTop_basis.frequently_iff.trans by simp

@[to_dual]
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

中文:
定理 frequently_atTop
  结论: (存在ᶠ x in atTop, p x) ↔ 对任意 a, 存在 b, a <= b ∧ p b
  证明: atTop_basis.frequently_iff.trans by simp

@[to_dual]
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

Depends on / 依赖: atTop_basis, atTop_basis.frequently_iff.trans, frequently_iff
-/
theorem frequently_atTop : (existsᶠ x in atTop, p x) ↔ forall a, exists b, a <= b ∧ p b :=
atTop_basis.frequently_iff.trans by simp

@[to_dual]
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

-- `to_dual` cannot translate `forall_ge_iff`
/--
lemma `exists_eventually_atTop` / 引理 `exists_eventually_atTop`

English:
lemma exists_eventually_atTop
  given: {r : α -> β -> Prop}
  proof: by
  simp_rw [eventually_atTop, ← exists_comm (α := α)]
exact exists_congr fun a => .symm forall_ge_iff Monotone.exists fun _ _ _ hb H n hn =>
    H n (hb.trans hn)

@[to_dual existing]

中文:
引理 存在_eventually_atTop
  条件: {r : α -> β -> 命题}
  证明: by
  simp_rw [eventually_atTop, ← exists_comm (α := α)]
exact exists_congr fun a => .symm forall_ge_iff Monotone.exists fun _ _ _ hb H n hn =>
    H n (hb.trans hn)

@[to_dual existing]

Depends on / 依赖: Monotone, Monotone.exists, eventually_atTop, exists_comm, exists_congr, forall_ge_iff, hb.trans, simp_rw
-/
lemma exists_eventually_atTop {r : α -> β -> Prop} :
    (exists b, forallᶠ a in atTop, r a b) ↔ forallᶠ a₀ in atTop, exists b, forall a, a₀ <= a -> r a b := by
  simp_rw [eventually_atTop, ← exists_comm (α := α)]
exact exists_congr fun a => .symm forall_ge_iff Monotone.exists fun _ _ _ hb H n hn =>
    H n (hb.trans hn)

@[to_dual existing]
/--
lemma `exists_eventually_atBot` / 引理 `exists_eventually_atBot`

English:
lemma exists_eventually_atBot
  statement: {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α]
  proof: exists_eventually_atTop (α := αᵒᵈ)

@[to_dual]

中文:
引理 存在_eventually_atBot
  结论: {α : 类型} [预序 α] [IsCodirectedOrder α] [非空 α]
  证明: exists_eventually_atTop (α := αᵒᵈ)

@[to_dual]

Depends on / 依赖: exists_eventually_atTop
-/
lemma exists_eventually_atBot {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α]
    {r : α -> β -> Prop} : (exists b, forallᶠ a in atBot, r a b) ↔ forallᶠ a₀ in atBot, exists b, forall a <= a₀, r a b :=
  exists_eventually_atTop (α := αᵒᵈ)

@[to_dual]
/--
theorem `map_atTop_eq` / 定理 `map_atTop_eq`

English:
theorem map_atTop_eq
  given: {f : α -> β}
  statement: atTop.map f = ⨅ a, 𝓟 (f '' { a' | a <= a' })
  proof: (atTop_basis.map f).eq_iInf

@[to_dual]

中文:
定理 map_atTop_eq
  条件: {f : α -> β}
  结论: atTop.map f = ⨅ a, 𝓟 (f '' { a' | a <= a' })
  证明: (atTop_basis.map f).eq_iInf

@[to_dual]

Depends on / 依赖: atTop_basis, atTop_basis.map, eq_iInf
-/
theorem map_atTop_eq {f : α -> β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a <= a' }) :=
  (atTop_basis.map f).eq_iInf

@[to_dual]
/--
theorem `frequently_atTop'` / 定理 `frequently_atTop'`

English:
theorem frequently_atTop'
  given: [NoMaxOrder α]
  statement: (existsᶠ x in atTop, p x) ↔ forall a, exists b > a, p b
  proof: atTop_basis_Ioi.frequently_iff.trans by simp

中文:
定理 frequently_atTop'
  条件: [NoMax序 α]
  结论: (存在ᶠ x in atTop, p x) ↔ 对任意 a, 存在 b > a, p b
  证明: atTop_basis_Ioi.frequently_iff.trans by simp

Depends on / 依赖: atTop_basis_Ioi, atTop_basis_Ioi.frequently_iff.trans, frequently_iff
-/
theorem frequently_atTop' [NoMaxOrder α] : (existsᶠ x in atTop, p x) ↔ forall a, exists b > a, p b :=
atTop_basis_Ioi.frequently_iff.trans by simp

end IsDirected


/--
theorem `extraction_of_frequently_atTop` / 定理 `extraction_of_frequently_atTop`

English:
theorem extraction_of_frequently_atTop
  given: {P : Nat -> Prop} (h : existsᶠ n in atTop, P n)
  proof: by
  rw [frequently_atTop'] at h
  exact Nat.exists_strictMono_subsequence h

中文:
定理 extraction_of_frequently_atTop
  条件: {P : 自然数 -> 命题} (h : 存在ᶠ n in atTop, P n)
  证明: by
  rw [frequently_atTop'] at h
  exact Nat.exists_strictMono_subsequence h

Depends on / 依赖: Nat.exists_strictMono_subsequence, exists_strictMono_subsequence, frequently_atTop
-/
theorem extraction_of_frequently_atTop {P : Nat -> Prop} (h : existsᶠ n in atTop, P n) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P (φ n) := by
  rw [frequently_atTop'] at h
  exact Nat.exists_strictMono_subsequence h

/--
theorem `extraction_of_eventually_atTop` / 定理 `extraction_of_eventually_atTop`

English:
theorem extraction_of_eventually_atTop
  given: {P : Nat -> Prop} (h : forallᶠ n in atTop, P n)
  proof: extraction_of_frequently_atTop h.frequently

中文:
定理 extraction_of_eventually_atTop
  条件: {P : 自然数 -> 命题} (h : 对任意ᶠ n in atTop, P n)
  证明: extraction_of_frequently_atTop h.frequently

Depends on / 依赖: extraction_of_frequently_atTop, frequently, h.frequently
-/
theorem extraction_of_eventually_atTop {P : Nat -> Prop} (h : forallᶠ n in atTop, P n) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P (φ n) :=
  extraction_of_frequently_atTop h.frequently

/--
theorem `extraction_forall_of_frequently` / 定理 `extraction_forall_of_frequently`

English:
theorem extraction_forall_of_frequently
  given: {P : Nat -> Nat -> Prop} (h : forall n, existsᶠ k in atTop, P n k)
  proof: by
  simp only [frequently_atTop'] at h
  choose u hu hu' using h
  use (fun n => Nat.recOn n (u 0 0) fun n v => u (n + 1) v : Nat -> Nat)
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply hu
  · intro n
    cases n <;> simp [hu']

中文:
定理 extraction_对任意_of_frequently
  条件: {P : 自然数 -> 自然数 -> 命题} (h : 对任意 n, 存在ᶠ k in atTop, P n k)
  证明: by
  simp only [frequently_atTop'] at h
  choose u hu hu' using h
  use (fun n => Nat.recOn n (u 0 0) fun n v => u (n + 1) v : Nat -> Nat)
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply hu
  · intro n
    cases n <;> simp [hu']

Depends on / 依赖: Nat.recOn, frequently_atTop, strictMono_nat_of_lt_succ
-/
theorem extraction_forall_of_frequently {P : Nat -> Nat -> Prop} (h : forall n, existsᶠ k in atTop, P n k) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P n (φ n) := by
  simp only [frequently_atTop'] at h
  choose u hu hu' using h
  use (fun n => Nat.recOn n (u 0 0) fun n v => u (n + 1) v : Nat -> Nat)
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply hu
  · intro n
    cases n <;> simp [hu']

/--
theorem `extraction_forall_of_eventually` / 定理 `extraction_forall_of_eventually`

English:
theorem extraction_forall_of_eventually
  given: {P : Nat -> Nat -> Prop} (h : forall n, forallᶠ k in atTop, P n k)
  proof: extraction_forall_of_frequently fun n => (h n).frequently

中文:
定理 extraction_对任意_of_eventually
  条件: {P : 自然数 -> 自然数 -> 命题} (h : 对任意 n, 对任意ᶠ k in atTop, P n k)
  证明: extraction_forall_of_frequently fun n => (h n).frequently

Depends on / 依赖: extraction_forall_of_frequently, frequently
-/
theorem extraction_forall_of_eventually {P : Nat -> Nat -> Prop} (h : forall n, forallᶠ k in atTop, P n k) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P n (φ n) :=
  extraction_forall_of_frequently fun n => (h n).frequently

/--
theorem `extraction_forall_of_eventually'` / 定理 `extraction_forall_of_eventually'`

English:
theorem extraction_forall_of_eventually'
  given: {P : Nat -> Nat -> Prop} (h : forall n, exists N, forall k >= N, P n k)
  proof: extraction_forall_of_eventually (by simp [eventually_atTop, h])

中文:
定理 extraction_对任意_of_eventually'
  条件: {P : 自然数 -> 自然数 -> 命题} (h : 对任意 n, 存在 N, 对任意 k >= N, P n k)
  证明: extraction_forall_of_eventually (by simp [eventually_atTop, h])

Depends on / 依赖: eventually_atTop, extraction_forall_of_eventually
-/
theorem extraction_forall_of_eventually' {P : Nat -> Nat -> Prop} (h : forall n, exists N, forall k >= N, P n k) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P n (φ n) :=
  extraction_forall_of_eventually (by simp [eventually_atTop, h])

section IsDirected
variable [Preorder α] [IsDirectedOrder α] {F : Filter β} {u : α -> β}

@[to_dual inf_map_atBot_neBot_iff]
/--
theorem `inf_map_atTop_neBot_iff` / 定理 `inf_map_atTop_neBot_iff`

English:
theorem inf_map_atTop_neBot_iff
  given: [Nonempty α]
  proof: by
  simp_rw [inf_neBot_iff_frequently_left, frequently_map, frequently_atTop]; rfl

中文:
定理 inf_map_atTop_neBot_iff
  条件: [非空 α]
  证明: by
  simp_rw [inf_neBot_iff_frequently_left, frequently_map, frequently_atTop]; rfl

Depends on / 依赖: frequently_atTop, frequently_map, inf_neBot_iff_frequently_left, simp_rw
-/
theorem inf_map_atTop_neBot_iff [Nonempty α] :
    NeBot (F ⊓ map u atTop) ↔ forall U in F, forall N, exists n, N <= n ∧ u n in U := by
  simp_rw [inf_neBot_iff_frequently_left, frequently_map, frequently_atTop]; rfl

variable [Preorder β]

@[to_dual (dont_translate := α)]
/--
lemma `exists_le_of_tendsto_atTop` / 引理 `exists_le_of_tendsto_atTop`

English:
lemma exists_le_of_tendsto_atTop
  given: (h : Tendsto u atTop atTop) (a : α) (b : β)
  proof: by
  have : Nonempty α := ⟨a⟩
  have : forallᶠ x in atTop, a <= x ∧ b <= u x :=
    (eventually_ge_atTop a).and (h.eventually <| eventually_ge_atTop b)
  exact this.exists

@[to_dual (dont_translate := α)]

中文:
引理 存在_le_of_tendsto_atTop
  条件: (h : 收敛 u atTop atTop) (a : α) (b : β)
  证明: by
  have : Nonempty α := ⟨a⟩
  have : forallᶠ x in atTop, a <= x ∧ b <= u x :=
    (eventually_ge_atTop a).and (h.eventually <| eventually_ge_atTop b)
  exact this.exists

@[to_dual (dont_translate := α)]

Depends on / 依赖: Nonempty, eventually, eventually_ge_atTop, h.eventually, this.exists
-/
lemma exists_le_of_tendsto_atTop (h : Tendsto u atTop atTop) (a : α) (b : β) :
    exists a', a <= a' ∧ b <= u a' := by
  have : Nonempty α := ⟨a⟩
  have : forallᶠ x in atTop, a <= x ∧ b <= u x :=
    (eventually_ge_atTop a).and (h.eventually <| eventually_ge_atTop b)
  exact this.exists

@[to_dual (dont_translate := α)]
/--
theorem `exists_lt_of_tendsto_atTop` / 定理 `exists_lt_of_tendsto_atTop`

English:
theorem exists_lt_of_tendsto_atTop
  given: [NoMaxOrder β] (h : Tendsto u atTop atTop) (a : α) (b : β)
  proof: by
  obtain ⟨b', hb'⟩ := exists_gt b
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩

中文:
定理 存在_lt_of_tendsto_atTop
  条件: [NoMax序 β] (h : 收敛 u atTop atTop) (a : α) (b : β)
  证明: by
  obtain ⟨b', hb'⟩ := exists_gt b
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩

Depends on / 依赖: exists_gt, exists_le_of_tendsto_atTop, lt_of_lt_of_le
-/
theorem exists_lt_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto u atTop atTop) (a : α) (b : β) :
    exists a', a <= a' ∧ b < u a' := by
  obtain ⟨b', hb'⟩ := exists_gt b
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩

end IsDirected

section IsDirected
variable [Nonempty α] [Preorder α] [IsDirectedOrder α] {f : α -> β} {l : Filter β}

@[to_dual]
/--
theorem `tendsto_atTop'` / 定理 `tendsto_atTop'`

English:
theorem tendsto_atTop'
  statement: Tendsto f atTop l ↔ forall s in l, exists a, forall b, a <= b -> f b in s
  proof: by
  simp only [tendsto_def, mem_atTop_sets, mem_preimage]

@[to_dual]

中文:
定理 tendsto_atTop'
  结论: 收敛 f atTop l ↔ 对任意 s in l, 存在 a, 对任意 b, a <= b -> f b in s
  证明: by
  simp only [tendsto_def, mem_atTop_sets, mem_preimage]

@[to_dual]

Depends on / 依赖: mem_atTop_sets, mem_preimage, tendsto_def
-/
theorem tendsto_atTop' : Tendsto f atTop l ↔ forall s in l, exists a, forall b, a <= b -> f b in s := by
  simp only [tendsto_def, mem_atTop_sets, mem_preimage]

@[to_dual]
/--
theorem `tendsto_atTop_principal` / 定理 `tendsto_atTop_principal`

English:
theorem tendsto_atTop_principal
  given: {s : Set β}
  proof: by
  simp_rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage]

中文:
定理 tendsto_atTop_principal
  条件: {s : 集合 β}
  证明: by
  simp_rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage]

Depends on / 依赖: comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage, simp_rw, tendsto_iff_comap
-/
theorem tendsto_atTop_principal {s : Set β} :
    Tendsto f atTop (𝓟 s) ↔ exists N, forall n, N <= n -> f n in s := by
  simp_rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage]

variable [Preorder β]

@[to_dual]
/--
theorem `tendsto_atTop_atTop` / 定理 `tendsto_atTop_atTop`

English:
theorem tendsto_atTop_atTop
  statement: Tendsto f atTop atTop ↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
  proof: tendsto_iInf.trans forall_congr' fun _ => tendsto_atTop_principal

@[to_dual]

中文:
定理 tendsto_atTop_atTop
  结论: 收敛 f atTop atTop ↔ 对任意 b : β, 存在 i : α, 对任意 a : α, i <= a -> b <= f a
  证明: tendsto_iInf.trans forall_congr' fun _ => tendsto_atTop_principal

@[to_dual]

Depends on / 依赖: forall_congr, tendsto_atTop_principal, tendsto_iInf, tendsto_iInf.trans
-/
theorem tendsto_atTop_atTop : Tendsto f atTop atTop ↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a :=
tendsto_iInf.trans forall_congr' fun _ => tendsto_atTop_principal

@[to_dual]
/--
theorem `tendsto_atTop_atBot` / 定理 `tendsto_atTop_atBot`

English:
theorem tendsto_atTop_atBot
  statement: Tendsto f atTop atBot ↔ forall b : β, exists i : α, forall a : α, i <= a -> f a <= b
  proof: tendsto_atTop_atTop (β := βᵒᵈ)

@[to_dual]

中文:
定理 tendsto_atTop_atBot
  结论: 收敛 f atTop atBot ↔ 对任意 b : β, 存在 i : α, 对任意 a : α, i <= a -> f a <= b
  证明: tendsto_atTop_atTop (β := βᵒᵈ)

@[to_dual]

Depends on / 依赖: tendsto_atTop_atTop
-/
theorem tendsto_atTop_atBot : Tendsto f atTop atBot ↔ forall b : β, exists i : α, forall a : α, i <= a -> f a <= b :=
  tendsto_atTop_atTop (β := βᵒᵈ)

@[to_dual]
/--
theorem `tendsto_atTop_atTop_iff_of_monotone` / 定理 `tendsto_atTop_atTop_iff_of_monotone`

English:
theorem tendsto_atTop_atTop_iff_of_monotone
  given: (hf : Monotone f)
  proof: tendsto_atTop_atTop.trans forall_congr' fun _ => exists_congr fun a =>
⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans h hf ha'⟩

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop_iff := tendsto_atTop_atTop_iff_of_monotone

@[to_dual]

中文:
定理 tendsto_atTop_atTop_iff_of_monotone
  条件: (hf : 递增 f)
  证明: tendsto_atTop_atTop.trans forall_congr' fun _ => exists_congr fun a =>
⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans h hf ha'⟩

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop_iff := tendsto_atTop_atTop_iff_of_monotone

@[to_dual]

Depends on / 依赖: exists_congr, forall_congr, le_refl, le_trans, tendsto_atTop_atTop, tendsto_atTop_atTop.trans
-/
theorem tendsto_atTop_atTop_iff_of_monotone (hf : Monotone f) :
    Tendsto f atTop atTop ↔ forall b : β, exists a, b <= f a :=
tendsto_atTop_atTop.trans forall_congr' fun _ => exists_congr fun a =>
⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans h hf ha'⟩

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop_iff := tendsto_atTop_atTop_iff_of_monotone

@[to_dual]
/--
theorem `tendsto_atTop_atBot_iff_of_antitone` / 定理 `tendsto_atTop_atBot_iff_of_antitone`

English:
theorem tendsto_atTop_atBot_iff_of_antitone
  given: (hf : Antitone f)
  proof: tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf

中文:
定理 tendsto_atTop_atBot_iff_of_antitone
  条件: (hf : 递减 f)
  证明: tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf

Depends on / 依赖: tendsto_atTop_atTop_iff_of_monotone
-/
theorem tendsto_atTop_atBot_iff_of_antitone (hf : Antitone f) :
    Tendsto f atTop atBot ↔ forall b : β, exists a, f a <= b :=
  tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf

end IsDirected

/--
theorem `Tendsto.subseq_mem` / 定理 `Tendsto.subseq_mem`

English:
theorem Tendsto.subseq_mem
  statement: {F : Filter α} {V : Nat -> Set α} (h : forall n, V n in F) {u : Nat -> α}
  proof: extraction_forall_of_eventually'
    (fun n => tendsto_atTop'.mp hu _ (h n) : forall n, exists N, forall k >= N, u k in V n)

中文:
定理 收敛.subseq_mem
  结论: {F : 滤子 α} {V : 自然数 -> 集合 α} (h : 对任意 n, V n in F) {u : 自然数 -> α}
  证明: extraction_forall_of_eventually'
    (fun n => tendsto_atTop'.mp hu _ (h n) : forall n, exists N, forall k >= N, u k in V n)

Depends on / 依赖: extraction_forall_of_eventually, tendsto_atTop
-/
theorem Tendsto.subseq_mem {F : Filter α} {V : Nat -> Set α} (h : forall n, V n in F) {u : Nat -> α}
    (hu : Tendsto u atTop F) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, u (φ n) in V n :=
  extraction_forall_of_eventually'
    (fun n => tendsto_atTop'.mp hu _ (h n) : forall n, exists N, forall k >= N, u k in V n)

/-- A function `f` maps upwards closed sets (atTop sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connection above `b`. -/
@[to_dual
/-- A function `f` maps downwards closed sets (atBot sets) to downwards closed sets when it is a
Galois coinsertion. The Galois "coinsertion" and "connection" is weakened to only require it to be
an insertion and a connection below `b`. -/]
/--
theorem `map_atTop_eq_of_gc_preorder` / 定理 `map_atTop_eq_of_gc_preorder`

English:
theorem map_atTop_eq_of_gc_preorder
  proof: by
  have : Nonempty α := (hgi b le_rfl).nonempty
  choose! g hfg hgle using hgi
  refine le_antisymm (hf.tendsto_atTop_atTop fun c => ?_) ?_
  · rcases exists_ge_ge c b with ⟨d, hcd, hbd⟩
    exact ⟨g d, hcd.trans (hfg d hbd).ge⟩
  · have : Nonempty α := ⟨g b⟩
    rw [(atTop_basis.map f).ge_iff]
  

中文:
定理 map_atTop_eq_of_gc_preorder
  证明: by
  have : Nonempty α := (hgi b le_rfl).nonempty
  choose! g hfg hgle using hgi
  refine le_antisymm (hf.tendsto_atTop_atTop fun c => ?_) ?_
  · rcases exists_ge_ge c b with ⟨d, hcd, hbd⟩
    exact ⟨g d, hcd.trans (hfg d hbd).ge⟩
  · have : Nonempty α := ⟨g b⟩
    rw [(atTop_basis.map f).ge_iff]
  

Depends on / 依赖: Nonempty, atTop_basis, atTop_basis.map, eventually_ge_atTop, exists_ge_ge, filter_upwards, ge_iff, hcd.trans, hf.tendsto_atTop_atTop, le_antisymm, le_rfl, nonempty, tendsto_atTop_atTop
-/
theorem map_atTop_eq_of_gc_preorder
    [Preorder α] [IsDirectedOrder α] [Preorder β] [IsDirectedOrder β] {f : α -> β}
    (hf : Monotone f) (b : β)
    (hgi : forall c, b <= c -> exists x, f x = c ∧ forall a, f a <= c ↔ a <= x) : map f atTop = atTop := by
  have : Nonempty α := (hgi b le_rfl).nonempty
  choose! g hfg hgle using hgi
  refine le_antisymm (hf.tendsto_atTop_atTop fun c => ?_) ?_
  · rcases exists_ge_ge c b with ⟨d, hcd, hbd⟩
    exact ⟨g d, hcd.trans (hfg d hbd).ge⟩
  · have : Nonempty α := ⟨g b⟩
    rw [(atTop_basis.map f).ge_iff]
    intro a _
    filter_upwards [eventually_ge_atTop (f a), eventually_ge_atTop b] with c hac hbc
    exact ⟨g c, (hgle _ hbc _).1 hac, hfg _ hbc⟩

/-- A function `f` maps upwards closed sets (atTop sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connection above `b`. -/
@[to_dual
/-- A function `f` maps downwards closed sets (atBot sets) to downwards closed sets when it is a
Galois coinsertion. The Galois "coinsertion" and "connection" is weakened to only require it to be
an insertion and a connection below `b`. -/]
/--
theorem `map_atTop_eq_of_gc` / 定理 `map_atTop_eq_of_gc`

English:
theorem map_atTop_eq_of_gc
  proof: map_atTop_eq_of_gc_preorder hf b fun c hc =>
    ⟨g c, le_antisymm ((gc _ _ hc).2 le_rfl) (hgi c hc), (gc · c hc)⟩

@[to_dual]

中文:
定理 map_atTop_eq_of_gc
  证明: map_atTop_eq_of_gc_preorder hf b fun c hc =>
    ⟨g c, le_antisymm ((gc _ _ hc).2 le_rfl) (hgi c hc), (gc · c hc)⟩

@[to_dual]

Depends on / 依赖: le_antisymm, le_rfl, map_atTop_eq_of_gc_preorder
-/
theorem map_atTop_eq_of_gc
    [Preorder α] [IsDirectedOrder α] [PartialOrder β] [IsDirectedOrder β]
    {f : α -> β} (g : β -> α) (b : β) (hf : Monotone f)
    (gc : forall a, forall c, b <= c -> (f a <= c ↔ a <= g c)) (hgi : forall c, b <= c -> (c <= f (g c))) :
    map f atTop = atTop :=
  map_atTop_eq_of_gc_preorder hf b fun c hc =>
    ⟨g c, le_antisymm ((gc _ _ hc).2 le_rfl) (hgi c hc), (gc · c hc)⟩

@[to_dual]
/--
theorem `map_val_atTop_of_Ici_subset` / 定理 `map_val_atTop_of_Ici_subset`

English:
theorem map_val_atTop_of_Ici_subset
  statement: [Preorder α] [IsDirectedOrder α] {a : α} {s : Set α}
  proof: by
  choose f hl hr using exists_ge_ge (α := α)
  have : DirectedOn (· <= ·) s := fun x _ y _ =>
⟨f a (f x y), h hl _ _, (hl x y).trans (hr _ _), (hr x y).trans (hr _ _)⟩
  have : IsDirectedOrder s := by
    rw [directedOn_iff_directed] at this
    rwa [IsDirectedOrder, ← directed_id_iff]
  refine m

中文:
定理 map_val_atTop_of_Ici_subset
  结论: [预序 α] [IsDirectedOrder α] {a : α} {s : 集合 α}
  证明: by
  choose f hl hr using exists_ge_ge (α := α)
  have : DirectedOn (· <= ·) s := fun x _ y _ =>
⟨f a (f x y), h hl _ _, (hl x y).trans (hr _ _), (hr x y).trans (hr _ _)⟩
  have : IsDirectedOrder s := by
    rw [directedOn_iff_directed] at this
    rwa [IsDirectedOrder, ← directed_id_iff]
  refine m

Depends on / 依赖: DirectedOn, IsDirectedOrder, Subtype, Subtype.mono_coe, directedOn_iff_directed, directed_id_iff, exists_ge_ge, map_atTop_eq_of_gc_preorder, mono_coe
-/
theorem map_val_atTop_of_Ici_subset [Preorder α] [IsDirectedOrder α] {a : α} {s : Set α}
    (h : Ici a subseteq s) : map ((↑) : s -> α) atTop = atTop := by
  choose f hl hr using exists_ge_ge (α := α)
  have : DirectedOn (· <= ·) s := fun x _ y _ =>
⟨f a (f x y), h hl _ _, (hl x y).trans (hr _ _), (hr x y).trans (hr _ _)⟩
  have : IsDirectedOrder s := by
    rw [directedOn_iff_directed] at this
    rwa [IsDirectedOrder, ← directed_id_iff]
  refine map_atTop_eq_of_gc_preorder (Subtype.mono_coe _) a fun c hc => ?_
  exact ⟨⟨c, h hc⟩, rfl, fun _ => .rfl⟩

@[simp]
/--
theorem `_root_.Nat.map_cast_int_atTop` / 定理 `_root_.Nat.map_cast_int_atTop`

English:
theorem _root_.Nat.map_cast_int_atTop
  statement: map ((↑) : Nat -> Int) atTop = atTop
  proof: by
  refine map_atTop_eq_of_gc_preorder (fun _ _ => Int.ofNat_le.2) 0 fun n hn => ?_
  lift n to Nat using hn
  exact ⟨n, rfl, fun _ => Int.ofNat_le⟩

中文:
定理 _root_.自然数.map_cast_int_atTop
  结论: map ((↑) : 自然数 -> 整数) atTop = atTop
  证明: by
  refine map_atTop_eq_of_gc_preorder (fun _ _ => Int.ofNat_le.2) 0 fun n hn => ?_
  lift n to Nat using hn
  exact ⟨n, rfl, fun _ => Int.ofNat_le⟩

Depends on / 依赖: Int.ofNat_le, map_atTop_eq_of_gc_preorder, ofNat_le
-/
theorem _root_.Nat.map_cast_int_atTop : map ((↑) : Nat -> Int) atTop = atTop := by
  refine map_atTop_eq_of_gc_preorder (fun _ _ => Int.ofNat_le.2) 0 fun n hn => ?_
  lift n to Nat using hn
  exact ⟨n, rfl, fun _ => Int.ofNat_le⟩

/-- The image of the filter `atTop` on `Ici a` under the coercion equals `atTop`. -/
@[to_dual (attr := simp)
/-- The image of the filter `atBot` on `Iic a` under the coercion equals `atBot`. -/]
/--
theorem `map_val_Ici_atTop` / 定理 `map_val_Ici_atTop`

English:
theorem map_val_Ici_atTop
  given: [Preorder α] [IsDirectedOrder α] (a : α)
  proof: map_val_atTop_of_Ici_subset Subset.rfl

中文:
定理 map_val_Ici_atTop
  条件: [预序 α] [IsDirectedOrder α] (a : α)
  证明: map_val_atTop_of_Ici_subset Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, map_val_atTop_of_Ici_subset
-/
theorem map_val_Ici_atTop [Preorder α] [IsDirectedOrder α] (a : α) :
    map ((↑) : Ici a -> α) atTop = atTop :=
  map_val_atTop_of_Ici_subset Subset.rfl

/-- The image of the filter `atTop` on `Ioi a` under the coercion equals `atTop`. -/
@[to_dual (attr := simp)
/-- The image of the filter `atBot` on `Iio a` under the coercion equals `atBot`. -/]
/--
theorem `map_val_Ioi_atTop` / 定理 `map_val_Ioi_atTop`

English:
theorem map_val_Ioi_atTop
  given: [Preorder α] [IsDirectedOrder α] [NoMaxOrder α] (a : α)
  proof: let ⟨_b, hb⟩ := exists_gt a
map_val_atTop_of_Ici_subset Ici_subset_Ioi.2 hb

中文:
定理 map_val_Ioi_atTop
  条件: [预序 α] [IsDirectedOrder α] [NoMax序 α] (a : α)
  证明: let ⟨_b, hb⟩ := exists_gt a
map_val_atTop_of_Ici_subset Ici_subset_Ioi.2 hb

Depends on / 依赖: Ici_subset_Ioi, exists_gt, map_val_atTop_of_Ici_subset
-/
theorem map_val_Ioi_atTop [Preorder α] [IsDirectedOrder α] [NoMaxOrder α] (a : α) :
    map ((↑) : Ioi a -> α) atTop = atTop :=
  let ⟨_b, hb⟩ := exists_gt a
map_val_atTop_of_Ici_subset Ici_subset_Ioi.2 hb

/-- The `atTop` filter for `↑(Ioi a)` comes from the `atTop` filter in the ambient order. -/
@[to_dual
/-- The `atBot` filter for `↑(Iio a)` comes from the `atBot` filter in the ambient order. -/]
/--
theorem `atTop_Ioi_eq` / 定理 `atTop_Ioi_eq`

English:
theorem atTop_Ioi_eq
  given: [Preorder α] [IsDirectedOrder α] (a : α)
  proof: by
  rcases isEmpty_or_nonempty (Ioi a) with h | ⟨⟨b, hb⟩⟩
  · subsingleton
  · rw [← map_val_atTop_of_Ici_subset (Ici_subset_Ioi.2 hb), comap_map Subtype.coe_injective]

中文:
定理 atTop_Ioi_eq
  条件: [预序 α] [IsDirectedOrder α] (a : α)
  证明: by
  rcases isEmpty_or_nonempty (Ioi a) with h | ⟨⟨b, hb⟩⟩
  · subsingleton
  · rw [← map_val_atTop_of_Ici_subset (Ici_subset_Ioi.2 hb), comap_map Subtype.coe_injective]

Depends on / 依赖: Ici_subset_Ioi, Subtype, Subtype.coe_injective, coe_injective, comap_map, isEmpty_or_nonempty, map_val_atTop_of_Ici_subset, subsingleton
-/
theorem atTop_Ioi_eq [Preorder α] [IsDirectedOrder α] (a : α) :
    atTop = comap ((↑) : Ioi a -> α) atTop := by
  rcases isEmpty_or_nonempty (Ioi a) with h | ⟨⟨b, hb⟩⟩
  · subsingleton
  · rw [← map_val_atTop_of_Ici_subset (Ici_subset_Ioi.2 hb), comap_map Subtype.coe_injective]

/-- The `atTop` filter for `↑(Ici a)` comes from the `atTop` filter in the ambient order. -/
@[to_dual
/-- The `atBot` filter for `↑(Iic a)` comes from the `atBot` filter in the ambient order. -/]
/--
theorem `atTop_Ici_eq` / 定理 `atTop_Ici_eq`

English:
theorem atTop_Ici_eq
  given: [Preorder α] [IsDirectedOrder α] (a : α)
  proof: by
  rw [← map_val_Ici_atTop a]; rw [comap_map Subtype.coe_injective]

@[to_dual]

中文:
定理 atTop_Ici_eq
  条件: [预序 α] [IsDirectedOrder α] (a : α)
  证明: by
  rw [← map_val_Ici_atTop a]; rw [comap_map Subtype.coe_injective]

@[to_dual]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, comap_map, map_val_Ici_atTop
-/
theorem atTop_Ici_eq [Preorder α] [IsDirectedOrder α] (a : α) :
    atTop = comap ((↑) : Ici a -> α) atTop := by
  rw [← map_val_Ici_atTop a]; rw [comap_map Subtype.coe_injective]

@[to_dual]
/--
theorem `tendsto_Ioi_atTop` / 定理 `tendsto_Ioi_atTop`

English:
theorem tendsto_Ioi_atTop
  statement: [Preorder α] [IsDirectedOrder α]
  proof: by
  rw [atTop_Ioi_eq]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[to_dual]

中文:
定理 tendsto_Ioi_atTop
  结论: [预序 α] [IsDirectedOrder α]
  证明: by
  rw [atTop_Ioi_eq]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[to_dual]

Depends on / 依赖: Function, Function.comp_def, atTop_Ioi_eq, comp_def, tendsto_comap_iff
-/
theorem tendsto_Ioi_atTop [Preorder α] [IsDirectedOrder α]
    {a : α} {f : β -> Ioi a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ioi_eq]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[to_dual]
/--
theorem `tendsto_Ici_atTop` / 定理 `tendsto_Ici_atTop`

English:
theorem tendsto_Ici_atTop
  statement: [Preorder α] [IsDirectedOrder α]
  proof: by
  rw [atTop_Ici_eq]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[to_dual (attr := simp)]

中文:
定理 tendsto_Ici_atTop
  结论: [预序 α] [IsDirectedOrder α]
  证明: by
  rw [atTop_Ici_eq]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[to_dual (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, atTop_Ici_eq, comp_def, tendsto_comap_iff
-/
theorem tendsto_Ici_atTop [Preorder α] [IsDirectedOrder α]
    {a : α} {f : β -> Ici a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ici_eq]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[to_dual (attr := simp)]
/--
theorem `tendsto_comp_val_Ioi_atTop` / 定理 `tendsto_comp_val_Ioi_atTop`

English:
theorem tendsto_comp_val_Ioi_atTop
  statement: [Preorder α] [IsDirectedOrder α] [NoMaxOrder α]
  proof: by
  rw [← map_val_Ioi_atTop a]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[to_dual (attr := simp)]

中文:
定理 tendsto_comp_val_Ioi_atTop
  结论: [预序 α] [IsDirectedOrder α] [NoMax序 α]
  证明: by
  rw [← map_val_Ioi_atTop a]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[to_dual (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, _iff, comp_def, map_val_Ioi_atTop, tendsto_map
-/
theorem tendsto_comp_val_Ioi_atTop [Preorder α] [IsDirectedOrder α] [NoMaxOrder α]
    {a : α} {f : α -> β} {l : Filter β} :
    Tendsto (fun x : Ioi a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ioi_atTop a]; rw [tendsto_map'_iff]; rw [Function.comp_def]

@[to_dual (attr := simp)]
/--
theorem `tendsto_comp_val_Ici_atTop` / 定理 `tendsto_comp_val_Ici_atTop`

English:
theorem tendsto_comp_val_Ici_atTop
  statement: [Preorder α] [IsDirectedOrder α]
  proof: by
  rw [← map_val_Ici_atTop a]; rw [tendsto_map'_iff]; rw [Function.comp_def]

中文:
定理 tendsto_comp_val_Ici_atTop
  结论: [预序 α] [IsDirectedOrder α]
  证明: by
  rw [← map_val_Ici_atTop a]; rw [tendsto_map'_iff]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, _iff, comp_def, map_val_Ici_atTop, tendsto_map
-/
theorem tendsto_comp_val_Ici_atTop [Preorder α] [IsDirectedOrder α]
    {a : α} {f : α -> β} {l : Filter β} :
    Tendsto (fun x : Ici a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ici_atTop a]; rw [tendsto_map'_iff]; rw [Function.comp_def]

/--
theorem `map_add_atTop_eq_nat` / 定理 `map_add_atTop_eq_nat`

English:
theorem map_add_atTop_eq_nat
  given: (k : Nat)
  statement: map (fun a => a + k) atTop = atTop
  proof: map_atTop_eq_of_gc (· - k) k (fun _ _ h => Nat.add_le_add_right h k)
    (fun _ _ h => (Nat.le_sub_iff_add_le h).symm) fun a h => by rw [Nat.sub_add_cancel h]

中文:
定理 map_add_atTop_eq_nat
  条件: (k : 自然数)
  结论: map (fun a => a + k) atTop = atTop
  证明: map_atTop_eq_of_gc (· - k) k (fun _ _ h => Nat.add_le_add_right h k)
    (fun _ _ h => (Nat.le_sub_iff_add_le h).symm) fun a h => by rw [Nat.sub_add_cancel h]

Depends on / 依赖: Nat.add_le_add_right, Nat.le_sub_iff_add_le, Nat.sub_add_cancel, add_le_add_right, le_sub_iff_add_le, map_atTop_eq_of_gc, sub_add_cancel
-/
theorem map_add_atTop_eq_nat (k : Nat) : map (fun a => a + k) atTop = atTop :=
  map_atTop_eq_of_gc (· - k) k (fun _ _ h => Nat.add_le_add_right h k)
    (fun _ _ h => (Nat.le_sub_iff_add_le h).symm) fun a h => by rw [Nat.sub_add_cancel h]

/--
theorem `map_sub_atTop_eq_nat` / 定理 `map_sub_atTop_eq_nat`

English:
theorem map_sub_atTop_eq_nat
  given: (k : Nat)
  statement: map (fun a => a - k) atTop = atTop
  proof: map_atTop_eq_of_gc (· + k) 0 (fun _ _ h => Nat.sub_le_sub_right h _)
    (fun _ _ _ => Nat.sub_le_iff_le_add) fun b _ => by rw [Nat.add_sub_cancel_right]

中文:
定理 map_sub_atTop_eq_nat
  条件: (k : 自然数)
  结论: map (fun a => a - k) atTop = atTop
  证明: map_atTop_eq_of_gc (· + k) 0 (fun _ _ h => Nat.sub_le_sub_right h _)
    (fun _ _ _ => Nat.sub_le_iff_le_add) fun b _ => by rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.sub_le_iff_le_add, Nat.sub_le_sub_right, add_sub_cancel_right, map_atTop_eq_of_gc, sub_le_iff_le_add, sub_le_sub_right
-/
theorem map_sub_atTop_eq_nat (k : Nat) : map (fun a => a - k) atTop = atTop :=
  map_atTop_eq_of_gc (· + k) 0 (fun _ _ h => Nat.sub_le_sub_right h _)
    (fun _ _ _ => Nat.sub_le_iff_le_add) fun b _ => by rw [Nat.add_sub_cancel_right]

/--
theorem `tendsto_add_atTop_nat` / 定理 `tendsto_add_atTop_nat`

English:
theorem tendsto_add_atTop_nat
  given: (k : Nat)
  statement: Tendsto (fun a => a + k) atTop atTop
  proof: le_of_eq (map_add_atTop_eq_nat k)

中文:
定理 tendsto_add_atTop_nat
  条件: (k : 自然数)
  结论: 收敛 (fun a => a + k) atTop atTop
  证明: le_of_eq (map_add_atTop_eq_nat k)

Depends on / 依赖: le_of_eq, map_add_atTop_eq_nat
-/
theorem tendsto_add_atTop_nat (k : Nat) : Tendsto (fun a => a + k) atTop atTop :=
  le_of_eq (map_add_atTop_eq_nat k)

/--
theorem `tendsto_sub_atTop_nat` / 定理 `tendsto_sub_atTop_nat`

English:
theorem tendsto_sub_atTop_nat
  given: (k : Nat)
  statement: Tendsto (fun a => a - k) atTop atTop
  proof: le_of_eq (map_sub_atTop_eq_nat k)

中文:
定理 tendsto_sub_atTop_nat
  条件: (k : 自然数)
  结论: 收敛 (fun a => a - k) atTop atTop
  证明: le_of_eq (map_sub_atTop_eq_nat k)

Depends on / 依赖: le_of_eq, map_sub_atTop_eq_nat
-/
theorem tendsto_sub_atTop_nat (k : Nat) : Tendsto (fun a => a - k) atTop atTop :=
  le_of_eq (map_sub_atTop_eq_nat k)

/--
theorem `tendsto_add_atTop_iff_nat` / 定理 `tendsto_add_atTop_iff_nat`

English:
theorem tendsto_add_atTop_iff_nat
  given: {f : Nat -> α} {l : Filter α} (k : Nat)
  proof: show Tendsto (f ∘ fun n => n + k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff]; rw [map_add_atTop_eq_nat]

中文:
定理 tendsto_add_atTop_iff_nat
  条件: {f : 自然数 -> α} {l : 滤子 α} (k : 自然数)
  证明: show Tendsto (f ∘ fun n => n + k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff]; rw [map_add_atTop_eq_nat]

Depends on / 依赖: Tendsto, _iff, map_add_atTop_eq_nat, tendsto_map
-/
theorem tendsto_add_atTop_iff_nat {f : Nat -> α} {l : Filter α} (k : Nat) :
    Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n => n + k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff]; rw [map_add_atTop_eq_nat]

/--
theorem `map_div_atTop_eq_nat` / 定理 `map_div_atTop_eq_nat`

English:
theorem map_div_atTop_eq_nat
  given: (k : Nat) (hk : 0 < k)
  statement: map (fun a => a / k) atTop = atTop
  proof: map_atTop_eq_of_gc (fun b => k * b + (k - 1)) 1 (fun _ _ h => Nat.div_le_div_right h)
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, Nat.add_zero]; lia

中文:
定理 map_div_atTop_eq_nat
  条件: (k : 自然数) (hk : 0 < k)
  结论: map (fun a => a / k) atTop = atTop
  证明: map_atTop_eq_of_gc (fun b => k * b + (k - 1)) 1 (fun _ _ h => Nat.div_le_div_right h)
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, Nat.add_zero]; lia

Depends on / 依赖: Nat.add_zero, Nat.div_eq_of_lt, Nat.div_le_div_right, Nat.div_le_iff_le_mul_add_pred, Nat.mul_add_div, add_zero, div_eq_of_lt, div_le_div_right, div_le_iff_le_mul_add_pred, map_atTop_eq_of_gc, mul_add_div
-/
theorem map_div_atTop_eq_nat (k : Nat) (hk : 0 < k) : map (fun a => a / k) atTop = atTop :=
  map_atTop_eq_of_gc (fun b => k * b + (k - 1)) 1 (fun _ _ h => Nat.div_le_div_right h)
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, Nat.add_zero]; lia

/--
theorem `tendsto_inf_atTop` / 定理 `tendsto_inf_atTop`

English:
theorem tendsto_inf_atTop
  statement: {α β : Type*} [SemilatticeInf α]
  proof: by
  rw [Filter.tendsto_atTop] at *
  simp [eventually_and, hf, hg]

中文:
定理 tendsto_inf_atTop
  结论: {α β : 类型} [SemilatticeInf α]
  证明: by
  rw [Filter.tendsto_atTop] at *
  simp [eventually_and, hf, hg]

Depends on / 依赖: Filter, Filter.tendsto_atTop, eventually_and, tendsto_atTop
-/
theorem tendsto_inf_atTop {α β : Type*} [SemilatticeInf α]
    {f g : β -> α} (F : Filter β) (hf : Tendsto f F atTop) (hg : Tendsto g F atTop) :
    Tendsto (fun x => f x ⊓ g x) F atTop := by
  rw [Filter.tendsto_atTop] at *
  simp [eventually_and, hf, hg]

/--
theorem `tendsto_sup_atBot` / 定理 `tendsto_sup_atBot`

English:
theorem tendsto_sup_atBot
  statement: {α β : Type*} [SemilatticeSup α]
  proof: by
  rw [Filter.tendsto_atBot] at *
  simp [eventually_and, hf, hg]

中文:
定理 tendsto_sup_atBot
  结论: {α β : 类型} [SemilatticeSup α]
  证明: by
  rw [Filter.tendsto_atBot] at *
  simp [eventually_and, hf, hg]

Depends on / 依赖: Filter, Filter.tendsto_atBot, eventually_and, tendsto_atBot
-/
theorem tendsto_sup_atBot {α β : Type*} [SemilatticeSup α]
    {f g : β -> α} (F : Filter β) (hf : Tendsto f F atBot) (hg : Tendsto g F atBot) :
    Tendsto (fun x => f x ⊔ g x) F atBot := by
  rw [Filter.tendsto_atBot] at *
  simp [eventually_and, hf, hg]

section NeBot
variable [Preorder β] {l : Filter α} [NeBot l] {f : α -> β}

@[to_dual]
/--
theorem `not_bddAbove_of_tendsto_atTop` / 定理 `not_bddAbove_of_tendsto_atTop`

English:
theorem not_bddAbove_of_tendsto_atTop
  given: [NoMaxOrder β] (h : Tendsto f l atTop)
  proof: by
  rintro ⟨M, hM⟩
  have : forall x, f x <= M := by aesop
  have : ∅ = f ⁻¹' Ioi M := by aesop (add forward safe not_le_of_gt)
  apply Filter.empty_notMem l
  aesop (add safe Ioi_mem_atTop)

中文:
定理 not_bddAbove_of_tendsto_atTop
  条件: [NoMax序 β] (h : 收敛 f l atTop)
  证明: by
  rintro ⟨M, hM⟩
  have : forall x, f x <= M := by aesop
  have : ∅ = f ⁻¹' Ioi M := by aesop (add forward safe not_le_of_gt)
  apply Filter.empty_notMem l
  aesop (add safe Ioi_mem_atTop)

Depends on / 依赖: Filter, Filter.empty_notMem, Ioi_mem_atTop, LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_subsingleton, empty_notMem, forward, not_le_of_gt, of_subsingleton
-/
theorem not_bddAbove_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto f l atTop) :
    ¬BddAbove (range f) := by
  rintro ⟨M, hM⟩
  have : forall x, f x <= M := by aesop
  have : ∅ = f ⁻¹' Ioi M := by aesop (add forward safe not_le_of_gt)
  apply Filter.empty_notMem l
  aesop (add safe Ioi_mem_atTop)

end NeBot

/--
theorem `HasAntitoneBasis.eventually_subset` / 定理 `HasAntitoneBasis.eventually_subset`

English:
theorem HasAntitoneBasis.eventually_subset
  statement: [Preorder ι] {l : Filter α} {s : ι -> Set α}
  proof: let ⟨i, _, hi⟩ := hl.1.mem_iff.1 ht
  (eventually_ge_atTop i).mono fun _j hj => (hl.antitone hj).trans hi

中文:
定理 有AntitoneBasis.eventually_subset
  结论: [预序 ι] {l : 滤子 α} {s : ι -> 集合 α}
  证明: let ⟨i, _, hi⟩ := hl.1.mem_iff.1 ht
  (eventually_ge_atTop i).mono fun _j hj => (hl.antitone hj).trans hi

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.of_subsingleton_top, antitone, eventually_ge_atTop, hl.antitone, mem_iff, of_subsingleton_top
-/
theorem HasAntitoneBasis.eventually_subset [Preorder ι] {l : Filter α} {s : ι -> Set α}
    (hl : l.HasAntitoneBasis s) {t : Set α} (ht : t in l) : forallᶠ i in atTop, s i subseteq t :=
  let ⟨i, _, hi⟩ := hl.1.mem_iff.1 ht
  (eventually_ge_atTop i).mono fun _j hj => (hl.antitone hj).trans hi

/--
theorem `HasAntitoneBasis.tendsto` / 定理 `HasAntitoneBasis.tendsto`

English:
theorem HasAntitoneBasis.tendsto
  statement: [Preorder ι] {l : Filter α} {s : ι -> Set α}
  proof: fun _t ht => mem_map.2 (hl.eventually_subset ht).mono fun i hi => hi (h i)

中文:
定理 有AntitoneBasis.tendsto
  结论: [预序 ι] {l : 滤子 α} {s : ι -> 集合 α}
  证明: fun _t ht => mem_map.2 (hl.eventually_subset ht).mono fun i hi => hi (h i)

Depends on / 依赖: LinearDisjoint, Submodule, Submodule.LinearDisjoint.symm_of_commute, symm_of_commute
-/
protected theorem HasAntitoneBasis.tendsto [Preorder ι] {l : Filter α} {s : ι -> Set α}
    (hl : l.HasAntitoneBasis s) {φ : ι -> α} (h : forall i : ι, φ i in s i) : Tendsto φ atTop l :=
fun _t ht => mem_map.2 (hl.eventually_subset ht).mono fun i hi => hi (h i)

/--
theorem `HasAntitoneBasis.comp_mono` / 定理 `HasAntitoneBasis.comp_mono`

English:
theorem HasAntitoneBasis.comp_mono
  statement: [Nonempty ι] [Preorder ι] [IsDirectedOrder ι] [Preorder ι']
  proof: ⟨hs.1.to_hasBasis
      (fun n _ => (hφ.eventually_ge_atTop n).exists.imp fun _m hm => ⟨trivial, hs.antitone hm⟩)
      fun n _ => ⟨φ n, trivial, Subset.rfl⟩,
    hs.antitone.comp_monotone φ_mono⟩

中文:
定理 有AntitoneBasis.comp_mono
  结论: [非空 ι] [预序 ι] [IsDirectedOrder ι] [预序 ι']
  证明: ⟨hs.1.to_hasBasis
      (fun n _ => (hφ.eventually_ge_atTop n).exists.imp fun _m hm => ⟨trivial, hs.antitone hm⟩)
      fun n _ => ⟨φ n, trivial, Subset.rfl⟩,
    hs.antitone.comp_monotone φ_mono⟩

Depends on / 依赖: Subset, Subset.rfl, antitone, comp_monotone, eventually_ge_atTop, exists.imp, hs.antitone, hs.antitone.comp_monotone, to_hasBasis
-/
theorem HasAntitoneBasis.comp_mono [Nonempty ι] [Preorder ι] [IsDirectedOrder ι] [Preorder ι']
    {l : Filter α}
    {s : ι' -> Set α} (hs : l.HasAntitoneBasis s) {φ : ι -> ι'} (φ_mono : Monotone φ)
    (hφ : Tendsto φ atTop atTop) : l.HasAntitoneBasis (s ∘ φ) :=
  ⟨hs.1.to_hasBasis
      (fun n _ => (hφ.eventually_ge_atTop n).exists.imp fun _m hm => ⟨trivial, hs.antitone hm⟩)
      fun n _ => ⟨φ n, trivial, Subset.rfl⟩,
    hs.antitone.comp_monotone φ_mono⟩

/--
theorem `HasAntitoneBasis.comp_strictMono` / 定理 `HasAntitoneBasis.comp_strictMono`

English:
theorem HasAntitoneBasis.comp_strictMono
  statement: {l : Filter α} {s : Nat -> Set α} (hs : l.HasAntitoneBasis s)
  proof: hs.comp_mono hφ.monotone hφ.tendsto_atTop

中文:
定理 有AntitoneBasis.comp_strictMono
  结论: {l : 滤子 α} {s : 自然数 -> 集合 α} (hs : l.有AntitoneBasis s)
  证明: hs.comp_mono hφ.monotone hφ.tendsto_atTop

Depends on / 依赖: comp_mono, hs.comp_mono, monotone, tendsto_atTop
-/
theorem HasAntitoneBasis.comp_strictMono {l : Filter α} {s : Nat -> Set α} (hs : l.HasAntitoneBasis s)
    {φ : Nat -> Nat} (hφ : StrictMono φ) : l.HasAntitoneBasis (s ∘ φ) :=
  hs.comp_mono hφ.monotone hφ.tendsto_atTop

/--
theorem `subseq_forall_of_frequently` / 定理 `subseq_forall_of_frequently`

English:
theorem subseq_forall_of_frequently
  statement: {ι : Type*} {x : Nat -> ι} {p : ι -> Prop} {l : Filter ι}
  proof: by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩

中文:
定理 subseq_对任意_of_frequently
  结论: {ι : 类型} {x : 自然数 -> ι} {p : ι -> 命题} {l : 滤子 ι}
  证明: by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩

Depends on / 依赖: frequently_atTop, h_tendsto, h_tendsto.comp, tendsto_atTop_mono, tendsto_id
-/
theorem subseq_forall_of_frequently {ι : Type*} {x : Nat -> ι} {p : ι -> Prop} {l : Filter ι}
    (h_tendsto : Tendsto x atTop l) (h : existsᶠ n in atTop, p (x n)) :
    exists ns : Nat -> Nat, Tendsto (fun n => x (ns n)) atTop l ∧ forall n, p (x (ns n)) := by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩

end Filter
