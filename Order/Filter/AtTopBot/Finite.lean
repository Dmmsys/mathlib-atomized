/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.Filter.Bases.Finite
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Finiteness and `Filter.atTop` and `Filter.atBot` filters

This file contains results on `Filter.atTop` and `Filter.atBot` that depend on
the finiteness theory developed in Mathlib.
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

/--
theorem `eventually_forall_ge_atTop` / 定理 `eventually_forall_ge_atTop`

English:
theorem eventually_forall_ge_atTop
  given: [Preorder α] {p : α -> Prop}
  proof: by
  refine ⟨fun h => h.mono fun x hx => hx x le_rfl, fun h => ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x => Ici x.1) (fun _ => Subset.rfl) fun x hx y hy => ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz 

中文:
定理 eventually_对任意_ge_atTop
  条件: [预序 α] {p : α -> 命题}
  证明: by
  refine ⟨fun h => h.mono fun x hx => hx x le_rfl, fun h => ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x => Ici x.1) (fun _ => Subset.rfl) fun x hx y hy => ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz 

Depends on / 依赖: Subset, Subset.rfl, eventually_iff, h.mono, hasBasis_iInf_principal_finite, le_rfl, le_trans, mem_iInf_of_iInter, mem_iInter
-/
theorem eventually_forall_ge_atTop [Preorder α] {p : α -> Prop} :
    (forallᶠ x in atTop, forall y, x <= y -> p y) ↔ forallᶠ x in atTop, p x := by
  refine ⟨fun h => h.mono fun x hx => hx x le_rfl, fun h => ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x => Ici x.1) (fun _ => Subset.rfl) fun x hx y hy => ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz => le_trans (hx ⟨z, hz⟩) hy

/--
theorem `eventually_forall_le_atBot` / 定理 `eventually_forall_le_atBot`

English:
theorem eventually_forall_le_atBot
  given: [Preorder α] {p : α -> Prop}
  proof: eventually_forall_ge_atTop (α := αᵒᵈ)

中文:
定理 eventually_对任意_le_atBot
  条件: [预序 α] {p : α -> 命题}
  证明: eventually_forall_ge_atTop (α := αᵒᵈ)

Depends on / 依赖: eventually_forall_ge_atTop
-/
theorem eventually_forall_le_atBot [Preorder α] {p : α -> Prop} :
    (forallᶠ x in atBot, forall y, y <= x -> p y) ↔ forallᶠ x in atBot, p x :=
  eventually_forall_ge_atTop (α := αᵒᵈ)

/--
theorem `Tendsto.eventually_forall_ge_atTop` / 定理 `Tendsto.eventually_forall_ge_atTop`

English:
theorem Tendsto.eventually_forall_ge_atTop
  statement: [Preorder β] {l : Filter α}
  proof: by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

中文:
定理 收敛.eventually_对任意_ge_atTop
  结论: [预序 β] {l : 滤子 α}
  证明: by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

Depends on / 依赖: Filter, Filter.eventually_forall_ge_atTop, eventually_forall_ge_atTop, filter_mono, h_evtl, h_evtl.comap, hf.le_comap, le_comap
-/
theorem Tendsto.eventually_forall_ge_atTop [Preorder β] {l : Filter α}
    {p : β -> Prop} {f : α -> β} (hf : Tendsto f l atTop) (h_evtl : forallᶠ x in atTop, p x) :
    forallᶠ x in l, forall y, f x <= y -> p y := by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

/--
theorem `Tendsto.eventually_forall_le_atBot` / 定理 `Tendsto.eventually_forall_le_atBot`

English:
theorem Tendsto.eventually_forall_le_atBot
  statement: [Preorder β] {l : Filter α}
  proof: by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

中文:
定理 收敛.eventually_对任意_le_atBot
  结论: [预序 β] {l : 滤子 α}
  证明: by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

Depends on / 依赖: Filter, Filter.eventually_forall_le_atBot, eventually_forall_le_atBot, filter_mono, h_evtl, h_evtl.comap, hf.le_comap, le_comap
-/
theorem Tendsto.eventually_forall_le_atBot [Preorder β] {l : Filter α}
    {p : β -> Prop} {f : α -> β} (hf : Tendsto f l atBot) (h_evtl : forallᶠ x in atBot, p x) :
    forallᶠ x in l, forall y, y <= f x -> p y := by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

/-!
### Sequences
-/

/--
theorem `high_scores` / 定理 `high_scores`

English:
theorem high_scores
  given: [LinearOrder β] [NoMaxOrder β] {u : Nat -> β} (hu : Tendsto u atTop atTop)
  proof: by
  intro N
  obtain ⟨k : Nat, - : k <= N, hku : forall l <= N, u l <= u k⟩ : exists k <= N, forall l <= N, u l <= u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : exists n >= N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : Nat, hnN : n >= N, hnk : u k < 

中文:
定理 high_scores
  条件: [线性序 β] [NoMax序 β] {u : 自然数 -> β} (hu : 收敛 u atTop atTop)
  证明: by
  intro N
  obtain ⟨k : Nat, - : k <= N, hku : forall l <= N, u l <= u k⟩ : exists k <= N, forall l <= N, u l <= u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : exists n >= N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : Nat, hnN : n >= N, hnk : u k < 

Depends on / 依赖: Nat.findX, exists_lt_of_tendsto_atTop, exists_max_image, finite_le_nat, hn_min, le_refl
-/
theorem high_scores [LinearOrder β] [NoMaxOrder β] {u : Nat -> β} (hu : Tendsto u atTop atTop) :
    forall N, exists n >= N, forall k < n, u k < u n := by
  intro N
  obtain ⟨k : Nat, - : k <= N, hku : forall l <= N, u l <= u k⟩ : exists k <= N, forall l <= N, u l <= u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : exists n >= N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : Nat, hnN : n >= N, hnk : u k < u n, hn_min : forall m, m < n -> N <= m -> u m <= u k⟩ :
      exists n >= N, u k < u n ∧ forall m, m < n -> N <= m -> u m <= u k := by
    rcases Nat.findX ex with ⟨n, ⟨hnN, hnk⟩, hn_min⟩
    push Not at hn_min
    exact ⟨n, hnN, hnk, hn_min⟩
  use n, hnN
  grind

/--
theorem `low_scores` / 定理 `low_scores`

English:
theorem low_scores
  given: [LinearOrder β] [NoMinOrder β] {u : Nat -> β} (hu : Tendsto u atTop atBot)
  proof: @high_scores βᵒᵈ _ _ _ hu

中文:
定理 low_scores
  条件: [线性序 β] [NoMin序 β] {u : 自然数 -> β} (hu : 收敛 u atTop atBot)
  证明: @high_scores βᵒᵈ _ _ _ hu

Depends on / 依赖: high_scores
-/
theorem low_scores [LinearOrder β] [NoMinOrder β] {u : Nat -> β} (hu : Tendsto u atTop atBot) :
    forall N, exists n >= N, forall k < n, u n < u k :=
  @high_scores βᵒᵈ _ _ _ hu

/--
theorem `frequently_high_scores` / 定理 `frequently_high_scores`

English:
theorem frequently_high_scores
  statement: [LinearOrder β] [NoMaxOrder β] {u : Nat -> β}
  proof: by
  simpa [frequently_atTop] using high_scores hu

中文:
定理 frequently_high_scores
  结论: [线性序 β] [NoMax序 β] {u : 自然数 -> β}
  证明: by
  simpa [frequently_atTop] using high_scores hu

Depends on / 依赖: frequently_atTop, high_scores
-/
theorem frequently_high_scores [LinearOrder β] [NoMaxOrder β] {u : Nat -> β}
    (hu : Tendsto u atTop atTop) : existsᶠ n in atTop, forall k < n, u k < u n := by
  simpa [frequently_atTop] using high_scores hu

/--
theorem `frequently_low_scores` / 定理 `frequently_low_scores`

English:
theorem frequently_low_scores
  statement: [LinearOrder β] [NoMinOrder β] {u : Nat -> β}
  proof: @frequently_high_scores βᵒᵈ _ _ _ hu

中文:
定理 frequently_low_scores
  结论: [线性序 β] [NoMin序 β] {u : 自然数 -> β}
  证明: @frequently_high_scores βᵒᵈ _ _ _ hu

Depends on / 依赖: frequently_high_scores
-/
theorem frequently_low_scores [LinearOrder β] [NoMinOrder β] {u : Nat -> β}
    (hu : Tendsto u atTop atBot) : existsᶠ n in atTop, forall k < n, u n < u k :=
  @frequently_high_scores βᵒᵈ _ _ _ hu

/--
theorem `strictMono_subseq_of_tendsto_atTop` / 定理 `strictMono_subseq_of_tendsto_atTop`

English:
theorem strictMono_subseq_of_tendsto_atTop
  statement: [LinearOrder β] [NoMaxOrder β] {u : Nat -> β}
  proof: let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩

中文:
定理 strictMono_subseq_of_tendsto_atTop
  结论: [线性序 β] [NoMax序 β] {u : 自然数 -> β}
  证明: let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩

Depends on / 依赖: extraction_of_frequently_atTop, frequently_high_scores
-/
theorem strictMono_subseq_of_tendsto_atTop [LinearOrder β] [NoMaxOrder β] {u : Nat -> β}
    (hu : Tendsto u atTop atTop) : exists φ : Nat -> Nat, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩

/--
theorem `strictMono_subseq_of_id_le` / 定理 `strictMono_subseq_of_id_le`

English:
theorem strictMono_subseq_of_id_le
  given: {u : Nat -> Nat} (hu : forall n, n <= u n)
  proof: strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)

中文:
定理 strictMono_subseq_of_id_le
  条件: {u : 自然数 -> 自然数} (hu : 对任意 n, n <= u n)
  证明: strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)

Depends on / 依赖: strictMono_subseq_of_tendsto_atTop, tendsto_atTop_mono, tendsto_id
-/
theorem strictMono_subseq_of_id_le {u : Nat -> Nat} (hu : forall n, n <= u n) :
    exists φ : Nat -> Nat, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)

/--
theorem `Eventually.atTop_of_arithmetic` / 定理 `Eventually.atTop_of_arithmetic`

English:
theorem Eventually.atTop_of_arithmetic
  statement: {p : Nat -> Prop} {n : Nat} (hn : n != 0)
  proof: by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [Nat.le_div_iff_mul_le hn.bot_lt]; rw [mul_comm]
  exact (Finset.le_sup (f := (n *

中文:
定理 Eventually.atTop_of_arithmetic
  结论: {p : 自然数 -> 命题} {n : 自然数} (hn : n != 0)
  证明: by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [Nat.le_div_iff_mul_le hn.bot_lt]; rw [mul_comm]
  exact (Finset.le_sup (f := (n *

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_range, Finset.range, Nat.div_add_mod, Nat.le_div_iff_mul_le, Nat.mod_lt, bot_lt, div_add_mod, eventually_atTop, hn.bot_lt, le_div_iff_mul_le, le_sup, mem_range, mod_lt, mul_comm
-/
theorem Eventually.atTop_of_arithmetic {p : Nat -> Prop} {n : Nat} (hn : n != 0)
    (hp : forall k < n, forallᶠ a in atTop, p (n * a + k)) : forallᶠ a in atTop, p a := by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [Nat.le_div_iff_mul_le hn.bot_lt]; rw [mul_comm]
  exact (Finset.le_sup (f := (n * N ·)) (Finset.mem_range.2 hlt)).trans hb

/--
theorem `HasAntitoneBasis.subbasis_with_rel` / 定理 `HasAntitoneBasis.subbasis_with_rel`

English:
theorem HasAntitoneBasis.subbasis_with_rel
  statement: {f : Filter α} {s : Nat -> Set α}
  proof: by
  rsuffices ⟨φ, hφ, hrφ⟩ : exists φ : Nat -> Nat, StrictMono φ ∧ forall m n, m < n -> r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : forall t : Set Nat, t.Finite -> forallᶠ n in atTop, forall m in t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (e

中文:
定理 有AntitoneBasis.subbasis_with_rel
  结论: {f : 滤子 α} {s : 自然数 -> 集合 α}
  证明: by
  rsuffices ⟨φ, hφ, hrφ⟩ : exists φ : Nat -> Nat, StrictMono φ ∧ forall m n, m < n -> r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : forall t : Set Nat, t.Finite -> forallᶠ n in atTop, forall m in t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (e

Depends on / 依赖: Finite, StrictMono, comp_strictMono, eventually_all_finite, eventually_gt_atTop, forall_and, forall_comm, forall_mem_image, hs.comp_strictMono, mem_Iio, rsuffices, seq_of_forall_finite_exists, t.Finite
-/
theorem HasAntitoneBasis.subbasis_with_rel {f : Filter α} {s : Nat -> Set α}
    (hs : f.HasAntitoneBasis s) {r : Nat -> Nat -> Prop} (hr : forall m, forallᶠ n in atTop, r m n) :
    exists φ : Nat -> Nat, StrictMono φ ∧ (forall ⦃m n⦄, m < n -> r (φ m) (φ n)) ∧ f.HasAntitoneBasis (s ∘ φ) := by
  rsuffices ⟨φ, hφ, hrφ⟩ : exists φ : Nat -> Nat, StrictMono φ ∧ forall m n, m < n -> r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : forall t : Set Nat, t.Finite -> forallᶠ n in atTop, forall m in t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (eventually_gt_atTop m).and (hr _)
  rcases seq_of_forall_finite_exists fun t ht => (this t ht).exists with ⟨φ, hφ⟩
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.2 hφ.1, forall_comm.2 hφ.2⟩

end Filter

open Filter Finset

namespace Nat

/--
theorem `eventually_pow_lt_factorial_sub` / 定理 `eventually_pow_lt_factorial_sub`

English:
theorem eventually_pow_lt_factorial_sub
  given: (c d : Nat)
  statement: forallᶠ n in atTop, c ^ n < (n - d)!
  proof: by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n :

中文:
定理 eventually_pow_lt_factorial_sub
  条件: (c d : 自然数)
  结论: 对任意ᶠ n in atTop, c ^ n < (n - d)!
  证明: by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n :

Depends on / 依赖: Nat.add_assoc, Nat.add_right_comm, Nat.exists_eq_add_of_le, Nat.factorial_mul_pow_le_facto, Nat.factorial_pos, Nat.le_mul_of_pos_right, Nat.pow_pos, Nat.two_mul, add_assoc, add_right_comm, c.eq_zero_or_pos, convert_to, eq_zero_or_pos, eventually_atTop, exists_eq_add_of_le, factorial_mul_pow_le_facto, factorial_pos, le_mul_of_pos_right, lt_of_lt_of_le, pow_add
-/
theorem eventually_pow_lt_factorial_sub (c d : Nat) : forallᶠ n in atTop, c ^ n < (n - d)! := by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d') c0)).trans_lt ?_
  convert_to! (c ^ 2) ^ (c ^ 2 + d' + d + 1) < (c ^ 2 + (c ^ 2 + d' + d + 1) + 1)!
  · rw [← pow_mul, ← pow_add]
    congr 1
    lia
  · congr 1
    lia
refine (lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial).trans_le
    (factorial_le (Nat.le_succ _))
  rw [← one_mul (_ ^ _ : Nat)]
  apply Nat.mul_lt_mul_of_le_of_lt
  · exact Nat.one_le_of_lt (Nat.factorial_pos _)
  · exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  · exact (Nat.factorial_pos _)

/--
theorem `eventually_mul_pow_lt_factorial_sub` / 定理 `eventually_mul_pow_lt_factorial_sub`

English:
theorem eventually_mul_pow_lt_factorial_sub
  given: (a c d : Nat)
  proof: by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn

中文:
定理 eventually_mul_pow_lt_factorial_sub
  条件: (a c d : 自然数)
  证明: by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn

Depends on / 依赖: Filter, Filter.eventually_gt_atTop, Nat.eventually_pow_lt_factorial_sub, Nat.le_self_pow, Nat.mul_le_mul_right, eventually_gt_atTop, eventually_pow_lt_factorial_sub, filter_upwards, hn0.ne, le_self_pow, mul_le_mul_right, mul_pow, trans_lt
-/
theorem eventually_mul_pow_lt_factorial_sub (a c d : Nat) :
    forallᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn

end Nat
