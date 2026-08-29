/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Order.Filter.AtTopBot.Prod
public import Mathlib.Order.Filter.CountablyGenerated

/-!
# Convergence to infinity and countably generated filters

In this file we prove that

- `Filter.atTop` and `Filter.atBot` filters on a countable type are countably generated;
- `Filter.exists_seq_tendsto`: if `f` is a nontrivial countably generated filter,
  then there exists a sequence that converges. to `f`;
- `Filter.tendsto_iff_seq_tendsto`: convergence along a countably generated filter
  is equivalent to convergence along all sequences that converge to this filter.
-/

public section

open Set

namespace Filter

variable {α β : Type*}

instance (priority := 200) atTop.isCountablyGenerated [Preorder α] [Countable α] :
    (atTop : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _

instance (priority := 200) atBot.isCountablyGenerated [Preorder α] [Countable α] :
    (atBot : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _

/--
Instance `instIsCountablyGeneratedAtTopProd` / 实例 `instIsCountablyGeneratedAtTopProd`

English:
instance instIsCountablyGeneratedAtTopProd
  signature: [Preorder α] [IsCountablyGenerated (atTop : Filter α)]
  body: by
  rw [← prod_atTop_atTop_eq]
  infer_instance

中文:
实例 instIsCountablyGeneratedAtTopProd
  签名: [预序 α] [是余untablyGenerated (atTop : 滤子 α)]
  定义体: by
  rw [← prod_atTop_atTop_eq]
  infer_instance

Depends on / 依赖: infer_instance, prod_atTop_atTop_eq
-/
instance instIsCountablyGeneratedAtTopProd [Preorder α] [IsCountablyGenerated (atTop : Filter α)]
    [Preorder β] [IsCountablyGenerated (atTop : Filter β)] :
    IsCountablyGenerated (atTop : Filter (α × β)) := by
  rw [← prod_atTop_atTop_eq]
  infer_instance

/--
Instance `instIsCountablyGeneratedAtBotProd` / 实例 `instIsCountablyGeneratedAtBotProd`

English:
instance instIsCountablyGeneratedAtBotProd
  signature: [Preorder α] [IsCountablyGenerated (atBot : Filter α)]
  body: by
  rw [← prod_atBot_atBot_eq]
  infer_instance

中文:
实例 instIsCountablyGeneratedAtBotProd
  签名: [预序 α] [是余untablyGenerated (atBot : 滤子 α)]
  定义体: by
  rw [← prod_atBot_atBot_eq]
  infer_instance

Depends on / 依赖: infer_instance, prod_atBot_atBot_eq
-/
instance instIsCountablyGeneratedAtBotProd [Preorder α] [IsCountablyGenerated (atBot : Filter α)]
    [Preorder β] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (atBot : Filter (α × β)) := by
  rw [← prod_atBot_atBot_eq]
  infer_instance

/--
Instance `_root_.OrderDual.instIsCountablyGeneratedAtTop` / 实例 `_root_.OrderDual.instIsCountablyGeneratedAtTop`

English:
instance _root_.OrderDual.instIsCountablyGeneratedAtTop
  signature: [Preorder α]
  body: ‹_›

中文:
实例 _root_.OrderDual.instIsCountablyGeneratedAtTop
  签名: [预序 α]
  定义体: ‹_›
-/
instance _root_.OrderDual.instIsCountablyGeneratedAtTop [Preorder α]
    [IsCountablyGenerated (atBot : Filter α)] : IsCountablyGenerated (atTop : Filter αᵒᵈ) := ‹_›

/--
Instance `_root_.OrderDual.instIsCountablyGeneratedAtBot` / 实例 `_root_.OrderDual.instIsCountablyGeneratedAtBot`

English:
instance _root_.OrderDual.instIsCountablyGeneratedAtBot
  signature: [Preorder α]
  body: ‹_›

中文:
实例 _root_.OrderDual.instIsCountablyGeneratedAtBot
  签名: [预序 α]
  定义体: ‹_›
-/
instance _root_.OrderDual.instIsCountablyGeneratedAtBot [Preorder α]
    [IsCountablyGenerated (atTop : Filter α)] : IsCountablyGenerated (atBot : Filter αᵒᵈ) := ‹_›

/--
lemma `atTop_countable_basis` / 引理 `atTop_countable_basis`

English:
lemma atTop_countable_basis
  given: [Preorder α] [IsDirectedOrder α] [Nonempty α] [Countable α]
  proof: { atTop_basis with countable := to_countable _ }

中文:
引理 atTop_countable_basis
  条件: [预序 α] [IsDirectedOrder α] [非空 α] [可数 α]
  证明: { atTop_basis with countable := to_countable _ }

Depends on / 依赖: atTop_basis, countable, to_countable
-/
lemma atTop_countable_basis [Preorder α] [IsDirectedOrder α] [Nonempty α] [Countable α] :
    HasCountableBasis (atTop : Filter α) (fun _ => True) Ici :=
  { atTop_basis with countable := to_countable _ }

/--
lemma `atBot_countable_basis` / 引理 `atBot_countable_basis`

English:
lemma atBot_countable_basis
  given: [Preorder α] [IsCodirectedOrder α] [Nonempty α] [Countable α]
  proof: { atBot_basis with countable := to_countable _ }

中文:
引理 atBot_countable_basis
  条件: [预序 α] [IsCodirectedOrder α] [非空 α] [可数 α]
  证明: { atBot_basis with countable := to_countable _ }

Depends on / 依赖: atBot_basis, countable, to_countable
-/
lemma atBot_countable_basis [Preorder α] [IsCodirectedOrder α] [Nonempty α] [Countable α] :
    HasCountableBasis (atBot : Filter α) (fun _ => True) Iic :=
  { atBot_basis with countable := to_countable _ }

/--
theorem `exists_seq_tendsto` / 定理 `exists_seq_tendsto`

English:
theorem exists_seq_tendsto
  given: (f : Filter α) [IsCountablyGenerated f] [NeBot f]
  proof: by
  obtain ⟨B, h⟩ := f.exists_antitone_basis
  choose x hx using fun n => Filter.nonempty_of_mem (h.mem n)
  exact ⟨x, h.tendsto hx⟩

中文:
定理 存在_seq_tendsto
  条件: (f : 滤子 α) [是余untablyGenerated f] [NeBot f]
  证明: by
  obtain ⟨B, h⟩ := f.exists_antitone_basis
  choose x hx using fun n => Filter.nonempty_of_mem (h.mem n)
  exact ⟨x, h.tendsto hx⟩

Depends on / 依赖: Filter, Filter.nonempty_of_mem, exists_antitone_basis, f.exists_antitone_basis, h.mem, h.tendsto, nonempty_of_mem, tendsto
-/
theorem exists_seq_tendsto (f : Filter α) [IsCountablyGenerated f] [NeBot f] :
    exists x : Nat -> α, Tendsto x atTop f := by
  obtain ⟨B, h⟩ := f.exists_antitone_basis
  choose x hx using fun n => Filter.nonempty_of_mem (h.mem n)
  exact ⟨x, h.tendsto hx⟩

/--
theorem `exists_seq_monotone_tendsto_atTop_atTop` / 定理 `exists_seq_monotone_tendsto_atTop_atTop`

English:
theorem exists_seq_monotone_tendsto_atTop_atTop
  statement: (α : Type*) [Preorder α] [Nonempty α]
  proof: by
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  choose c hleft hright using exists_ge_ge (α := α)
  set xs : Nat -> α := fun n => (List.range n).foldl (fun x n => c x (ys n)) (ys 0)
  have hsucc (n : Nat) : xs (n + 1) = c (xs n) (ys n) := by simp [xs, List.range_succ]
  refine ⟨xs, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [hsucc]
    apply hleft
· refine (tendsto_add_atTop_iff_nat 1).1 tendsto_atTop_mono (fun n => ?_) h
    rw [hsucc]
    apply hright

中文:
定理 存在_seq_monotone_tendsto_atTop_atTop
  结论: (α : 类型) [预序 α] [非空 α]
  证明: by
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  choose c hleft hright using exists_ge_ge (α := α)
  set xs : Nat -> α := fun n => (List.range n).foldl (fun x n => c x (ys n)) (ys 0)
  have hsucc (n : Nat) : xs (n + 1) = c (xs n) (ys n) := by simp [xs, List.range_succ]
  refine ⟨xs, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [hsucc]
    apply hleft
· refine (tendsto_add_atTop_iff_nat 1).1 tendsto_atTop_mono (fun n => ?_) h
    rw [hsucc]
    apply hright

Depends on / 依赖: Filter, List.range, List.range_succ, exists_ge_ge, exists_seq_tendsto, hright, monotone_nat_of_le_succ, range_succ, tendsto_add_atTop_iff_nat, tendsto_atTop_mono
-/
theorem exists_seq_monotone_tendsto_atTop_atTop (α : Type*) [Preorder α] [Nonempty α]
    [IsDirectedOrder α] [(atTop : Filter α).IsCountablyGenerated] :
    exists xs : Nat -> α, Monotone xs ∧ Tendsto xs atTop atTop := by
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  choose c hleft hright using exists_ge_ge (α := α)
  set xs : Nat -> α := fun n => (List.range n).foldl (fun x n => c x (ys n)) (ys 0)
  have hsucc (n : Nat) : xs (n + 1) = c (xs n) (ys n) := by simp [xs, List.range_succ]
  refine ⟨xs, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [hsucc]
    apply hleft
· refine (tendsto_add_atTop_iff_nat 1).1 tendsto_atTop_mono (fun n => ?_) h
    rw [hsucc]
    apply hright

/--
theorem `exists_seq_antitone_tendsto_atTop_atBot` / 定理 `exists_seq_antitone_tendsto_atTop_atBot`

English:
theorem exists_seq_antitone_tendsto_atTop_atBot
  statement: (α : Type*) [Preorder α] [Nonempty α]
  proof: exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ

中文:
定理 存在_seq_antitone_tendsto_atTop_atBot
  结论: (α : 类型) [预序 α] [非空 α]
  证明: exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ

Depends on / 依赖: exists_seq_monotone_tendsto_atTop_atTop
-/
theorem exists_seq_antitone_tendsto_atTop_atBot (α : Type*) [Preorder α] [Nonempty α]
    [IsCodirectedOrder α] [(atBot : Filter α).IsCountablyGenerated] :
    exists xs : Nat -> α, Antitone xs ∧ Tendsto xs atTop atBot :=
  exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ

/--
theorem `tendsto_iff_seq_tendsto` / 定理 `tendsto_iff_seq_tendsto`

English:
theorem tendsto_iff_seq_tendsto
  given: {f : α -> β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated]
  proof: by
  refine ⟨fun h x hx => h.comp hx, fun H s hs => ?_⟩
  contrapose! H
  have : NeBot (k ⊓ 𝓟 (f ⁻¹' sᶜ)) := by simpa [neBot_iff, inf_principal_eq_bot]
  rcases (k ⊓ 𝓟 (f ⁻¹' sᶜ)).exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_inf]; rw [tendsto_principal] at hx
  refine ⟨x, hx.1, fun h => ?_⟩
  rcases (hx.2.and (h hs)).exists with ⟨N, hnotMem, hmem⟩
  exact hnotMem hmem

中文:
定理 tendsto_iff_seq_tendsto
  条件: {f : α -> β} {k : 滤子 α} {l : 滤子 β} [k.是余untablyGenerated]
  证明: by
  refine ⟨fun h x hx => h.comp hx, fun H s hs => ?_⟩
  contrapose! H
  have : NeBot (k ⊓ 𝓟 (f ⁻¹' sᶜ)) := by simpa [neBot_iff, inf_principal_eq_bot]
  rcases (k ⊓ 𝓟 (f ⁻¹' sᶜ)).exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_inf]; rw [tendsto_principal] at hx
  refine ⟨x, hx.1, fun h => ?_⟩
  rcases (hx.2.and (h hs)).exists with ⟨N, hnotMem, hmem⟩
  exact hnotMem hmem

Depends on / 依赖: contrapose, exists_seq_tendsto, h.comp, hnotMem, inf_principal_eq_bot, neBot_iff, tendsto_inf, tendsto_principal
-/
theorem tendsto_iff_seq_tendsto {f : α -> β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    Tendsto f k l ↔ forall x : Nat -> α, Tendsto x atTop k -> Tendsto (f ∘ x) atTop l := by
  refine ⟨fun h x hx => h.comp hx, fun H s hs => ?_⟩
  contrapose! H
  have : NeBot (k ⊓ 𝓟 (f ⁻¹' sᶜ)) := by simpa [neBot_iff, inf_principal_eq_bot]
  rcases (k ⊓ 𝓟 (f ⁻¹' sᶜ)).exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_inf]; rw [tendsto_principal] at hx
  refine ⟨x, hx.1, fun h => ?_⟩
  rcases (hx.2.and (h hs)).exists with ⟨N, hnotMem, hmem⟩
  exact hnotMem hmem

/--
theorem `tendsto_of_seq_tendsto` / 定理 `tendsto_of_seq_tendsto`

English:
theorem tendsto_of_seq_tendsto
  given: {f : α -> β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated]
  proof: tendsto_iff_seq_tendsto.2

中文:
定理 tendsto_of_seq_tendsto
  条件: {f : α -> β} {k : 滤子 α} {l : 滤子 β} [k.是余untablyGenerated]
  证明: tendsto_iff_seq_tendsto.2

Depends on / 依赖: tendsto_iff_seq_tendsto
-/
theorem tendsto_of_seq_tendsto {f : α -> β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    (forall x : Nat -> α, Tendsto x atTop k -> Tendsto (f ∘ x) atTop l) -> Tendsto f k l :=
  tendsto_iff_seq_tendsto.2

/--
theorem `eventually_iff_seq_eventually` / 定理 `eventually_iff_seq_eventually`

English:
theorem eventually_iff_seq_eventually
  statement: {ι : Type*} {l : Filter ι} {p : ι -> Prop}
  proof: by
  simpa using tendsto_iff_seq_tendsto (f := id) (l := 𝓟 {x | p x})

中文:
定理 eventually_iff_seq_eventually
  结论: {ι : 类型} {l : 滤子 ι} {p : ι -> 命题}
  证明: by
  simpa using tendsto_iff_seq_tendsto (f := id) (l := 𝓟 {x | p x})

Depends on / 依赖: tendsto_iff_seq_tendsto
-/
theorem eventually_iff_seq_eventually {ι : Type*} {l : Filter ι} {p : ι -> Prop}
    [l.IsCountablyGenerated] :
    (forallᶠ n in l, p n) ↔ forall x : Nat -> ι, Tendsto x atTop l -> forallᶠ n : Nat in atTop, p (x n) := by
  simpa using tendsto_iff_seq_tendsto (f := id) (l := 𝓟 {x | p x})

/--
theorem `frequently_iff_seq_frequently` / 定理 `frequently_iff_seq_frequently`

English:
theorem frequently_iff_seq_frequently
  statement: {ι : Type*} {l : Filter ι} {p : ι -> Prop}
  proof: by
  simp only [Filter.Frequently, eventually_iff_seq_eventually (l := l)]
  push Not; rfl

中文:
定理 frequently_iff_seq_frequently
  结论: {ι : 类型} {l : 滤子 ι} {p : ι -> 命题}
  证明: by
  simp only [Filter.Frequently, eventually_iff_seq_eventually (l := l)]
  push Not; rfl

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_iff_seq_eventually
-/
theorem frequently_iff_seq_frequently {ι : Type*} {l : Filter ι} {p : ι -> Prop}
    [l.IsCountablyGenerated] :
    (existsᶠ n in l, p n) ↔ exists x : Nat -> ι, Tendsto x atTop l ∧ existsᶠ n : Nat in atTop, p (x n) := by
  simp only [Filter.Frequently, eventually_iff_seq_eventually (l := l)]
  push Not; rfl

/--
theorem `exists_seq_forall_of_frequently` / 定理 `exists_seq_forall_of_frequently`

English:
theorem exists_seq_forall_of_frequently
  statement: {ι : Type*} {l : Filter ι} {p : ι -> Prop}
  proof: by
  rw [frequently_iff_seq_frequently] at h
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩

中文:
定理 存在_seq_对任意_of_frequently
  结论: {ι : 类型} {l : 滤子 ι} {p : ι -> 命题}
  证明: by
  rw [frequently_iff_seq_frequently] at h
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩

Depends on / 依赖: frequently_iff_seq_frequently, h_freq, h_tendsto, hx_freq, hx_tendsto, n_to_n, subseq_forall_of_frequently
-/
theorem exists_seq_forall_of_frequently {ι : Type*} {l : Filter ι} {p : ι -> Prop}
    [l.IsCountablyGenerated] (h : existsᶠ n in l, p n) :
    exists ns : Nat -> ι, Tendsto ns atTop l ∧ forall n, p (ns n) := by
  rw [frequently_iff_seq_frequently] at h
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩

/--
lemma `frequently_iff_seq_forall` / 引理 `frequently_iff_seq_forall`

English:
lemma frequently_iff_seq_forall
  statement: {ι : Type*} {l : Filter ι} {p : ι -> Prop}
  proof: ⟨exists_seq_forall_of_frequently, fun ⟨_ns, hnsl, hpns⟩ =>
hnsl.frequently Frequently.of_forall hpns⟩

中文:
引理 frequently_iff_seq_对任意
  结论: {ι : 类型} {l : 滤子 ι} {p : ι -> 命题}
  证明: ⟨exists_seq_forall_of_frequently, fun ⟨_ns, hnsl, hpns⟩ =>
hnsl.frequently Frequently.of_forall hpns⟩

Depends on / 依赖: Frequently, Frequently.of_forall, exists_seq_forall_of_frequently, frequently, hnsl.frequently, of_forall
-/
lemma frequently_iff_seq_forall {ι : Type*} {l : Filter ι} {p : ι -> Prop}
    [l.IsCountablyGenerated] :
    (existsᶠ n in l, p n) ↔ exists ns : Nat -> ι, Tendsto ns atTop l ∧ forall n, p (ns n) :=
  ⟨exists_seq_forall_of_frequently, fun ⟨_ns, hnsl, hpns⟩ =>
hnsl.frequently Frequently.of_forall hpns⟩

/--
theorem `tendsto_of_subseq_tendsto` / 定理 `tendsto_of_subseq_tendsto`

English:
theorem tendsto_of_subseq_tendsto
  statement: {ι : Type*} {x : ι -> α} {f : Filter α} {l : Filter ι}
  proof: by
  contrapose! hxy
  obtain ⟨s, hs, hfreq⟩ : exists s in f, existsᶠ n in l, x n ∉ s := by
    rwa [not_tendsto_iff_exists_frequently_notMem] at hxy
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq
  refine ⟨y, hy_tendsto, fun ms hms_tendsto => ?_⟩
  rcases (hms_tendsto.eventually_mem hs).exists with ⟨n, hn⟩
exact absurd hn hy_freq _

中文:
定理 tendsto_of_subseq_tendsto
  结论: {ι : 类型} {x : ι -> α} {f : 滤子 α} {l : 滤子 ι}
  证明: by
  contrapose! hxy
  obtain ⟨s, hs, hfreq⟩ : exists s in f, existsᶠ n in l, x n ∉ s := by
    rwa [not_tendsto_iff_exists_frequently_notMem] at hxy
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq
  refine ⟨y, hy_tendsto, fun ms hms_tendsto => ?_⟩
  rcases (hms_tendsto.eventually_mem hs).exists with ⟨n, hn⟩
exact absurd hn hy_freq _

Depends on / 依赖: absurd, contrapose, eventually_mem, exists_seq_forall_of_frequently, hms_tendsto, hms_tendsto.eventually_mem, hy_freq, hy_tendsto, not_tendsto_iff_exists_frequently_notMem
-/
theorem tendsto_of_subseq_tendsto {ι : Type*} {x : ι -> α} {f : Filter α} {l : Filter ι}
    [l.IsCountablyGenerated]
    (hxy : forall ns : Nat -> ι, Tendsto ns atTop l ->
      exists ms : Nat -> Nat, Tendsto (fun n => x (ns <| ms n)) atTop f) :
    Tendsto x l f := by
  contrapose! hxy
  obtain ⟨s, hs, hfreq⟩ : exists s in f, existsᶠ n in l, x n ∉ s := by
    rwa [not_tendsto_iff_exists_frequently_notMem] at hxy
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq
  refine ⟨y, hy_tendsto, fun ms hms_tendsto => ?_⟩
  rcases (hms_tendsto.eventually_mem hs).exists with ⟨n, hn⟩
exact absurd hn hy_freq _

/--
theorem `exists_seq_comp_tendsto` / 定理 `exists_seq_comp_tendsto`

English:
theorem exists_seq_comp_tendsto
  statement: {ι : Type*} {g : Filter ι} [IsCountablyGenerated g] {u : ι -> α}
  proof: by
  rw [← Filter.push_pull']; rw [map_neBot_iff] at hx
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto (comap u f ⊓ g)
  exact ⟨θ, (tendsto_inf.1 hθ).2, tendsto_comap_iff.1 (tendsto_inf.1 hθ).1⟩

中文:
定理 存在_seq_comp_tendsto
  结论: {ι : 类型} {g : 滤子 ι} [是余untablyGenerated g] {u : ι -> α}
  证明: by
  rw [← Filter.push_pull']; rw [map_neBot_iff] at hx
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto (comap u f ⊓ g)
  exact ⟨θ, (tendsto_inf.1 hθ).2, tendsto_comap_iff.1 (tendsto_inf.1 hθ).1⟩

Depends on / 依赖: Filter, Filter.push_pull, exists_seq_tendsto, map_neBot_iff, push_pull, tendsto_comap_iff, tendsto_inf
-/
theorem exists_seq_comp_tendsto {ι : Type*} {g : Filter ι} [IsCountablyGenerated g] {u : ι -> α}
    {f : Filter α} [IsCountablyGenerated f]
    (hx : NeBot (f ⊓ map u g)) : exists θ : Nat -> ι, Tendsto θ atTop g ∧ Tendsto (u ∘ θ) atTop f := by
  rw [← Filter.push_pull']; rw [map_neBot_iff] at hx
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto (comap u f ⊓ g)
  exact ⟨θ, (tendsto_inf.1 hθ).2, tendsto_comap_iff.1 (tendsto_inf.1 hθ).1⟩

/--
theorem `subseq_tendsto_of_neBot` / 定理 `subseq_tendsto_of_neBot`

English:
theorem subseq_tendsto_of_neBot
  statement: {f : Filter α} [IsCountablyGenerated f] {u : Nat -> α}
  proof: by
  obtain ⟨φ, hφ⟩ := exists_seq_comp_tendsto hx
  obtain ⟨ψ, hψ, hψφ⟩ : exists ψ : Nat -> Nat, StrictMono ψ ∧ StrictMono (φ ∘ ψ) :=
    strictMono_subseq_of_tendsto_atTop hφ.1
  exact ⟨φ ∘ ψ, hψφ, hφ.2.comp hψ.tendsto_atTop⟩

中文:
定理 subseq_tendsto_of_neBot
  结论: {f : 滤子 α} [是余untablyGenerated f] {u : 自然数 -> α}
  证明: by
  obtain ⟨φ, hφ⟩ := exists_seq_comp_tendsto hx
  obtain ⟨ψ, hψ, hψφ⟩ : exists ψ : Nat -> Nat, StrictMono ψ ∧ StrictMono (φ ∘ ψ) :=
    strictMono_subseq_of_tendsto_atTop hφ.1
  exact ⟨φ ∘ ψ, hψφ, hφ.2.comp hψ.tendsto_atTop⟩

Depends on / 依赖: StrictMono, exists_seq_comp_tendsto, strictMono_subseq_of_tendsto_atTop, tendsto_atTop
-/
theorem subseq_tendsto_of_neBot {f : Filter α} [IsCountablyGenerated f] {u : Nat -> α}
    (hx : NeBot (f ⊓ map u atTop)) : exists θ : Nat -> Nat, StrictMono θ ∧ Tendsto (u ∘ θ) atTop f := by
  obtain ⟨φ, hφ⟩ := exists_seq_comp_tendsto hx
  obtain ⟨ψ, hψ, hψφ⟩ : exists ψ : Nat -> Nat, StrictMono ψ ∧ StrictMono (φ ∘ ψ) :=
    strictMono_subseq_of_tendsto_atTop hφ.1
  exact ⟨φ ∘ ψ, hψφ, hφ.2.comp hψ.tendsto_atTop⟩

end Filter
