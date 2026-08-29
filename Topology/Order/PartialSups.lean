/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Order.PartialSups

/-!
# Continuity of `partialSups`

In this file we prove that `partialSups` of a sequence of continuous functions is continuous
as well as versions for `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, and `ContinuousOn`.
-/

public section

open Filter
open scoped Topology

variable {L : Type*} [SemilatticeSup L] [TopologicalSpace L] [ContinuousSup L]

namespace Filter.Tendsto

variable {α : Type*} {l : Filter α} {f : Nat -> α -> L} {g : Nat -> L} {n : Nat}

/--
lemma `partialSups` / 引理 `partialSups`

English:
lemma partialSups
  given: (hf : forall k <= n, Tendsto (f k) l (𝓝 (g k)))
  proof: by
  simp only [partialSups_eq_sup'_range]
  refine finset_sup'_nhds _ ?_
  simpa [Nat.lt_succ_iff]

中文:
引理 partialSups
  条件: (hf : 对任意 k <= n, Tendsto (f k) l (𝓝 (g k)))
  证明: by
  simp only [partialSups_eq_sup'_range]
  refine finset_sup'_nhds _ ?_
  simpa [Nat.lt_succ_iff]
-/
protected lemma partialSups (hf : forall k <= n, Tendsto (f k) l (𝓝 (g k))) :
    Tendsto (partialSups f n) l (𝓝 (partialSups g n)) := by
  simp only [partialSups_eq_sup'_range]
  refine finset_sup'_nhds _ ?_
  simpa [Nat.lt_succ_iff]

/--
lemma `partialSups_apply` / 引理 `partialSups_apply`

English:
lemma partialSups_apply
  given: (hf : forall k <= n, Tendsto (f k) l (𝓝 (g k)))
  proof: by
  simpa only [← Pi.partialSups_apply] using Tendsto.partialSups hf

中文:
引理 partialSups_apply
  条件: (hf : 对任意 k <= n, Tendsto (f k) l (𝓝 (g k)))
  证明: by
  simpa only [← Pi.partialSups_apply] using Tendsto.partialSups hf
-/
protected lemma partialSups_apply (hf : forall k <= n, Tendsto (f k) l (𝓝 (g k))) :
    Tendsto (fun a => partialSups (f · a) n) l (𝓝 (partialSups g n)) := by
  simpa only [← Pi.partialSups_apply] using Tendsto.partialSups hf

end Filter.Tendsto

variable {X : Type*} [TopologicalSpace X] {f : Nat -> X -> L} {n : Nat} {s : Set X} {x : X}

/--
lemma `ContinuousAt.partialSups_apply` / 引理 `ContinuousAt.partialSups_apply`

English:
lemma ContinuousAt.partialSups_apply
  given: (hf : forall k <= n, ContinuousAt (f k) x)
  proof: Tendsto.partialSups_apply hf

中文:
引理 ContinuousAt.partialSups_apply
  条件: (hf : 对任意 k <= n, ContinuousAt (f k) x)
  证明: Tendsto.partialSups_apply hf
-/
protected lemma ContinuousAt.partialSups_apply (hf : forall k <= n, ContinuousAt (f k) x) :
    ContinuousAt (fun a => partialSups (f · a) n) x :=
  Tendsto.partialSups_apply hf

/--
lemma `ContinuousAt.partialSups` / 引理 `ContinuousAt.partialSups`

English:
lemma ContinuousAt.partialSups
  given: (hf : forall k <= n, ContinuousAt (f k) x)
  proof: by
  simpa only [← Pi.partialSups_apply] using ContinuousAt.partialSups_apply hf

中文:
引理 ContinuousAt.partialSups
  条件: (hf : 对任意 k <= n, ContinuousAt (f k) x)
  证明: by
  simpa only [← Pi.partialSups_apply] using ContinuousAt.partialSups_apply hf
-/
protected lemma ContinuousAt.partialSups (hf : forall k <= n, ContinuousAt (f k) x) :
    ContinuousAt (partialSups f n) x := by
  simpa only [← Pi.partialSups_apply] using ContinuousAt.partialSups_apply hf

/--
lemma `ContinuousWithinAt.partialSups_apply` / 引理 `ContinuousWithinAt.partialSups_apply`

English:
lemma ContinuousWithinAt.partialSups_apply
  given: (hf : forall k <= n, ContinuousWithinAt (f k) s x)
  proof: Tendsto.partialSups_apply hf

中文:
引理 ContinuousWithinAt.partialSups_apply
  条件: (hf : 对任意 k <= n, ContinuousWithinAt (f k) s x)
  证明: Tendsto.partialSups_apply hf
-/
protected lemma ContinuousWithinAt.partialSups_apply (hf : forall k <= n, ContinuousWithinAt (f k) s x) :
    ContinuousWithinAt (fun a => partialSups (f · a) n) s x :=
  Tendsto.partialSups_apply hf

/--
lemma `ContinuousWithinAt.partialSups` / 引理 `ContinuousWithinAt.partialSups`

English:
lemma ContinuousWithinAt.partialSups
  given: (hf : forall k <= n, ContinuousWithinAt (f k) s x)
  proof: by
  simpa only [← Pi.partialSups_apply] using ContinuousWithinAt.partialSups_apply hf

中文:
引理 ContinuousWithinAt.partialSups
  条件: (hf : 对任意 k <= n, ContinuousWithinAt (f k) s x)
  证明: by
  simpa only [← Pi.partialSups_apply] using ContinuousWithinAt.partialSups_apply hf
-/
protected lemma ContinuousWithinAt.partialSups (hf : forall k <= n, ContinuousWithinAt (f k) s x) :
    ContinuousWithinAt (partialSups f n) s x := by
  simpa only [← Pi.partialSups_apply] using ContinuousWithinAt.partialSups_apply hf

/--
lemma `ContinuousOn.partialSups_apply` / 引理 `ContinuousOn.partialSups_apply`

English:
lemma ContinuousOn.partialSups_apply
  given: (hf : forall k <= n, ContinuousOn (f k) s)
  proof: fun x hx =>
  ContinuousWithinAt.partialSups_apply fun k hk => hf k hk x hx

中文:
引理 ContinuousOn.partialSups_apply
  条件: (hf : 对任意 k <= n, ContinuousOn (f k) s)
  证明: fun x hx =>
  ContinuousWithinAt.partialSups_apply fun k hk => hf k hk x hx
-/
protected lemma ContinuousOn.partialSups_apply (hf : forall k <= n, ContinuousOn (f k) s) :
    ContinuousOn (fun a => partialSups (f · a) n) s := fun x hx =>
  ContinuousWithinAt.partialSups_apply fun k hk => hf k hk x hx

/--
lemma `ContinuousOn.partialSups` / 引理 `ContinuousOn.partialSups`

English:
lemma ContinuousOn.partialSups
  given: (hf : forall k <= n, ContinuousOn (f k) s)
  proof: fun x hx =>
  ContinuousWithinAt.partialSups fun k hk => hf k hk x hx

中文:
引理 ContinuousOn.partialSups
  条件: (hf : 对任意 k <= n, ContinuousOn (f k) s)
  证明: fun x hx =>
  ContinuousWithinAt.partialSups fun k hk => hf k hk x hx
-/
protected lemma ContinuousOn.partialSups (hf : forall k <= n, ContinuousOn (f k) s) :
    ContinuousOn (partialSups f n) s := fun x hx =>
  ContinuousWithinAt.partialSups fun k hk => hf k hk x hx

/--
lemma `Continuous.partialSups_apply` / 引理 `Continuous.partialSups_apply`

English:
lemma Continuous.partialSups_apply
  given: (hf : forall k <= n, Continuous (f k))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.partialSups_apply fun k hk =>
    (hf k hk).continuousAt

中文:
引理 Continuous.partialSups_apply
  条件: (hf : 对任意 k <= n, Continuous (f k))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.partialSups_apply fun k hk =>
    (hf k hk).continuousAt
-/
protected lemma Continuous.partialSups_apply (hf : forall k <= n, Continuous (f k)) :
    Continuous (fun a => partialSups (f · a) n) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.partialSups_apply fun k hk =>
    (hf k hk).continuousAt

/--
lemma `Continuous.partialSups` / 引理 `Continuous.partialSups`

English:
lemma Continuous.partialSups
  given: (hf : forall k <= n, Continuous (f k))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.partialSups fun k hk => (hf k hk).continuousAt

中文:
引理 Continuous.partialSups
  条件: (hf : 对任意 k <= n, Continuous (f k))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.partialSups fun k hk => (hf k hk).continuousAt
-/
protected lemma Continuous.partialSups (hf : forall k <= n, Continuous (f k)) :
    Continuous (partialSups f n) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.partialSups fun k hk => (hf k hk).continuousAt
