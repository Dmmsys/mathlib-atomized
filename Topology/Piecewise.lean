/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
### Continuity of piecewise defined functions
-/

public section

open Set Filter Function Topology Filter

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  {f g : α -> β} {s s' t : Set α} {x : α}


@[simp]
/--
theorem `continuousWithinAt_update_same` / 定理 `continuousWithinAt_update_same`

English:
theorem continuousWithinAt_update_same
  given: [DecidableEq α] {y : β}
  proof: calc
    ContinuousWithinAt (update f x y) s x ↔ Tendsto (update f x y) (𝓝[s \ {x}] x) (𝓝 y) := by
    { rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, update_self] }
    _ ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
tendsto_congr' eventually_nhdsWithin_iff.2 Eventually.of_forall
        fun _ hz 

中文:
定理 continuousWithinAt_update_same
  条件: [DecidableEq α] {y : β}
  证明: calc
    ContinuousWithinAt (update f x y) s x ↔ Tendsto (update f x y) (𝓝[s \ {x}] x) (𝓝 y) := by
    { rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, update_self] }
    _ ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
tendsto_congr' eventually_nhdsWithin_iff.2 Eventually.of_forall
        fun _ hz 

Depends on / 依赖: ContinuousWithinAt, Eventually, Eventually.of_forall, Tendsto, continuousWithinAt_sdiff_self, eventually_nhdsWithin_iff, of_forall, tendsto_congr, update, update_of_ne, update_self
-/
theorem continuousWithinAt_update_same [DecidableEq α] {y : β} :
    ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
  calc
    ContinuousWithinAt (update f x y) s x ↔ Tendsto (update f x y) (𝓝[s \ {x}] x) (𝓝 y) := by
    { rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, update_self] }
    _ ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
tendsto_congr' eventually_nhdsWithin_iff.2 Eventually.of_forall
        fun _ hz => update_of_ne hz.2 ..

@[simp]
/--
theorem `continuousAt_update_same` / 定理 `continuousAt_update_same`

English:
theorem continuousAt_update_same
  given: [DecidableEq α] {y : β}
  proof: by
  rw [← continuousWithinAt_univ]; rw [continuousWithinAt_update_same]; rw [compl_eq_univ_sdiff]

中文:
定理 continuousAt_update_same
  条件: [DecidableEq α] {y : β}
  证明: by
  rw [← continuousWithinAt_univ]; rw [continuousWithinAt_update_same]; rw [compl_eq_univ_sdiff]

Depends on / 依赖: compl_eq_univ_sdiff, continuousWithinAt_univ, continuousWithinAt_update_same
-/
theorem continuousAt_update_same [DecidableEq α] {y : β} :
    ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[!=] x) (𝓝 y) := by
  rw [← continuousWithinAt_univ]; rw [continuousWithinAt_update_same]; rw [compl_eq_univ_sdiff]

/--
theorem `ContinuousOn.if'` / 定理 `ContinuousOn.if'`

English:
theorem ContinuousOn.if'
  statement: {s : Set α} {p : α -> Prop} {f g : α -> β} [forall a, Decidable (p a)]
  proof: by
  intro x hx
  by_cases hx' : x in frontier { a | p a }
  · exact (hpf x ⟨hx, hx'⟩).piecewise_nhdsWithin (hpg x ⟨hx, hx'⟩)
  · rw [← inter_univ s, ← union_compl_self { a | p a }, inter_union_distrib_left] at hx ⊢
    rcases hx with hx | hx
    · apply ContinuousWithinAt.union
      · exact (hf x 

中文:
定理 ContinuousOn.if'
  结论: {s : 集合 α} {p : α -> 命题} {f g : α -> β} [对任意 a, 可判定 (p a)]
  证明: by
  intro x hx
  by_cases hx' : x in frontier { a | p a }
  · exact (hpf x ⟨hx, hx'⟩).piecewise_nhdsWithin (hpg x ⟨hx, hx'⟩)
  · rw [← inter_univ s, ← union_compl_self { a | p a }, inter_union_distrib_left] at hx ⊢
    rcases hx with hx | hx
    · apply ContinuousWithinAt.union
      · exact (hf x 

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.union, closure, closure_compl, closure_inter, continuousWithinAt_of_notMem_closure, frontier, if_pos, inter_union_distrib_left, inter_univ, piecewise_nhdsWithin, subset_closure, union_compl_self
-/
theorem ContinuousOn.if' {s : Set α} {p : α -> Prop} {f g : α -> β} [forall a, Decidable (p a)]
    (hpf : forall a in s inter frontier { a | p a },
      Tendsto f (𝓝[s inter { a | p a }] a) (𝓝 <| if p a then f a else g a))
    (hpg :
      forall a in s inter frontier { a | p a },
        Tendsto g (𝓝[s inter { a | ¬p a }] a) (𝓝 <| if p a then f a else g a))
    (hf : ContinuousOn f <| s inter { a | p a }) (hg : ContinuousOn g <| s inter { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s := by
  intro x hx
  by_cases hx' : x in frontier { a | p a }
  · exact (hpf x ⟨hx, hx'⟩).piecewise_nhdsWithin (hpg x ⟨hx, hx'⟩)
  · rw [← inter_univ s, ← union_compl_self { a | p a }, inter_union_distrib_left] at hx ⊢
    rcases hx with hx | hx
    · apply ContinuousWithinAt.union
      · exact (hf x hx).congr (fun y hy => if_pos hy.2) (if_pos hx.2)
      · have : x ∉ closure { a | p a }ᶜ := fun h => hx' ⟨subset_closure hx.2, by
          rwa [closure_compl] at h⟩
        exact continuousWithinAt_of_notMem_closure fun h =>
          this (closure_inter_subset_inter_closure _ _ h).2
    · apply ContinuousWithinAt.union
      · have : x ∉ closure { a | p a } := fun h =>
          hx' ⟨h, fun h' : x in interior { a | p a } => hx.2 (interior_subset h')⟩
        exact continuousWithinAt_of_notMem_closure fun h =>
          this (closure_inter_subset_inter_closure _ _ h).2
      · exact (hg x hx).congr (fun y hy => if_neg hy.2) (if_neg hx.2)

/--
theorem `ContinuousOn.piecewise'` / 定理 `ContinuousOn.piecewise'`

English:
theorem ContinuousOn.piecewise'
  statement: [forall a, Decidable (a in t)]
  proof: hf.if' hpf hpg hg

中文:
定理 ContinuousOn.piecewise'
  结论: [对任意 a, 可判定 (a in t)]
  证明: hf.if' hpf hpg hg

Depends on / 依赖: hf.if
-/
theorem ContinuousOn.piecewise' [forall a, Decidable (a in t)]
    (hpf : forall a in s inter frontier t, Tendsto f (𝓝[s inter t] a) (𝓝 (piecewise t f g a)))
    (hpg : forall a in s inter frontier t, Tendsto g (𝓝[s inter tᶜ] a) (𝓝 (piecewise t f g a)))
    (hf : ContinuousOn f <| s inter t) (hg : ContinuousOn g <| s inter tᶜ) :
    ContinuousOn (piecewise t f g) s :=
  hf.if' hpf hpg hg

/--
theorem `ContinuousOn.if` / 定理 `ContinuousOn.if`

English:
theorem ContinuousOn.if
  statement: {p : α -> Prop} [forall a, Decidable (p a)]
  proof: by
  apply ContinuousOn.if'
  · rintro a ha
    simp only [← hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    exact hf a ⟨ha.1, ha.2.1⟩
  · rintro a ha
    simp only [hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inte

中文:
定理 ContinuousOn.if
  结论: {p : α -> 命题} [对任意 a, 可判定 (p a)]
  证明: by
  apply ContinuousOn.if'
  · rintro a ha
    simp only [← hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    exact hf a ⟨ha.1, ha.2.1⟩
  · rintro a ha
    simp only [hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inte

Depends on / 依赖: ContinuousOn, ContinuousOn.if, closure_compl, hf.mono, hg.mono, inter_subset_inter_righ, inter_subset_inter_right, ite_self, mem_compl_iff, subset_closure, tendsto_nhdsWithin_mono_left
-/
theorem ContinuousOn.if {p : α -> Prop} [forall a, Decidable (p a)]
    (hp : forall a in s inter frontier { a | p a }, f a = g a)
    (hf : ContinuousOn f <| s inter closure { a | p a })
    (hg : ContinuousOn g <| s inter closure { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s := by
  apply ContinuousOn.if'
  · rintro a ha
    simp only [← hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    exact hf a ⟨ha.1, ha.2.1⟩
  · rintro a ha
    simp only [hp a ha, ite_self]
    apply tendsto_nhdsWithin_mono_left (inter_subset_inter_right s subset_closure)
    rcases ha with ⟨has, ⟨_, ha⟩⟩
    rw [← mem_compl_iff]; rw [← closure_compl] at ha
    apply hg a ⟨has, ha⟩
  · exact hf.mono (inter_subset_inter_right s subset_closure)
  · exact hg.mono (inter_subset_inter_right s subset_closure)

/--
theorem `ContinuousOn.piecewise` / 定理 `ContinuousOn.piecewise`

English:
theorem ContinuousOn.piecewise
  statement: [forall a, Decidable (a in t)]
  proof: hf.if ht hg

中文:
定理 ContinuousOn.piecewise
  结论: [对任意 a, 可判定 (a in t)]
  证明: hf.if ht hg

Depends on / 依赖: hf.if
-/
theorem ContinuousOn.piecewise [forall a, Decidable (a in t)]
    (ht : forall a in s inter frontier t, f a = g a) (hf : ContinuousOn f <| s inter closure t)
    (hg : ContinuousOn g <| s inter closure tᶜ) : ContinuousOn (piecewise t f g) s :=
  hf.if ht hg

/--
theorem `continuous_if'` / 定理 `continuous_if'`

English:
theorem continuous_if'
  statement: {p : α -> Prop} [forall a, Decidable (p a)]
  proof: by
  rw [← continuousOn_univ]
  apply ContinuousOn.if' <;> simpa

中文:
定理 continuous_if'
  结论: {p : α -> 命题} [对任意 a, 可判定 (p a)]
  证明: by
  rw [← continuousOn_univ]
  apply ContinuousOn.if' <;> simpa

Depends on / 依赖: ContinuousOn, ContinuousOn.if, continuousOn_univ
-/
theorem continuous_if' {p : α -> Prop} [forall a, Decidable (p a)]
    (hpf : forall a in frontier { x | p x }, Tendsto f (𝓝[{ x | p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hpg : forall a in frontier { x | p x }, Tendsto g (𝓝[{ x | ¬p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hf : ContinuousOn f { x | p x }) (hg : ContinuousOn g { x | ¬p x }) :
    Continuous fun a => ite (p a) (f a) (g a) := by
  rw [← continuousOn_univ]
  apply ContinuousOn.if' <;> simpa

/--
theorem `continuous_if` / 定理 `continuous_if`

English:
theorem continuous_if
  statement: {p : α -> Prop} [forall a, Decidable (p a)]
  proof: by
  rw [← continuousOn_univ]
  apply ContinuousOn.if <;> simpa

中文:
定理 continuous_if
  结论: {p : α -> 命题} [对任意 a, 可判定 (p a)]
  证明: by
  rw [← continuousOn_univ]
  apply ContinuousOn.if <;> simpa

Depends on / 依赖: ContinuousOn, ContinuousOn.if, continuousOn_univ
-/
theorem continuous_if {p : α -> Prop} [forall a, Decidable (p a)]
    (hp : forall a in frontier { x | p x }, f a = g a) (hf : ContinuousOn f (closure { x | p x }))
    (hg : ContinuousOn g (closure { x | ¬p x })) :
    Continuous fun a => if p a then f a else g a := by
  rw [← continuousOn_univ]
  apply ContinuousOn.if <;> simpa

/--
theorem `Continuous.if` / 定理 `Continuous.if`

English:
theorem Continuous.if
  statement: {p : α -> Prop} [forall a, Decidable (p a)]
  proof: continuous_if hp hf.continuousOn hg.continuousOn

中文:
定理 连续.if
  结论: {p : α -> 命题} [对任意 a, 可判定 (p a)]
  证明: continuous_if hp hf.continuousOn hg.continuousOn

Depends on / 依赖: continuousOn, continuous_if, hf.continuousOn, hg.continuousOn
-/
theorem Continuous.if {p : α -> Prop} [forall a, Decidable (p a)]
    (hp : forall a in frontier { x | p x }, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => if p a then f a else g a :=
  continuous_if hp hf.continuousOn hg.continuousOn

/--
theorem `continuous_if_const` / 定理 `continuous_if_const`

English:
theorem continuous_if_const
  statement: (p : Prop) [Decidable p] (hf : p -> Continuous f)
  proof: by
  split_ifs with h
  exacts [hf h, hg h]

中文:
定理 continuous_if_const
  结论: (p : 命题) [可判定 p] (hf : p -> 连续 f)
  证明: by
  split_ifs with h
  exacts [hf h, hg h]

Depends on / 依赖: exacts, split_ifs
-/
theorem continuous_if_const (p : Prop) [Decidable p] (hf : p -> Continuous f)
    (hg : ¬p -> Continuous g) : Continuous fun a => if p then f a else g a := by
  split_ifs with h
  exacts [hf h, hg h]

/--
theorem `Continuous.if_const` / 定理 `Continuous.if_const`

English:
theorem Continuous.if_const
  statement: (p : Prop) [Decidable p] (hf : Continuous f)
  proof: continuous_if_const p (fun _ => hf) fun _ => hg

中文:
定理 连续.if_const
  结论: (p : 命题) [可判定 p] (hf : 连续 f)
  证明: continuous_if_const p (fun _ => hf) fun _ => hg

Depends on / 依赖: continuous_if_const
-/
theorem Continuous.if_const (p : Prop) [Decidable p] (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a => if p then f a else g a :=
  continuous_if_const p (fun _ => hf) fun _ => hg

/--
theorem `continuous_piecewise` / 定理 `continuous_piecewise`

English:
theorem continuous_piecewise
  statement: [forall a, Decidable (a in s)]
  proof: continuous_if hs hf hg

中文:
定理 continuous_piecewise
  结论: [对任意 a, 可判定 (a in s)]
  证明: continuous_if hs hf hg

Depends on / 依赖: continuous_if
-/
theorem continuous_piecewise [forall a, Decidable (a in s)]
    (hs : forall a in frontier s, f a = g a) (hf : ContinuousOn f (closure s))
    (hg : ContinuousOn g (closure sᶜ)) : Continuous (piecewise s f g) :=
  continuous_if hs hf hg

/--
theorem `Continuous.piecewise` / 定理 `Continuous.piecewise`

English:
theorem Continuous.piecewise
  statement: [forall a, Decidable (a in s)]
  proof: hf.if hs hg

中文:
定理 连续.piecewise
  结论: [对任意 a, 可判定 (a in s)]
  证明: hf.if hs hg

Depends on / 依赖: hf.if
-/
theorem Continuous.piecewise [forall a, Decidable (a in s)]
    (hs : forall a in frontier s, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous (piecewise s f g) :=
  hf.if hs hg

/--
theorem `IsOpen.ite'` / 定理 `IsOpen.ite'`

English:
theorem IsOpen.ite'
  statement: (hs : IsOpen s) (hs' : IsOpen s')
  proof: by
  classical
    simp only [isOpen_iff_continuous_mem, Set.ite] at *
    convert!
      continuous_piecewise (fun x hx => propext (ht x hx)) hs.continuousOn hs'.continuousOn using 2
    rename_i x
    by_cases hx : x in t <;> simp [hx]

中文:
定理 是开集.ite'
  结论: (hs : 是开集 s) (hs' : 是开集 s')
  证明: by
  classical
    simp only [isOpen_iff_continuous_mem, Set.ite] at *
    convert!
      continuous_piecewise (fun x hx => propext (ht x hx)) hs.continuousOn hs'.continuousOn using 2
    rename_i x
    by_cases hx : x in t <;> simp [hx]

Depends on / 依赖: Set.ite, classical, continuousOn, continuous_piecewise, convert, hs.continuousOn, isOpen_iff_continuous_mem, propext, rename_i
-/
theorem IsOpen.ite' (hs : IsOpen s) (hs' : IsOpen s')
    (ht : forall x in frontier t, x in s ↔ x in s') : IsOpen (t.ite s s') := by
  classical
    simp only [isOpen_iff_continuous_mem, Set.ite] at *
    convert!
      continuous_piecewise (fun x hx => propext (ht x hx)) hs.continuousOn hs'.continuousOn using 2
    rename_i x
    by_cases hx : x in t <;> simp [hx]

/--
theorem `IsOpen.ite` / 定理 `IsOpen.ite`

English:
theorem IsOpen.ite
  statement: (hs : IsOpen s) (hs' : IsOpen s')
  proof: hs.ite' hs' fun x hx => by simpa [hx] using Set.ext_iff.1 ht x

中文:
定理 是开集.ite
  结论: (hs : 是开集 s) (hs' : 是开集 s')
  证明: hs.ite' hs' fun x hx => by simpa [hx] using Set.ext_iff.1 ht x

Depends on / 依赖: Set.ext_iff, ext_iff, hs.ite
-/
theorem IsOpen.ite (hs : IsOpen s) (hs' : IsOpen s')
    (ht : s inter frontier t = s' inter frontier t) : IsOpen (t.ite s s') :=
  hs.ite' hs' fun x hx => by simpa [hx] using Set.ext_iff.1 ht x

/--
theorem `ite_inter_closure_eq_of_inter_frontier_eq` / 定理 `ite_inter_closure_eq_of_inter_frontier_eq`

English:
theorem ite_inter_closure_eq_of_inter_frontier_eq
  proof: by
  rw [closure_eq_self_union_frontier]; rw [inter_union_distrib_left]; rw [inter_union_distrib_left]; rw [ite_inter_self]; rw [ite_inter_of_inter_eq _ ht]

中文:
定理 ite_inter_closure_eq_of_inter_frontier_eq
  证明: by
  rw [closure_eq_self_union_frontier]; rw [inter_union_distrib_left]; rw [inter_union_distrib_left]; rw [ite_inter_self]; rw [ite_inter_of_inter_eq _ ht]

Depends on / 依赖: closure_eq_self_union_frontier, inter_union_distrib_left, ite_inter_of_inter_eq, ite_inter_self
-/
theorem ite_inter_closure_eq_of_inter_frontier_eq
    (ht : s inter frontier t = s' inter frontier t) : t.ite s s' inter closure t = s inter closure t := by
  rw [closure_eq_self_union_frontier]; rw [inter_union_distrib_left]; rw [inter_union_distrib_left]; rw [ite_inter_self]; rw [ite_inter_of_inter_eq _ ht]

/--
theorem `ite_inter_closure_compl_eq_of_inter_frontier_eq` / 定理 `ite_inter_closure_compl_eq_of_inter_frontier_eq`

English:
theorem ite_inter_closure_compl_eq_of_inter_frontier_eq
  proof: by
  rw [← ite_compl]; rw [ite_inter_closure_eq_of_inter_frontier_eq]
  rwa [frontier_compl, eq_comm]

中文:
定理 ite_inter_closure_compl_eq_of_inter_frontier_eq
  证明: by
  rw [← ite_compl]; rw [ite_inter_closure_eq_of_inter_frontier_eq]
  rwa [frontier_compl, eq_comm]

Depends on / 依赖: eq_comm, frontier_compl, ite_compl, ite_inter_closure_eq_of_inter_frontier_eq
-/
theorem ite_inter_closure_compl_eq_of_inter_frontier_eq
    (ht : s inter frontier t = s' inter frontier t) : t.ite s s' inter closure tᶜ = s' inter closure tᶜ := by
  rw [← ite_compl]; rw [ite_inter_closure_eq_of_inter_frontier_eq]
  rwa [frontier_compl, eq_comm]

/--
theorem `continuousOn_piecewise_ite'` / 定理 `continuousOn_piecewise_ite'`

English:
theorem continuousOn_piecewise_ite'
  statement: [forall x, Decidable (x in t)]
  proof: by
  apply ContinuousOn.piecewise
  · rwa [ite_inter_of_inter_eq _ H]
  · rwa [ite_inter_closure_eq_of_inter_frontier_eq H]
  · rwa [ite_inter_closure_compl_eq_of_inter_frontier_eq H]

中文:
定理 continuousOn_piecewise_ite'
  结论: [对任意 x, 可判定 (x in t)]
  证明: by
  apply ContinuousOn.piecewise
  · rwa [ite_inter_of_inter_eq _ H]
  · rwa [ite_inter_closure_eq_of_inter_frontier_eq H]
  · rwa [ite_inter_closure_compl_eq_of_inter_frontier_eq H]

Depends on / 依赖: ContinuousOn, ContinuousOn.piecewise, ite_inter_closure_compl_eq_of_inter_frontier_eq, ite_inter_closure_eq_of_inter_frontier_eq, ite_inter_of_inter_eq, piecewise
-/
theorem continuousOn_piecewise_ite' [forall x, Decidable (x in t)]
    (h : ContinuousOn f (s inter closure t)) (h' : ContinuousOn g (s' inter closure tᶜ))
    (H : s inter frontier t = s' inter frontier t) (Heq : EqOn f g (s inter frontier t)) :
    ContinuousOn (t.piecewise f g) (t.ite s s') := by
  apply ContinuousOn.piecewise
  · rwa [ite_inter_of_inter_eq _ H]
  · rwa [ite_inter_closure_eq_of_inter_frontier_eq H]
  · rwa [ite_inter_closure_compl_eq_of_inter_frontier_eq H]

/--
theorem `continuousOn_piecewise_ite` / 定理 `continuousOn_piecewise_ite`

English:
theorem continuousOn_piecewise_ite
  statement: [forall x, Decidable (x in t)]
  proof: continuousOn_piecewise_ite' (h.mono inter_subset_left) (h'.mono inter_subset_left) H Heq

中文:
定理 continuousOn_piecewise_ite
  结论: [对任意 x, 可判定 (x in t)]
  证明: continuousOn_piecewise_ite' (h.mono inter_subset_left) (h'.mono inter_subset_left) H Heq

Depends on / 依赖: continuousOn_piecewise_ite, h.mono, inter_subset_left
-/
theorem continuousOn_piecewise_ite [forall x, Decidable (x in t)]
    (h : ContinuousOn f s) (h' : ContinuousOn g s') (H : s inter frontier t = s' inter frontier t)
    (Heq : EqOn f g (s inter frontier t)) : ContinuousOn (t.piecewise f g) (t.ite s s') :=
  continuousOn_piecewise_ite' (h.mono inter_subset_left) (h'.mono inter_subset_left) H Heq
